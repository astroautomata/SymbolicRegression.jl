import DynExpr.NodeUtils.Success
import SymReg.Templates.Structure

/-!
Scalar constants of template and composable expressions:
`get_scalar_constants`/`set_scalar_constants!` (`src/TemplateExpression.jl:440-484`),
`get_optimizable_parameters`/`set_optimizable_parameters!` (lines 486-508), and the composable
forwards (`src/ComposableExpression.jl:103-108,131-136`). Inner trees use DE's node getter and
setter (`DynExpr.NodeUtils.getScalarConstants`, `setScalarConstants`) on one shared node heap;
parameter vectors use DE's scalar `pack`/`unpack` (`DynExpr.NodeUtils.packScalar`, `unpackScalar`).
-/

namespace SymReg.Templates
open DynExpr DynExpr.NodeUtils

structure ParameterCodec (V S : Type) where
  width : V → Nat
  pack : List (Option S) → Nat → V → Jl (Nat × List (Option S))
  unpack : List S → Nat → V → Jl (Nat × V)

def scalarParameterCodec (T : Type) : ParameterCodec T T where
  width := fun _ => 1
  pack := fun buf i v => packScalar buf i (some v)
  unpack := fun buf i _ => unpackScalar buf i

/-- Parameter keys carry backing array addresses. Two keys can name the same array. -/
structure TConst (T : Type) (V : Type := T) where
  g : Graph T
  roots : List Addr
  paramRefs : List Nat
  params : Nat → Option (List V)
  hasParams : Bool
  codec : ParameterCodec V T

/-- `(; n=length(first(c_ref)), ref=last(c_ref))`, `src/TemplateExpression.jl:465`. -/
structure TRefs where
  n : Nat
  ref : List Addr
  deriving DecidableEq, Repr

/-- A Julia call that mutates its arguments in place: the result or exception, together with
the mutated state, which persists after an exception. -/
inductive Res (S α : Type) (E : Type := JlError) where
  | ok (a : α) (s : S)
  | err (e : E) (s : S)

-- Source: src/TemplateExpression.jl:440-447
/-
function _pack_parameters(p::ParamVector{T}) where {T}
    buffer = Vector{DE.get_number_type(T)}(undef, DE.count_scalar_constants(p))
    idx = firstindex(buffer)
    for value in p._data
        idx = DE.pack_scalar_constants!(buffer, idx, value)
    end
    return buffer
end
-/
def packParam {T V : Type} (codec : ParameterCodec V T) (p : List V) : Jl (List T) := do
  let (_, slots) ← p.foldlM (fun (i, buf) v => codec.pack buf i v)
    (1, List.replicate (p.map codec.width).sum none)
  slots.mapM fun
    | some v => .ok v
    | none => .error .undefRefError

-- Source: src/TemplateExpression.jl:454-467
/-
function DE.get_scalar_constants(e::TemplateExpression)
    # Get constants for each inner expression
    consts_and_refs = map(DE.get_scalar_constants, values(get_contents(e)))
    parameter_chunks = if has_params(e)
        map(_pack_parameters, values(get_metadata(e).parameters))
    else
        ()
    end
    flat_constants = vcat(map(first, consts_and_refs)..., parameter_chunks...)
    # Collect info so we can put them back in the right place,
    # like the indexes of the constants in the flattened array
    refs = map(c_ref -> (; n=length(first(c_ref)), ref=last(c_ref)), consts_and_refs)
    return flat_constants, refs
end
-/
def templateGet {T V : Type} (fuel : Nat) (x : TConst T V) : Jl (List T × List TRefs) := do
  let cr ← x.roots.mapM (getScalarConstants x.g false fuel)
  let chunks ← if x.hasParams then x.paramRefs.mapM (fun a =>
      match x.params a with
      | none => .error .undefRefError
      | some p => packParam x.codec p) else pure []
  pure ((cr.map Prod.fst).flatten ++ chunks.flatten, cr.map fun p => ⟨p.1.length, p.2⟩)

/-- One-based `constants[i:(i + n - 1)]` (`src/TemplateExpression.jl:473`); an empty range is
always in bounds. -/
def slice {T : Type} (c : List T) (i n : Nat) : Jl (List T) :=
  if n = 0 then .ok []
  else if 1 ≤ i ∧ i + n - 1 ≤ c.length then .ok ((c.drop (i - 1)).take n)
  else .error .boundsError

/-- The `foreach` over `zip(values(get_contents(e)), refs)` with the cursor,
`src/TemplateExpression.jl:469-476`; each inner forwards to the node setter
(`src/ComposableExpression.jl:106-108`). -/
def setInners {T : Type} (c : List T) : List Addr → List TRefs → Nat → Graph T → Res (Graph T) Nat
  | _ :: rs, r :: refs, i, g =>
    match slice c i r.n with
    | .error e => .err e g
    | .ok cs =>
      match setScalarConstants g cs r.ref with
      | .error e => .err e g
      | .ok g' => setInners c rs refs (i + r.n) g'
  | _, _, i, g => .ok i g

-- Source: src/TemplateExpression.jl:448-453
/-
function _unpack_parameters!(p::ParamVector, constants, idx::Int)
    for i in eachindex(p._data)
        (idx, p._data[i]) = DE.unpack_scalar_constants(constants, idx, p._data[i])
    end
    return idx
end
-/
def unpackVec {T V : Type} (codec : ParameterCodec V T) (c : List T) :
    List V → List V → Nat → Res (List V) Nat
  | done, [], idx => .ok idx done
  | done, v :: rest, idx =>
    match codec.unpack c idx v with
    | .error e => .err e (done ++ v :: rest)
    | .ok (idx', w) => unpackVec codec c (done ++ [w]) rest idx'

-- Source: src/TemplateExpression.jl:477-482
def unpackAll {T V : Type} (codec : ParameterCodec V T) (c : List T) :
    List Nat → (Nat → Option (List V)) → Nat → Res (Nat → Option (List V)) Nat
  | [], arrays, idx => .ok idx arrays
  | a :: rest, arrays, idx =>
    match arrays a with
    | none => .err .undefRefError arrays
    | some p =>
      match unpackVec codec c [] p idx with
      | .err e p' => .err e (fun b => if b = a then some p' else arrays b)
      | .ok idx' p' =>
        unpackAll codec c rest (fun b => if b = a then some p' else arrays b) idx'

-- Source: src/TemplateExpression.jl:468-484
/-
function DE.set_scalar_constants!(e::TemplateExpression, constants, refs)
    cursor = Ref(1)
    foreach(values(get_contents(e)), refs) do tree, r
        n = r.n
        i = cursor[]
        c = constants[i:(i + n - 1)]
        DE.set_scalar_constants!(tree, c, r.ref)
        cursor[] = i + n
    end
    if has_params(e)
        parameters = get_metadata(e).parameters
        for k in keys(parameters)
            cursor[] = _unpack_parameters!(parameters[k], constants, cursor[])
        end
    end
    return e
end
-/
def templateSet {T V : Type} (x : TConst T V) (c : List T) (refs : List TRefs) :
    Res (TConst T V) Unit :=
  match setInners c x.roots refs 1 x.g with
  | .err e g => .err e { x with g := g }
  | .ok i g =>
    if x.hasParams then
      match unpackAll x.codec c x.paramRefs x.params i with
      | .err e ps => .err e { x with g := g, params := ps }
      | .ok _ ps => .ok () { x with g := g, params := ps }
    else .ok () { x with g := g }

/-- `TemplateOptimizableRefs`, `src/TemplateExpression.jl:486-489`. -/
structure TOptRefs where
  scalarRefs : List TRefs
  length : Nat
  deriving DecidableEq, Repr

/-- `get_optimizable_parameters(_context, ::TemplateExpression, _options)` and its combiner
dispatch, `src/TemplateExpression.jl:491-498`. -/
def optGet {T V : Type} (fuel : Nat) (x : TConst T V) : Jl (List T × TOptRefs) := do
  let (p, r) ← templateGet fuel x
  pure (p, ⟨r, p.length⟩)

-- Source: src/TemplateExpression.jl:499-508
/-
function CO.set_optimizable_parameters!(
    e::TemplateExpression, parameters, refs::TemplateOptimizableRefs
)
    length(parameters) == refs.length || throw(
        DimensionMismatch(
            "received $(length(parameters)) optimizable parameters but expected $(refs.length)",
        ),
    )
    return DE.set_scalar_constants!(e, parameters, refs.scalar_refs)
end
-/
def optSet {T V : Type} (x : TConst T V) (p : List T) (r : TOptRefs) : Res (TConst T V) Unit :=
  if p.length = r.length then templateSet x p r.scalarRefs
  else .err (.dimensionMismatch s!"received {p.length} optimizable parameters but expected {r.length}") x

/-! ## Heap lemmas for the node setter, for any scalar type -/

section Heap
variable {T : Type}

/-- The structure of a node cell, ignoring its value field. -/
def strip (c : Cell T) : Cell T := { c with val := none }

/-- Two heaps with the same allocated cells up to their value fields. -/
def Shape (g h : Graph T) : Prop := ∀ a, (g.cells a).map strip = (h.cells a).map strip

theorem Shape.refl (g : Graph T) : Shape g g := fun _ => rfl
theorem Shape.trans {g h k : Graph T} (a : Shape g h) (b : Shape h k) : Shape g k :=
  fun x => (a x).trans (b x)

theorem readValues_length (g : Graph T) :
    ∀ rs vs, readValues g rs = .ok vs → vs.length = rs.length := by
  intro rs
  induction rs with
  | nil => intro vs h; cases h; rfl
  | cons a rs ih =>
    intro vs h
    simp only [readValues] at h
    cases hr : g.read a with
    | error e => rw [hr] at h; cases h
    | ok c =>
      rw [hr, okBind] at h
      cases hv : c.val with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, okBind] at h
        cases hrs : readValues g rs with
        | error e => rw [hrs] at h; cases h
        | ok vs' => rw [hrs] at h; cases h; simp [ih vs' hrs]

theorem readValues_cells (g : Graph T) :
    ∀ rs vs, readValues g rs = .ok vs → ∀ a ∈ rs, ∃ c v, g.cells a = some c ∧ c.val = some v := by
  intro rs
  induction rs with
  | nil => simp
  | cons a rs ih =>
    intro vs h b hb
    simp only [readValues] at h
    cases hr : g.read a with
    | error e => rw [hr] at h; cases h
    | ok c =>
      rw [hr, okBind] at h
      cases hv : c.val with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, okBind] at h
        cases hrs : readValues g rs with
        | error e => rw [hrs] at h; cases h
        | ok vs' =>
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · refine ⟨c, v, ?_, hv⟩
            unfold Heap.read at hr; split at hr <;> simp_all
          · exact ih vs' hrs b hb

theorem readValues_append (g : Graph T) (a b : List Addr) :
    readValues g (a ++ b) = (do let x ← readValues g a; let y ← readValues g b; pure (x ++ y)) := by
  induction a with
  | nil =>
    simp only [List.nil_append, readValues, okBind]
    cases readValues g b <;> rfl
  | cons r a ih =>
    simp only [List.cons_append, readValues, ih]
    cases g.read r with
    | error e => rfl
    | ok c =>
      simp only [okBind]
      cases c.val with
      | none => rfl
      | some v =>
        simp only [okBind]
        cases readValues g a with
        | error e => rfl
        | ok x => cases readValues g b <;> rfl

theorem write_self (g : Heap α) (a : Addr) (c : α) (h : g.cells a = some c) :
    g.write a c = .ok g := by
  unfold Heap.write
  rw [dif_neg (by simp [h])]
  congr 1
  cases g
  simp only [Heap.mk.injEq, and_true]
  funext b
  by_cases hb : b = a
  · subst hb; simp_all
  · simp [hb]

theorem read_cells {g : Heap α} {a : Addr} {c : α} (h : g.read a = .ok c) : g.cells a = some c := by
  unfold Heap.read at h; split at h <;> simp_all

theorem setLoop_restore (g : Graph T) :
    ∀ rs vs, readValues g rs = .ok vs → setScalarConstantsLoop g vs rs = .ok g := by
  intro rs
  induction rs with
  | nil => intro vs h; cases h; rfl
  | cons a rs ih =>
    intro vs h
    simp only [readValues] at h
    cases hr : g.read a with
    | error e => rw [hr] at h; cases h
    | ok c =>
      rw [hr, okBind] at h
      cases hv : c.val with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, okBind] at h
        cases hrs : readValues g rs with
        | error e => rw [hrs] at h; cases h
        | ok vs' =>
          rw [hrs] at h; cases h
          have hcv : { c with val := some v } = c := by cases c; simp_all
          simp only [setScalarConstantsLoop, setValue, hr, okBind, hcv,
            write_self g a c (read_cells hr)]
          exact ih vs' hrs

theorem getSet_node (g : Graph T) (fuel r : Nat) (vs : List T) (rs : List Addr)
    (h : getScalarConstants g false fuel r = .ok (vs, rs)) : setScalarConstants g vs rs = .ok g := by
  simp only [getScalarConstants] at h
  cases hc : constantRefs g false fuel r [] with
  | error e => rw [hc] at h; cases h
  | ok p =>
    obtain ⟨refs, seen⟩ := p
    rw [hc, okBind] at h
    cases hv : readValues g refs with
    | error e => rw [hv] at h; cases h
    | ok v =>
      rw [hv] at h; cases h
      unfold setScalarConstants
      rw [if_pos (readValues_length g _ _ hv)]
      exact setLoop_restore g _ _ hv

theorem getScalar_parts (g : Graph T) (fuel r : Nat) (vs : List T) (rs : List Addr)
    (h : getScalarConstants g false fuel r = .ok (vs, rs)) :
    (∃ seen, constantRefs g false fuel r [] = .ok (rs, seen)) ∧ readValues g rs = .ok vs := by
  simp only [getScalarConstants] at h
  cases hc : constantRefs g false fuel r [] with
  | error e => rw [hc] at h; cases h
  | ok p =>
    obtain ⟨refs, seen⟩ := p
    rw [hc, okBind] at h
    cases hv : readValues g refs with
    | error e => rw [hv] at h; cases h
    | ok v => rw [hv] at h; cases h; exact ⟨⟨seen, rfl⟩, hv⟩

theorem setValue_shape (g h : Graph T) (a : Addr) (v : T) (hw : setValue g a v = .ok h) :
    Shape g h ∧ (∀ b, b ≠ a → h.read b = g.read b) ∧
      ∃ c : Cell T, h.cells a = some { c with val := some v } := by
  simp only [setValue] at hw
  cases hr : g.read a with
  | error e => rw [hr] at hw; cases hw
  | ok c =>
    rw [hr, okBind] at hw
    have hca := read_cells hr
    unfold Heap.write at hw
    rw [dif_neg (by simp [hca])] at hw
    cases hw
    refine ⟨?_, ?_, c, by simp⟩
    · intro b
      by_cases hb : b = a
      · subst hb; simp [hca, strip]
      · simp [hb]
    · intro b hb; simp [Heap.read, hb]

theorem setLoop_props (vs : List T) :
    ∀ (rs : List Addr) (g h : Graph T), setScalarConstantsLoop g vs rs = .ok h →
      Shape g h ∧ (∀ b, b ∉ rs → h.read b = g.read b) ∧ (rs.Nodup → readValues h rs = .ok vs) := by
  induction vs with
  | nil =>
    intro rs g h hw
    cases rs with
    | nil => cases hw; exact ⟨Shape.refl g, fun _ _ => rfl, fun _ => rfl⟩
    | cons a rs => simp [setScalarConstantsLoop] at hw
  | cons v vs ih =>
    intro rs g h hw
    cases rs with
    | nil => simp [setScalarConstantsLoop] at hw
    | cons a rs =>
      simp only [setScalarConstantsLoop] at hw
      cases hs : setValue g a v with
      | error e => rw [hs] at hw; cases hw
      | ok k =>
        rw [hs, okBind] at hw
        obtain ⟨sh1, fr1, c, hc⟩ := setValue_shape g k a v hs
        obtain ⟨sh2, fr2, rd2⟩ := ih rs k h hw
        refine ⟨sh1.trans sh2, ?_, ?_⟩
        · intro b hb
          rw [fr2 b (fun h => hb (by simp [h])), fr1 b (fun h => hb (by simp [h]))]
        · intro hn
          have hn' := List.nodup_cons.mp hn
          have ha : h.read a = .ok { c with val := some v } := by
            rw [fr2 a hn'.1]; simp [Heap.read, hc]
          simp [readValues, ha, rd2 hn'.2]

theorem setLoop_ok (g : Graph T) :
    ∀ (vs : List T) (rs : List Addr), vs.length = rs.length →
      (∀ a ∈ rs, ∃ c, g.cells a = some c) → ∃ h, setScalarConstantsLoop g vs rs = .ok h := by
  intro vs
  induction vs generalizing g with
  | nil => intro rs hl _; cases rs with
    | nil => exact ⟨g, rfl⟩
    | cons _ _ => simp at hl
  | cons v vs ih =>
    intro rs hl hal
    cases rs with
    | nil => simp at hl
    | cons a rs =>
      obtain ⟨c, hc⟩ := hal a (by simp)
      have hr : g.read a = .ok c := by simp [Heap.read, hc]
      have hw : ∃ k, setValue g a v = .ok k := by
        simp only [setValue, hr, okBind]
        unfold Heap.write; rw [dif_neg (by simp [hc])]; exact ⟨_, rfl⟩
      obtain ⟨k, hk⟩ := hw
      obtain ⟨sh, _, _⟩ := setValue_shape g k a v hk
      have hal' : ∀ b ∈ rs, ∃ c, k.cells b = some c := by
        intro b hb
        obtain ⟨cb, hcb⟩ := hal b (by simp [hb])
        have := sh b; rw [hcb] at this
        cases hkb : k.cells b with
        | none => rw [hkb] at this; cases this
        | some cb' => exact ⟨cb', rfl⟩
      obtain ⟨h, hh⟩ := ih k rs (by simpa using hl) hal'
      exact ⟨h, by simp [setScalarConstantsLoop, hk, hh]⟩

theorem Shape.cells {g h : Graph T} (s : Shape g h) {a : Addr} {c : Cell T} (hc : g.cells a = some c) :
    ∃ c', h.cells a = some c' ∧ strip c' = strip c := by
  have := s a; rw [hc] at this
  cases hh : h.cells a with
  | none => rw [hh] at this; cases this
  | some c' => rw [hh] at this; exact ⟨c', rfl, (Option.some.inj this).symm⟩

theorem strip_fields {c c' : Cell T} (h : strip c' = strip c) :
    c'.degree = c.degree ∧ c'.constant = c.constant ∧ c'.children = c.children := by
  have h1 := congrArg Cell.degree h
  have h2 := congrArg Cell.constant h
  have h3 := congrArg Cell.children h
  exact ⟨h1, h2, h3⟩

theorem constantRefs_shape {g h : Graph T} (s : Shape g h) (sharing : Bool) :
    ∀ fuel a seen, constantRefs g sharing fuel a seen = constantRefs h sharing fuel a seen := by
  intro fuel
  induction fuel with
  | zero => intro a seen; rfl
  | succ fuel ih =>
    intro a seen
    simp only [constantRefs]
    cases hg : g.cells a with
    | none =>
      have := s a; rw [hg] at this
      cases hh : h.cells a with
      | none => simp [Heap.read, hg, hh]
      | some _ => rw [hh] at this; cases this
    | some c =>
      obtain ⟨c', hh, hst⟩ := s.cells hg
      obtain ⟨hd, hc, hch⟩ := strip_fields hst
      simp only [Heap.read, hg, hh, okBind, hd, hc, hch, ih]

end Heap

/-! ## List lemmas -/

theorem slice_ok {T : Type} (c : List T) (m n : Nat) (h : m + n ≤ c.length) :
    slice c (m + 1) n = .ok ((c.drop m).take n) := by
  unfold slice
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_pos (by omega)]; simp

theorem take_split {T : Type} (c : List T) (m a b : Nat) :
    (c.drop m).take a ++ (c.drop (m + a)).take b = (c.drop m).take (a + b) := by
  rw [List.take_add, List.drop_drop]


/-- Restoring each inner's own values leaves the heap unchanged. -/
theorem setInners_restore {T : Type} (g : Graph T) (fuel : Nat) (c : List T) :
    ∀ (roots : List Addr) cr (pre post : List T),
      roots.mapM (getScalarConstants g false fuel) = .ok cr →
      c = pre ++ (cr.map Prod.fst).flatten ++ post →
      setInners c roots (cr.map fun p => ⟨p.1.length, p.2⟩) (pre.length + 1) g =
        .ok (pre.length + 1 + ((cr.map Prod.fst).map List.length).sum) g := by
  intro roots
  induction roots with
  | nil => intro cr pre post h _; cases h; simp [setInners]
  | cons r roots ih =>
    intro cr pre post h hc
    simp only [List.mapM_cons] at h
    cases hr : getScalarConstants g false fuel r with
    | error e => rw [hr] at h; cases h
    | ok p =>
      rw [hr, okBind] at h
      cases hrs : roots.mapM (getScalarConstants g false fuel) with
      | error e => rw [hrs] at h; cases h
      | ok cr' =>
        rw [hrs] at h; cases h
        obtain ⟨vs, rs⟩ := p
        have hs : slice c (pre.length + 1) vs.length = .ok vs := by
          rw [slice_ok c pre.length vs.length (by subst hc; simp)]
          subst hc; simp
        simp only [List.map_cons, setInners, hs, getSet_node g fuel r vs rs hr]
        have := ih cr' (pre ++ vs) post hrs (by subst hc; simp)
        simp only [List.length_append] at this
        rw [show pre.length + 1 + vs.length = pre.length + vs.length + 1 by omega, this]
        simp; omega

theorem readValues_frame {T : Type} (h g : Graph T) :
    ∀ rs : List Addr, (∀ a ∈ rs, h.read a = g.read a) → readValues h rs = readValues g rs := by
  intro rs
  induction rs with
  | nil => intro _; rfl
  | cons a rs ih =>
    intro hf
    simp only [readValues, hf a (by simp), ih (fun b hb => hf b (by simp [hb]))]

/-- Writing new values through all inner refs, assuming no constant node is shared. -/
theorem setInners_write {T : Type} (c : List T) :
    ∀ (crs : List (List T × List Addr)) (roots : List Addr) (m : Nat) (g : Graph T),
      roots.length = crs.length → (∀ p ∈ crs, p.1.length = p.2.length) →
      (∀ p ∈ crs, ∀ a ∈ p.2, ∃ cell, g.cells a = some cell) →
      (crs.flatMap Prod.snd).Nodup → m + ((crs.map Prod.fst).map List.length).sum ≤ c.length →
      ∃ h, setInners c roots (crs.map fun p => ⟨p.1.length, p.2⟩) (m + 1) g =
          .ok (m + 1 + ((crs.map Prod.fst).map List.length).sum) h ∧ Shape g h ∧
        (∀ b, b ∉ crs.flatMap Prod.snd → h.read b = g.read b) ∧
        readValues h (crs.flatMap Prod.snd) = .ok ((c.drop m).take ((crs.map Prod.fst).map List.length).sum) := by
  intro crs
  induction crs with
  | nil =>
    intro roots m g _ _ _ _ _
    exact ⟨g, by cases roots <;> simp [setInners], Shape.refl g, fun _ _ => rfl, by simp; rfl⟩
  | cons p crs ih =>
    intro roots m g hlen hpl hal hnd hb
    obtain ⟨vs, rs⟩ := p
    cases roots with
    | nil => simp at hlen
    | cons r roots =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatMap_cons] at hlen hb hnd ⊢
      have hlvs : vs.length = rs.length := hpl (vs, rs) (by simp)
      have hs := slice_ok c m vs.length (by omega)
      obtain ⟨g1, hg1⟩ := setLoop_ok g ((c.drop m).take vs.length) rs
        (by simp; omega) (hal (vs, rs) (by simp))
      have hset : setScalarConstants g ((c.drop m).take vs.length) rs = .ok g1 := by
        unfold setScalarConstants; rw [if_pos (by simp; omega)]; exact hg1
      obtain ⟨sh1, fr1, rd1⟩ := setLoop_props _ rs g g1 hg1
      have hnd' := List.nodup_append.mp hnd
      have hal' : ∀ p ∈ crs, ∀ a ∈ p.2, ∃ cell, g1.cells a = some cell := by
        intro p hp a ha
        obtain ⟨cell, hcell⟩ := hal p (by simp [hp]) a ha
        obtain ⟨c', hc', _⟩ := sh1.cells hcell
        exact ⟨c', hc'⟩
      obtain ⟨h, hh, sh2, fr2, rd2⟩ := ih roots (m + vs.length) g1 (by omega)
        (fun p hp => hpl p (by simp [hp])) hal' hnd'.2.1 (by omega)
      refine ⟨h, ?_, sh1.trans sh2, ?_, ?_⟩
      · simp only [setInners, hs, hset]
        rw [show m + 1 + vs.length = m + vs.length + 1 by omega, hh]
        congr 1; omega
      · intro b hb
        rw [fr2 b (fun hm => hb (List.mem_append_right _ hm)),
          fr1 b (fun hm => hb (List.mem_append_left _ hm))]
      · have hfr : ∀ a ∈ rs, h.read a = g1.read a := by
          intro a ha
          exact fr2 a (fun hm => hnd'.2.2 a ha a hm rfl)
        have r1 : readValues h rs = .ok ((c.drop m).take vs.length) := by
          rw [readValues_frame h g1 rs hfr]; exact rd1 hnd'.1
        rw [readValues_append, r1, okBind, rd2, okBind, pureOk, take_split]

end SymReg.Templates
