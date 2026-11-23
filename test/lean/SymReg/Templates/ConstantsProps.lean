import SymReg.Templates.Constants

/-!
Round-trip and length properties of the template, optimizer and composable constant
interfaces (`src/TemplateExpression.jl:440-508`, `src/ComposableExpression.jl:103-108,131-136`).
-/

namespace SymReg.Templates
open DynExpr DynExpr.NodeUtils

section Lemmas
variable {T : Type}

/-- `TRefs` built by the getter (`src/TemplateExpression.jl:465`). -/
def mkRefs (cr : List (List T × List Addr)) : List TRefs := cr.map fun p => ⟨p.1.length, p.2⟩

theorem mkRefs_flatMap (cr : List (List T × List Addr)) :
    (mkRefs cr).flatMap TRefs.ref = cr.flatMap Prod.snd := by
  induction cr with
  | nil => rfl
  | cons p cr ih => simp [mkRefs] at ih ⊢; rw [ih]

theorem mapM_get_props (g : Graph T) (fuel : Nat) :
    ∀ (roots : List Addr) cr, roots.mapM (getScalarConstants g false fuel) = .ok cr →
      roots.length = cr.length ∧ ∀ p ∈ cr, readValues g p.2 = .ok p.1 := by
  intro roots
  induction roots with
  | nil => intro cr h; cases h; simp
  | cons r roots ih =>
    intro cr h
    simp only [List.mapM_cons] at h
    cases hr : getScalarConstants g false fuel r with
    | error e => rw [hr] at h; cases h
    | ok p =>
      rw [hr, okBind] at h
      cases hrs : roots.mapM (getScalarConstants g false fuel) with
      | error e => rw [hrs] at h; cases h
      | ok cr' =>
        rw [hrs] at h; cases h
        obtain ⟨h1, h2⟩ := ih cr' hrs
        refine ⟨by simp [h1], ?_⟩
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact (getScalar_parts g fuel r q.1 q.2 hr).2
        · exact h2 q hq

theorem readValues_append_ok (g : Graph T) (a b : List Addr) (w : List T)
    (h : readValues g (a ++ b) = .ok w) :
    ∃ w1 w2, readValues g a = .ok w1 ∧ readValues g b = .ok w2 ∧ w = w1 ++ w2 := by
  rw [readValues_append] at h
  cases h1 : readValues g a with
  | error e => rw [h1] at h; cases h
  | ok w1 =>
    rw [h1, okBind] at h
    cases h2 : readValues g b with
    | error e => rw [h2] at h; cases h
    | ok w2 => rw [h2] at h; cases h; exact ⟨w1, w2, rfl, rfl, rfl⟩

/-- After value-only writes, the getter finds the same refs and reads the current values. -/
theorem get_after_write (g h : Graph T) (fuel : Nat) (s : Shape g h) :
    ∀ (roots : List Addr) cr w, roots.mapM (getScalarConstants g false fuel) = .ok cr →
      readValues h (cr.flatMap Prod.snd) = .ok w →
      ∃ cr', roots.mapM (getScalarConstants h false fuel) = .ok cr' ∧
        mkRefs cr' = mkRefs cr ∧ (cr'.map Prod.fst).flatten = w := by
  intro roots
  induction roots with
  | nil => intro cr w h hw; cases h; cases hw; exact ⟨[], rfl, rfl, rfl⟩
  | cons r roots ih =>
    intro cr w hm hw
    simp only [List.mapM_cons] at hm
    cases hr : getScalarConstants g false fuel r with
    | error e => rw [hr] at hm; cases hm
    | ok p =>
      rw [hr, okBind] at hm
      cases hrs : roots.mapM (getScalarConstants g false fuel) with
      | error e => rw [hrs] at hm; cases hm
      | ok cr0 =>
        rw [hrs] at hm; cases hm
        obtain ⟨vs, rs⟩ := p
        simp only [List.flatMap_cons] at hw
        obtain ⟨w1, w2, hw1, hw2, rfl⟩ := readValues_append_ok h rs _ w hw
        obtain ⟨⟨seen, hc⟩, hv⟩ := getScalar_parts g fuel r vs rs hr
        obtain ⟨cr0', h1, h2, h3⟩ := ih cr0 w2 hrs hw2
        have hg : getScalarConstants h false fuel r = .ok (w1, rs) := by
          simp only [getScalarConstants]
          rw [← constantRefs_shape s, hc, okBind, hw1]; rfl
        refine ⟨(w1, rs) :: cr0', ?_, ?_, ?_⟩
        · simp [List.mapM_cons, hg, h1]
        · simp only [mkRefs, List.map_cons] at h2 ⊢
          rw [h2, readValues_length h _ _ hw1, ← readValues_length g _ _ hv]
        · simp [h3]

theorem flatten_length (cr : List (List T × List Addr)) :
    ((cr.map Prod.fst).flatten).length = ((cr.map Prod.fst).map List.length).sum := by
  simp [List.length_flatten]


/-- A successful run of the inner loop consumes the expected number of entries and never
reads past the end of the constants vector. -/
theorem setInners_bound (c : List T) :
    ∀ (roots : List Addr) (refs : List TRefs) (i : Nat) (g : Graph T) j h,
      roots.length = refs.length → 1 ≤ i → setInners c roots refs i g = .ok j h →
      j = i + (refs.map TRefs.n).sum ∧ (i - 1 ≤ c.length → j - 1 ≤ c.length) := by
  intro roots
  induction roots with
  | nil => intro refs i g j h hl _ hs; cases refs with
    | nil => simp [setInners] at hs; obtain ⟨rfl, _⟩ := hs; simp
    | cons _ _ => simp at hl
  | cons r roots ih =>
    intro refs i g j h hl hi hs
    cases refs with
    | nil => simp at hl
    | cons ref refs =>
      simp only [setInners] at hs
      cases hsl : slice c i ref.n with
      | error e => rw [hsl] at hs; cases hs
      | ok cs =>
        simp only [hsl] at hs
        cases hset : setScalarConstants g cs ref.ref with
        | error e => simp [hset] at hs
        | ok g' =>
          simp only [hset] at hs
          obtain ⟨h1, h2⟩ := ih refs (i + ref.n) g' j h (by simpa using hl) (by omega) hs
          refine ⟨by simp [h1]; omega, fun hb => h2 ?_⟩
          unfold slice at hsl
          by_cases hn : ref.n = 0
          · omega
          · rw [if_neg hn] at hsl
            split at hsl
            · omega
            · cases hsl

end Lemmas

def FixedPacking {T V : Type} (codec : ParameterCodec V T)
    (width : Nat) (encode : V → List T) : Prop :=
  (∀ v, codec.width v = width ∧ (encode v).length = width) ∧
  (∀ v pre post, codec.pack (pre ++ List.replicate width none ++ post) (pre.length + 1) v =
    .ok (pre.length + width + 1, pre ++ (encode v).map some ++ post)) ∧
  (∀ v pre body post, body.length = width →
    ∃ new, codec.unpack (pre ++ body ++ post) (pre.length + 1) v =
      .ok (pre.length + width + 1, new) ∧ encode new = body ∧ (body = encode v → new = v)) ∧
  ∀ v pre body, body.length < width →
    ∃ err, codec.unpack (pre ++ body) (pre.length + 1) v = .error err

def templateGetSet : Prop :=
  ∀ (T V : Type) (fuel width : Nat) (encode : V → List T)
    (x changed : TConst T V) (c : List T) (refs : List TRefs),
    FixedPacking x.codec width encode →
    x.codec = changed.codec →
    x.roots = changed.roots → Shape x.g changed.g →
    x.paramRefs = changed.paramRefs → x.hasParams = changed.hasParams →
    (∀ a, (x.params a).map List.length = (changed.params a).map List.length) →
    (∀ addr original other, x.params addr = some original → changed.params addr = some other →
      ∀ pair ∈ original.zip other,
        ∀ pre post, x.codec.unpack (pre ++ encode pair.1 ++ post) (pre.length + 1) pair.2 =
          .ok (pre.length + width + 1, pair.1)) →
    templateGet fuel x = .ok (c, refs) →
    ∃ cr, x.roots.mapM (getScalarConstants x.g false fuel) = .ok cr ∧ refs = mkRefs cr ∧
      c = (cr.map Prod.fst).flatten ++ (if x.hasParams then
        x.paramRefs.flatMap (fun a => ((x.params a).getD []).flatMap encode) else []) ∧
      ∃ restored, templateSet changed c refs = .ok () restored ∧
        (∀ a ∈ refs.flatMap TRefs.ref, restored.g.cells a = x.g.cells a) ∧
        ∀ a ∈ x.paramRefs, x.hasParams = true → restored.params a = x.params a

def templateSetGet : Prop :=
  ∀ (T V : Type) (fuel width : Nat) (encode : V → List T)
    (x : TConst T V) (c0 : List T) (refs : List TRefs) (c : List T),
    FixedPacking x.codec width encode →
    templateGet fuel x = .ok (c0, refs) →
    (refs.flatMap TRefs.ref).Nodup → x.paramRefs.Nodup → c0.length ≤ c.length →
    ∃ x', templateSet x c refs = .ok () x' ∧ x'.roots = x.roots ∧
      x'.paramRefs = x.paramRefs ∧ x'.hasParams = x.hasParams ∧
      templateGet fuel x' = .ok (c.take c0.length, refs)

def templateSetShort : Prop :=
  ∀ (T V : Type) (fuel width : Nat) (encode : V → List T)
    (x : TConst T V) (c0 : List T) (refs : List TRefs) (c : List T),
    FixedPacking x.codec width encode →
    templateGet fuel x = .ok (c0, refs) → c.length < c0.length →
    ∃ e s, templateSet x c refs = .err e s

/-- A length-mismatched constants vector throws and leaves the expression unchanged. -/
def templateSetMismatchAtomic : Prop :=
  ∀ (T : Type) (fuel : Nat) (x : TConst T) (c0 : List T) (refs : List TRefs) (c : List T),
    templateGet fuel x = .ok (c0, refs) → c.length ≠ c0.length →
    ∃ e, templateSet x c refs = .err e x

/-- One inner constant `2.0` and a parameter vector `[5.0, 7.0]`. -/
def xTwoParams : TConst JF :=
  ⟨(Heap.empty.alloc (⟨0, true, some (.fin 2), 0, 0, []⟩ : Cell JF)).2, [0],
    [0], fun a => if a = 0 then some [.fin 5, .fin 7] else none, true, scalarParameterCodec JF⟩

theorem xTwoParams_get :
    templateGet 2 xTwoParams = .ok ([.fin 2, .fin 5, .fin 7], [⟨1, [0]⟩]) := rfl

/-- Two values for three constants and parameters: the inner node and the first parameter
are overwritten before the `BoundsError` on the second parameter. -/
theorem xTwoParams_short : ∃ s, templateSet xTwoParams [.fin 1, .fin 2] [⟨1, [0]⟩] =
    .err .boundsError s ∧ s.params 0 = some [.fin 2, .fin 7] := ⟨_, rfl, rfl⟩

theorem templateSetMismatchAtomic_refuted : ¬ templateSetMismatchAtomic := by
  intro h
  obtain ⟨e, he⟩ := h JF 2 xTwoParams _ _ [.fin 1, .fin 2] xTwoParams_get (by decide)
  obtain ⟨s, hs, hps⟩ := xTwoParams_short
  rw [hs] at he
  injection he with _ hsx
  rw [hsx] at hps
  exact absurd hps (by decide)

/-- `set_optimizable_parameters!` checks the length first: a mismatched vector throws a
`DimensionMismatch` and leaves the expression unchanged. -/
def optSetLength : Prop :=
  ∀ (T V : Type) (fuel : Nat) (x : TConst T V) (p : List T) (r : TOptRefs) (p' : List T),
    optGet fuel x = .ok (p, r) → p'.length ≠ p.length →
    optSet x p' r = .err
      (.dimensionMismatch s!"received {p'.length} optimizable parameters but expected {p.length}") x

theorem optGet_ok {T V : Type} (fuel : Nat) (x : TConst T V) (p : List T) (r : TOptRefs)
    (h : optGet fuel x = .ok (p, r)) :
    templateGet fuel x = .ok (p, r.scalarRefs) ∧ r.length = p.length := by
  simp only [optGet] at h
  cases hg : templateGet fuel x with
  | error e => rw [hg] at h; cases h
  | ok q => obtain ⟨a, b⟩ := q; rw [hg] at h; cases h; exact ⟨rfl, rfl⟩

theorem optSetLength_holds : optSetLength := by
  intro T V fuel x p r p' h hne
  obtain ⟨_, hl⟩ := optGet_ok fuel x p r h
  unfold optSet
  rw [if_neg (by omega), hl]

def optRoundtrip : Prop :=
  ∀ (T V : Type) (fuel width : Nat) (encode : V → List T) (x : TConst T V) (p : List T) (r : TOptRefs),
    FixedPacking x.codec width encode → optGet fuel x = .ok (p, r) →
      optSet x p r = .ok () x ∧
      ((r.scalarRefs.flatMap TRefs.ref).Nodup → x.paramRefs.Nodup →
        ∀ p' : List T, p'.length = p.length →
        ∃ x', optSet x p' r = .ok () x' ∧ optGet fuel x' = .ok (p', r))

/-- `get_scalar_constants`/`set_scalar_constants!` and the optimizer hooks on a
`ComposableExpression` forward to its `Node` tree (`src/ComposableExpression.jl:103-108,131-136`). -/
def composableGet {T : Type} (g : Graph T) (fuel root : Nat) := getScalarConstants g false fuel root
def composableSet {T : Type} (g : Graph T) (vs : List T) (rs : List Addr) := setScalarConstants g vs rs

/-- Composable constants round-trip, and unlike the template setter, a mismatched length
throws `DimensionMismatch` before any write. -/
def composableRoundtrip : Prop :=
  ∀ (T : Type) (g : Graph T) (fuel root : Nat) (vs : List T) (rs : List Addr),
    composableGet g fuel root = .ok (vs, rs) →
      composableSet g vs rs = .ok g ∧
      (rs.Nodup → ∀ vs' : List T, vs'.length = vs.length →
        ∃ h, composableSet g vs' rs = .ok h ∧ composableGet h fuel root = .ok (vs', rs)) ∧
      ∀ vs' : List T, vs'.length ≠ vs.length →
        composableSet g vs' rs = .error (.argumentError "DimensionMismatch")

theorem composableRoundtrip_holds : composableRoundtrip := by
  intro T g fuel root vs rs h
  unfold composableGet at h
  obtain ⟨⟨seen, hc⟩, hv⟩ := getScalar_parts g fuel root vs rs h
  have hl := readValues_length g _ _ hv
  refine ⟨getSet_node g fuel root vs rs h, ?_, ?_⟩
  · intro hnd vs' hl'
    obtain ⟨h1, h1ok⟩ := setLoop_ok g vs' rs (by omega) (fun a ha => by
      obtain ⟨c, _, hc, _⟩ := readValues_cells g rs vs hv a ha; exact ⟨c, hc⟩)
    obtain ⟨sh, _, rd⟩ := setLoop_props vs' rs g h1 h1ok
    refine ⟨h1, ?_, ?_⟩
    · unfold composableSet setScalarConstants; rw [if_pos (by omega)]; exact h1ok
    · unfold composableGet getScalarConstants
      rw [← constantRefs_shape sh, hc, okBind]
      simp only [rd hnd]
      rfl
  · intro vs' hne
    unfold composableSet setScalarConstants
    rw [if_neg (by omega)]

end SymReg.Templates
