import SymReg.SimpCons.Constraints

namespace SymReg.Options

-- placed here to break an import cycle with Options/Core
/-- Source: `src/Options.jl:181-201,219`.
Operator identities 1..19 name, in order, plus, mult, sub, div, ^, pow, >, <,
>=, <=, log, log10, log2, log1p, sqrt, asin, acos, acosh, atanh. Canonical
identities 101..118 name +, *, -, /, safe_pow, greater, less, greater_equal,
less_equal, safe_log, safe_log10, safe_log2, safe_log1p, safe_sqrt, safe_asin,
safe_acos, safe_acosh, safe_atanh. Every other natural denotes an arbitrary
function identity. Mapping changes identities, never evaluates an operator. -/
def opmap (op : Nat) : Nat :=
  if 1 <= op ∧ op <= 4 then op + 100
  else if op = 5 ∨ op = 6 then 105
  else if 7 <= op ∧ op <= 19 then op + 99
  else op

end SymReg.Options

namespace SymReg.SimpCons
open DynExpr SymReg.Constraints SymReg.HeapLemmas
open SymReg.Options (opmap)

/-- Dictionary assignment in `src/Options.jl:225`: the last value for an equal
operator key replaces earlier entries. Operator identities are natural numbers. -/
def dictPut {V : Type} (xs : List (Nat × V)) (p : Nat × V) : List (Nat × V) :=
  p :: xs.filter (fun q => q.1 != p.1)

/-- `Dict(ops)` in `src/Options.jl:225`; iteration order is irrelevant to the tables. -/
def toDict {V : Type} (xs : List (Nat × V)) : List (Nat × V) := xs.foldl dictPut []

/-- `opmap_keys`, `src/Options.jl:223-230`. `canon` is the fixed `OP_MAP` lookup
(`src/Options.jl:181-219`), abstracting function identity, not numerical evaluation. -/
def mapKeys {V : Type} (canon : Nat → Nat) (xs : List (Nat × V)) : Jl (List (Nat × V)) :=
  let d := toDict xs
  let mapped := toDict (d.map (fun (op, v) => (canon op, v)))
  if mapped.length = d.length then pure mapped
  else throw (.errorException "Operator keys refer to the same operator more than once.")

private theorem foldDict_keys {V : Type} (xs acc : List (Nat × V)) (k : Nat) :
    k ∈ (xs.foldl dictPut acc).map Prod.fst ↔ k ∈ acc.map Prod.fst ∨
      k ∈ xs.map Prod.fst := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hk : k = x.1
    · simp [hk, dictPut]
    · simp [dictPut, List.mem_map, List.mem_filter, hk]

private theorem foldDict_length {V : Type} (xs acc : List (Nat × V)) :
    (xs.foldl dictPut acc).length ≤ xs.length + acc.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have h := ih (dictPut acc x)
    have hf := List.length_filter_le (fun q : Nat × V => q.1 != x.1) acc
    simp only [List.foldl_cons, List.length_cons, dictPut] at h ⊢
    omega

private theorem foldDict_strict {V : Type} (xs acc : List (Nat × V)) :
    (¬ (xs.map Prod.fst).Nodup ∨
      ∃ k ∈ xs.map Prod.fst, k ∈ acc.map Prod.fst) →
    (xs.foldl dictPut acc).length < xs.length + acc.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    intro h
    by_cases hx : x.1 ∈ acc.map Prod.fst
    · have hf : (acc.filter (fun q => q.1 != x.1)).length < acc.length := by
        have hle := List.length_filter_le (fun q : Nat × V => q.1 != x.1) acc
        apply Classical.byContradiction
        intro hn
        have hn : acc.length ≤ (acc.filter (fun q => q.1 != x.1)).length := by omega
        have hall := List.length_filter_eq_length_iff.mp (Nat.le_antisymm hle hn)
        obtain ⟨q, hq, he⟩ := List.mem_map.mp hx
        simpa [he] using hall q hq
      have hle := foldDict_length xs (dictPut acc x)
      simp only [List.foldl_cons, List.length_cons, dictPut] at hle ⊢
      omega
    · have htail : ¬ (xs.map Prod.fst).Nodup ∨
          ∃ k ∈ xs.map Prod.fst, k ∈ (dictPut acc x).map Prod.fst := by
        simp only [List.map_cons, List.nodup_cons, List.mem_cons] at h
        rcases h with hr | ⟨k, hk | hk, ha⟩
        · by_cases hm : x.1 ∈ xs.map Prod.fst
          · exact Or.inr ⟨x.1, hm, by simp [dictPut]⟩
          · exact Or.inl (fun hn => hr ⟨hm, hn⟩)
        · exact False.elim (hx (hk ▸ ha))
        · refine Or.inr ⟨k, hk, ?_⟩
          by_cases he : k = x.1
          · simp [dictPut, he]
          · obtain ⟨q, hq, hqk⟩ := List.mem_map.mp ha
            exact List.mem_cons_of_mem _ (List.mem_map.mpr
              ⟨q, List.mem_filter.mpr ⟨hq, by simp [hqk, he]⟩, hqk⟩)
      have hs := ih (dictPut acc x) htail
      have hf := List.length_filter_le (fun q : Nat × V => q.1 != x.1) acc
      simp only [List.foldl_cons, List.length_cons, dictPut] at hs ⊢
      omega

theorem mapKeys_fails_on_alias {V : Type} (canon : Nat → Nat) (pairs : List (Nat × V))
    (k₁ k₂ : Nat) (v₁ v₂ : V) (h₁ : (k₁, v₁) ∈ pairs) (h₂ : (k₂, v₂) ∈ pairs)
    (hne : k₁ ≠ k₂) (he : canon k₁ = canon k₂) :
    mapKeys canon pairs = .error
      (.errorException "Operator keys refer to the same operator more than once.") := by
  let d := toDict pairs
  let image := d.map (fun (op, v) => (canon op, v))
  have present (k : Nat) (v : V) (h : (k, v) ∈ pairs) : k ∈ d.map Prod.fst := by
    apply (foldDict_keys pairs [] k).mpr
    exact Or.inr (List.mem_map.mpr ⟨(k, v), h, rfl⟩)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (present k₁ v₁ h₁)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (present k₂ v₂ h₂)
  have hnot : ¬ (image.map Prod.fst).Nodup := by
    intro hn
    have hiv : (image.map Prod.fst)[i]? = some (canon k₁) := by
      simpa [image, List.map_map, Function.comp_def] using congrArg (Option.map canon) hi
    have hjv : (image.map Prod.fst)[j]? = some (canon k₁) := by
      simpa [image, List.map_map, Function.comp_def, he] using congrArg (Option.map canon) hj
    have hij := hn.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp hiv).choose
      (hiv.trans hjv.symm)
    subst j
    exact hne (Option.some.inj (hi.symm.trans hj))
  have hlen : (toDict image).length < d.length := by
    simpa [image, toDict] using foldDict_strict image [] (Or.inl hnot)
  change (if (toDict image).length = d.length then _ else _) = _
  rw [if_neg (Nat.ne_of_lt hlen)]
  rfl

theorem toDict_subset {V : Type} (xs : List (Nat × V)) : toDict xs ⊆ xs := by
  have aux (ys acc : List (Nat × V)) : ys.foldl dictPut acc ⊆ acc ++ ys := by
    induction ys generalizing acc with
    | nil => simp
    | cons y ys ih =>
      intro p hp
      have hm := ih (dictPut acc y) hp
      simp only [dictPut, List.mem_append, List.mem_cons, List.mem_filter] at hm ⊢
      rcases hm with (rfl | ⟨ha, _⟩) | ht
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ha
      · exact Or.inr (Or.inr ht)
  simpa [toDict] using aux xs []

theorem toDict_nodup {V : Type} (xs : List (Nat × V)) : ((toDict xs).map Prod.fst).Nodup := by
  have aux (ys acc : List (Nat × V)) (h : (acc.map Prod.fst).Nodup) :
      ((ys.foldl dictPut acc).map Prod.fst).Nodup := by
    induction ys generalizing acc with
    | nil => exact h
    | cons y ys ih =>
      apply ih (dictPut acc y)
      simp only [dictPut, List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
        have hne := (List.mem_filter.mp hp).2
        simp [he] at hne
      · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h
  exact aux xs [] (by simp)

theorem mapKeys_of_injective {V : Type} (canon : Nat → Nat) (xs : List (Nat × V))
    (hi : ∀ p ∈ toDict xs, ∀ q ∈ toDict xs, canon p.1 = canon q.1 → p.1 = q.1) :
    mapKeys canon xs = .ok ((toDict xs).map (fun (op, v) => (canon op, v))).reverse := by
  have aux (ys acc : List (Nat × V)) (hn : ((acc ++ ys).map Prod.fst).Nodup) :
      ys.foldl dictPut acc = ys.reverse ++ acc := by
    induction ys generalizing acc with
    | nil => rfl
    | cons y ys ih =>
      have hy : y.1 ∉ acc.map Prod.fst := by
        simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hn
        grind
      have hf : acc.filter (fun q => q.1 != y.1) = acc := by
        apply List.filter_eq_self.mpr
        intro q hq
        have hne : q.1 ≠ y.1 := fun he => hy (List.mem_map.mpr ⟨q, hq, he⟩)
        simp [hne]
      have hn' : (((y :: acc) ++ ys).map Prod.fst).Nodup := by
        simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hn ⊢
        grind
      change ys.foldl dictPut (dictPut acc y) = _
      simp only [dictPut, hf, ih (y :: acc) hn', List.reverse_cons, List.append_assoc,
        List.singleton_append]
  let image := (toDict xs).map (fun (op, v) => (canon op, v))
  have hn : (image.map Prod.fst).Nodup := by
    simp only [image, List.map_map]
    have hcomp : Prod.fst ∘ (fun p : Nat × V => (canon p.1, p.2)) =
        (fun p : Nat × V => canon p.1) := by
      funext p
      cases p
      rfl
    change (((toDict xs).map (Prod.fst ∘ (fun p : Nat × V => (canon p.1, p.2))))).Nodup
    rw [hcomp]
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    have hd := toDict_nodup xs
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hd
    exact hd.imp_of_mem (fun hp hq hne he => hne (hi _ hp _ hq he))
  have he : toDict image = image.reverse := by
    simpa [toDict] using aux image [] (by simpa using hn)
  change (if (toDict image).length = (toDict xs).length then _ else _) =
    (Except.ok image.reverse : Jl (List (Nat × V)))
  rw [he]
  have hlen : image.reverse.length = (toDict xs).length := by simp [image]
  rw [if_pos hlen]
  rfl

inductive ConstraintValue where
  | scalar (n : Int)
  | tuple (ns : List Int)
  deriving Repr, DecidableEq

/-- Source: `src/Options.jl:81-100`. `ready` encodes a vector of the right
element type for its degree, regardless of its supplied length. -/
inductive DegreeInput where
  | missing
  | pairs (xs : List (Nat × ConstraintValue))
  | ready (xs : List ConstraintValue)

/-- Source: `src/Options.jl:87-89`, the per-degree normalization phase. -/
def normalizeDegree (canon : Nat → Nat) : DegreeInput → Jl DegreeInput
  | .pairs xs => (mapKeys canon xs).map DegreeInput.pairs
  | other => pure other

/-- Source: `src/Options.jl:90-102`.
```
let default_value = i == 1 ? -1 : ntuple(j -> -1, i)
    if isnothing(_op_constraints[i])
        fill(default_value, length(operators_by_degree[i]))
    elseif !is_constraints_already_done[i]
        typeof(default_value)[
            get(_op_constraints[i], op, default_value) for
            op in operators_by_degree[i]
        ]
    else
        _op_constraints[i]::Vector{typeof(default_value)}
    end
end
```
-/
def buildDegree (degree : Nat) (ops : List Nat) (input : DegreeInput) :
    Jl (List ConstraintValue) := do
  let default : ConstraintValue :=
    if degree = 1 then .scalar (-1) else .tuple (List.replicate degree (-1))
  match input with
  | .missing => pure (List.replicate ops.length default)
  | .ready xs => pure xs
  | .pairs xs => ops.mapM fun op => do
    let v := ((xs.find? (fun q => q.1 == op)).map Prod.snd).getD default
    match v with
    | .scalar _ =>
      if degree = 1 then pure v
      else throw (.methodError "convert constraint to NTuple")
    | .tuple ns =>
      if degree ≠ 1 ∧ ns.length = degree then pure v
      else throw (.methodError "convert constraint to degree element type")

/-- Container indexed as `constraints[i]` in `src/Options.jl:81-87`. Operator-keyed
dictionaries have function keys, which are distinct from integer degree indices. -/
inductive ConstraintInput where
  | degrees (inputs : List DegreeInput)
  | operatorPairs (pairs : List (Nat × ConstraintValue))

/-- Integer indexing performed before key normalization, `src/Options.jl:81-84`. -/
def degreeInputAt (inputs : ConstraintInput) (degree : Nat) : Jl DegreeInput :=
  match inputs with
  | .degrees xs => match xs[degree - 1]? with
    | some x => pure x
    | none => throw .boundsError
  | .operatorPairs _ => throw (.errorException "KeyError: degree is not an operator key")

/-- Source: `src/Options.jl:76-103`.
```
is_constraints_already_done = ntuple(Val(D)) do i
    i == 1 && constraints[i] isa Vector{Int} ||
        i > 1 && constraints[i] isa Vector{NTuple{i,Int}}
end
_op_constraints = ntuple(Val(D)) do i
    is_constraints_already_done[i] ? constraints[i] : opmap_keys(constraints[i])
end
```
Read all degree slots, normalize all dictionaries, then assemble typed vectors. -/
def buildAll (canon : Nat → Nat) (ops : List (List Nat))
    (inputs : ConstraintInput) : Jl (List (List ConstraintValue)) := do
  let selected ← (enum1 ops).mapM (fun (degree, _) => degreeInputAt inputs degree)
  let normalized ← selected.mapM (normalizeDegree canon)
  (normalized.zip (enum1 ops)).mapM (fun (input, degree, ds) => buildDegree degree ds input)

/-- `build_constraints`, `src/Options.jl:60-74`: explicit degree input conflicts
with either legacy keyword; the legacy pair always has two degree slots. -/
def buildConstraints (canon : Nat → Nat) (ops : List (List Nat))
    (constraints : Option ConstraintInput) (unary binary : Option DegreeInput) :
    Jl (List (List ConstraintValue)) := do
  let inputs ← match constraints with
    | some xs =>
      if unary.isSome || binary.isSome then
        throw (.assertionError "all(isnothing, (una_constraints, bin_constraints))")
      else pure xs
    | none =>
      if unary.isSome || binary.isSome then
        pure (.degrees [unary.getD .missing, binary.getD .missing])
      else pure (.degrees (List.replicate ops.length .missing))
  buildAll canon ops inputs

/-- The one-based `findfirst` in `src/Options.jl:144-150,160-166`. -/
def findOp (op : Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if x = op then some 1 else (findOp op xs).map (· + 1)

/-- The first `(degree, index)` in the nested-constraint builder,
`src/Options.jl:141-154,157-170`. -/
def locateOp (op : Nat) : List (List Nat) → Option (Nat × Nat)
  | [] => none
  | xs :: rest => match findOp op xs with
    | some i => some (1, i)
    | none => (locateOp op rest).map (fun (d, i) => (d + 1, i))

/-- A validated operator lookup, `src/Options.jl:127-134,152-154,168-170`. -/
def requireOp (ops : List (List Nat)) (op : Nat) : Jl (Nat × Nat) :=
  match locateOp op ops with
  | some di => pure di
  | none => throw (.errorException "Operator is not in the operator set.")

abbrev NestedInput := List (Nat × List (Nat × Int))

/-- Normalize the outer and inner dictionaries, `src/Options.jl:123-125`. -/
def mapNested (canon : Nat → Nat) (xs : NestedInput) : Jl NestedInput := do
  let xs ← xs.mapM (fun (op, inner) => do
    let inner ← mapKeys canon inner
    pure (op, inner))
  mapKeys canon xs

/-- `build_nested_constraints`, `src/Options.jl:106-178`. It rejects any repeated
operator identity, unknown outer/inner keys and nesting limits below -1. The returned
triples contain the actual one-based degree and index, in dictionary iteration order. -/
def buildNested (canon : Nat → Nat) (ops : List (List Nat))
    (input : Option NestedInput) : Jl (Option (List (Nat × Nat × List (Nat × Nat × Int)))) := do
  let some input := input | return none
  if !(decide ops.flatten.Nodup) then
    throw (.errorException "Operator appears in multiple degrees. You can't use nested constraints.")
  let xs ← mapNested canon input
  xs.forM (fun (op, inner) => do
    let _ ← requireOp ops op
    inner.forM (fun (nested, mx) => do
      let _ ← requireOp ops nested
      if mx < -1 then throw (.assertionError "max_nesting >= -1 && typeof(max_nesting) <: Int")
      else pure ()))
  let result ← xs.mapM (fun (op, inner) => do
    let (d, i) ← requireOp ops op
    let inner ← inner.mapM (fun (nested, mx) => do
      let (nd, ni) ← requireOp ops nested
      pure (nd, ni, mx))
    pure (d, i, inner))
  pure (some result)

def builderDefaults : Prop :=
  ∀ (ops : List (List Nat)),
    ∃ table, buildConstraints opmap ops none none none = .ok table ∧
      table.length = ops.length ∧
      ∀ (d : Nat) (ds : List Nat), ops[d]? = some ds →
        ∃ slots, table[d]? = some slots ∧ slots.length = ds.length ∧
          ∀ v ∈ slots, (d = 0 → v = .scalar (-1)) ∧
            (0 < d → ∃ ns, v = .tuple ns ∧ ns.length = d + 1 ∧ ∀ n ∈ ns, n = -1)

theorem mapM_ok_on {A B : Type} (f : A → Jl B) (g : A → B) (xs : List A)
    (h : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp [List.mapM_cons, hx, hs, bind, Except.bind, pure, Except.pure]

theorem builderDefaults_holds : builderDefaults := by
  intro ops
  let es := enum1 ops
  let defaults := List.replicate ops.length DegreeInput.missing
  let slots : Nat × List Nat → List ConstraintValue := fun (d, ds) =>
    List.replicate ds.length (if d = 1 then .scalar (-1) else .tuple (List.replicate d (-1)))
  have he : es.length = ops.length := by simp [es, enum1]
  have hs : ∀ pair ∈ es, degreeInputAt (.degrees defaults) pair.1 = .ok .missing := by
    intro pair hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    obtain ⟨d, row⟩ := pair
    obtain ⟨hd, hr⟩ := List.getElem?_zip_eq_some.mp hi
    have hlt : i < ops.length := (List.getElem?_eq_some_iff.mp hr).choose
    simp [List.getElem?_range', hlt] at hd
    subst d
    simp [degreeInputAt, defaults, hlt, Nat.add_comm, pure, Except.pure]
  have hselected : es.mapM (fun p => degreeInputAt (.degrees defaults) p.1) =
      .ok defaults := by
    rw [mapM_ok_on _ (fun _ => DegreeInput.missing) _ hs]
    simp [defaults, he, List.map_const']
  have hnormalized : defaults.mapM (normalizeDegree opmap) = .ok defaults := by
    rw [mapM_ok_on _ id]
    · simp
    · intro x hx
      rw [List.eq_of_mem_replicate hx]
      rfl
  have htable : (defaults.zip es).mapM
      (fun (input, degree, ds) => buildDegree degree ds input) = .ok (es.map slots) := by
    have hzip : defaults.zip es = es.map (fun p => (DegreeInput.missing, p)) := by
      apply List.ext_getElem?
      intro i
      cases h : es[i]? with
      | none => simp [List.zip, List.getElem?_zipWith, h]
      | some v =>
        have hi : i < ops.length := he ▸ (List.getElem?_eq_some_iff.mp h).choose
        simp [List.zip, List.getElem?_zipWith, h, defaults, hi]
    rw [hzip, List.mapM_map]
    exact mapM_ok_on _ slots _ (by rintro ⟨d, ds⟩ _; rfl)
  refine ⟨es.map slots, ?_, by simp [he], ?_⟩
  · change (do
      let chosen ← es.mapM (fun (p : Nat × List Nat) => degreeInputAt (.degrees defaults) p.1)
      let normalized ← chosen.mapM (normalizeDegree opmap)
      (normalized.zip es).mapM (fun (input, degree, ds) => buildDegree degree ds input)) = _
    rw [hselected]
    change (do
      let normalized ← defaults.mapM (normalizeDegree opmap)
      (normalized.zip es).mapM (fun (input, degree, ds) => buildDegree degree ds input)) = _
    rw [hnormalized]
    exact htable
  · intro d ds hd
    obtain ⟨hlt, hds⟩ := List.getElem?_eq_some_iff.mp hd
    refine ⟨slots (d + 1, ds), ?_, by simp [slots], ?_⟩
    · simp [slots, es, enum1, List.zip, hlt, hds, Nat.add_comm]
    · intro v hv
      have hval := List.eq_of_mem_replicate hv
      constructor
      · intro hz
        simpa [hz] using hval
      · intro hp
        have hn : d ≠ 0 := by omega
        refine ⟨List.replicate (d + 1) (-1), by simpa [hn] using hval, by simp, ?_⟩
        intro n hn'
        exact List.eq_of_mem_replicate hn'

/-- Typed vectors pass through unchanged, even if their length differs from the enum. -/
def builderReady : Prop :=
  ∀ degree ops limits, buildDegree degree ops (.ready limits) = .ok limits

theorem builderReady_holds : builderReady := by
  unfold builderReady
  intros
  rfl


/-- Explicit generic constraints cannot be combined with the unary legacy keyword. -/
def builderConflictUnary : Prop :=
  ∀ (canon : Nat → Nat) ops constraints unary binary,
    buildConstraints canon ops (some constraints) (some unary) binary =
      .error (.assertionError "all(isnothing, (una_constraints, bin_constraints))")

theorem builderConflictUnary_holds : builderConflictUnary := by
  unfold builderConflictUnary
  intros
  simp [buildConstraints]
  rfl

/-- Explicit generic constraints cannot be combined with the binary legacy keyword. -/
def builderConflictBinary : Prop :=
  ∀ (canon : Nat → Nat) ops constraints unary binary,
    buildConstraints canon ops (some constraints) unary (some binary) =
      .error (.assertionError "all(isnothing, (una_constraints, bin_constraints))")

theorem builderConflictBinary_holds : builderConflictBinary := by
  unfold builderConflictBinary
  intros
  simp [buildConstraints]
  rfl

/-- No nested constraints returns `nothing` before validating duplicated operators. -/
def nestedAbsent : Prop :=
  ∀ (canon : Nat → Nat) ops, buildNested canon ops none = .ok none

theorem nestedAbsent_holds : nestedAbsent := by
  unfold nestedAbsent
  intros
  rfl

/-- A repeated operator prevents nested constraints, including repetition in one degree. -/
def nestedDuplicate : Prop :=
  ∀ (canon : Nat → Nat) ops input, ¬ ops.flatten.Nodup →
    buildNested canon ops (some input) =
      .error (.errorException "Operator appears in multiple degrees. You can't use nested constraints.")

theorem nestedDuplicate_holds : nestedDuplicate := by
  intro canon ops input h
  simp [buildNested, h]
  rfl

private theorem findOp_none (op : Nat) (xs : List Nat) :
    findOp op xs = none ↔ op ∉ xs := by
  induction xs with
  | nil => simp [findOp]
  | cons x xs ih =>
    by_cases h : x = op
    · subst x; simp [findOp]
    · simp [findOp, h, ih, Ne.symm h]

private theorem locateOp_none (op : Nat) (ops : List (List Nat)) :
    locateOp op ops = none ↔ op ∉ ops.flatten := by
  induction ops with
  | nil => simp [locateOp]
  | cons xs rest ih =>
    cases h : findOp op xs with
    | none => simp [locateOp, h, ih, (findOp_none op xs).mp h]
    | some i =>
      have hm : op ∈ xs := by
        apply Classical.byContradiction
        intro hn
        have he := (findOp_none op xs).mpr hn
        rw [h] at he
        cases he
      simp [locateOp, h, hm]

private def validInnerKeys (ops : List (List Nat)) (xs : List (Nat × Int)) : Prop :=
  ∀ p ∈ xs, p.1 ∈ ops.flatten ∧ -1 ≤ p.2

private def validOuterKeys (ops : List (List Nat)) (xs : NestedInput) : Prop :=
  ∀ p ∈ xs, p.1 ∈ ops.flatten ∧ validInnerKeys ops p.2

def unknownOperator : Prop :=
  ∀ (ops : List (List Nat)) raw normalized pre op inner post,
    ops.flatten.Nodup → mapNested opmap raw = .ok normalized →
    normalized = pre ++ (op, inner) :: post →
    validOuterKeys ops pre →
    (op ∉ ops.flatten ∨
      (op ∈ ops.flatten ∧ ∃ before key limit after,
        inner = before ++ (key, limit) :: after ∧ validInnerKeys ops before ∧
        key ∉ ops.flatten)) →
    buildNested opmap ops (some raw) = .error (.errorException "Operator is not in the operator set.")

def aliasCollision : Prop :=
  ∀ (V : Type) (pairs : List (Nat × V)) k₁ k₂ v₁ v₂,
    (k₁, v₁) ∈ pairs → (k₂, v₂) ∈ pairs → k₁ ≠ k₂ →
    opmap k₁ = opmap k₂ →
    mapKeys opmap pairs = .error
      (.errorException "Operator keys refer to the same operator more than once.")

theorem aliasCollision_holds : aliasCollision := by
  intro V pairs k₁ k₂ v₁ v₂ h₁ h₂ hne he
  exact mapKeys_fails_on_alias opmap pairs k₁ k₂ v₁ v₂ h₁ h₂ hne he

def nestedUnknownOuter : Prop :=
  ∀ (ops : List (List Nat)) raw normalized pre op inner post,
    ops.flatten.Nodup → mapNested opmap raw = .ok normalized →
    normalized = pre ++ (op, inner) :: post →
    validOuterKeys ops pre → op ∉ ops.flatten →
    buildNested opmap ops (some raw) = .error (.errorException "Operator is not in the operator set.")

private theorem forM_prefix {A : Type} (f : A → Jl Unit) (pre post : List A)
    (ok : ∀ x ∈ pre, f x = .ok ()) :
    (pre ++ post).forM f = post.forM f := by
  induction pre with
  | nil => rfl
  | cons x xs ih =>
    have hx := ok x (by simp)
    have hs := ih (fun y hy => ok y (by simp [hy]))
    change (do f x; (xs ++ post).forM f) = _
    rw [hx]
    exact hs

theorem unknownOperator_holds : unknownOperator := by
  intro ops raw normalized pre op inner post hn hm hh hpre hfail
  subst normalized
  let innerCheck : Nat × Int → Jl Unit := fun (key, limit) => do
    let _ ← requireOp ops key
    if limit < -1 then throw (.assertionError "max_nesting >= -1 && typeof(max_nesting) <: Int")
    else pure ()
  let outerCheck : Nat × List (Nat × Int) → Jl Unit := fun (key, limits) => do
    let _ ← requireOp ops key
    limits.forM innerCheck
  have lookup (key : Nat) (hk : key ∈ ops.flatten) : ∃ di, requireOp ops key = .ok di := by
    cases hl : locateOp key ops with
    | none => exact False.elim ((locateOp_none key ops).mp hl hk)
    | some di => exact ⟨di, by simp [requireOp, hl, pure, Except.pure]⟩
  have innerOk : ∀ row, validInnerKeys ops row → ∀ p ∈ row, innerCheck p = .ok () := by
    rintro row hv ⟨key, limit⟩ hp
    obtain ⟨hk, hl⟩ := hv (key, limit) hp
    obtain ⟨di, hd⟩ := lookup key hk
    simp [innerCheck, hd, show ¬ limit < -1 by omega, bind, Except.bind, pure, Except.pure]
  have outerOk : ∀ p ∈ pre, outerCheck p = .ok () := by
    rintro ⟨key, limits⟩ hp
    obtain ⟨hk, hi⟩ := hpre (key, limits) hp
    obtain ⟨di, hd⟩ := lookup key hk
    have hs := forM_prefix innerCheck limits [] (innerOk limits hi)
    simpa [outerCheck, hd, bind, Except.bind, pure, Except.pure] using hs
  have fails : outerCheck (op, inner) =
      .error (.errorException "Operator is not in the operator set.") := by
    rcases hfail with ho | ⟨ho, before, key, limit, after, rfl, hv, hk⟩
    · have he : requireOp ops op = .error (.errorException "Operator is not in the operator set.") := by
        unfold requireOp
        rw [(locateOp_none _ _).mpr ho]
        rfl
      simp [outerCheck, he, bind, Except.bind]
    · obtain ⟨di, hd⟩ := lookup op ho
      simp only [outerCheck, hd, bind, Except.bind]
      rw [forM_prefix _ _ _ (innerOk before hv)]
      have he : requireOp ops key = .error (.errorException "Operator is not in the operator set.") := by
        unfold requireOp
        rw [(locateOp_none _ _).mpr hk]
        rfl
      simp [List.forM_cons, innerCheck, he, bind, Except.bind]
  have hcheck : (pre ++ (op, inner) :: post).forM outerCheck =
      .error (.errorException "Operator is not in the operator set.") := by
    rw [forM_prefix _ _ _ outerOk]
    change (do outerCheck (op, inner); post.forM outerCheck) = _
    rw [fails]
    rfl
  unfold buildNested
  simp only [hn, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hm]
  change (do
    (pre ++ (op, inner) :: post).forM outerCheck
    _) = _
  rw [hcheck]
  rfl

theorem nestedUnknownOuter_holds : nestedUnknownOuter := by
  intro ops raw normalized pre op inner post hn hm hh hp ho
  exact unknownOperator_holds ops raw normalized pre op inner post hn hm hh hp (Or.inl ho)

private theorem findOp_sound (op : Nat) (xs : List Nat) (i : Nat)
    (h : findOp op xs = some i) : 1 ≤ i ∧ xs[i - 1]? = some op := by
  induction xs generalizing i with
  | nil => simp [findOp] at h
  | cons x xs ih =>
    by_cases hx : x = op
    · simp [findOp, hx] at h
      subst i
      simp [hx]
    · cases ht : findOp op xs with
      | none => simp [findOp, hx, ht] at h
      | some j =>
        simp [findOp, hx, ht] at h
        subst i
        obtain ⟨hj, hi⟩ := ih j ht
        refine ⟨by omega, ?_⟩
        rw [show j + 1 - 1 = (j - 1) + 1 by omega, List.getElem?_cons_succ]
        exact hi

private def namesOp (ops : List (List Nat)) (op d i : Nat) : Prop :=
  1 ≤ d ∧ 1 ≤ i ∧ ∃ ds, ops[d - 1]? = some ds ∧ ds[i - 1]? = some op

private theorem locateOp_sound (ops : List (List Nat)) (op d i : Nat)
    (h : locateOp op ops = some (d, i)) : namesOp ops op d i := by
  revert d i
  induction ops with
  | nil => intro d i h; simp [locateOp] at h
  | cons xs rest ih =>
    intro d i h
    cases hf : findOp op xs with
    | some j =>
      simp [locateOp, hf] at h
      rcases h with ⟨rfl, rfl⟩
      obtain ⟨hj, hi⟩ := findOp_sound op xs j hf
      exact ⟨by omega, hj, xs, rfl, hi⟩
    | none =>
      cases hl : locateOp op rest with
      | none => simp [locateOp, hf, hl] at h
      | some p =>
        rcases p with ⟨nd, ni⟩
        simp [locateOp, hf, hl] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hd, hi, ds, hds, hop⟩ := ih nd ni hl
        refine ⟨by omega, hi, ds, ?_, hop⟩
        rw [show nd + 1 - 1 = (nd - 1) + 1 by omega, List.getElem?_cons_succ]
        exact hds

def nestedIndicesSound : Prop :=
  ∀ (ops : List (List Nat)) raw result,
    buildNested opmap ops (some raw) = .ok (some result) →
    ∃ normalized, mapNested opmap raw = .ok normalized ∧ result.length = normalized.length ∧
    ∀ (r d i : Nat) out key limits,
      normalized[r]? = some (key, limits) → result[r]? = some (d, i, out) →
      namesOp ops key d i ∧ out.length = limits.length ∧
      ∀ (k nd ni : Nat) inner mx resultLimit,
        limits[k]? = some (inner, mx) → out[k]? = some (nd, ni, resultLimit) →
        namesOp ops inner nd ni ∧ resultLimit = mx

def nestedFirstIndex : Prop :=
  ∀ (op : Nat) tail rest raw normalized result,
    let ops := (op :: tail) :: rest
    ops.flatten.Nodup → mapNested opmap raw = .ok normalized →
    buildNested opmap ops (some raw) = .ok (some result) →
    ∀ (r key : Nat) (limits : List (Nat × Int)) (d i : Nat) (out : List (Nat × Nat × Int)),
      normalized[r]? = some (key, limits) →
      result[r]? = some (d, i, out) →
      (key = op → d = 1 ∧ i = 1) ∧
      (∀ (k inner : Nat) (limit : Int) (nd ni : Nat) (resultLimit : Int),
        limits[k]? = some (inner, limit) →
        out[k]? = some (nd, ni, resultLimit) → inner = op → nd = 1 ∧ ni = 1)

private theorem mapM_entries {A B : Type} (f : A → Jl B) (xs : List A)
    (ys : List B) (h : xs.mapM f = .ok ys) :
    ys.length = xs.length ∧ ∀ (k : Nat) (x : A) (y : B),
      xs[k]? = some x → ys[k]? = some y → f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    change Except.ok ([] : List B) = .ok ys at h
    have hy : ys = [] := (Except.ok.inj h).symm
    subst ys
    simp
  | cons a rest ih =>
    cases hf : f a with
    | error err => simp [List.mapM_cons, hf, bind, Except.bind] at h
    | ok b =>
      cases hg : rest.mapM f with
      | error err => simp [List.mapM_cons, hf, hg, bind, Except.bind] at h
      | ok remaining =>
        have hy : b :: remaining = ys := by
          simpa [List.mapM_cons, hf, hg, bind, Except.bind, pure, Except.pure] using h
        subst ys
        obtain ⟨hl, hi⟩ := ih remaining hg
        refine ⟨by simp [hl], ?_⟩
        intro k x y hx hy
        cases k with
        | zero =>
          simp at hx hy
          simpa [← hx, ← hy] using hf
        | succ k => exact hi k x y (by simpa using hx) (by simpa using hy)

private theorem requireOp_ok {ops : List (List Nat)} {op d i : Nat}
    (h : requireOp ops op = .ok (d, i)) : locateOp op ops = some (d, i) := by
  cases hl : locateOp op ops with
  | none =>
    rw [requireOp, hl] at h
    cases h
  | some j => simpa [requireOp, hl, pure, Except.pure] using h

private theorem buildNested_entries {ops : List (List Nat)} {raw : NestedInput}
    {result : List (Nat × Nat × List (Nat × Nat × Int))}
    (h : buildNested opmap ops (some raw) = .ok (some result)) :
    ∃ normalized, mapNested opmap raw = .ok normalized ∧ result.length = normalized.length ∧
    ∀ (r d i : Nat) (out : List (Nat × Nat × Int)) (key : Nat) (limits : List (Nat × Int)),
      normalized[r]? = some (key, limits) → result[r]? = some (d, i, out) →
      locateOp key ops = some (d, i) ∧ out.length = limits.length ∧
      ∀ (k nd ni inner : Nat) (mx resultLimit : Int),
        limits[k]? = some (inner, mx) → out[k]? = some (nd, ni, resultLimit) →
        locateOp inner ops = some (nd, ni) ∧ resultLimit = mx := by
  simp only [buildNested] at h
  split at h
  · cases h
  cases hn : mapNested opmap raw with
  | error err => simp [hn, bind, Except.bind] at h
  | ok normalized =>
    simp only [hn, bind, Except.bind] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i mapped hm
        have he : mapped = result := by simpa [pure, Except.pure] using h
        subst mapped
        obtain ⟨hlen, hentries⟩ := mapM_entries _ _ _ hm
        refine ⟨normalized, rfl, hlen, ?_⟩
        intro r d i out key limits hk hd
        have ho := hentries r (key, limits) (d, i, out) hk hd
        cases hl : requireOp ops key with
        | error err => simp [hl, bind, Except.bind] at ho
        | ok pos =>
          rcases pos with ⟨degree, index⟩
          simp only [hl, bind, Except.bind] at ho
          split at ho
          · contradiction
          · rename_i output houtput
            have he : degree = d ∧ index = i ∧ output = out := by
              simpa [pure, Except.pure] using ho
            rcases he with ⟨rfl, rfl, rfl⟩
            obtain ⟨hlen', hentries'⟩ := mapM_entries _ _ _ houtput
            refine ⟨requireOp_ok hl, hlen', ?_⟩
            intro k nd ni inner mx resultLimit hk hd
            have hi := hentries' k (inner, mx) (nd, ni, resultLimit) hk hd
            cases hp : requireOp ops inner with
            | error err => simp [hp, bind, Except.bind] at hi
            | ok pos =>
              rcases pos with ⟨degree, index⟩
              simp [hp, bind, Except.bind, pure, Except.pure] at hi
              rcases hi with ⟨rfl, rfl, rfl⟩
              exact ⟨requireOp_ok hp, rfl⟩

theorem nestedIndicesSound_holds : nestedIndicesSound := by
  intro ops raw result h
  obtain ⟨normalized, hn, hlen, he⟩ := buildNested_entries h
  refine ⟨normalized, hn, hlen, ?_⟩
  intro r d i out key limits hr hs
  obtain ⟨ho, hl, hi⟩ := he r d i out key limits hr hs
  refine ⟨locateOp_sound _ _ _ _ ho, hl, ?_⟩
  intro k nd ni inner limit resultLimit hlim hout
  obtain ⟨hi, hm⟩ := hi k nd ni inner limit resultLimit hlim hout
  exact ⟨locateOp_sound _ _ _ _ hi, hm⟩

theorem nestedFirstIndex_holds : nestedFirstIndex := by
  dsimp only [nestedFirstIndex]
  intro op tail rest raw normalized result _ hn h
  obtain ⟨actual, ha, _, he⟩ := buildNested_entries h
  rw [hn] at ha
  cases ha
  intro r key limits d i out hr hs
  obtain ⟨ho, _, hi⟩ := he r d i out key limits hr hs
  constructor
  · rintro rfl
    simpa [locateOp, findOp, eq_comm] using ho
  · intro k inner limit nd ni resultLimit hl hout hinner
    subst inner
    simpa [locateOp, findOp, eq_comm] using
      (hi k nd ni op limit resultLimit hl hout).1

/-- An explicit operator enum should accept documented pairs keyed by known functions. -/
def genericOperatorPairs : Prop :=
  ∀ (canon : Nat → Nat) (ops : List (List Nat)) (pairs : List (Nat × ConstraintValue)),
    ops.flatten.Nodup → (∀ p ∈ pairs, p.1 ∈ ops.flatten) →
    ∃ table, buildConstraints canon ops (some (.operatorPairs pairs)) none none = .ok table

theorem genericOperatorPairs_refuted : ¬ genericOperatorPairs := by
  intro h
  obtain ⟨table, ht⟩ := h id [[], [101]] [(101, .tuple [-1, 3])] (by decide) (by simp)
  have he : buildConstraints id [[], [101]] (some (.operatorPairs [(101, .tuple [-1, 3])]))
      none none = .error (.errorException "KeyError: degree is not an operator key") := rfl
  rw [he] at ht
  cases ht

example : buildConstraints opmap [[111], [105]] none none none =
    .ok [[.scalar (-1)], [.tuple [-1, -1]]] := by decide
example : ¬ ([[1, 1]] : List (List Nat)).flatten.Nodup := by decide
example : mapKeys opmap [(5, 0), (105, 1)] = .error
    (.errorException "Operator keys refer to the same operator more than once.") := by decide
example : buildNested opmap [[105]] (some [(5, [(6, 2)])]) =
    .ok (some [(1, 1, [(1, 1, 2)])]) := rfl

end SymReg.SimpCons
