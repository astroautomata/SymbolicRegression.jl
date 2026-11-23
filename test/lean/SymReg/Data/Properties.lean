import SymReg.Data.Core

namespace SymReg.Data
open DynExpr

private def unitIdentity : UnitServices :=
  ⟨pure, pure, pure, pure, fun n => pure (some (List.replicate n 1)),
    fun n => pure (some (List.replicate n 1))⟩

private def numeric (a : In) : Except ConstructionError Built :=
  construct a unitIdentity (.ok ()) (.ok ()) none none (fun _ => .ok (.fin 1))

def constructorChecks : Prop := ∀ (a : In) units rx ry ty dep baseline,
  let run := construct a units rx ry ty dep baseline
  (∀ e, rx = .error e → run = .error (.julia e)) ∧
  (∀ y e, a.y = some y → rx = .ok () → ry = .error e → run = .error (.julia e)) ∧
  (∀ y, a.y = some y → rx = .ok () → ry = .ok () → dep = none →
    a.matrix.ncols ≠ y.length → ∃ msg, run = .error (.dimensionMismatch msg)) ∧
  (∀ e, a.y = none → rx = .ok () → dep = none → baseline ty = .error e → run = .error (.julia e)) ∧
  (∀ b ys ysym xs xsym, a.y = none → rx = .ok () → dep = none → baseline ty = .ok b →
    units.ySi a.yUnits = .ok ys → units.ySym a.yUnits = .ok ysym →
    units.xSi a.xUnits = .ok (some xs) → units.xSym a.xUnits = .ok (some xsym) →
    a.matrix.nrows ≠ xs.length → run = .error (.julia (.errorException
      s!"Number of features ({a.matrix.nrows}) does not match number of units ({xs.length})")))

theorem constructorChecks_holds : constructorChecks := by
  intro a units rx ry ty dep baseline
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e hr
    simp [construct, jl, hr, bind, Except.bind, Except.mapError]
  · intro y e hy hr he
    simp [construct, jl, hy, hr, he, bind, Except.bind, Except.mapError]
  · intro y hy hx hr hd hn
    refine ⟨s!"Number of samples in `X` (size(X, 2) = {a.matrix.ncols}) does not match the length of `y` ({y.length}). `X` should have shape (nfeatures, nsamples).", ?_⟩
    simp [construct, jl, hy, hx, hr, hd, Ne.symm hn, bind, pure, Except.bind,
      Except.pure, Except.mapError, throw, throwThe, MonadExceptOf.throw]
  · intro e hy hx hd he
    simp [construct, jl, hy, hx, hd, he, bind, pure, Except.bind, Except.pure, Except.mapError]
  · intro b ys ysym xs xsym hy hx hd hb hys hsym hs hxs hn
    simp [construct, jl, hy, hx, hd, hb, hys, hsym, hs, hxs, hn, checkUnits,
      checkPresentUnits, bind, pure, Except.bind, Except.pure, Except.mapError]

example : (SymReg.Loss.columnsMatrix [[.fin 1]]).ncols ≠ ([.fin 1, .fin 2] : List JF).length := by decide

def unitPresence : Prop :=
  ∀ a d indices, numeric a = .ok d →
    (hasUnits ⟨d.fields, indices⟩ = true ↔ a.xUnits.isSome ∨ a.yUnits.isSome) ∧
    (a.xUnits = none → ∀ y, a.yUnits = some y →
      d.xSiUnits = some (List.replicate a.matrix.nrows 1) ∧
      d.xSymUnits = some (List.replicate a.matrix.nrows 1))

theorem unitPresence_holds : unitPresence := by
  intro a d indices h
  cases hx : a.xUnits <;> cases hy : a.yUnits <;> cases ht : a.y <;>
    simp [numeric, construct, jl, unitIdentity, hx, hy, ht, checkUnits,
      checkAbsentUnits, checkPresentUnits, Except.bind, Except.mapError, pure, bind, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h <;>
    repeat' first | (solve | cases h; simp [hasUnits]) | split at h | contradiction

example : (numeric ⟨SymReg.Loss.columnsMatrix [[.fin 2]], none, none, 1, none, none,
    none, .namedTuple [], none, some 1⟩).isOk = true := by decide

/-- Independent visitation specification: flatten only named-tuple values. -/
private def observedArrays (x : FillValue Nat) : List Nat :=
  match x with
  | .array r => [r]
  | .namedTuple xs => xs.flatMap observedArrays
  | .nothing | .other _ => []

private def recordFill (r : Nat) (v : Int) : Effect (List (Nat × Int)) Nat :=
  fun trace => (.ok r, trace ++ [(r, v)])

mutual
  private theorem recordValue (x : FillValue Nat) (v : Int) (s : List (Nat × Int)) :
      (fillValue recordFill v x s).2 = s ++ (observedArrays x).map (·, v) ∧
      (fillValue recordFill v x s).1.isOk = true := by
    cases x with
    | array r => simp [fillValue, recordFill, observedArrays, Except.map, Except.isOk, Except.toBool]
    | namedTuple xs => rw [fillValue, recordValues xs v s]; simp [observedArrays, Except.map, Except.isOk, Except.toBool]
    | nothing => simp [fillValue, observedArrays, Except.isOk, Except.toBool]
    | other x => simp [fillValue, observedArrays, Except.isOk, Except.toBool]
  private theorem recordValues (xs : List (FillValue Nat)) (v : Int) (s : List (Nat × Int)) :
      fillValues recordFill v xs s = (.ok (), s ++ (xs.flatMap observedArrays).map (·, v)) := by
    cases xs with
    | nil => simp [fillValues]
    | cons x xs =>
      have h := recordValue x v s
      rw [fillValues]
      cases he : fillValue recordFill v x s with
      | mk out s' =>
        rw [he] at h
        cases out with
        | error e => cases h.2
        | ok r =>
          have hs := h.1
          change s' = _ at hs
          simp only [List.flatMap_cons, List.map_append]
          change fillValues recordFill v xs s' = _
          rw [recordValues xs v s', hs, List.append_assoc]
end

private def properties (x y w extra : FillValue Nat) (_ : Nat) (name : String) :
    Effect (List (Nat × Int)) (FillValue Nat) := fun s =>
  (.ok (if name = "X" then x else if name = "y" then y else if name = "weights" then w else extra), s)

-- Dense arrays retain shape, and writes target an identity in a shared store.
private def denseFill (r : Nat) (v : Int) : Effect (Nat → List Int) Nat :=
  fun s => (.ok r, fun i => if i = r then List.replicate (s i).length v else s i)

private def typedProperties (x : Nat) (y w : Option Nat) (extra : List (FillValue Nat))
    (_ : Nat) (name : String) : Effect (Nat → List Int) (FillValue Nat) := fun s =>
  (.ok (if name = "X" then .array x else if name = "y" then y.elim .nothing .array
    else if name = "weights" then w.elim .nothing .array else .namedTuple extra), s)

private def failingTarget (sizeError : JlError) (x y : Nat) (_ : Nat) (name : String) :
    Effect (Nat → List Int) (FillValue Nat) := fun s =>
  (if name = "X" then .ok (.array x) else if name = "y" then .ok (.array y)
    else .error sizeError, s)

private def fillUnless (bad : Nat) (e : JlError) (r : Nat) (v : Int) : Effect (Nat → List Int) Nat :=
  fun s => if r = bad then (.error e, s) else denseFill r v s

def fillVisits : Prop :=
  (∀ (d x : Nat) (y w : Option Nat) extra (v : Int),
    fillDataset (properties (.array x) (y.elim .nothing .array) (w.elim .nothing .array) (.namedTuple extra)) recordFill d v [] =
      (.ok d, (observedArrays (.array x) ++ observedArrays (y.elim .nothing .array) ++
        observedArrays (w.elim .nothing .array) ++ extra.flatMap observedArrays).map (·, v))) ∧
  (∀ (d x : Nat) (v : Int) s,
    let r := fillDataset (typedProperties x none none []) denseFill d v s
    r.1 = .ok d ∧ r.2 x = List.replicate (s x).length v ∧ (∀ i, i ≠ x → r.2 i = s i)) ∧
  (∀ (d x y : Nat) (v : Int) e s, x ≠ y →
    let r := fillDataset (failingTarget e x y) (fillUnless y e) d v s
    r.1 = .error e ∧ r.2 x = List.replicate (s x).length v ∧ r.2 y = s y)

private theorem fillGo (r : String → FillValue Nat) (d : Nat) (v : Int)
    (fs : List String) (s : List (Nat × Int)) :
    fillDataset.go (fun _ name trace => (.ok (r name), trace)) recordFill d v fs s =
      (.ok d, s ++ (fs.flatMap fun f => observedArrays (r f)).map (·, v)) := by
  induction fs generalizing s with
  | nil => simp [fillDataset.go]
  | cons f fs ih =>
    have h := recordValue (r f) v s
    rw [fillDataset.go]
    cases he : fillValue recordFill v (r f) s with
    | mk out s' =>
      rw [he] at h
      cases out with
      | error e => cases h.2
      | ok a =>
        have hs := h.1
        change s' = _ at hs
        simp [he, ih, hs, List.append_assoc]

theorem fillVisits_holds : fillVisits := by
  refine ⟨?_, ?_, ?_⟩
  · intro d x y w extra v
    unfold fillDataset properties
    rw [fillGo]
    simp [observedArrays, List.append_assoc]
  · intro d x v s
    refine ⟨rfl, ?_, ?_⟩
    · simp [fillDataset, fillDataset.go, typedProperties, fillValue, fillValues, denseFill, Except.map]
    · intro i hi
      simp [fillDataset, fillDataset.go, typedProperties, fillValue, fillValues, denseFill, Except.map, hi]
  · intro d x y v e s hxy
    simp [fillDataset, fillDataset.go, failingTarget, fillValue, fillUnless, denseFill, Except.map, hxy, Ne.symm hxy]

def batchMetadata : Prop :=
  ∀ d (indices : List Int) names (size : Int),
    let b := batch d indices
    getFullDataset b = d ∧ getIndices b = some indices ∧
    propertyNames names b = propertyNames names ⟨d, none⟩ ∧ sampleCount b = indices.length ∧
    (∀ (R : Type) (rng : R) sample,
      (∀ e, sample rng d.columns.length size = .error e → batchDefault sample rng d size = .error e) ∧
      (sample rng d.columns.length size = .ok indices → batchDefault sample rng d size = .ok b))

theorem batchMetadata_holds : batchMetadata := by
  intro d indices names size
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro R rng sample
  constructor <;> intros <;> simp_all [batchDefault, batchWithRNG, Except.map]

open DynExpr.Registry

def entries : List Entry := [
  { id := "dataset-constructor-checks", juliaFile := "src/Dataset.jl",
    juliaFns := ["Dataset", "error_on_mismatched_size"],
    statement := "Indexing errors take precedence over constructor shape checks. The constructor rejects mismatched target length before baseline initialization and validates the length of the converted SI feature units.",
    preconditions := "Shape-error clauses require earlier stages to succeed on the nondeprecated path; the SI mismatch clause uses absent targets and supplied converted units."
    status := .proven, prop := ``constructorChecks, thm := some ``constructorChecks_holds,
    notes := "The constructor accepts arbitrary NamedTuple extra payloads and never checks weight length; see cfg-weights-shape." },
  { id := "dataset-unit-presence", juliaFile := "src/Dataset.jl",
    juliaFns := ["Dataset", "has_units"],
    statement := "Feature or target units make has_units true for full datasets and batches. Target-only units initialize one dimensionless unit per feature in both representations.",
    preconditions := "Ordinary numeric data and supported units, with successful construction.",
    status := .proven, prop := ``unitPresence, thm := some ``unitPresence_holds },
  { id := "dataset-fill-visits", juliaFile := "src/Dataset.jl",
    juliaFns := ["fill!", "_fill!"],
    statement := "In-place fill visits X, y, weights and named-tuple array leaves in order. Dense fill changes array contents, preserves shape and unrelated arrays, and retains earlier writes if filling the target fails.",
    preconditions := "Stock dataset field types; dense-array storage is modeled by a shared store."
    status := .proven, prop := ``fillVisits, thm := some ``fillVisits_holds },
  { id := "dataset-batch-metadata", juliaFile := "src/Dataset.jl",
    juliaFns := ["batch", "get_full_dataset", "get_indices", "propertynames", "getproperty"],
    statement := "A batch retains its source and signed indices unchanged, counts repeated samples, and forwards property names. Random batch construction forwards the exact sampler error or wraps the drawn indices."
    preconditions := "None; sampler receives the signed size, including negative sizes."
    status := .proven, prop := ``batchMetadata, thm := some ``batchMetadata_holds }
]

end SymReg.Data
