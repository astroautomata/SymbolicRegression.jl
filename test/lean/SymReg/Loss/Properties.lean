import SymReg.Data.Core
import SymReg.Units.Core
import SymReg.Loss.Headroom

namespace SymReg.Loss
open DynExpr SymReg.HeapLemmas

/-- Ordered floating-point operations for a prescribed divisor and complexity.
The Float64 parsimony product promotes its integer count before multiplying. -/
def costWithDivisor (p : LossPrecision) (loss divisor parsimony : JF) (size : Int) : JF :=
  let count := LossPrecision.float64.round (.fin (size : Rat))
  let term := LossPrecision.float64.round (count * parsimony)
  p.round (p.round (loss / divisor) + p.round term)

private def ieeeCostSpec (p : LossPrecision) (loss divisor parsimony : SignedFloat)
    (n : Int64) : SignedFloat :=
  let size := SignedFloat.ordinary (LossPrecision.float64.round (.fin (n.toInt : Rat)))
  let penalty := (SignedFloat.mul .float64 size parsimony).convert p
  SignedFloat.add p (SignedFloat.div p loss divisor) penalty

/-- Disabled baseline use does not depend on the stored baseline. -/
def disabled_floor : Prop :=
  ∀ (p : LossPrecision) (loss baseline other parsimony : SignedFloat)
    (member : Nat) (S : Type) (compute : Nat → S → Jl Int64 × S)
    (size : Option Int64) (s : S),
    loss.Representable p → baseline.Representable p → other.Representable p →
    parsimony.Representable .float64 →
    lossToCostIEEE p loss false baseline parsimony member compute size s =
      lossToCostIEEE p loss false other parsimony member compute size s ∧
    ∀ n, size = some n →
      lossToCostIEEE p loss false baseline parsimony member compute size s =
        (.ok (ieeeCostSpec p loss (.ordinary (.fin p.floor)) parsimony n), s)

theorem disabled_floor_holds : disabled_floor := by
  intro p loss baseline other parsimony member S compute size s _ _ _ _
  refine ⟨?_, ?_⟩
  · simp [lossToCostIEEE]
  · intro n hn
    subst size
    simp [lossToCostIEEE, costAfterDivisor, ieeeCostSpec, Except.map]

/-- Numeric comparison with the already converted threshold, independent of the
normalization helper. `NaN` is unordered. -/
def belowOrUnordered (baseline : JF) (floor : Rat) : Prop :=
  match baseline with
  | .nan | .negInf => True
  | .fin b => b < floor
  | .posInf => False

def ineligible_floor : Prop :=
  ∀ (p : LossPrecision) (loss baseline parsimony : SignedFloat)
    (member : Nat) (S : Type) (compute : Nat → S → Jl Int64 × S)
    (size : Option Int64) (s : S),
    loss.Representable p → baseline.Representable p → parsimony.Representable .float64 →
    belowOrUnordered baseline.value p.floor →
    lossToCostIEEE p loss true baseline parsimony member compute size s =
      lossToCostIEEE p loss false baseline parsimony member compute size s ∧
    ∀ n, size = some n →
      lossToCostIEEE p loss true baseline parsimony member compute size s =
        (.ok (ieeeCostSpec p loss (.ordinary (.fin p.floor)) parsimony n), s)

theorem ineligible_floor_holds : ineligible_floor := by
  intro p loss baseline parsimony member S compute size s _ _ _ h
  have ineligible : baselineEligible p baseline.value = false := by
    cases hv : baseline.value with
    | fin b =>
      rw [hv] at h
      exact decide_eq_false (Rat.not_le.mpr h)
    | posInf =>
      rw [hv] at h
      exact False.elim h
    | nan | negInf => rfl
  refine ⟨?_, ?_⟩
  · simp [lossToCostIEEE, ineligible]
  · intro n hn
    subst size
    simp [lossToCostIEEE, ineligible, costAfterDivisor, ieeeCostSpec, Except.map]

example : belowOrUnordered .nan LossPrecision.float32.floor := True.intro

private abbrev BaselineWorld (R L W : Type) := (Nat → BaselineFields R L) × W

private def storeBaseline {R L W : Type} (d : Nat) (loss : L) :
    LossEffect (BaselineWorld R L W) Unit := fun (fields, world) =>
  (.ok (), (fun a => if a = d then { fields a with loss } else fields a, world))

private def storeBaselineEnabled {R L W : Type} (d : Nat) (enabled : Bool) :
    LossEffect (BaselineWorld R L W) Unit := fun (fields, world) =>
  (.ok (), (fun a => if a = d then { fields a with enabled } else fields a, world))

private theorem baseline_write_frame {R L W : Type} (d : Nat)
    (loss : L) (enabled : Bool) (s : BaselineWorld R L W) :
    let after := (storeBaselineEnabled d enabled (storeBaseline d loss s).2).2
    (after.1 d).loss = loss ∧ (after.1 d).enabled = enabled ∧
      (∀ a, (after.1 a).references = (s.1 a).references) ∧
      (∀ a, a ≠ d → after.1 a = s.1 a) ∧ after.2 = s.2 := by
  simp only [storeBaseline, storeBaselineEnabled, ↓reduceIte]
  refine ⟨by simp, by simp, ?_, ?_, trivial⟩
  · intro a
    by_cases h : a = d <;> simp [h]
  · intro a ha
    simp [ha]

theorem baseline_effect_success {R L W T E : Type}
    (init : LossEffect (BaselineWorld R L W) T)
    (create : T → Nat → LossEffect (BaselineWorld R L W) E)
    (eval : E → Nat → LossEffect (BaselineWorld R L W) L)
    (finite : L → LossEffect (BaselineWorld R L W) Bool)
    (one : LossEffect (BaselineWorld R L W) L)
    (d : Nat) (start s₁ s₂ s₃ checked ready : BaselineWorld R L W)
    (t : T) (e : E) (loss baseline : L) (enabled : Bool)
    (hi : init start = (.ok t, s₁)) (hc : create t d s₁ = (.ok e, s₂))
    (he : eval e d s₂ = (.ok loss, s₃)) (hf : finite loss s₃ = (.ok enabled, checked))
    (hOne : if enabled then baseline = loss ∧ ready = checked else
      one checked = (.ok baseline, ready)) :
    ∃ after, updateBaselineFields init create eval finite one storeBaseline
        storeBaselineEnabled d start = (.ok (), after) ∧
      (after.1 d).loss = baseline ∧ (after.1 d).enabled = enabled ∧
      (∀ a, (after.1 a).references = (ready.1 a).references) ∧
      (∀ a, a ≠ d → after.1 a = ready.1 a) ∧ after.2 = ready.2 := by
  refine ⟨(storeBaselineEnabled d enabled (storeBaseline d baseline ready).2).2, ?_,
    baseline_write_frame d baseline enabled ready⟩
  cases enabled
  · simp only [Bool.false_eq_true, ↓reduceIte] at hOne
    simp [updateBaselineFields, hi, hc, he, hf, hOne, storeBaseline, storeBaselineEnabled]
  · simp only [↓reduceIte] at hOne
    obtain ⟨rfl, rfl⟩ := hOne
    simp [updateBaselineFields, hi, hc, he, hf, storeBaseline, storeBaselineEnabled]

theorem baseline_effect_failures {R L W T E : Type}
    (init : LossEffect (BaselineWorld R L W) T)
    (create : T → Nat → LossEffect (BaselineWorld R L W) E)
    (eval : E → Nat → LossEffect (BaselineWorld R L W) L)
    (finite : L → LossEffect (BaselineWorld R L W) Bool)
    (one : LossEffect (BaselineWorld R L W) L)
    (d : Nat) (start : BaselineWorld R L W) :
    let update := updateBaselineFields init create eval finite one storeBaseline
      storeBaselineEnabled d start
    (∀ err after, init start = (.error err, after) → update = (.error err, after)) ∧
    ∀ t s₁, init start = (.ok t, s₁) →
      (∀ err after, create t d s₁ = (.error err, after) → update = (.error err, after)) ∧
      ∀ e s₂, create t d s₁ = (.ok e, s₂) →
        ∀ err after, eval e d s₂ = (.error err, after) → update = (.error err, after) := by
  dsimp only
  constructor
  · intro err after h
    simp [updateBaselineFields, h]
  · intro t s₁ hi
    constructor
    · intro err after h
      simp [updateBaselineFields, hi, h]
    · intro e s₂ hc err after h
      simp [updateBaselineFields, hi, hc, h]

def baseline_update : Prop :=
  ∀ (R W T E L : Type) (initial : InitValueMethod (BaselineWorld R L W) T)
    (create : T → Nat → LossEffect (BaselineWorld R L W) E)
    (eval : E → Nat → LossEffect (BaselineWorld R L W) L)
    (finite : L → LossEffect (BaselineWorld R L W) Bool)
    (one : LossEffect (BaselineWorld R L W) L) (d : Nat) (start : BaselineWorld R L W),
    let init := initValue initial
    let update := updateBaselineFields init create eval finite one
      storeBaseline storeBaselineEnabled d start
    (∀ err after, init start = (.error err, after) → update = (.error err, after)) ∧
    ∀ t s₁, init start = (.ok t, s₁) →
      (∀ err after, create t d s₁ = (.error err, after) → update = (.error err, after)) ∧
      ∀ e s₂, create t d s₁ = (.ok e, s₂) →
        (∀ err after, eval e d s₂ = (.error err, after) → update = (.error err, after)) ∧
        ∀ loss s₃, eval e d s₂ = (.ok loss, s₃) →
          (∀ err after, finite loss s₃ = (.error err, after) → update = (.error err, after)) ∧
          ∀ enabled checked, finite loss s₃ = (.ok enabled, checked) →
            (enabled = false → ∀ err after, one checked = (.error err, after) →
              update = (.error err, after)) ∧
            ∀ value ready, (if enabled then value = loss ∧ ready = checked
              else one checked = (.ok value, ready)) →
              ∃ after, update = (.ok (), after) ∧ (after.1 d).loss = value ∧
                (after.1 d).enabled = enabled

theorem baseline_update_holds : baseline_update := by
  intro R W T E L initial create eval finite one d start
  let init := initValue initial
  obtain ⟨initError, rest⟩ := baseline_effect_failures init create eval finite one d start
  refine ⟨initError, ?_⟩
  intro t s₁ hi
  obtain ⟨createError, rest⟩ := rest t s₁ hi
  refine ⟨createError, ?_⟩
  intro e s₂ hc
  refine ⟨rest e s₂ hc, ?_⟩
  intro loss s₃ he
  refine ⟨?_, ?_⟩
  · intro err after hf
    simp [updateBaselineFields, hi, hc, he, hf, init]
  · intro enabled checked hf
    refine ⟨?_, ?_⟩
    · rintro rfl err after ho
      simp [updateBaselineFields, hi, hc, he, hf, ho, init]
    · intro value ready hv
      obtain ⟨after, h, hl, hb, _⟩ := baseline_effect_success init create eval finite one
        d start s₁ s₂ s₃ checked ready t e loss value enabled hi hc he hf hv
      exact ⟨after, h, hl, hb⟩

example : initValue (S := Unit) (.numeric (T := JF) (fun s => (.ok (.fin 0), s))) () =
    (.ok (.fin 0), ()) := rfl

example : initValue (S := Unit) (.extension (fun s => (.ok (3 : Int), s))) () =
    (.ok 3, ()) := rfl

private def ieeeFinite {S : Type} (v : SignedFloat) : LossEffect S Bool :=
  fun s => (.ok v.value.valid, s)

private def ieeeOne {S : Type} : LossEffect S SignedFloat :=
  fun s => (.ok (.ordinary (.fin 1)), s)

private def updateIEEEBaseline {R W T E : Type}
    (initial : InitValueMethod (BaselineWorld R SignedFloat W) T)
    (create : T → Nat → LossEffect (BaselineWorld R SignedFloat W) E)
    (eval : E → Nat → LossEffect (BaselineWorld R SignedFloat W) SignedFloat)
    (d : Nat) : LossEffect (BaselineWorld R SignedFloat W) Unit :=
  updateBaselineFields (initValue initial) create eval ieeeFinite ieeeOne
    storeBaseline storeBaselineEnabled d

def baseline_finite : Prop :=
  ∀ (R W T E : Type) (zero : LossEffect (BaselineWorld R SignedFloat W) T)
    (create : T → Nat → LossEffect (BaselineWorld R SignedFloat W) E)
    (eval : E → Nat → LossEffect (BaselineWorld R SignedFloat W) SignedFloat)
    (d : Nat) (start s₁ s₂ s₃ : BaselineWorld R SignedFloat W)
    (t : T) (e : E) (p : LossPrecision) (value : SignedFloat),
    value.Representable p →
    (∃ q, value.value = .fin q) →
    zero start = (.ok t, s₁) →
    create t d s₁ = (.ok e, s₂) →
    eval e d s₂ = (.ok value, s₃) →
    ∃ after, updateIEEEBaseline (.numeric zero) create eval d start =
          (.ok (), after) ∧ (after.1 d).loss = value ∧ (after.1 d).enabled = true

theorem baseline_finite_holds : baseline_finite := by
  intro R W T E zero create eval d start s₁ s₂ s₃ t e p value _ hv hi hc he
  obtain ⟨q, hq⟩ := hv
  have hf : ieeeFinite value s₃ = (.ok true, s₃) := by simp [ieeeFinite, hq, JF.valid]
  obtain ⟨after, h, hl, hb, _⟩ := baseline_effect_success zero create eval ieeeFinite ieeeOne
    d start s₁ s₂ s₃ s₃ s₃ t e value value true hi hc he hf ⟨rfl, rfl⟩
  exact ⟨after, h, hl, hb⟩

def baseline_nonfinite : Prop :=
  ∀ (R W T E : Type) (zero : LossEffect (BaselineWorld R SignedFloat W) T)
    (create : T → Nat → LossEffect (BaselineWorld R SignedFloat W) E)
    (eval : E → Nat → LossEffect (BaselineWorld R SignedFloat W) SignedFloat)
    (d : Nat) (start s₁ s₂ s₃ : BaselineWorld R SignedFloat W)
    (t : T) (e : E) (value : SignedFloat),
    (value.value = .nan ∨ value.value = .posInf ∨ value.value = .negInf) →
    zero start = (.ok t, s₁) →
    create t d s₁ = (.ok e, s₂) →
    eval e d s₂ = (.ok value, s₃) →
    ∃ after, updateIEEEBaseline (.numeric zero) create eval d start =
          (.ok (), after) ∧ (after.1 d).loss = .ordinary (.fin 1) ∧
          (after.1 d).enabled = false

theorem baseline_nonfinite_holds : baseline_nonfinite := by
  intro R W T E zero create eval d start s₁ s₂ s₃ t e value hv hi hc he
  have hf : ieeeFinite value s₃ = (.ok false, s₃) := by
    rcases hv with h | h | h <;> simp [ieeeFinite, h, JF.valid]
  obtain ⟨after, h, hl, hb, _⟩ := baseline_effect_success zero create eval ieeeFinite ieeeOne
    d start s₁ s₂ s₃ s₃ s₃ t e value (.ordinary (.fin 1)) false hi hc he hf rfl
  exact ⟨after, h, hl, hb⟩

example : SignedFloat.negativeZero.Representable .float32 ∧
    ∃ q, SignedFloat.negativeZero.value = .fin q := ⟨rfl, 0, rfl⟩

example : SignedFloat.value (.ordinary .nan) = .nan := rfl

/-- Dispatch never reports completion for an absent prediction. -/
def dispatch_missing : Prop :=
  ∀ complete : Bool, dispatchReply (none, complete) = (none, false)

theorem dispatch_missing_holds : dispatch_missing := by
  intro complete
  rfl

/-- The DE adapter preserves both the array and its completion flag. -/
def de_contract : Prop :=
  ∀ (prediction : JVec JF) (complete : Bool),
    fromDE (.ok (prediction, complete)) = .ok (some prediction, complete) ∧
    dispatchReply (some prediction, complete) = (some prediction, complete)

theorem de_contract_holds : de_contract := by
  intro prediction complete
  exact ⟨rfl, rfl⟩

private def batchData (d : Basic) (indices : List Int) : Dataset :=
  ⟨d, some (indices.map Int.toNat)⟩

private def observation {A : Type} (xs : List A) (i : Int) : Option A :=
  if i < 1 then none else xs[(i - 1).toNat]?

private def fieldSpec {A : Type} (xs : List A) (indices : List Int) : Jl (List A) :=
  let samples := indices.filterMap (observation xs)
  if samples.length = indices.length then .ok samples else .error .boundsError

private def optionalFieldSpec (xs : Option (List JF)) (indices : List Int) :
    Jl (Option (List JF)) :=
  match xs with
  | none => .ok none
  | some xs => (fieldSpec xs indices).map some

/-- Value and bounds projections of the batch views. Nonpositive `Int`
indices reach the same bounds failure as zero in the list evaluator. -/
def batch_fields : Prop :=
  ∀ (d : Basic) (indices : List Int),
    let b := batchData d indices
    Data.sampleCount (Data.batch d indices) = indices.length ∧
    getX b = fieldSpec d.columns indices ∧
    getTarget b = optionalFieldSpec d.y indices ∧
    getWeights b = optionalFieldSpec d.weights indices

private def atBatchPosition {A : Type} (get : Dataset → Jl (List A))
    (xs : List A) (d : Basic) (indices : List Int) : Prop :=
  (∀ i, i ∈ indices → (observation xs i).isSome) →
  ∀ (k : Nat) (i : Int) (x : A),
    indices[k]? = some i → observation xs i = some x →
    ∃ values, get (batchData d indices) = .ok values ∧ values[k]? = some x

private def orderedFields (d : Basic) (indices : List Int) : Prop :=
  atBatchPosition getX d.columns d indices ∧
  (∀ y, d.y = some y → atBatchPosition getY y d indices) ∧
  ∀ w, d.weights = some w →
    atBatchPosition (fun b => do
      match ← getWeights b with
      | none => throw .boundsError
      | some ws => pure ws) w d indices

def batch_order : Prop :=
  ∀ (d : Basic),
    (∀ indices, orderedFields d indices) ∧
    ∀ (R : Type) (rng : R) (draw : R → Nat → Int → Jl (List Int)) (size : Int)
      (batch : Data.BatchView),
      Data.batchWithRNG draw rng d size = .ok batch →
      ∃ indices, draw rng d.columns.length size = .ok indices ∧
        Data.getIndices batch = some indices ∧ orderedFields d indices

/-- An explicitly provided index vector makes the batched and unbatched
four-argument calls indistinguishable. -/
def evaluator_explicit : Prop :=
  ∀ (f : Objective) (e : Expr) (d : Basic) (idx : List Nat) (a b : Option (List Nat)),
    f.accepts4 e d (some idx) = true →
    evaluator f e ⟨d, a⟩ (some idx) = evaluator f e ⟨d, b⟩ (some idx) ∧
    evaluator f e ⟨d, a⟩ (some idx) = f.call4 e d (some idx)

def evaluator_inherited : Prop :=
  ∀ (f : Objective) (e : Expr) (d : Basic) (stored : Option (List Nat)),
    f.accepts4 e d stored = true →
    evaluator f e ⟨d, stored⟩ none = f.call4 e d stored ∧
    ∀ idx, stored = some idx →
      evaluator f e ⟨d, stored⟩ none = evaluator f e ⟨d, none⟩ (some idx)

def evaluator_three : Prop :=
  ∀ (f : Objective) (e : Expr) (d : Dataset) (idx : Option (List Nat)),
    f.accepts4 e d.full (idx.or d.indices) = false →
    evaluator f e d idx = f.call3 e d ∧
    ∀ i, f.accepts4 e d.full (i.or d.indices) = false →
      evaluator f e d idx = evaluator f e d i

theorem evaluator_explicit_holds : evaluator_explicit := by
  intro f e d idx a b h
  simp [evaluator, evaluatorWith, h]

theorem evaluator_inherited_holds : evaluator_inherited := by
  intro f e d stored h
  refine ⟨by simp [evaluator, evaluatorWith, h], ?_⟩
  intro idx hi
  subst stored
  simp [evaluator, evaluatorWith, h]

theorem evaluator_three_holds : evaluator_three := by
  intro f e d idx h
  exact ⟨by simp [evaluator, evaluatorWith, h],
    fun i hi => by simp [evaluator, evaluatorWith, h, hi]⟩

structure ObjectiveRef where
  address : Nat
  typeId : Nat

inductive ObjectiveData where
  | basic (ref : ObjectiveRef)
  | batch (ref full indices : ObjectiveRef)

def ObjectiveData.original : ObjectiveData → ObjectiveRef
  | .basic ref | .batch ref _ _ => ref

def ObjectiveData.full : ObjectiveData → ObjectiveRef
  | .basic ref | .batch _ ref _ => ref

def ObjectiveData.indices : ObjectiveData → Option ObjectiveRef
  | .basic _ => none
  | .batch _ _ indices => some indices

/-- Julia method lookup sees only the concrete argument types. Calls see the
original objects, including the options and the index vector. -/
structure ObjectiveMethods (L : Type) where
  nothingType : Nat
  method3 : Nat × Nat × Nat → Option (ObjectiveRef → ObjectiveRef → ObjectiveRef → Jl L)
  method4 : Nat × Nat × Nat × Nat →
    Option (ObjectiveRef → ObjectiveRef → ObjectiveRef → Option ObjectiveRef → Jl L)

private def objectiveTypes4 (nothingType : Nat) (tree full options : ObjectiveRef)
    (i : Option ObjectiveRef) : Nat × Nat × Nat × Nat :=
  (tree.typeId, full.typeId, options.typeId, (i.map ObjectiveRef.typeId).getD nothingType)

def typedEvaluator {L : Type} (f : ObjectiveMethods L) (tree : ObjectiveRef)
    (data : ObjectiveData) (options : ObjectiveRef) (idx : Option ObjectiveRef) : Jl L :=
  let four := fun e d o i => f.method4 (objectiveTypes4 f.nothingType e d o i)
  evaluatorWith ObjectiveData.full ObjectiveData.indices (fun e d o i => (four e d o i).isSome)
    (fun e d o => match f.method3 (e.typeId, d.original.typeId, o.typeId) with
      | some method => method e d.original o
      | none => .error (.methodError "three-argument objective"))
    (fun e d o i => match four e d o i with
      | some method => method e d o i
      | none => .error (.methodError "four-argument objective")) tree data options idx

theorem typedEvaluator_four {L : Type} (f : ObjectiveMethods L)
    (tree options : ObjectiveRef) (d : ObjectiveData) (i : Option ObjectiveRef)
    (method : ObjectiveRef → ObjectiveRef → ObjectiveRef → Option ObjectiveRef → Jl L)
    (h : f.method4 (objectiveTypes4 f.nothingType tree d.full options (i.or d.indices)) = some method) :
    typedEvaluator f tree d options i = method tree d.full options (i.or d.indices) := by
  simp [typedEvaluator, evaluatorWith, h]

theorem typedEvaluator_three {L : Type} (f : ObjectiveMethods L)
    (tree options : ObjectiveRef) (d : ObjectiveData) (i : Option ObjectiveRef)
    (h : f.method4 (objectiveTypes4 f.nothingType tree d.full options (i.or d.indices)) = none) :
    typedEvaluator f tree d options i =
      match f.method3 (tree.typeId, d.original.typeId, options.typeId) with
      | some method => method tree d.original options
      | none => .error (.methodError "three-argument objective") := by
  simp [typedEvaluator, evaluatorWith, h]

example (stored explicit : ObjectiveRef) :
    typedEvaluator (L := Nat)
      ⟨0, fun _ => none, fun sig => if sig.2.2.2 = explicit.typeId then
        some (fun _ _ _ i => .ok (i.map ObjectiveRef.address |>.getD 0)) else none⟩
      ⟨1, 1⟩ (.batch ⟨2, 2⟩ ⟨3, 3⟩ stored) ⟨4, 4⟩ (some explicit) = .ok explicit.address := by
  simp [typedEvaluator, evaluatorWith, objectiveTypes4, ObjectiveData.full]

/-- A node objective takes priority over the expression objective, unwraps the tree,
and neither resets the context nor adds dimensional regularization. -/
def node_objective : Prop :=
  ∀ (e : Expr) (d : Dataset) (o : Options) (f : Objective) (regularization : Bool)
    (idx : Option (List Nat)) (context : Option Context),
    evalLoss e d { o with lossFunction := some f } regularization idx context =
      (evaluator f (.node e.tree) d idx).map (fun value => (value, context))

theorem node_objective_holds : node_objective := by
  intro e d o f regularization idx context
  simp [evalLoss, processContext]
  rfl

/-- Probe the callback's first argument rather than comparing two calls to the
same evaluator. Both callback arities can read the whole expression projection. -/
def expression_objective : Prop :=
  ∀ (t : Tree JF) (metadata : Nat) (d : Dataset) (o : Options)
    (reg useFour : Bool) (idx : Option (List Nat)) (context : Option Context)
    (observe : Expr → Jl JF),
    let e := Expr.expression t metadata
    let f : Objective := ⟨fun _ _ _ => useFour, fun v _ => observe v, fun v _ _ => observe v⟩
    evalLoss e d { o with lossFunction := none, lossFunctionExpression := some f }
      reg idx context = (observe e).map (fun v => (v, context))

/-- Expression-only objectives reject a bare node before invoking the callback. -/
def expression_assertion : Prop :=
  ∀ (t : Tree JF) (d : Dataset) (o : Options) (f : Objective) (regularization : Bool)
    (idx : Option (List Nat)) (context : Option Context),
    evalLoss (.node t) d
      { o with lossFunction := none, lossFunctionExpression := some f }
      regularization idx context =
      .error (.assertionError "tree isa AbstractExpression")

theorem expression_assertion_holds : expression_assertion := by
  intro t d o f regularization idx context
  rfl

/-- Unsupported evaluation-context backends skip allocation and even dataset access. -/
def context_bypass : Prop :=
  ∀ (d : Dataset) (o : Options) (numArrays : Int),
    (o.bumper || !o.takesContext) = true →
    createEvalContext d o numArrays = .ok none

theorem context_bypass_holds : context_bypass := by
  intro d o numArrays h
  simp [createEvalContext, h]
  rfl

def context_storage : Prop :=
  ∀ (d : Dataset) (o : Options) (numArrays : Int),
    (o.bumper || !o.takesContext) = false →
    (∀ e, getX d = .error e → createEvalContext d o numArrays = .error e) ∧
    ∀ c, createEvalContext d o numArrays = .ok (some c) →
      c.turbo = o.turbo ∧ ∃ slots columns, getX d = .ok columns ∧
        c.buffer = .vec slots 0 ∧ slots.size = numArrays.toNat ∧
        ∀ slot ∈ slots.toList, slot.size = columns.length

def context_reset : Prop :=
  ∀ (c : Context),
    let after := resetContext (some c)
    resetContext after = after ∧
    ∃ c', after = some c' ∧ c'.turbo = c.turbo ∧
      (match c.buffer, c'.buffer with
      | .none, .none => True
      | .mat data _, .mat newData i => newData = data ∧ i = 0
      | .vec data _, .vec newData i => newData = data ∧ i = 0
      | _, _ => False)

theorem context_reset_holds : context_reset := by
  intro c
  cases c with
  | mk turbo bumper early buffer strict =>
    cases buffer <;> exact ⟨rfl, _, rfl, rfl, by simp [resetContext, resetBuffer]⟩

-- Source: DynamicExpressions.jl src/Evaluate.jl:65-66
-- reset_index!(buffer::ArrayBuffer) = buffer.index[] = 0
-- reset_index!(::Nothing) = nothing
def resetIndexReference (ref : Option Nat) (indices : Nat → Int) : Nat → Int :=
  match ref with
  | none => indices
  | some address => fun a => if a = address then 0 else indices a

theorem resetIndexAliased (indices : Nat → Int) (a : Nat) :
    let reset := resetIndexReference (some a) indices
    reset a = 0 ∧ (∀ j, j ≠ a → reset j = indices j) ∧
      resetIndexReference (some a) reset = reset := by
  dsimp [resetIndexReference]
  refine ⟨by simp, by simp_all, ?_⟩
  funext j
  by_cases hj : j = a <;> simp [hj]

abbrev EvalM (S : Type) := EStateM JlError S

structure ContextWorld (H : Type) where
  indices : Nat → Int
  heap : H

def resetBorrowedContext {H : Type} (ref : Option Nat) : EvalM (ContextWorld H) Unit :=
  fun w => .ok () { w with indices := resetIndexReference ref w.indices }

inductive ExpectedOutput where
  | any
  | concrete (typeId : Nat)

structure TypedPrediction (P : Type) where
  typeId : Nat
  value : P

def ExpectedOutput.accepts (expected : ExpectedOutput) (id : Nat) : Bool :=
  match expected with
  | .any => true
  | .concrete ty => decide (ty = id)

structure DispatchStages (H X P : Type) where
  readX : Unit → EvalM (ContextWorld H) X
  expected : X → EvalM (ContextWorld H) ExpectedOutput
  evaluate : X → EvalM (ContextWorld H) (Option (TypedPrediction P) × Option Bool)

def DispatchStages.run {H X P : Type} (st : DispatchStages H X P) :
    EvalM (ContextWorld H) (Option P × Bool) :=
  evalDispatchWith st.readX st.expected st.evaluate
    (fun expected out s => if expected.accepts out.typeId then .ok out.value s else
      .error (.errorException "TypeError: prediction array") s)
    (fun flag s => match flag with
      | some b => .ok b s
      | none => .error (.errorException "TypeError: completion flag") s)

structure LossTail (H P V L : Type) where
  infinity : Unit → EvalM (ContextWorld H) L
  aggregate : P → EvalM (ContextWorld H) V
  addPenalty : V → EvalM (ContextWorld H) V
  convert : V → EvalM (ContextWorld H) L

def defaultWithContext {H X P V L : Type} (st : DispatchStages H X P)
    (tail : LossTail H P V L) (ref : Option Nat) (regularize : Bool) :
    EvalM (ContextWorld H) L :=
  evalLossDefaultWith (fun _ => resetBorrowedContext ref) (fun _ => st.run)
    tail.infinity tail.aggregate regularize tail.addPenalty tail.convert

-- Source: Julia v1.12.0 base/float.jl (IEEE conversion and checked integer truncation)
def ieeeInfinity {H : Type} (_ : LossPrecision) : EvalM (ContextWorld H) SignedFloat :=
  fun s => .ok (.ordinary .posInf) s

def integerInfinity {H : Type} : EvalM (ContextWorld H) Int64 :=
  fun s => .error .inexactError s

def incomplete_infinity : Prop :=
  ∀ (H X P V L : Type) (st : DispatchStages H X P)
    (tail : LossTail H P V L) (ref : Option Nat) (reg : Bool)
    (start first typed second after : ContextWorld H) (x₁ x₂ : X)
    (expected : ExpectedOutput) (prediction : TypedPrediction P),
    let reset := { start with indices := resetIndexReference ref start.indices }
    st.readX () reset = .ok x₁ first →
    st.expected x₁ first = .ok expected typed →
    st.readX () typed = .ok x₂ second →
    st.evaluate x₂ second = .ok (some prediction, some false) after →
    defaultWithContext st tail ref reg start =
      if expected.accepts prediction.typeId then tail.infinity () after
      else .error (.errorException "TypeError: prediction array") after

theorem incomplete_infinity_holds : incomplete_infinity := by
  intro H X P V L st tail ref reg start first typed second after x₁ x₂ expected prediction
  dsimp only
  intro h₁ he h₂ hr
  cases hp : expected.accepts prediction.typeId <;>
    simp [defaultWithContext, evalLossDefaultWith, resetBorrowedContext, DispatchStages.run,
      evalDispatchWith, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h₁, he, h₂, hr, hp]

def missing_infinity : Prop :=
  ∀ (H X P V L : Type) (st : DispatchStages H X P)
    (tail : LossTail H P V L) (ref : Option Nat) (reg : Bool)
    (start first typed second after : ContextWorld H) (x₁ x₂ : X)
    (expected : ExpectedOutput) (flag : Option Bool),
    let reset := { start with indices := resetIndexReference ref start.indices }
    st.readX () reset = .ok x₁ first →
    st.expected x₁ first = .ok expected typed →
    st.readX () typed = .ok x₂ second →
    st.evaluate x₂ second = .ok (none, flag) after →
    defaultWithContext st tail ref reg start = tail.infinity () after

theorem missing_infinity_holds : missing_infinity := by
  intro H X P V L st tail ref reg start first typed second after x₁ x₂ expected flag
  dsimp only
  intro h₁ he h₂ hr
  simp [defaultWithContext, evalLossDefaultWith, resetBorrowedContext, DispatchStages.run,
    evalDispatchWith, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, h₁, he, h₂, hr]

example (s : ContextWorld Unit) : integerInfinity s = .error .inexactError s := rfl

private def noUnitsResult {L : Type} (columns : Jl (List (List JF))) (zero : Jl L) :
    Jl L :=
  match columns with
  | .error e => .error e
  | .ok [] => .error .boundsError
  | .ok (_ :: _) => zero

def dimension_no_units : Prop :=
  ∀ (E L : Type) (ex : E) (getTree : E → Jl (Tree JF))
    (columns : Unit → Jl (List (List JF))) (zero penalty : Unit → Jl L)
    (checker : Tree JF → List JF → Jl Bool) (tree : Tree JF),
    dimensionalRegularizationWith
      (fun _ => nodeDimensionalCheck (columns ()) false false (checker tree))
      zero penalty = noUnitsResult (columns ()) (zero ()) ∧
    dimensionalRegularizationWith
      (fun _ => expressionDimensionalCheck getTree ex columns false false checker)
      zero penalty = (getTree ex >>= fun _ => noUnitsResult (columns ()) (zero ())) ∧
    dimensionalRegularizationWith (fun _ => templateDimensionalCheck false false)
      zero penalty = zero ()

theorem dimension_no_units_holds : dimension_no_units := by
  intro E L ex getTree columns zero penalty checker tree
  have node (t : Tree JF) :
      dimensionalRegularizationWith
        (fun _ => nodeDimensionalCheck (columns ()) false false (checker t))
        zero penalty = noUnitsResult (columns ()) (zero ()) := by
    cases h : columns () with
    | error e => simp [h, noUnitsResult, dimensionalRegularizationWith, nodeDimensionalCheck] <;> rfl
    | ok xs => cases xs <;>
      simp [h, noUnitsResult, dimensionalRegularizationWith, nodeDimensionalCheck, at1] <;> rfl
  refine ⟨node tree, ?_, rfl⟩
  cases h : getTree ex with
  | error e => simp [h, dimensionalRegularizationWith, expressionDimensionalCheck] <;> rfl
  | ok t =>
    simpa [h, expressionDimensionalCheck, bind, Except.bind] using node t

def dimension_empty : Prop :=
  ∀ (L : Type) (xUnits yUnits : Bool) (zero penalty : Unit → Jl L)
    (checker : List JF → Jl Bool) (columns : Jl (List (List JF))),
    (columns = .ok [] →
      dimensionalRegularizationWith (fun _ => nodeDimensionalCheck columns xUnits yUnits checker)
        zero penalty = .error .boundsError) ∧
    (dimensionalRegularizationWith (fun _ => templateDimensionalCheck xUnits yUnits)
      zero penalty = if xUnits ∨ yUnits then .error (.assertionError "!has_units(dataset)")
        else zero ())

theorem dimension_empty_holds : dimension_empty := by
  intro L xUnits yUnits zero penalty checker columns
  refine ⟨fun h => ?_, ?_⟩
  · subst columns
    rfl
  · cases xUnits <;> cases yUnits <;> simp [dimensionalRegularizationWith,
      templateDimensionalCheck] <;> rfl

example : (Except.ok [] : Jl (List (List JF))) = .ok [] := rfl

/-- Stock built-in dimensional rules, independent of the implementation's
traversal result. The explicit target dimension applies when supplied. -/
def dimensionallyTyped (table : List (List Units.Builtin)) (xu : List Units.Q)
    (yu : Option Units.Q) (allow : Bool) (t : Tree JF) : Prop :=
  ∃ dim, Units.Typed table (xu.map Units.Q.dim) allow t dim ∧
    ∀ y, yu = some y → dim = y.dim

private def unitOptions (o : Options) (degree : Nat) (sc : Units.Scalars)
    (table : List (List Units.Builtin)) (xu : List Units.Q) (yu : Option Units.Q)
    (allow : Bool) : Options :=
  { o with dimensionalCheck := fun e d => do
      let columns ← getX d
      Units.violatesDataset degree (Units.opsOf sc table) columns (some xu) yu allow e.tree }

def dimension_penalty : Prop :=
  ∀ (d : Dataset) (o : Options) (t : Tree JF) (degree : Nat) (sc : Units.Scalars)
    (table : List (List Units.Builtin)) (xu : List Units.Q) (yu : Option Units.Q)
    (allow : Bool) (p : LossPrecision),
    d.full.xUnits = true → ¬ dimensionallyTyped table xu yu allow t →
    ∀ row rows, getX d = .ok (row :: rows) →
      dimensionalRegularization (.node t) d (unitOptions o degree sc table xu yu allow) =
        .ok (p.round (o.penalty.getD (.fin 1000)))

def dimension_satisfied : Prop :=
  ∀ (d : Dataset) (o : Options) (t : Tree JF) (degree : Nat) (sc : Units.Scalars)
    (table : List (List Units.Builtin)) (xu : List Units.Q) (yu : Option Units.Q)
    (allow : Bool),
    d.full.xUnits = true → dimensionallyTyped table xu yu allow t →
    ∀ row rows, getX d = .ok (row :: rows) →
      ∀ penalty, dimensionalRegularization (.node t) d
        (unitOptions { o with penalty } degree sc table xu yu allow) = .ok (.fin 0)

def costDivisorSpec (p : LossPrecision) (enabled : Bool) (baseline : JF) : JF :=
  if enabled then
    match baseline with
    | .posInf => .posInf
    | .fin x => if p.floor ≤ x then baseline else .fin p.floor
    | .negInf | .nan => .fin p.floor
  else .fin p.floor

def cached_cost : Prop :=
  ∀ (p : LossPrecision) (loss baseline parsimony : SignedFloat) (flag : Bool)
    (member : Nat) (compute : Nat → (Nat → Int64) → Jl Int64 × (Nat → Int64))
    (size : Int64) (cache : Nat → Int64),
    loss.Representable p → baseline.Representable p → parsimony.Representable .float64 →
    let divisor := SignedFloat.ordinary (costDivisorSpec p flag baseline.value)
    lossToCostIEEE p loss flag baseline parsimony member compute (some size) cache =
      (.ok (ieeeCostSpec p loss divisor parsimony size), cache)

theorem cached_cost_holds : cached_cost := by
  intro p loss baseline parsimony flag member compute size cache _ _ _
  suffices hd : (if baselineEligible p baseline.value && flag then baseline else
      .ordinary (.fin p.floor)) = .ordinary (costDivisorSpec p flag baseline.value) by
    dsimp only
    unfold lossToCostIEEE
    rw [hd]
    rfl
  cases flag
  · simp [costDivisorSpec]
  · cases baseline with
    | negativeZero =>
      have hf : (0 : Rat) < p.floor := by cases p <;> decide +kernel
      simp [baselineEligible, SignedFloat.value, costDivisorSpec, Rat.not_le.mpr hf]
    | ordinary v =>
      cases v with
      | nan | negInf | posInf => simp [baselineEligible, SignedFloat.value, costDivisorSpec]
      | fin q =>
        by_cases h : p.floor ≤ q <;>
          simp [baselineEligible, SignedFloat.value, costDivisorSpec, h]

def computed_cost : Prop :=
  ∀ (p : LossPrecision) (loss baseline : JF) (useBaseline : Bool) (t : Tree JF)
    (metadata : Nat) (o : Options) (cached : Int) (degree : Nat) (mapping : Complexity.CMap),
    let expr := Expr.expression t metadata
    let divisor := costDivisorSpec p useBaseline baseline
    let size := if cached = -1 then Complexity.computeComplexityT degree mapping t else .ok cached
    let options := { o with complexity := fun m =>
      Complexity.computeComplexityT degree mapping (getTreeFromMember m).tree }
    lossToCost loss useBaseline baseline (.population expr cached) options none p =
      size.map (costWithDivisor p loss divisor o.parsimony)

private theorem normalization_spec (p : LossPrecision) (flag : Bool) (baseline : JF) :
    normalization flag baseline p = costDivisorSpec p flag baseline := by
  cases flag <;> cases baseline <;> simp [normalization, costDivisorSpec, baselineEligible]

theorem computed_cost_holds : computed_cost := by
  intro p loss baseline flag t metadata o cached degree mapping
  dsimp only
  unfold lossToCost
  rw [normalization_spec]
  by_cases h : cached = -1
  · cases hc : Complexity.computeComplexityT degree mapping t <;>
      simp [costAfterDivisor, memberCostSize, h, getTreeFromMember, Expr.tree, hc,
        costWithDivisor, Except.map] <;> rfl
  · simp [costAfterDivisor, memberCostSize, h, costWithDivisor, Except.map] <;> rfl

theorem recompute_cost_cache (tree : Expr) (compute : Member → Jl Int) :
    (∀ cached, cached ≠ -1 →
      memberCostSize compute (.population tree cached) = (.ok cached, .population tree cached)) ∧
    (∀ size, compute (.direct tree) = .ok size →
      memberCostSize compute (.population tree (-1)) = (.ok size, .population tree size)) ∧
    (∀ err, compute (.direct tree) = .error err →
      memberCostSize compute (.population tree (-1)) = (.error err, .population tree (-1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cached h
    simp [memberCostSize, h]
  · intro size h
    simp [memberCostSize, h]
  · intro err h
    simp [memberCostSize, h]

example : memberCostSize (fun _ => .error .boundsError)
    (.population (.node (.feature 1)) 2) =
      (.ok 2, .population (.node (.feature 1)) 2) := rfl

def eligible_normalization : Prop :=
  ∀ (p : LossPrecision) (loss baseline parsimony : SignedFloat)
    (member : Nat) (S : Type) (compute : Nat → S → Jl Int64 × S) (size : Int64) (s : S),
    loss.Representable p → baseline.Representable p → parsimony.Representable .float64 →
    (baseline.value = .posInf ∨ ∃ b : Rat, baseline.value = .fin b ∧ p.floor ≤ b) →
    lossToCostIEEE p loss true baseline parsimony member compute (some size) s =
      (.ok (ieeeCostSpec p loss baseline parsimony size), s)

theorem eligible_normalization_holds : eligible_normalization := by
  intro p loss baseline parsimony member S compute size s _ _ _ h
  have eligible : baselineEligible p baseline.value = true := by
    rcases h with he | ⟨b, he, hb⟩
    · rw [he]
      rfl
    · rw [he]
      exact decide_eq_true hb
  simp [lossToCostIEEE, eligible, costAfterDivisor, ieeeCostSpec, Except.map]

example : lossToCostIEEE .float32 (.ordinary (.fin (-1))) true
    (.ordinary .posInf) .negativeZero 0
    (fun _ s => (.error .boundsError, s + 1)) (some 1) (0 : Nat) =
    (.ok .negativeZero, 0) := by decide +kernel

def finite_cost : Prop :=
  ∀ (p : LossPrecision) (loss parsimony : Rat) (baseline : JF)
    (useBaseline : Bool) (member : Member) (o : Options) (size : Int),
    p.round (.fin loss) = .fin loss →
    LossPrecision.float64.round (.fin parsimony) = .fin parsimony →
    ∃ cost : Rat, lossToCost (.fin loss) useBaseline baseline member
      { o with parsimony := .fin parsimony } (some size) p = .ok (.fin cost)

theorem finite_cost_refuted : ¬ finite_cost := by
  intro h
  let member : Member := .direct (.expression (.const (.fin 0)) 0)
  let o : Options := {
    elementwise := .supervised (fun _ _ => .ok (.fin 0))
    run := fun _ _ c => .ok ((none, false), c) }
  obtain ⟨cost, hc⟩ := h .float64 LossPrecision.float64.maxFinite 0 (.fin 1)
    false member o 1 (by decide +kernel) (by decide +kernel)
  have hw : lossToCost (.fin LossPrecision.float64.maxFinite) false (.fin 1) member
      { o with parsimony := .fin 0 } (some 1) = .ok .posInf := by
    clear h hc
    subst member o
    decide +kernel
  rw [hw] at hc
  cases hc

def finite_cost_normal_range : Prop :=
  ∀ (p : LossPrecision) (loss parsimony : Rat) (baseline : JF)
    (useBaseline : Bool) (member : Member) (o : Options) (size : Int),
    p.round (.fin loss) = .fin loss →
    LossPrecision.float64.round (.fin parsimony) = .fin parsimony →
    p.round baseline = baseline →
    loss.abs ≤ p.maxFinite / 400 → size.natAbs ≤ 2 ^ 53 →
    ((size : Rat) * parsimony).abs ≤ p.maxFinite / 4 →
    ∃ cost : Rat, lossToCost (.fin loss) useBaseline baseline member
      { o with parsimony := .fin parsimony } (some size) p = .ok (.fin cost)

private theorem normalization_positive (p : LossPrecision) (flag : Bool) (baseline : JF) :
    normalization flag baseline p = .posInf ∨
      ∃ b, normalization flag baseline p = .fin b ∧ 3 / 400 ≤ b := by
  have hf : (3 / 400 : Rat) ≤ p.floor := by cases p <;> decide +kernel
  cases flag
  · exact Or.inr ⟨p.floor, by simp [normalization], hf⟩
  · cases baseline with
    | posInf => exact Or.inl rfl
    | negInf | nan => exact Or.inr ⟨p.floor, rfl, hf⟩
    | fin b =>
      by_cases h : p.floor ≤ b
      · exact Or.inr ⟨b, by simp [normalization, baselineEligible, h], Rat.le_trans hf h⟩
      · exact Or.inr ⟨p.floor, by simp [normalization, baselineEligible, h], hf⟩

private theorem abs_interval (q : Rat) : -q.abs ≤ q ∧ q ≤ q.abs := by
  by_cases h : 0 ≤ q
  · rw [Rat.abs_of_nonneg h]; grind
  · rw [Rat.abs_of_nonpos (by grind : q ≤ 0)]; grind

private theorem abs_sum_le (a b : Rat) : (a + b).abs ≤ a.abs + b.abs := by
  obtain ⟨al, au⟩ := abs_interval a
  obtain ⟨bl, bu⟩ := abs_interval b
  by_cases h : 0 ≤ a + b
  · rw [Rat.abs_of_nonneg h]; grind
  · rw [Rat.abs_of_nonpos (by grind : a + b ≤ 0)]; grind

private theorem normalization_range (p : LossPrecision) (loss : Rat) (flag : Bool)
    (baseline : JF) (hl : loss.abs ≤ p.maxFinite / 400) :
    ∃ q, JF.fin loss / normalization flag baseline p = .fin q ∧ q.abs ≤ p.maxFinite / 3 := by
  have hmax : 0 ≤ p.maxFinite / 3 := by cases p <;> decide +kernel
  rcases normalization_positive p flag baseline with h | ⟨b, hb, hmin⟩
  · exact ⟨0, by rw [h]; rfl, by simpa using hmax⟩
  · have hp : 0 < b := by
      have hpos : (0 : Rat) < 3 / 400 := by decide +kernel
      grind
    have hd : loss / b * b = loss := Rat.div_mul_cancel (Rat.ne_of_gt hp)
    have ha : (loss / b).abs * b = loss.abs := by
      by_cases h : 0 ≤ loss / b
      · have h' : 0 ≤ loss := hd ▸ Rat.mul_nonneg h (Rat.le_of_lt hp)
        rwa [Rat.abs_of_nonneg h, Rat.abs_of_nonneg h']
      · have hq : loss / b ≤ 0 := by grind
        have h' : loss ≤ 0 := by
          have ht := Rat.mul_le_mul_of_nonneg_right hq (Rat.le_of_lt hp)
          rwa [hd, Rat.zero_mul] at ht
        rw [Rat.abs_of_nonpos hq, Rat.abs_of_nonpos h', Rat.neg_mul, hd]
    have hh := Rat.mul_le_mul_of_nonneg_left hmin hmax
    have hs : p.maxFinite / 3 * (3 / 400) = p.maxFinite / 400 := by
      simp only [Rat.div_def, Rat.mul_assoc]
      rw [show (3 : Rat)⁻¹ * (3 * (400 : Rat)⁻¹) = (400 : Rat)⁻¹ by decide +kernel]
    rw [hs] at hh
    refine ⟨loss / b, ?_, Rat.le_of_mul_le_mul_right (c := b) ?_ hp⟩
    · rw [hb]
      change (if b = 0 then _ else _) = _
      rw [ite_eq_right (Rat.ne_of_gt hp)]
    · rw [ha]
      exact Rat.le_trans hl hh

theorem finite_cost_normal_range_holds : finite_cost_normal_range := by
  intro p loss parsimony baseline flag member o size _ _ _ hl hs ht
  obtain ⟨q, hq, hqa⟩ := normalization_range p loss flag baseline hl
  let m := p.maxFinite
  have hsmall64 : LossPrecision.float64.minNormal ≤ m / 4 := by cases p <;> decide +kernel
  have hlarge64 : m / 4 + m / 4 / 16 ≤ LossPrecision.float64.maxFinite := by
    cases p <;> decide +kernel
  obtain ⟨penalty64, h64, h64a⟩ := LossPrecision.float64.round_abs_le
    ((size : Rat) * parsimony) (m / 4) hsmall64 ht hlarge64
  have hconv : m / 4 + m / 4 / 16 ≤ m / 3 := by cases p <;> decide +kernel
  have hsmall' : p.minNormal ≤ m / 3 := by cases p <;> decide +kernel
  have hlarge' : m / 3 + m / 3 / 16 ≤ m := by cases p <;> decide +kernel
  obtain ⟨normalized, hn, hna⟩ := p.round_abs_le q (m / 3) hsmall' hqa hlarge'
  obtain ⟨penalty, hp, hpa⟩ := p.round_abs_le penalty64 (m / 3) hsmall'
    (Rat.le_trans h64a hconv) hlarge'
  have hsum : (normalized + penalty).abs ≤ 3 * m / 4 := by
    apply Rat.le_trans (abs_sum_le normalized penalty)
    have hm : (m / 3 + m / 3 / 16) + (m / 3 + m / 3 / 16) ≤ 3 * m / 4 := by
      cases p <;> decide +kernel
    exact Rat.le_trans (by grind : normalized.abs + penalty.abs ≤ _) hm
  have hsmall'' : p.minNormal ≤ 3 * m / 4 := by cases p <;> decide +kernel
  have hlarge'' : 3 * m / 4 + (3 * m / 4) / 16 ≤ m := by cases p <;> decide +kernel
  obtain ⟨cost, hc, _⟩ := p.round_abs_le (normalized + penalty) (3 * m / 4)
    hsmall'' hsum hlarge''
  refine ⟨cost, ?_⟩
  change (Except.ok (p.round (p.round (.fin loss / normalization flag baseline p) +
    p.round (LossPrecision.float64.round
      (LossPrecision.float64.round (.fin (size : Rat)) * .fin parsimony)))) : Jl JF) = .ok (.fin cost)
  rw [hq, hn, LossPrecision.round_float64_int size hs]
  change (Except.ok (p.round (.fin normalized + p.round
    (LossPrecision.float64.round (.fin ((size : Rat) * parsimony))))) : Jl JF) = .ok (.fin cost)
  rw [h64, hp]
  exact congrArg Except.ok hc

example : ∃ cost, lossToCost (.fin 1) true .posInf
    (.direct (.node (.const (.fin 0)))) { squaredOptions with parsimony := .fin 0 }
    (some 1) .float32 = .ok (.fin cost) := by
  apply finite_cost_normal_range_holds
  all_goals decide +kernel

private structure DatasetConstFields (T : Type) where
  columns : Nat
  targets : Option Nat
  weights : Option Nat
  average : Option T

def baseline_frame : Prop :=
  ∀ (T L W E : Type)
    (initial : InitValueMethod (BaselineWorld (DatasetConstFields T) L W) T)
    (create : T → Nat → LossEffect (BaselineWorld (DatasetConstFields T) L W) E)
    (eval : E → Nat → LossEffect (BaselineWorld (DatasetConstFields T) L W) L)
    (finite : L → LossEffect (BaselineWorld (DatasetConstFields T) L W) Bool)
    (one : LossEffect (BaselineWorld (DatasetConstFields T) L W) L)
    (d : Nat) (start s₁ s₂ s₃ checked ready : BaselineWorld (DatasetConstFields T) L W)
    (initialValue : T) (e : E) (raw stored : L) (enabled : Bool),
    initValue initial start = (.ok initialValue, s₁) →
    create initialValue d s₁ = (.ok e, s₂) →
    eval e d s₂ = (.ok raw, s₃) →
    finite raw s₃ = (.ok enabled, checked) →
    (if enabled then stored = raw ∧ ready = checked else one checked = (.ok stored, ready)) →
    ∃ after, updateBaselineFields (initValue initial) create eval finite one
      storeBaseline storeBaselineEnabled d start = (.ok (), after) ∧
      (after.1 d).references = (ready.1 d).references ∧ after.2 = ready.2 ∧
      ∀ a, a ≠ d → after.1 a = ready.1 a

theorem baseline_frame_holds : baseline_frame := by
  intro T L W E initial create eval finite one d start s₁ s₂ s₃ checked ready t e raw stored enabled
    hi hc he hf ho
  obtain ⟨after, h, _, _, refs, other, world⟩ :=
    baseline_effect_success (initValue initial) create eval finite one d start
      s₁ s₂ s₃ checked ready t e raw stored enabled hi hc he hf ho
  exact ⟨after, h, refs d, world, other⟩

def member_tree : Prop :=
  ∀ (t : Tree JF) (metadata : Nat) (cachedComplexity : Int),
    let node := Expr.node t
    let expr := Expr.expression t metadata
    getTreeFromMember (.direct node) = node ∧
    getTreeFromMember (.direct expr) = expr ∧
    getTreeFromMember (.population expr cachedComplexity) = expr

def context_keyword_conflict : Prop :=
  ∀ (e : Expr) (d : Dataset) (member : Member) (o : Options) (reg : Bool)
    (idx : Option (List Nat)) (complexity : Option Int) (context deprecated : Context),
    let conflict := JlError.assertionError "Cannot use both `eval_context` and deprecated `eval_options`."
    evalLoss e d o reg idx (some context) (some deprecated) = .error conflict ∧
      evalCost d member o complexity (some context) (some deprecated) = .error conflict

theorem context_keyword_conflict_holds : context_keyword_conflict := by
  intro e d member o reg idx complexity context deprecated
  exact ⟨rfl, rfl⟩

theorem context_keyword_conflict_when_warned {A : Type} (context deprecated : A)
    (warn : String → String → Jl Unit) (name : String) :
    processContext (some context) (some deprecated) warn name =
      match warn "The `eval_options` keyword is deprecated; use `eval_context` instead." name with
      | .error error => .error error
      | .ok () => .error (.assertionError
          "Cannot use both `eval_context` and deprecated `eval_options`.") := by
  cases hw : warn "The `eval_options` keyword is deprecated; use `eval_context` instead." name with
  | error e => simp [processContext, hw, bind, Except.bind]
  | ok u => cases u; simp [processContext, hw, bind, Except.bind] <;> rfl

theorem context_keyword_public (e : Expr) (d : Dataset) (member : Member) (o : Options)
    (reg : Bool) (idx : Option (List Nat)) (complexity : Option Int)
    (context deprecated : Context) (warn : String → String → Jl Unit) :
    let msg := "The `eval_options` keyword is deprecated; use `eval_context` instead."
    let conflict := JlError.assertionError "Cannot use both `eval_context` and deprecated `eval_options`."
    evalLoss e d o reg idx (some context) (some deprecated) [] warn =
      (warn msg "eval_loss" >>= fun _ => .error conflict) ∧
    evalCost d member o complexity (some context) (some deprecated) [] warn =
      (warn msg "eval_cost" >>= fun _ => .error conflict) := by
  dsimp only
  constructor
  · cases h : warn "The `eval_options` keyword is deprecated; use `eval_context` instead." "eval_loss" <;>
      simp [evalLoss, context_keyword_conflict_when_warned, h, bind, Except.bind] <;>
      rename_i u <;> cases u <;> rfl
  · cases h : warn "The `eval_options` keyword is deprecated; use `eval_context` instead." "eval_cost" <;>
      simp [evalCost, context_keyword_conflict_when_warned, h, bind, Except.bind] <;>
      rename_i u <;> cases u <;> rfl

def score_deprecated : Prop :=
  ∀ (d : Dataset) (member : Member) (o : Options) (complexity : Option Int),
    scoreFunc d member o complexity = evalCost d member o complexity

theorem score_deprecated_holds : score_deprecated := by
  intro d member o complexity
  rfl

theorem score_deprecated_when_warned (d : Dataset) (member : Member) (o : Options)
    (complexity : Option Int) (warn : Jl Unit) :
    scoreFunc d member o complexity warn =
      match warn with
      | .error error => .error error
      | .ok () => evalCost d member o complexity := by
  cases warn with
  | error _ => rfl
  | ok u => cases u; rfl

/-- A context-capable backend can take the allocation path on a valid dataset. -/
example : ({ squaredOptions with bumper := true }.bumper ||
    !{ squaredOptions with bumper := true }.takesContext) = true := rfl

/-- Fast positional `eval_tree_dispatch` agrees with `eval_tree_array` whenever `_eval_tree_array_fast`
agrees with `eval_tree_array`; direct `_eval_loss` in `eval_cost` agrees identically with `eval_loss`. -/
def fast_dispatch_and_cost_agree : Prop :=
  (∀ (R : Type) (isExpr turbo isOpEnum : Bool) (fastEval slowEval : Jl (Option R × Bool)),
    (isExpr = true → turbo = false → isOpEnum = true → fastEval = slowEval) →
    evalDispatchFast isExpr turbo isOpEnum fastEval slowEval = slowEval) ∧
  (∀ (d : Dataset) (member : Member) (o : Options) (complexity : Option Int)
    (context deprecated : Option Context) (unknownKeywords : List String)
    (depwarn : String → String → Jl Unit),
    evalCostFast d member o complexity context deprecated unknownKeywords depwarn =
      evalCost d member o complexity context deprecated unknownKeywords depwarn)

theorem fast_dispatch_and_cost_agree_holds : fast_dispatch_and_cost_agree := by
  refine ⟨?_, ?_⟩
  · intro R isExpr turbo isOpEnum fastEval slowEval heq
    unfold evalDispatchFast
    cases isExpr <;> cases turbo <;> cases isOpEnum <;> simp_all
  · intro d member o complexity context deprecated unknownKeywords depwarn
    unfold evalCostFast evalCost
    congr 1
    funext ctx
    by_cases hkw : !unknownKeywords.isEmpty
    · simp [hkw, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · simp only [hkw, Bool.false_eq_true, ↓reduceIte]
      cases hlf : o.lossFunction <;> cases hlfe : o.lossFunctionExpression <;>
        simp [evalLoss, processContext, hlf, hlfe]

end SymReg.Loss
