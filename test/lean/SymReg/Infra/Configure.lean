import SymReg.Loss.Core
import SymReg.Search.Scheduler

namespace SymReg.Infra
open DynExpr

/-- Call metadata for `test_operator`, src/Configure.jl:5-29. Type names and
printed inputs are supplied by Julia's rendering protocol, independently of values. -/
structure OperatorCall where
  name : String
  inputType : String
  x : Nat
  y : Option Nat
  display : Nat → String
  complex : Bool


structure OperatorOutput where
  value : JF
  typeName : String
  isaInput : Bool
  deriving DecidableEq, Repr

/-- Exact diagnostic concatenation, src/Configure.jl:10-17. -/
def operatorExceptionMessage (c : OperatorCall) (errorType : String) : String :=
  "The operator `" ++ c.name ++ "` is not well-defined over the " ++
  (if c.complex then "complex plane, " else "real line, ") ++
  "as it threw the error `" ++ errorType ++ "` when evaluating the " ++
  (match c.y with
   | none => "input " ++ c.display c.x ++ ". "
   | some y => "inputs " ++ c.display c.x ++ " and " ++ c.display y ++ ". ") ++
  "You can work around this by returning NaN for invalid inputs. For example, " ++
  "`safe_log(x::T) where {T} = x > 0 ? log(x) : T(NaN)`."

/-- Exact type-error concatenation, src/Configure.jl:20-27. -/
def operatorTypeMessage (c : OperatorCall) (actualType : String) : String :=
  "The operator `" ++ c.name ++ "` returned an output of type `" ++ actualType ++
  "`, when it was given " ++
  (match c.y with
   | none => "an input " ++ c.display c.x ++ " "
   | some y => "inputs " ++ c.display c.x ++ " and " ++ c.display y ++ " ") ++
  "of type `" ++ c.inputType ++ "`. " ++
  "Please ensure that your operators return the same type as their inputs."

/-- `src/Configure.jl:5-29`. Arguments carry their value identity independently
of the display protocol used only for diagnostics. -/
def testOperator (c : OperatorCall) (errorType : JlError → String)
    (invoke : List Nat → Jl OperatorOutput) : Jl Unit :=
  match invoke (c.x :: c.y.toList) with
  | .error e => .error (.errorException (operatorExceptionMessage c (errorType e)))
  | .ok v => if v.isaInput then .ok ()
             else .error (.errorException (operatorTypeMessage c v.typeName))

def operatorAcceptance : Prop := ∀ c render invoke args,
  (c.y = none ∧ args = [c.x] ∨ ∃ y, c.y = some y ∧ args = [c.x,y]) →
  (∀ v, invoke args = .ok v → v.isaInput = true → testOperator c render invoke = .ok ()) ∧
  (∀ v, invoke args = .ok v → v.isaInput = false →
    testOperator c render invoke = .error (.errorException (operatorTypeMessage c v.typeName))) ∧
  (∀ e, invoke args = .error e →
    testOperator c render invoke = .error (.errorException (operatorExceptionMessage c (render e))))

theorem operatorAcceptance_holds : operatorAcceptance := by
  intro c render invoke args h
  have hargs : c.x :: c.y.toList = args := by
    rcases h with ⟨hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> simp [hy]
  simp [testOperator, hargs]
  exact ⟨fun v h hv => by simp [h, hv], fun v h hv => by simp [h, hv],
    fun e h => by simp [h]⟩

def operatorNonfinite : Prop := ∀ c render typeName (value : JF),
  testOperator c render (fun _ => .ok ⟨value, typeName, true⟩) = .ok ()

theorem operatorNonfinite_holds : operatorNonfinite := by
  unfold operatorNonfinite; intros; rfl

private def operatorDiagnosticsContract : Prop := ∀ c render e (v : OperatorOutput),
  testOperator c render (fun _ => .error e) =
    .error (.errorException (operatorExceptionMessage c (render e))) ∧
  testOperator c render (fun _ => .ok { v with isaInput := false }) =
    .error (.errorException (operatorTypeMessage c v.typeName))

private theorem operatorDiagnosticsContract_holds : operatorDiagnosticsContract := by
  unfold operatorDiagnosticsContract; intros; exact ⟨rfl,rfl⟩

def operatorDiagnostics : Prop := operatorDiagnosticsContract ∧ ∀ c render e (v : OperatorOutput),
  let region := if c.complex then "complex plane, " else "real line, "
  let thrownInputs := match c.y with
    | none => "input " ++ c.display c.x ++ ". "
    | some y => "inputs " ++ c.display c.x ++ " and " ++ c.display y ++ ". "
  let typedInputs := match c.y with
    | none => "an input " ++ c.display c.x ++ " "
    | some y => "inputs " ++ c.display c.x ++ " and " ++ c.display y ++ " "
  testOperator c render (fun _ => .error e) = .error (.errorException
    ("The operator `" ++ c.name ++ "` is not well-defined over the " ++ region ++
     "as it threw the error `" ++ render e ++ "` when evaluating the " ++ thrownInputs ++
     "You can work around this by returning NaN for invalid inputs. For example, " ++
     "`safe_log(x::T) where {T} = x > 0 ? log(x) : T(NaN)`.")) ∧
  testOperator c render (fun _ => .ok { v with isaInput := false }) = .error (.errorException
    ("The operator `" ++ c.name ++ "` returned an output of type `" ++ v.typeName ++
     "`, when it was given " ++ typedInputs ++ "of type `" ++ c.inputType ++ "`. " ++
     "Please ensure that your operators return the same type as their inputs."))

theorem operatorDiagnostics_holds : operatorDiagnostics := by
  refine ⟨operatorDiagnosticsContract_holds, ?_⟩
  intro c render e v
  exact ⟨rfl, rfl⟩

-- Source: src/Configure.jl:36-42
-- const TEST_INPUTS = collect(range(-100, 100; length=99))
-- function get_test_inputs(::Type{T}, ::AbstractOptions) where {T<:Number}
--     return Base.Fix1(convert, T).(TEST_INPUTS)
-- end
-- function get_test_inputs(::Type{T}, ::AbstractOptions) where {T<:Complex}
--     return Base.Fix1(convert, T).(TEST_INPUTS .+ TEST_INPUTS .* im)
-- end
-- Julia base/twiceprecision.jl:480-485,718-734. The reference at offset 50
-- is zero, and the 200/98 step has six low significand bits cleared.
private def gridRound (x : JF) : JF :=
  SymReg.Loss.LossPrecision.round .float64 x

private def gridHighStep : JF :=
  .fin (((((100 : Rat) / 49) * 2^45).floor : Rat) / 2^45)

private def gridLowStep : JF :=
  let quotient := gridRound (.fin 200 / .fin 98)
  let product := gridRound (quotient * .fin 98)
  -- mul12's low part is the rounded fused residual.
  let error := gridRound (quotient * .fin 98 - product)
  let correction := gridRound (gridRound (gridRound (.fin 200 - product) - error) / .fin 98)
  let high := gridRound (quotient + correction)
  let low := gridRound (gridRound (quotient - high) + correction)
  gridRound (gridRound (high - gridHighStep) + low)

private def gridPoint (i : Nat) : JF :=
  let u := JF.fin (((i : Int) - 49 : Int) : Rat)
  gridRound (gridRound (u * gridHighStep) + gridRound (u * gridLowStep))

private def exactGridPoint (i : Nat) : JF :=
  gridRound (.fin (((Int.ofNat i - 49) * 100 : Int) : Rat) / .fin 49)

def numericTestInputs (convert : JF → Option JF → Jl Nat) (complex : Bool) : Jl (List Nat) :=
  (List.range 99).mapM fun i =>
    let x := gridPoint i
    convert x (if complex then some x else none)

private def drawInputs {R : Type} (sample : R → Nat → Nat → Jl (Nat × R))
    (typ options : Nat) : Nat → R → Jl (List Nat × R)
  | 0, rng => .ok ([], rng)
  | n + 1, rng => do
      let (x, rng') ← sample rng typ options
      let (xs, rng'') ← drawInputs sample typ options n rng'
      pure (x :: xs, rng'')

-- Source: src/Configure.jl:44-47
-- function get_test_inputs(::Type{T}, options::AbstractOptions) where {T}
--     rng = MersenneTwister(0)
--     return [sample_value(rng, T, options) for _ in 1:100]
-- end
def customTestInputs (mersenneTwister : Nat → Jl Nat)
    (sample : Nat → Nat → Nat → Jl (Nat × Nat)) (typ options : Nat) : Jl (List Nat) := do
  let rng ← mersenneTwister 0
  let (xs, _) ← drawInputs sample typ options 100 rng
  pure xs

/-- Ordered Cartesian traversal, src/Configure.jl:49-57. Entries are
(operator id, first input, optional second input). Binary checks precede unary. -/
def operatorTests (inputs binops unaops : List Nat) : List (Nat × Nat × Option Nat) :=
  inputs.flatMap (fun x => inputs.flatMap (fun y => binops.map (fun op => (op,x,some y)))) ++
    inputs.flatMap (fun x => unaops.map (fun op => (op,x,none)))

-- Source: src/Configure.jl:49-57.
-- test_input = get_test_inputs(T, options)
-- for x in test_input, y in test_input, op in options.operators.binops
--     test_operator(op, x, y)
-- end
-- for x in test_input, op in options.operators.unaops
--     test_operator(op, x)
-- end
-- return nothing
def runOperatorTests {m : Type → Type} [Monad m]
    (test : Nat × Nat × Option Nat → m Unit) :
    List (Nat × Nat × Option Nat) → m Unit
  | [] => pure ()
  | x :: xs => do
    test x
    runOperatorTests test xs

def assertOperatorsWellDefined {m : Type → Type} [Monad m]
    (getInputs : m (List Nat)) (binops unaops : List Nat)
    (test : Nat × Nat × Option Nat → m Unit) : m Unit := do
  runOperatorTests test (operatorTests (← getInputs) binops unaops)

def numericInputShape : Prop := ∀ (convert : JF → Option JF → Jl Nat) complex xs,
  numericTestInputs convert complex = .ok xs →
    xs.length = 99 ∧ ∀ (i : Nat) (hi : i < xs.length),
      let point := exactGridPoint i
      convert point (if complex then some point else none) = .ok xs[i]

private theorem gridPointsAgree :
    (List.range 99).map gridPoint = (List.range 99).map exactGridPoint := by
  decide +kernel

private theorem successfulMapMIndex {α β : Type} (f : α → Jl β) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) :
    xs.length = ys.length ∧
      ∀ i : Nat, (xs[i]?.map f) = (ys[i]?.map (Except.ok : β → Jl β)) := by
  induction xs generalizing ys with
  | nil =>
    have hy : [] = ys := Except.ok.inj h
    subst ys
    simp
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, Bind.bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs, Bind.bind, Except.bind] at h
      | ok tail =>
        have hy : y :: tail = ys := by
          simpa [hx, hxs, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst ys
        have ⟨hlen, hin⟩ := ih tail hxs
        refine ⟨by simp [hlen], ?_⟩
        intro i
        cases i with
        | zero => simp [hx]
        | succ i => exact hin i

theorem numericInputShape_holds : numericInputShape := by
  intro convert complex xs h
  let applyConversion := fun x => convert x (if complex then some x else none)
  have hmap : (((List.range 99).map gridPoint).mapM applyConversion) = .ok xs := by
    simpa only [List.mapM_map, Function.comp_def, numericTestInputs] using h
  rw [gridPointsAgree] at hmap
  rw [List.mapM_map] at hmap
  have ⟨hlen, hidx⟩ := successfulMapMIndex _ _ _ hmap
  rw [List.length_range] at hlen
  refine ⟨hlen.symm, ?_⟩
  intro i hi
  have out := hidx i
  rw [List.getElem?_range (by omega), List.getElem?_eq_getElem hi] at out
  exact Option.some.inj out

private inductive SampleRun (sample : Nat → Nat → Nat → Jl (Nat × Nat))
    (typ options : Nat) : Nat → Nat → Jl (List Nat) → Prop
  | done rng : SampleRun sample typ options 0 rng (.ok [])
  | failed {n rng e} : sample rng typ options = .error e →
      SampleRun sample typ options (n+1) rng (.error e)
  | drew {n rng x rng' result} : sample rng typ options = .ok (x,rng') →
      SampleRun sample typ options n rng' result →
      SampleRun sample typ options (n+1) rng (result.map (x :: ·))

def customInputCount : Prop := ∀ (init : Nat → Jl Nat) sample typ options,
  match init 0 with
  | .error e => customTestInputs init sample typ options = .error e
  | .ok rng => SampleRun sample typ options 100 rng (customTestInputs init sample typ options)

private theorem drawInputs_run (sample : Nat → Nat → Nat → Jl (Nat × Nat)) (typ options : Nat)
    (n rng : Nat) :
    SampleRun sample typ options n rng ((drawInputs sample typ options n rng).map Prod.fst) := by
  induction n generalizing rng with
  | zero => exact .done rng
  | succ n ih =>
    cases h : sample rng typ options with
    | error e => simpa [drawInputs, h, Bind.bind, Except.bind, Except.map] using
        (SampleRun.failed (n := n) h)
    | ok pair =>
      obtain ⟨x,rng'⟩ := pair
      have hr := SampleRun.drew h (ih rng')
      cases he : drawInputs sample typ options n rng' with
      | error e => simpa [drawInputs, h, he, Bind.bind, Except.bind, Except.map] using hr
      | ok ys => obtain ⟨ys,s⟩ := ys
                 simpa [drawInputs, h, he, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map] using hr

theorem customInputCount_holds : customInputCount := by
  intro init sample typ options
  cases h : init 0 with
  | error e => simp [customTestInputs, h, Bind.bind, Except.bind]
  | ok rng =>
    have hr := drawInputs_run sample typ options 100 rng
    cases he : drawInputs sample typ options 100 rng with
    | error e => simpa [customTestInputs, h, he, Bind.bind, Except.bind, Except.map] using hr
    | ok ys => obtain ⟨ys,s⟩ := ys
               simpa [customTestInputs, h, he, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map] using hr

def operatorTestCount : Prop := ∀ (inputs binops unaops : List Nat),
  let calls := operatorTests inputs binops unaops
  let binaryCount := inputs.length * (inputs.length * binops.length)
  calls.length = binaryCount + inputs.length * unaops.length ∧
  (∀ x y op, inputs[x]? ≠ none → inputs[y]? ≠ none → binops[op]? ≠ none →
    calls[(x * inputs.length + y) * binops.length + op]? =
      (do let a ← inputs[x]?; let b ← inputs[y]?; let f ← binops[op]?; pure (f,a,some b))) ∧
  (∀ x op, inputs[x]? ≠ none → unaops[op]? ≠ none →
    calls[binaryCount + x * unaops.length + op]? =
      (do let a ← inputs[x]?; let f ← unaops[op]?; pure (f,a,none)))

private theorem sum_constant (xs : List Nat) (n : Nat) :
    (xs.map (fun _ => n)).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]

private theorem operatorTestLength (inputs binops unaops : List Nat) :
    (operatorTests inputs binops unaops).length =
      inputs.length * (inputs.length * binops.length) + inputs.length * unaops.length := by
  simp [operatorTests, List.length_flatMap, sum_constant]

private theorem indexed_flatMap {α β : Type} (f : α → List β) (xs : List α)
    (stride : Nat) (hlen : ∀ a, (f a).length = stride)
    (i j : Nat) (hi : xs[i]? ≠ none) (hj : j < stride) :
    (xs.flatMap f)[i * stride + j]? = (xs[i]?.bind fun a => (f a)[j]?) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem?_cons_zero,
        Option.bind]
      exact List.getElem?_append_left (by rw [hlen]; exact hj)
    | succ i =>
      have eq : (i + 1) * stride + j = (f a).length + (i * stride + j) := by
        rw [Nat.succ_mul, hlen]
        omega
      simp only [List.flatMap_cons, List.getElem?_cons_succ] at hi ⊢
      rw [eq, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih i hi

theorem operatorTestCount_holds : operatorTestCount := by
  intro inputs binops unaops
  refine ⟨operatorTestLength _ _ _, ?_, ?_⟩
  · intro x y op hx hy ho
    let row := fun (a : Nat) => inputs.flatMap fun b => binops.map fun f => (f,a,some b)
    have hr : ∀ a, (row a).length = inputs.length * binops.length := by
      intro a
      simp [row, List.length_flatMap, sum_constant]
    have hy' : y < inputs.length := by
      by_cases h : y < inputs.length
      · exact h
      · exact False.elim (hy (List.getElem?_eq_none (by omega)))
    have hx' : x < inputs.length := by
      by_cases h : x < inputs.length
      · exact h
      · exact False.elim (hx (List.getElem?_eq_none (by omega)))
    have ho' : op < binops.length := by
      by_cases h : op < binops.length
      · exact h
      · exact False.elim (ho (List.getElem?_eq_none (by omega)))
    have inner : y * binops.length + op < inputs.length * binops.length := by
      calc
        _ < (y + 1) * binops.length := by rw [Nat.succ_mul]; omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have total : x * (inputs.length * binops.length) + (y * binops.length + op) <
        (inputs.flatMap row).length := by
      rw [List.length_flatMap]
      simp only [hr, sum_constant]
      calc
        _ < (x + 1) * (inputs.length * binops.length) := by rw [Nat.succ_mul]; omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have eq : (x * inputs.length + y) * binops.length + op =
        x * (inputs.length * binops.length) + (y * binops.length + op) := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    unfold operatorTests
    rw [eq, List.getElem?_append_left (l₁ := inputs.flatMap row) total,
      indexed_flatMap row inputs _ hr x _ hx inner]
    cases h : inputs[x]? with
    | none => rfl
    | some a =>
      simp only [Option.bind]
      unfold row
      rw [indexed_flatMap (fun b => binops.map fun f => (f,a,some b)) inputs _
        (fun _ => List.length_map _) y op hy ho']
      simp only [List.getElem?_map]
      cases inputs[y]? <;> cases binops[op]? <;> rfl
  · intro x op hx ho
    let row := fun (a : Nat) => unaops.map fun f => (f,a,(none : Option Nat))
    have hn : (inputs.flatMap fun a => inputs.flatMap fun b =>
        binops.map fun f => (f,a,some b)).length =
        inputs.length * (inputs.length * binops.length) := by
      simp [List.length_flatMap, sum_constant]
    have ho' : op < unaops.length := by
      by_cases h : op < unaops.length
      · exact h
      · exact False.elim (ho (List.getElem?_eq_none (by omega)))
    unfold operatorTests
    rw [List.getElem?_append_right (by rw [hn]; omega), hn, Nat.add_assoc, Nat.add_sub_cancel_left,
      indexed_flatMap row inputs _ (fun _ => List.length_map _) x op hx ho']
    simp only [row, List.getElem?_map]
    cases inputs[x]? <;> cases unaops[op]? <;> rfl

def operatorTestsAccept : Prop := ∀ test inputs binops unaops,
  let tests := operatorTests inputs binops unaops
  (runOperatorTests (m := Jl) test tests = .ok () ↔ ∀ t ∈ tests, test t = .ok ()) ∧
  (∀ prior t suffix e, tests = prior ++ t :: suffix →
    (∀ p ∈ prior, test p = .ok ()) → test t = .error e →
    runOperatorTests test tests = .error e)

theorem operatorTestsAccept_holds : operatorTestsAccept := by
  intro test inputs binops unaops
  constructor
  · generalize operatorTests inputs binops unaops = tests
    induction tests with
    | nil => simp [runOperatorTests, Pure.pure, Except.pure]
    | cons t ts ih =>
      cases h : test t with
      | error e => simp [runOperatorTests, h, Bind.bind, Except.bind]
      | ok u => cases u; simp [runOperatorTests, h, ih, Bind.bind, Except.bind]
  · intro prior t suffix e hs hp he
    rw [hs]
    clear hs
    induction prior with
    | nil => simp [runOperatorTests, he, Bind.bind, Except.bind]
    | cons p ps ih =>
      have hm := hp p (by simp)
      simp [runOperatorTests, hm, Bind.bind, Except.bind]
      exact ih (fun x hx => hp x (by simp [hx]))

/-- Validator observations reuse Loss.Basic rather than creating another dataset.
`n` is Dataset.n, separate because the validator checks it against X and y.
Method arities include the function object, src/Configure.jl:99-126. -/
def datasetConfiguration (d : SymReg.Loss.Basic) (n : Nat)
    (supervised : Bool) (methodNargs : List Nat) (verbosity : Int := 0)
    (warn : Nat → Jl Unit := fun _ => .ok ()) : Jl Unit := do
  if n ≠ d.columns.length ∨ (d.y.isSome ∧ n ≠ (d.y.getD []).length) then
    throw (.assertionError "Dataset dimensions are invalid. Make sure X is of shape [features, rows], y is of shape [rows] and if there are weights, they are of shape [rows].")
  if n > 50000 && verbosity > 0 then
    warn 1
  if !supervised && d.weights.isSome && !(methodNargs.map (· - 1)).contains 3 then
    throw (.assertionError "When you create a custom loss function, and are using weights, you need to define your loss function with three scalar arguments: f(prediction, target, weight).")

def datasetAcceptance : Prop := ∀ d n supervised nargs,
  datasetConfiguration d n supervised nargs = .ok () →
    n = d.columns.length ∧
    (∀ y ∈ d.y, y.length = n) ∧
    (∀ w ∈ d.weights, w.length = n) ∧
    (supervised = true ∨ d.weights.isSome = false ∨ 4 ∈ nargs)

theorem datasetAcceptance_refuted : ¬ datasetAcceptance := by
  intro h
  let d : SymReg.Loss.Basic :=
    { columns := [[.fin 1], [.fin 2], [.fin 3]], y := some [.fin 0, .fin 0, .fin 0],
      weights := some [.fin 1] }
  have bad := (h d 3 true [] (by decide)).2.2.1 [.fin 1] (by simp [d])
  exact (by decide : (1 : Nat) ≠ 3) bad

def datasetWarningBoundary : Prop := ∀ d n supervised nargs verbosity,
  n = (d : SymReg.Loss.Basic).columns.length →
  (d.y.isSome → n = (d.y.getD []).length) →
  (∀ e, 50000 < n → 0 < verbosity →
    datasetConfiguration d n supervised nargs verbosity
      (fun maxlog => .error (.errorException (toString maxlog ++ e))) =
      .error (.errorException ("1" ++ e))) ∧
  (∀ warn, (n ≤ 50000 ∨ verbosity ≤ 0) →
    datasetConfiguration d n supervised nargs verbosity warn =
      datasetConfiguration d n supervised nargs)

theorem datasetWarningBoundary_holds : datasetWarningBoundary := by
  intro d n supervised nargs verbosity hx hy
  have shape : ¬ (n ≠ d.columns.length ∨ (d.y.isSome ∧ n ≠ (d.y.getD []).length)) := by
    rintro (h | ⟨h, ht⟩)
    · exact h hx
    · exact ht (hy h)
  constructor
  · intro e hn hv
    simp [datasetConfiguration, shape, hn, hv, Bind.bind, Except.bind]; rfl
  · intro warn h
    have off : ¬ (n > 50000 ∧ verbosity > 0) := by omega
    simp [datasetConfiguration, off]

/-- Intended shape guarantee follows the diagnostic in src/Configure.jl:107.
The constructor permits unequal weight lengths for numeric data, confirmed by
repro/cfg-weights-shape.jl on Julia 1.12. The validator never reads weight length. -/
def datasetWeightsShape : Prop := ∀ d n,
  datasetConfiguration d n true [] = .ok () →
  d.weights.isSome → (d.weights.getD []).length = n

theorem datasetWeightsShape_refuted : ¬ datasetWeightsShape := by
  intro h
  have bad := h ({ columns := [[.fin 1],[.fin 2],[.fin 3]], y := some [.fin 0,.fin 0,.fin 0], weights := some [.fin 1] } : SymReg.Loss.Basic) 3 (by decide) (by decide)
  contradiction

/-- src/Configure.jl:61-95. Warnings do not change return values. Operator
identity sets and anonymity are runtime observations; checks retain their errors. -/
-- if options.deterministic && parallelism != :serial
--     error("Determinism is only guaranteed for serial mode.")
-- end
-- assert_operators_well_defined(T, options)
-- operator_intersection = intersect(options.operators.binops, options.operators.unaops)
def optionConfiguration {m : Type → Type} [Monad m] [MonadExceptOf JlError m]
    (mode : SymReg.Search.Parallelism) (deterministic : Bool)
    (singleThread : Bool) (verbosity : Int) (hasUnits noPenalty : Bool)
    (warn : String → m Unit) (anonymous : Unit → m Bool)
    (operatorCheck : Unit → m Unit) (intersection : Unit → m (Option String)) : m Unit := do
  if deterministic && mode != .serial then
    throw (.errorException "Determinism is only guaranteed for serial mode.")
  if mode == .multithreading && singleThread && decide (0 < verbosity) then
    warn "single thread"
  if hasUnits && noPenalty && decide (0 < verbosity) then
    warn "dimensional penalty"
  if ← anonymous () then
    throw (.assertionError "Anonymous functions can't be used as operators for SymbolicRegression.jl")
  operatorCheck ()
  if let some text ← intersection () then
    throw (.assertionError ("Your configuration is invalid - " ++ text ++
      " appear in both the binary operators and unary operators."))

def deterministicSerial : Prop := ∀ mode single verbosity units penalty warn anonymous check intersect,
  mode ≠ .serial → optionConfiguration (m := Jl) mode true single verbosity units penalty warn anonymous
    check intersect = .error (.errorException "Determinism is only guaranteed for serial mode.")

theorem deterministicSerial_holds : deterministicSerial := by
  intro mode single verbosity units penalty warn anonymous check intersect h
  simp [optionConfiguration,h,Except.bind,Bind.bind]; rfl
example : SymReg.Search.Parallelism.multithreading ≠ .serial := by decide

def optionOperatorOrder : Prop := ∀ mode single verbosity units penalty warn anonymous check e left right,
  ((mode == .multithreading && single && decide (0 < verbosity)) = true →
    warn "single thread" = .ok ()) →
  ((units && penalty && decide (0 < verbosity)) = true →
    warn "dimensional penalty" = .ok ()) →
  anonymous () = .ok false → check () = .error e →
  optionConfiguration (m := Jl) mode false single verbosity units penalty warn anonymous check left = .error e ∧
  optionConfiguration mode false single verbosity units penalty warn anonymous check right = .error e

theorem optionOperatorOrder_holds : optionOperatorOrder := by
  intro mode single verbosity units penalty warn anonymous check e left right hw hu ha hc
  have ht : (mode == .multithreading && single && decide (0 < verbosity)) = true ∨
      (mode == .multithreading && single && decide (0 < verbosity)) = false := by
    cases (mode == .multithreading && single && decide (0 < verbosity)) <;> simp
  have hd : (units && penalty && decide (0 < verbosity)) = true ∨
      (units && penalty && decide (0 < verbosity)) = false := by
    cases (units && penalty && decide (0 < verbosity)) <;> simp
  rcases ht with ht | ht <;> rcases hd with hd | hd
  · have hw' := hw ht
    have hu' := hu hd
    simp only [optionConfiguration, Bool.false_and, Bool.false_eq_true, ite_false, ht, hd,
      ite_true, hw', hu', ha, hc, Bind.bind, Except.bind]
    simp
  · have hw' := hw ht
    simp only [optionConfiguration, Bool.false_and, Bool.false_eq_true, ite_false, ht, hd,
      ite_true, hw', ha, hc, Bind.bind, Except.bind]
    simp
  · have hu' := hu hd
    simp only [optionConfiguration, Bool.false_and, Bool.false_eq_true, ite_false, ht, hd,
      ite_true, hu', ha, hc, Bind.bind, Except.bind]
    simp
  · simp only [optionConfiguration, Bool.false_and, Bool.false_eq_true, ite_false, ht, hd,
      ite_true, ha, hc, Bind.bind, Except.bind]
    simp

private theorem runConfigBind {S α β : Type} (x : ExceptT JlError (StateM S) α)
    (f : α → ExceptT JlError (StateM S) β) (s : S) :
    ((x >>= f).run s) = match x.run s with
    | (.error e, next) => (.error e, next)
    | (.ok value, next) => (f value).run next := by
  change (match x.run s with
    | (result, next) => (ExceptT.bindCont f result : StateM S (Jl β)) next) = _
  cases x.run s with
  | mk result next => cases result <;> rfl

theorem operatorChecks_stop_at_failure {S : Type}
    (test : (Nat × Nat × Option Nat) → ExceptT JlError (StateM S) Unit)
    (prior suffix : List (Nat × Nat × Option Nat)) (bad : Nat × Nat × Option Nat)
    (start before after : S) (e : JlError)
    (hp : (runOperatorTests test prior).run start = (.ok (), before))
    (hb : (test bad).run before = (.error e, after)) :
    (runOperatorTests test (prior ++ bad :: suffix)).run start = (.error e, after) := by
  induction prior generalizing start with
  | nil =>
    have eq : start = before := congrArg Prod.snd hp
    subst before
    simpa only [List.nil_append, runOperatorTests, runConfigBind, hb]
  | cons testCall prior ih =>
    simp only [runOperatorTests, runConfigBind] at hp
    cases h : (test testCall).run start with
    | mk r next =>
      cases r with
      | error err =>
        rw [h] at hp
        cases (congrArg Prod.fst hp : Except.error err = Except.ok ())
      | ok token =>
        simp only [List.cons_append, runOperatorTests, runConfigBind, h]
        exact ih next (by simpa only [h] using hp)

theorem assertOperators_stops_at_failure {S : Type}
    (getInputs : ExceptT JlError (StateM S) (List Nat)) (input binops unaops : List Nat)
    (test : (Nat × Nat × Option Nat) → ExceptT JlError (StateM S) Unit)
    (prior suffix : List (Nat × Nat × Option Nat)) (bad : Nat × Nat × Option Nat)
    (start inputState before after : S) (e : JlError)
    (hi : getInputs.run start = (.ok input, inputState))
    (hs : operatorTests input binops unaops = prior ++ bad :: suffix)
    (hp : (runOperatorTests test prior).run inputState = (.ok (), before))
    (hb : (test bad).run before = (.error e, after)) :
    (assertOperatorsWellDefined getInputs binops unaops test).run start = (.error e, after) := by
  simp only [assertOperatorsWellDefined, runConfigBind, hi, hs]
  exact operatorChecks_stop_at_failure test prior suffix bad inputState before after e hp hb

theorem optionConfiguration_operator_failure {S : Type} (mode : SymReg.Search.Parallelism)
    (det single : Bool) (verbosity : Int) (units penalty : Bool)
    (warn : String → ExceptT JlError (StateM S) Unit)
    (anonymous : Unit → ExceptT JlError (StateM S) Bool)
    (check : Unit → ExceptT JlError (StateM S) Unit)
    (intersection : Unit → ExceptT JlError (StateM S) (Option String))
    (start s₁ s₂ s₃ s₄ : S) (e : JlError)
    (allowed : (det && mode != .serial) = false)
    (hw : (if mode == .multithreading && single && decide (0 < verbosity)
        then (warn "single thread").run start else (.ok (), start)) = (.ok (), s₁))
    (hu : (if units && penalty && decide (0 < verbosity)
        then (warn "dimensional penalty").run s₁ else (.ok (), s₁)) = (.ok (), s₂))
    (ha : (anonymous ()).run s₂ = (.ok false, s₃))
    (hc : (check ()).run s₃ = (.error e, s₄)) :
    ((optionConfiguration mode det single verbosity units penalty warn anonymous check intersection).run start) =
      (.error e, s₄) := by
  generalize h₁ : (mode == .multithreading && single && decide (0 < verbosity)) = t at hw
  generalize h₂ : (units && penalty && decide (0 < verbosity)) = u at hu
  cases t <;> cases u <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] at hw hu
  all_goals
    try
      have h := congrArg Prod.snd hw
      change start = s₁ at h
      subst s₁
    try
      have h := congrArg Prod.snd hu
      first | change start = s₂ at h | change s₁ = s₂ at h
      subst s₂
    simp only [optionConfiguration, allowed, Bool.false_eq_true, ite_false, h₁, h₂, ite_true,
      runConfigBind, hw, hu, ha, hc]

example : (0 : Int) ≤ 0 := by decide

end SymReg.Infra
