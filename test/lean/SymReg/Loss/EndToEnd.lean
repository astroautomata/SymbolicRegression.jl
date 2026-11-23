import SymReg.Loss.Properties
import SymReg.Templates.Template

namespace SymReg.Loss
open DynExpr SymReg.HeapLemmas

private def withRegularization (p : LossPrecision) (reg : Bool) (penalty : Jl JF)
    (value : JF) : Jl JF :=
  if reg then penalty.map (fun amount => p.round (value + p.round amount))
  else .ok (p.round value)

private def pointLosses {A : Type} (f : JF → A → Jl JF) (xs : JVec JF)
    (samples : List A) : Jl (List JF) :=
  (List.zip xs.toList samples).mapM (fun (pred, sample) => f pred sample)

private def unweightedPoint (l : Elementwise) : JF → JF → Jl JF :=
  match l with
  | .supervised f | .custom f _ => f

private def weightedPoint (p : LossPrecision) (l : Elementwise) : JF → JF × JF → Jl JF :=
  fun pred sample =>
    let (target, w) := sample
    match l with
    | .supervised f => (f pred target).map (fun value => p.round (w * value))
    | .custom _ f => f pred target w

private def pointMean (p : LossPrecision) (values : List JF) : JF :=
  p.round (pairwiseSum p values / floatCount p values.length)

private def normalizedWeighted (p : LossPrecision) (values weights : List JF) : JF :=
  p.round (pairwiseSum p values / pairwiseSum p weights)

/-- Aggregation is specified from observation pairs, including exceptions from
point loss, without assuming that the implementation's aggregation succeeds. -/
def complete_unweighted : Prop :=
  ∀ (e : Expr) (d : Dataset) (o : Options) (reg : Bool)
    (context after : Option Context) (columns : List (List JF))
    (prediction : JVec JF) (y : List JF),
    let p := d.full.lossPrecision
    getX d = .ok columns →
    o.run e columns (resetContext context) = .ok ((some prediction, true), after) →
    getTarget d = .ok (some y) → d.full.weights = none → d.full.targetSameType = true →
    y.length = prediction.size → y ≠ [] →
    evalLossDefault e d o reg context = (do
      let point := unweightedPoint o.elementwise
      let _ ← pointLosses point prediction (y.take 1)
      let points ← pointLosses point prediction y
      let value ← withRegularization p reg (dimensionalRegularization e d o) (pointMean p points)
      pure (value, after))

def complete_weighted : Prop :=
  ∀ (e : Expr) (d : Dataset) (o : Options) (reg : Bool)
    (context after : Option Context) (columns : List (List JF))
    (prediction : JVec JF) (y w : List JF),
    let p := d.full.lossPrecision
    getX d = .ok columns →
    o.run e columns (resetContext context) = .ok ((some prediction, true), after) →
    getTarget d = .ok (some y) → getWeights d = .ok (some w) →
    d.full.targetSameType = true → d.full.weightsSameType = true →
    y.length = prediction.size → w.length = y.length → y ≠ [] →
    evalLossDefault e d o reg context = (do
      let points ← pointLosses (weightedPoint p o.elementwise) prediction (List.zip y w)
      let value ← withRegularization p reg (dimensionalRegularization e d o)
        (normalizedWeighted p points w)
      pure (value, after))

def cost_pair : Prop :=
  ∀ (d : Dataset) (member : Member) (o : Options) (size : Int)
    (context after : Option Context) (loss : JF),
    evalLoss (getTreeFromMember member) d o true none context = .ok (loss, after) →
    let p := d.full.lossPrecision
    let divisor := costDivisorSpec p d.full.useBaseline d.full.baselineLoss
    evalCost d member o (some size) context =
      .ok ((costWithDivisor p loss divisor o.parsimony size, loss), after)

/-- The explicit index keyword is ignored without a custom objective. -/
private def default_dispatchContract : Prop :=
  ∀ (e : Expr) (d : Dataset) (o : Options) (reg : Bool)
    (idx : Option (List Nat)) (context : Option Context),
    evalLoss e d { o with lossFunction := none, lossFunctionExpression := none }
      reg idx context =
      evalLossDefault e d { o with lossFunction := none, lossFunctionExpression := none }
        reg context

private theorem default_dispatchContract_holds : default_dispatchContract := by
  intro e d o reg idx context
  rfl

private def default_dispatchLaw : Prop :=
  ∀ (e : Expr) (d : Dataset) (o : Options) (reg : Bool)
    (idx idx' : Option (List Nat)) (context : Option Context),
    evalLoss e d { o with lossFunction := none, lossFunctionExpression := none }
      reg idx context =
    evalLoss e d { o with lossFunction := none, lossFunctionExpression := none }
      reg idx' context

private theorem default_dispatchLaw_holds : default_dispatchLaw := by
  intro e d o reg idx idx' context
  rfl

def default_dispatch : Prop := default_dispatchContract ∧ default_dispatchLaw

theorem default_dispatch_holds : default_dispatch := ⟨default_dispatchContract_holds, default_dispatchLaw_holds⟩

/-- Unknown keywords fail before either evaluation or complexity computation. -/
def keyword_errors : Prop :=
  ∀ (e : Expr) (d : Dataset) (member : Member) (o : Options) (reg : Bool)
    (idx : Option (List Nat)) (context : Option Context) (keyword : String)
    (keywords : List String) (complexity : Option Int),
    evalLoss e d o reg idx context none (keyword :: keywords) =
      .error (.methodError "unknown loss keyword") ∧
    evalCost d member o complexity context none (keyword :: keywords) =
      .error (.methodError "unknown cost keyword")

theorem keyword_errors_holds : keyword_errors := by
  intro e d member o reg idx context keyword keywords complexity
  exact ⟨rfl, rfl⟩

/-- A deprecated eval_options context is passed through exactly as eval_context. -/
def deprecated_context : Prop :=
  ∀ (e : Expr) (d : Dataset) (member : Member) (o : Options) (reg : Bool)
    (idx : Option (List Nat)) (context : Context) (complexity : Option Int),
    evalLoss e d o reg idx none (some context) = evalLoss e d o reg idx (some context) ∧
    evalCost d member o complexity none (some context) = evalCost d member o complexity (some context)

theorem deprecated_context_holds : deprecated_context := by
  intro e d member o reg idx context complexity
  exact ⟨rfl, rfl⟩

/-- Template evaluation's invalid-feature path feeds `nothing` into the same
default-loss dispatch; the public expected-array-type method returns `Any`. -/
theorem missing_template_infinity {H P L : Type}
    (readX : Unit → EvalM (ContextWorld H) (List (List JF)))
    (combine : Templates.Combiner)
    (expression : Templates.TExpr (DynExpr.Expressions.Settings JF))
    (tail : LossTail H (List JF) P L) (ref : Option Nat) (reg : Bool)
    (s s₁ s₂ : ContextWorld H) (x₁ x₂ : List (List JF))
    (bad : Templates.hasInvalid expression = true)
    (first : readX () { s with indices := resetIndexReference ref s.indices } = .ok x₁ s₁)
    (second : readX () s₁ = .ok x₂ s₂) :
    let st : DispatchStages H (List (List JF)) (List JF) := {
      readX
      expected := fun _ => pure .any
      evaluate := fun x w => match Templates.templateEval combine expression x with
        | .ok (out, complete) => .ok (out.map fun v => ⟨0, v⟩, some complete) w
        | .error e => .error e w }
    defaultWithContext st tail ref reg s = tail.infinity () s₂ := by
  dsimp only
  apply missing_infinity_holds H _ _ P L _ tail ref reg s s₁ s₁ s₂ s₂ x₁ x₂ .any (some false)
  · exact first
  · rfl
  · exact second
  · simp [Templates.templateEval, bad, Pure.pure, Except.pure]

def evaluation_error : Prop :=
  ∀ (H X P V L : Type) (st : DispatchStages H X P)
    (tail : LossTail H P V L) (ref : Option Nat) (reg : Bool)
    (start : ContextWorld H),
    let reset := { start with indices := resetIndexReference ref start.indices }
    let run := defaultWithContext st tail ref reg start
    (∀ err after, st.readX () reset = .error err after → run = .error err after) ∧
    ∀ x₁ first, st.readX () reset = .ok x₁ first →
      (∀ err after, st.expected x₁ first = .error err after → run = .error err after) ∧
      ∀ expected typed, st.expected x₁ first = .ok expected typed →
        (∀ err after, st.readX () typed = .error err after → run = .error err after) ∧
        ∀ x₂ second, st.readX () typed = .ok x₂ second →
          ∀ err after, st.evaluate x₂ second = .error err after → run = .error err after

theorem evaluation_error_holds : evaluation_error := by
  intro H X P V L st tail ref reg start
  dsimp only
  constructor
  · intro err after h
    simp [defaultWithContext, evalLossDefaultWith, resetBorrowedContext, DispatchStages.run,
      evalDispatchWith, Bind.bind, EStateM.bind, h]
  · intro x₁ first h₁
    constructor
    · intro err after h
      simp [defaultWithContext, evalLossDefaultWith, resetBorrowedContext, DispatchStages.run,
        evalDispatchWith, Bind.bind, EStateM.bind, h₁, h]
    · intro expected typed he
      constructor
      · intro err after h
        simp [defaultWithContext, evalLossDefaultWith, resetBorrowedContext, DispatchStages.run,
          evalDispatchWith, Bind.bind, EStateM.bind, h₁, he, h]
      · intro x₂ second h₂ err after hr
        simp [defaultWithContext, evalLossDefaultWith, resetBorrowedContext, DispatchStages.run,
          evalDispatchWith, Bind.bind, EStateM.bind, h₁, he, h₂, hr]

/-- Use the installed constructor with input checking and loss type selection,
rather than a numeric dataset literal. A deprecated type overrides the
positional one after warning; `none` selects the constructor's default. -/
def initial_baseline : Prop :=
  ∀ (a : Data.In) (units : Data.UnitServices) (requireX requireY : Jl Unit)
    (lossType : Option Nat) (legacy : Option (Jl Unit × Option Nat))
    (one : Option Nat → Jl JF) (dataset : Data.Built),
    Data.construct a units requireX requireY lossType legacy one = .ok dataset →
    dataset.fields.useBaseline = true ∧
      one (match legacy with | none => lossType | some (_, ty) => ty) =
        .ok dataset.fields.baselineLoss

end SymReg.Loss
