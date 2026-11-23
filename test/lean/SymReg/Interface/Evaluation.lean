import SymReg.Loss.Core
import DynExpr.Expressions.Wrapper
import DynExpr.NodeBase.Types

namespace SymReg.Interface
open DynExpr

/-- Projections missing from the existing Loss.Options model are supplied separately.
`operators` is the result of DE.get_operators(tree, options), so custom AbstractOptions
selection remains arbitrary. src/InterfaceDynamicExpressions.jl:91-105. -/
structure EvalOptions where
  shared : SymReg.Loss.Options
  operators : OpEnum JF

abbrev Context := SymReg.Loss.Context
abbrev Keywords := List (String × Nat)

/-- Standard OperatorEnum accepts contexts, GenericOperatorEnum does not;
type and value overloads use the same predicate. src/InterfaceDynamicExpressions.jl:21-23. -/
def takesEvalContext (standard : Bool) : Bool := standard

/-- Deprecated eval_options is processed before dispatch, even for generic operators.
The warning is outside this return-value model. src/InterfaceDynamicExpressions.jl:25-42. -/
def processContext (context legacy : Option Context) : Jl (Option Context) :=
  match legacy with
  | none => .ok context
  | some old => if context.isSome then
      .error (.assertionError "Cannot use both `eval_context` and deprecated `eval_options`.")
    else .ok (some old)

/-- Exact context construction, with the existing DE EvalContext and defaults.
src/InterfaceDynamicExpressions.jl:93-105. -/
def selectContext (o : EvalOptions) (turbo bumper : Option Bool) (context : Option Context) :
    Option Context :=
  if takesEvalContext o.shared.takesContext then
    some (context.getD ⟨turbo.getD o.shared.turbo, bumper.getD o.shared.bumper,
      true, .none, true⟩)
  else none

/-- Strip the deprecated keyword and retain every other key in insertion order.
src/InterfaceDynamicExpressions.jl:89-90. -/
def remainingKeywords (kws : Keywords) : Keywords :=
  kws.filter (fun kv => kv.1 != "eval_options")

/-- Wrapper forwards the original expression, matrix, resolved enum and remaining
keywords, and normalizes an absent output to (nothing,false). Concrete array type
assertions are represented by the typed service. src/InterfaceDynamicExpressions.jl:80-111. -/
def evalTree (run : E → JMat JF → OpEnum JF → Option Context → Keywords → Jl SymReg.Loss.Reply)
    (tree : E) (X : JMat JF) (o : EvalOptions) (turbo bumper : Option Bool)
    (context legacy : Option Context) (kws : Keywords) : Jl SymReg.Loss.Reply := do
  let c ← processContext context legacy
  let reply ← run tree X o.operators (selectContext o turbo bumper c) (remainingKeywords kws)
  return SymReg.Loss.dispatchReply reply

inductive GradientMode where
  | constants | features | both
  deriving DecidableEq

-- Source: src/InterfaceDynamicExpressions.jl:180-191
-- function DE.eval_grad_tree_array(
--     tree::Union{AbstractExpression,AbstractExpressionNode},
--     X::AbstractArray,
--     options::AbstractOptions;
--     kws...,
-- )
--     A = expected_array_type(X, typeof(tree))
--     dA = expected_array_type(X, typeof(tree), Val(:eval_grad_tree_array))
--     out, grad, complete = DE.eval_grad_tree_array(
--         tree, X, DE.get_operators(tree, options); kws...
--     )
--     return out::A, convert(dA, grad)::dA, complete::Bool
-- end
def evalGrad (run : E → JMat JF → OpEnum JF → GradientMode → Keywords → Jl (JVec JF × G × Bool))
    (convert : G → Jl D) (tree : E) (X : JMat JF) (o : EvalOptions) (kws : Keywords)
    (mode : Option GradientMode := none) : Jl (JVec JF × D × Bool) := do
  -- Effective default at the DE standard-enum backend.
  let (value, grad, complete) ← run tree X o.operators (mode.getD .constants) kws
  return (value, ← convert grad, complete)

inductive ArrayType where
  | dense (element rank : Nat)
  | view (element rank : Nat) (parent : ArrayType)
  | other (typeObject : Nat)
  deriving DecidableEq

structure ArrayInput (X : Type) where
  value : X
  runtimeType : ArrayType
  axes : Nat → Nat

-- Source: src/InterfaceDynamicExpressions.jl:116-123
-- function expected_array_type(X::AbstractArray, ::Type)
--     return typeof(similar(X, axes(X, 2)))
-- end
-- function expected_array_type(X::AbstractArray, ::Type, ::Val{:eval_grad_tree_array})
--     typeof(similar(X))
-- end
-- expected_array_type(::Matrix{T}, ::Type) where {T} = Vector{T}
-- expected_array_type(::SubArray{T,2,Matrix{T}}, ::Type) where {T} = Vector{T}
def expectedArray (similar : X → Nat → Jl ArrayType) (input : ArrayInput X) : Jl ArrayType :=
  match input.runtimeType with
  | .dense t 2 => .ok (.dense t 1)
  | .view t 2 (.dense p 2) =>
    if t = p then .ok (.dense t 1) else similar input.value (input.axes 2)
  | _ => similar input.value (input.axes 2)

def expectedGradientArray (similar : X → Jl ArrayType) (input : ArrayInput X) : Jl ArrayType :=
  similar input.value

structure CheckedArray (V : Type) where
  runtimeType : ArrayType
  value : V

abbrev EvalEffect (S A : Type) := ExceptT JlError (StateM S) A

private def assertArray (expected : ArrayType) (a : CheckedArray V) : EvalEffect S (CheckedArray V) :=
  if a.runtimeType = expected then pure a else throw (.errorException "TypeError: in typeassert")

-- Source: src/InterfaceDynamicExpressions.jl:145-157
-- function DE.eval_diff_tree_array(
--     tree::Union{AbstractExpression,AbstractExpressionNode},
--     X::AbstractArray,
--     options::AbstractOptions,
--     direction::Int,
-- )
--     # TODO: Add `AbstractExpression` implementation in `Expression.jl`
--     A = expected_array_type(X, typeof(tree))
--     out, grad, complete = DE.eval_diff_tree_array(
--         DE.get_tree(tree), X, DE.get_operators(tree, options), direction
--     )
--     return out::A, grad::A, complete::Bool
-- end
def evalDiff (expected : ArrayInput X → EvalEffect S ArrayType)
    (getTree : E → EvalEffect S N) (resolve : E → EvalOptions → EvalEffect S (OpEnum JF))
    (run : N → X → OpEnum JF → Int → EvalEffect S (CheckedArray V × CheckedArray V × Bool))
    (tree : E) (X : ArrayInput X) (o : EvalOptions) (direction : Int) :
    EvalEffect S (CheckedArray V × CheckedArray V × Bool) := do
  let a ← expected X
  let node ← getTree tree
  let ops ← resolve tree o
  let (out, grad, complete) ← run node X.value ops direction
  return (← assertArray a out, ← assertArray a grad, complete)

-- Source: src/InterfaceDynamicExpressions.jl:199-210
-- function DE.differentiable_eval_tree_array(
--     tree::Union{AbstractExpression,AbstractExpressionNode},
--     X::AbstractArray,
--     options::AbstractOptions,
-- )
--     # TODO: Add `AbstractExpression` implementation in `Expression.jl`
--     A = expected_array_type(X, typeof(tree))
--     out, complete = DE.differentiable_eval_tree_array(
--         DE.get_tree(tree), X, DE.get_operators(tree, options)
--     )
--     return out::A, complete::Bool
-- end
def evalDifferentiable (expected : ArrayInput X → EvalEffect S ArrayType)
    (getTree : E → EvalEffect S N) (resolve : E → EvalOptions → EvalEffect S (OpEnum JF))
    (run : N → X → OpEnum JF → EvalEffect S (CheckedArray V × Bool))
    (tree : E) (X : ArrayInput X) (o : EvalOptions) : EvalEffect S (CheckedArray V × Bool) := do
  let a ← expected X
  let node ← getTree tree
  let ops ← resolve tree o
  let (out, complete) ← run node X.value ops
  return (← assertArray a out, complete)

/-- Runtime array element types must also be checked: `out::A` does not
convert. Reuses DE's scalar type and promotion model for standard vectors.
src/InterfaceDynamicExpressions.jl:91,110,115-123. -/
structure TypedArray where
  arrayType : NodeBase.Elt
  values : JVec JF

def assertOutput (expected : NodeBase.Elt) (out : Option TypedArray) (complete : Bool) :
    Jl (Option TypedArray × Bool) :=
  match out with
  | none => .ok (none, false)
  | some a => if a.arrayType = expected then .ok (some a, complete)
    else .error (.errorException "TypeError: in typeassert")

/-- DE promotes mixed floating scalar types; the SR assertion instead selects
the X element type, ignoring typeof(tree). The concrete promotion fact is
checked by repro/ide-mixed-type-eval.jl.
SR src/InterfaceDynamicExpressions.jl:91,110,122; DE src/Evaluate.jl:promotion overload. -/
def promotedArray (treeType dataType : NodeBase.Elt) (values : JVec JF) : TypedArray :=
  ⟨NodeBase.promoteElt treeType dataType, values⟩

def mixedTypeForwarding : Prop := ∀ (treeType dataType : NodeBase.Elt)
  (values : JVec JF) (complete : Bool),
  assertOutput dataType (some (promotedArray treeType dataType values)) complete =
    .ok (some (promotedArray treeType dataType values), complete)
 theorem mixedTypeForwarding_refuted : ¬ mixedTypeForwarding := by
  intro h
  have bad := h .float64 .float32 (JVec.fill 2 (.fin 1)) true
  simp [assertOutput, promotedArray, NodeBase.promoteElt] at bad

def matchingTypeAssertion : Prop := ∀ (expected : NodeBase.Elt) (values : JVec JF) (complete : Bool),
  assertOutput expected (some ⟨expected, values⟩) complete =
    .ok (some ⟨expected, values⟩, complete)
 theorem matchingTypeAssertion_holds : matchingTypeAssertion := by
  intro expected values complete; simp [assertOutput]

/-- Callable trees seed turbo/bumper, then caller keywords win, as Julia keyword
splatting takes the rightmost occurrence. src/InterfaceDynamicExpressions.jl:384-403. -/
-- Source: src/InterfaceDynamicExpressions.jl:387-393,401-403
-- turbo=options.turbo, bumper=options.bumper, kws...
-- turbo=options.turbo, kws...
def callKeywords (o : EvalOptions) (kws : Keywords) : Keywords :=
  (Expressions.mergeMetadata
    ⟨[("turbo", if o.shared.turbo then 1 else 0), ("bumper", if o.shared.bumper then 1 else 0)]⟩
    ⟨kws⟩).data

def gradCallKeywords (o : EvalOptions) (kws : Keywords) : Keywords :=
  (Expressions.mergeMetadata ⟨[("turbo", if o.shared.turbo then 1 else 0)]⟩ ⟨kws⟩).data

/-- src/InterfaceDynamicExpressions.jl:384-403. The backend callback retains
all return values, exceptions and effects in its result type. -/
def callTree (run : E → X → OpEnum JF → Keywords → Jl R)
    (tree : E) (data : X) (o : EvalOptions) (kws : Keywords) : Jl R :=
  run tree data o.operators (callKeywords o kws)

def callGradient (run : E → X → OpEnum JF → GradientMode → Keywords → Jl R)
    (tree : E) (data : X) (o : EvalOptions) (kws : Keywords)
    (mode : Option GradientMode := none) : Jl R :=
  -- Effective default at DE's adjoint helper (EvaluationHelpers.jl:56-66).
  run tree data o.operators (mode.getD .features) (gradCallKeywords o kws)

private def contextPolicyContract : Prop := ∀ (o : EvalOptions) (t b : Option Bool) (c : Option Context),
  selectContext o t b c = if o.shared.takesContext then
    some (c.getD ⟨t.getD o.shared.turbo, b.getD o.shared.bumper, true, .none, true⟩)
  else none

private theorem contextPolicyContract_holds : contextPolicyContract := by intro o t b c; rfl

private def contextPolicyLaw : Prop := ∀ (o : EvalOptions) (t b : Bool) (c : Context),
  (o.shared.takesContext = false → selectContext o (some t) (some b) (some c) = none) ∧
  (o.shared.takesContext = true → selectContext o (some t) (some b) (some c) = some c) ∧
  (o.shared.takesContext = true →
    (selectContext o (some t) (some b) none).map (fun c => (c.turbo, c.bumper)) =
      some (t, b))
private theorem contextPolicyLaw_holds : contextPolicyLaw := by
  intro o t b c
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [selectContext, takesEvalContext, h]

def contextPolicy : Prop := contextPolicyContract ∧ contextPolicyLaw

theorem contextPolicy_holds : contextPolicy := ⟨contextPolicyContract_holds, contextPolicyLaw_holds⟩

def deprecatedPolicy : Prop := ∀ (c : Context),
  processContext none (some c) = .ok (some c) ∧
  processContext (some c) (some c) = .error
    (.assertionError "Cannot use both `eval_context` and deprecated `eval_options`.") ∧
  processContext (some c) none = .ok (some c)
 theorem deprecatedPolicy_holds : deprecatedPolicy := by intro c; exact ⟨rfl,rfl,rfl⟩

private def evalForwardingContract : Prop := ∀ (E : Type)
  (run : E → JMat JF → OpEnum JF → Option Context → Keywords → Jl SymReg.Loss.Reply)
  (tree : E) (X : JMat JF) (o : EvalOptions) (t b : Option Bool) (kws : Keywords),
  evalTree run tree X o t b none none kws =
    (run tree X o.operators (selectContext o t b none) (remainingKeywords kws)).map
      SymReg.Loss.dispatchReply

private theorem evalForwardingContract_holds : evalForwardingContract := by
  intro E run tree X o t b kws
  simp [evalTree, processContext, Except.map, bind, Except.bind, pure, Except.pure]

private def evalForwardingLaw : Prop := ∀ (E : Type)
  (run : E → JMat JF → OpEnum JF → Option Context → Keywords → Jl SymReg.Loss.Reply)
  (tree : E) (X : JMat JF) (o : EvalOptions) (t b : Option Bool) (kws : Keywords) old,
  evalTree run tree X o t b none none (("eval_options", old) :: kws) =
    evalTree run tree X o t b none none kws

private theorem evalForwardingLaw_holds : evalForwardingLaw := by
  intro E run tree X o t b kws old
  simp [evalTree, remainingKeywords]

private def evalContextRouting : Prop := ∀ (E : Type)
  (run : E → JMat JF → OpEnum JF → Option Context → Keywords → Jl SymReg.Loss.Reply)
  (tree : E) (X : JMat JF) (o : EvalOptions) (t b : Option Bool) (kws : Keywords) (c old : Context),
  evalTree run tree X o t b none (some old) kws =
    evalTree run tree X o t b (some old) none kws ∧
  evalTree run tree X o t b (some c) (some old) kws =
    .error (.assertionError "Cannot use both `eval_context` and deprecated `eval_options`.")

private theorem evalContextRouting_holds : evalContextRouting := by
  intro E run tree X o t b kws c old
  exact ⟨rfl, rfl⟩

def evalForwarding : Prop := evalForwardingContract ∧ evalForwardingLaw ∧ evalContextRouting

theorem evalForwarding_holds : evalForwarding :=
  ⟨evalForwardingContract_holds, evalForwardingLaw_holds, evalContextRouting_holds⟩

def absentOutput : Prop := ∀ (E : Type) (tree : E) (X : JMat JF) (o : EvalOptions)
  (t b : Option Bool) (kws : Keywords) (complete : Bool) (c : Context),
  let run := fun (_ : E) (_ : JMat JF) (_ : OpEnum JF) (_ : Option Context) (_ : Keywords) =>
    (Except.ok (none, complete) : Jl SymReg.Loss.Reply)
  evalTree run tree X o t b none none kws = .ok (none, false) ∧
  evalTree run tree X o t b (some c) none kws = .ok (none, false) ∧
  evalTree run tree X o t b none (some c) kws = .ok (none, false)
theorem absentOutput_holds : absentOutput := by
  intro E tree X o t b kws complete c
  exact ⟨rfl,rfl,rfl⟩

private inductive DerivativeCall (E X N : Type) where
  | expected (data : ArrayInput X)
  | tree (expression : E)
  | operators (expression : E) (options : EvalOptions)
  | backend (node : N) (data : X) (ops : OpEnum JF) (direction : Option Int)

private def recordCall (call : C) (reply : Jl A) : EvalEffect (List C) A :=
  ExceptT.mk fun calls => (reply, calls ++ [call])

def derivativeForwarding : Prop := ∀ (E X N V : Type)
  (ex : E) (data : ArrayInput X) (o : EvalOptions) (direction : Int)
  (node : E → N) (ops : E → EvalOptions → OpEnum JF) (lookup : Jl ArrayType)
  (value deriv : V) (complete : Bool),
  let expected := fun x => recordCall (DerivativeCall.expected x) lookup
  let getTree := fun t => recordCall (DerivativeCall.tree t) (.ok (node t))
  let resolve := fun t opts => recordCall (DerivativeCall.operators t opts) (.ok (ops t opts))
  let tag := match lookup with | .ok ty => ty | .error _ => .other 0
  let diff := fun n x op i => recordCall (DerivativeCall.backend n x op (some i))
    (.ok (⟨tag, value⟩, ⟨tag, deriv⟩, complete) : Jl (CheckedArray V × CheckedArray V × Bool))
  let ad := fun n x op => recordCall (DerivativeCall.backend n x op none)
    (.ok (⟨tag, value⟩, complete) : Jl (CheckedArray V × Bool))
  let calls := [DerivativeCall.expected data, .tree ex, .operators ex o]
  ((evalDiff expected getTree resolve diff ex data o direction).run []) =
    (match lookup with
     | .error e => (.error e, [.expected data])
     | .ok ty => (.ok (⟨ty, value⟩, ⟨ty, deriv⟩, complete),
       calls ++ [.backend (node ex) data.value (ops ex o) (some direction)])) ∧
  ((evalDifferentiable expected getTree resolve ad ex data o).run []) =
    (match lookup with
     | .error e => (.error e, [.expected data])
     | .ok ty => (.ok (⟨ty, value⟩, complete),
       calls ++ [.backend (node ex) data.value (ops ex o) none]))
theorem derivativeForwarding_holds : derivativeForwarding := by
  intro E X N V ex data o direction node ops lookup value deriv complete
  cases lookup
  · exact ⟨rfl, rfl⟩
  · constructor <;>
      simp [evalDiff, evalDifferentiable, recordCall, assertArray, bind,
        ExceptT.bind, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
        ExceptT.mk, ExceptT.run]

private def gradientForwardingContract : Prop := ∀ (E G D : Type)
  (run : E → JMat JF → OpEnum JF → GradientMode → Keywords → Jl (JVec JF × G × Bool))
  (convert : G → Jl D) (tree : E) (X : JMat JF) (o : EvalOptions) (kws : Keywords),
  evalGrad run convert tree X o kws = do
    let (v,g,c) ← run tree X o.operators .constants kws
    return (v, ← convert g, c)

private theorem gradientForwardingContract_holds : gradientForwardingContract := by
  intro E G D run convert tree X o kws; rfl

private def gradientForwardingLaw : Prop := ∀ (E G D : Type)
  (run : E → JMat JF → OpEnum JF → GradientMode → Keywords → Jl (JVec JF × G × Bool))
  (convert : G → Jl D) (tree : E) (X : JMat JF) (o : EvalOptions) (kws : Keywords),
  (evalGrad run convert tree X o kws).map (fun (v, _, c) => (v, c)) =
    (evalGrad run (fun g => (convert g).map (fun _ => ())) tree X o kws).map
      (fun (v, _, c) => (v, c))
private theorem gradientForwardingLaw_holds : gradientForwardingLaw := by
  intro E G D run convert tree X o kws
  cases h : run tree X o.operators .constants kws with
  | error e => simp [evalGrad, h, Except.map, bind, Except.bind]
  | ok r =>
    obtain ⟨v, g, c⟩ := r
    cases hc : convert g <;>
      simp [evalGrad, h, hc, Except.map, bind, Except.bind, pure, Except.pure]

private def gradientReplies : Prop := ∀ (E G D : Type)
  (run : E → JMat JF → OpEnum JF → GradientMode → Keywords → Jl (JVec JF × G × Bool))
  (convert : G → Jl D) (tree : E) (X : JMat JF) (o : EvalOptions) (kws : Keywords),
  (∀ e, run tree X o.operators .constants kws = .error e → evalGrad run convert tree X o kws = .error e) ∧
  (∀ v g c, run tree X o.operators .constants kws = .ok (v, g, c) →
    (∀ e, convert g = .error e → evalGrad run convert tree X o kws = .error e) ∧
    (∀ d, convert g = .ok d → evalGrad run convert tree X o kws = .ok (v, d, c)))

private theorem gradientReplies_holds : gradientReplies := by
  intro E G D run convert tree X o kws
  refine ⟨?_, ?_⟩
  · intro e he
    simp [evalGrad, he, bind, Except.bind]
  · intro v g c hr
    constructor <;> intro r h <;> simp [evalGrad, hr, h, bind, Except.bind, pure, Except.pure]

def gradientForwarding : Prop := gradientForwardingContract ∧ gradientForwardingLaw ∧ gradientReplies

theorem gradientForwarding_holds : gradientForwarding :=
  ⟨gradientForwardingContract_holds, gradientForwardingLaw_holds, gradientReplies_holds⟩

def defaultModes : Prop := ∀ (E : Type) (tree : E) (X : JMat JF) (o : EvalOptions)
  (kws : Keywords) (v : JVec JF) (m : GradientMode),
  let observe := fun (_ : E) (_ : JMat JF) (_ : OpEnum JF) (mode : GradientMode)
      (_ : Keywords) => (Except.ok (v, mode, true) : Jl (JVec JF × GradientMode × Bool))
  let identity := fun (x : GradientMode) => (Except.ok x : Jl GradientMode)
  evalGrad observe identity tree X o kws = .ok (v, .constants, true) ∧
  callGradient observe tree X o kws = .ok (v, .features, true) ∧
  evalGrad observe identity tree X o kws (some m) = .ok (v, m, true) ∧
  callGradient observe tree X o kws (some m) = .ok (v, m, true)
theorem defaultModes_holds : defaultModes := by
  intro E tree X o kws v m; exact ⟨rfl,rfl,rfl,rfl⟩

def expectedTypes : Prop := ∀ (X : Type) (x : X) (t : Nat) (kind : ArrayType) (axes : Nat → Nat)
  (columns : X → Nat → Jl ArrayType) (full : X → Jl ArrayType),
  expectedArray columns (⟨x, .dense t 2, axes⟩ : ArrayInput X) = .ok (.dense t 1) ∧
  expectedArray columns ⟨x, .view t 2 (.dense t 2), axes⟩ = .ok (.dense t 1) ∧
  ((∀ p, kind ≠ .dense p 2 ∧ kind ≠ .view p 2 (.dense p 2)) →
    expectedArray columns ⟨x, kind, axes⟩ = columns x (axes 2)) ∧
  expectedGradientArray full ⟨x, kind, axes⟩ = full x
theorem expectedTypes_holds : expectedTypes := by
  intro X x t kind axes columns full
  refine ⟨rfl, by simp [expectedArray], ?_, rfl⟩
  intro other
  unfold expectedArray
  split
  · rename_i e _
    exact False.elim ((other e).1 (by assumption))
  · rename_i e p heq
    by_cases h : e = p
    · subst p; exact False.elim ((other e).2 heq)
    · simp [h]
  · rfl

example : ∀ p, ArrayType.other 0 ≠ .dense p 2 ∧
    ArrayType.other 0 ≠ .view p 2 (.dense p 2) := by intro p; simp

private def keywordValue (key : String) (xs : Keywords) : Option Nat :=
  (xs.find? (fun kv => kv.1 == key)).map Prod.snd

private def effectiveKeywords (key : String) (old : Option Nat) : Keywords → Option Nat
  | [] => old
  | kv :: rest => effectiveKeywords key (if kv.1 == key then some kv.2 else old) rest

private theorem keywordLookup_set (xs : Keywords) (key k : String) (v : Nat) :
    ((Expressions.setField k v xs).find? (fun kv => kv.1 == key)).map Prod.snd =
      if k == key then some v else (xs.find? (fun kv => kv.1 == key)).map Prod.snd := by
  induction xs with
  | nil => by_cases h : k = key <;> simp [Expressions.setField, h]
  | cons kv xs ih =>
    obtain ⟨a, b⟩ := kv
    by_cases hak : a = k
    · subst a; by_cases h : k = key <;> simp [Expressions.setField, h]
    · by_cases h : k = key
      · subst k; simp [Expressions.setField, hak, ih]
      · by_cases ha : a = key
        · subst a; simp [Expressions.setField, h, Ne.symm h]
        · simp [Expressions.setField, hak, h, ha, ih]

private theorem keywordLookup_fold (defaults kws : Keywords) (key : String) :
    keywordValue key (kws.foldl (fun xs kv => Expressions.setField kv.1 kv.2 xs) defaults) =
      effectiveKeywords key (keywordValue key defaults) kws := by
  induction kws generalizing defaults with
  | nil => rfl
  | cons kv kws ih =>
    simp only [List.foldl_cons, effectiveKeywords, ih]
    congr 1
    exact keywordLookup_set defaults key kv.1 kv.2

def callableForwarding : Prop := ∀ (E X : Type) (tree : E) (data : X)
  (o : EvalOptions) (kws : Keywords) (key : String),
  let observe := fun (_ : E) (_ : X) (_ : OpEnum JF) (ks : Keywords) =>
    (Except.ok (keywordValue key ks) : Jl (Option Nat))
  callTree observe tree data o kws = .ok (effectiveKeywords key (keywordValue key
    [("turbo", if o.shared.turbo then 1 else 0), ("bumper", if o.shared.bumper then 1 else 0)]) kws) ∧
  callGradient (fun e x ops _ ks => observe e x ops ks) tree data o kws = .ok (effectiveKeywords key (keywordValue key
    [("turbo", if o.shared.turbo then 1 else 0)]) kws)
theorem callableForwarding_holds : callableForwarding := by
  intro E X tree data o kws key
  simp [callTree, callGradient, callKeywords, gradCallKeywords, Expressions.mergeMetadata,
    keywordLookup_fold]

/-- Reuses the expression-level enum selection law rather than a second
metadata model. src/InterfaceDynamicExpressions.jl:92; DE src/Expression.jl:251-254. -/
def expressionOperatorSelection : Prop := ∀ (ex : Expressions.Expression JF (Expressions.Settings JF))
  (ops : OpEnum JF), Expressions.get_operators ex (some ops) = .ok ops
 theorem expressionOperatorSelection_holds : expressionOperatorSelection := by intro ex ops; rfl

end SymReg.Interface
