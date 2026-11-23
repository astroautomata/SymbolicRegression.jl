import SymReg.ConstOpt.Core
import DynExpr.Expressions.Wrapper
import DynExpr.NodeUtils.Nodes

namespace SymReg.ConstOpt
open DynExpr
open DynExpr.ParamStruct

/-- Compatibility hooks, `src/ConstantOptimization.jl:40,53-55,68`. -/
def getConstantsForOptimization {E R : Type} (getScalar : E → R) (ex : E) : R := getScalar ex
def setConstantsForOptimization {E C R A : Type} (setScalar : E → C → R → A)
    (ex : E) (x : C) (refs : R) : A := setScalar ex x refs
def extractGradientForOptimization {G E A : Type} (extract : G → E → A)
    (grad : G) (ex : E) : A := extract grad ex

inductive HookMethod where
  | expression
  | fallback
  | composable
  | template
  deriving DecidableEq

-- Source: src/ConstantOptimization.jl:85-90; src/ComposableExpression.jl:131-133;
-- src/TemplateExpression.jl:491-496
-- function get_optimizable_parameters(ex, options)
--     return get_constants_for_optimization(ex)
-- end
-- function get_optimizable_parameters(ex::Expression, options)
--     return get_scalar_constants(ex)
-- end
def getOptimizable {E A : Type} (method : HookMethod)
    (legacy scalar composable template : E → A) (ex : E) : A :=
  match method with
  | .expression => scalar ex
  | .fallback => legacy ex
  | .composable => composable ex
  | .template => template ex

-- Source: src/ConstantOptimization.jl:115-120; src/ComposableExpression.jl:135-139;
-- src/TemplateExpression.jl:498-508
-- function set_optimizable_parameters!(ex, x, refs)
--     return set_constants_for_optimization!(ex, x, refs)
-- end
-- function set_optimizable_parameters!(ex::Expression, x, refs)
--     return set_scalar_constants!(ex, x, refs)
-- end
def setOptimizable {E C R A : Type} (method : HookMethod)
    (legacy scalar composable template : E → C → R → A) (ex : E) (x : C) (refs : R) : A :=
  match method with
  | .expression => scalar ex x refs
  | .fallback => legacy ex x refs
  | .composable => composable ex x refs
  | .template => template ex x refs

-- Source: src/ConstantOptimization.jl:134-139
-- function extract_optimizable_gradient(grad, ex, refs)
--     return extract_gradient_for_optimization(grad, ex)
-- end
-- function extract_optimizable_gradient(grad, ex::Expression, refs)
--     return extract_gradient(grad, ex)
-- end
def extractOptimizable {G E R A : Type} (method : HookMethod) (legacy scalar : G → E → A)
    (grad : G) (ex : E) (_refs : R) : A :=
  match method with
  | .expression => scalar grad ex
  | .fallback | .composable | .template => legacy grad ex

/-- Owning-context fallback, `src/ConstantOptimization.jl:100-102`.
Expression integrations may override this method; the fallback itself ignores context. -/
def getContextParameters {Context E O A : Type} (_context : Context)
    (get : E → O → A) (ex : E) (options : O) : A := get ex options

inductive HookCall where
  | get (method : HookMethod) (expression : Nat)
  | set (method : HookMethod) (expression vector refs : Nat)
  | extract (method : HookMethod) (gradient expression : Nat)
  deriving DecidableEq

def hookDispatch : Prop :=
  ∀ method (expression vector refs otherRefs gradient : Nat) (before : List HookCall),
    let get := fun kind ex => modifyEffect (· ++ [.get kind ex])
    let set := fun kind ex x rs => modifyEffect (· ++ [.set kind ex x rs])
    let extract := fun kind g ex => modifyEffect (· ++ [.extract kind g ex])
    let operations : Effect (List HookCall) Unit := do
      getOptimizable method (get .fallback) (get .expression) (get .composable) (get .template) expression
      setOptimizable method (set .fallback) (set .expression) (set .composable) (set .template)
        expression vector refs
      extractOptimizable method (extract .fallback) (extract .expression) gradient expression otherRefs
    operations before = (.ok (), before ++ [
      .get method expression, .set method expression vector refs,
      .extract (if method = .expression then .expression else .fallback) gradient expression])

theorem hookDispatch_holds : hookDispatch := by
  intro method expression vector refs otherRefs gradient before
  cases method <;>
    simp [getOptimizable, setOptimizable, extractOptimizable, List.append_assoc]

private def compatibilityOrderContract : Prop :=
  ∀ (E C R G A : Type) (ex : E) (x : C) (refs : R) (grad : G)
    (get : E → A) (set : E → C → R → A) (extract : G → E → A),
    getConstantsForOptimization get ex = get ex ∧
    setConstantsForOptimization set ex x refs = set ex x refs ∧
    extractGradientForOptimization extract grad ex = extract grad ex

private theorem compatibilityOrderContract_holds : compatibilityOrderContract := by
  intro E C R G A ex x refs grad get set extract
  exact ⟨rfl, rfl, rfl⟩

private def compatibilityOrderLaw : Prop :=
  ∀ (E C R G : Type) (ex : E) (x : C) (refs : R) (grad : G),
    getOptimizable .fallback (getConstantsForOptimization fun e : E => e) id id id ex = ex ∧
    setOptimizable .fallback (setConstantsForOptimization fun e cs rs => (e, cs, rs))
      (fun e cs rs => (e, cs, rs)) (fun e cs rs => (e, cs, rs)) (fun e cs rs => (e, cs, rs))
      ex x refs = (ex, x, refs) ∧
    extractOptimizable .fallback (extractGradientForOptimization fun g e => (g, e))
      (fun g e => (g, e)) grad ex refs = (grad, ex)

private theorem compatibilityOrderLaw_holds : compatibilityOrderLaw := by
  intro E C R G ex x refs grad
  exact ⟨rfl, rfl, rfl⟩

private def compatibilitySession : Prop :=
  ∀ (E C R G A : Type) (ex : E) (replacement : C) (gradient : G)
    (get : E → Jl (C × R)) (set : E → C → R → Jl E) (extract : G → E → Jl A),
    (do
      let (_, refs) ← getOptimizable .fallback (getConstantsForOptimization get) get get get ex
      let updated ← setOptimizable .fallback (setConstantsForOptimization set) set set set ex replacement refs
      extractOptimizable .fallback (extractGradientForOptimization extract) extract gradient updated refs) =
      (get ex).bind (fun (_, refs) => (set ex replacement refs).bind (extract gradient))

def compatibilityOrder : Prop := compatibilityOrderContract ∧ compatibilityOrderLaw ∧ compatibilitySession

theorem compatibilityOrder_holds : compatibilityOrder := by
  refine ⟨compatibilityOrderContract_holds, compatibilityOrderLaw_holds, ?_⟩
  intro E C R G A ex replacement gradient get set extract
  rfl

theorem compatibilityEffects {S E C R G A : Type} (ex : E) (x : C) (grad : G)
    (get : E → Effect S (C × R)) (set : E → C → R → Effect S Unit)
    (extract : G → E → Effect S A) (start : S) :
    let run : Effect S A := do
      let (_, refs) ← getOptimizable .fallback (getConstantsForOptimization get) get get get ex
      setOptimizable .fallback (setConstantsForOptimization set) set set set ex x refs
      extractOptimizable .fallback (extractGradientForOptimization extract) extract grad ex refs
    run start = match get ex start with
      | (.error err, after) => (.error err, after)
      | (.ok (_, refs), after) =>
        match set ex x refs after with
        | (.error err, stopped) => (.error err, stopped)
        | (.ok (), updated) => extract grad ex updated := by
  dsimp only
  cases h : get ex start with
  | mk reply after =>
    cases reply with
    | error _ => simp [getOptimizable, getConstantsForOptimization, h]
    | ok values =>
      rcases values with ⟨values, refs⟩
      cases hset : set ex x refs after with
      | mk out updated =>
        cases out <;>
          simp [getOptimizable, getConstantsForOptimization, setOptimizable, setConstantsForOptimization,
            extractOptimizable, extractGradientForOptimization, h, hset]

def contextDoesNotSelect : Prop :=
  ∀ (Context E O A : Type) (first second : Context) (get : E → O → A) ex options,
    getContextParameters first get ex options = getContextParameters second get ex options

theorem contextDoesNotSelect_holds : contextDoesNotSelect := by
  intro Context E O A first second get ex options; rfl

/-- Adapter supplies the otherwise opaque reference argument without copying it. -/
def setParametric (s : ConstantState) (values : List JF) (_refs : Unit) := setConstants s values

/-- The default SR hooks reuse DE's constant-reference model. Distinct references
read back every exact-size optimizer vector in getter order, followed by the
column-major parametric-expression parameter array. -/
def scalarRoundtrip : Prop :=
  ∀ (s out : ConstantState) (old values : List JF),
    s.refs.Nodup → getConstantsForOptimization getConstants s = .ok old →
    values.length = old.length →
    setConstantsForOptimization setParametric s values () = .ok out →
    getConstantsForOptimization getConstants out = .ok values

theorem scalarRoundtrip_holds : scalarRoundtrip := by
  intro s out old values hn hg hl hw
  have hlen := getConstants_length s old hg
  exact setConstants_read_values s out values hn (by omega) hw

example : (ConstantState.mk Heap.empty [] [JF.fin 1]).refs.Nodup ∧
    getConstants (ConstantState.mk Heap.empty [] [JF.fin 1]) = .ok [JF.fin 1] ∧
    ([JF.fin 2] : List JF).length = [JF.fin 1].length ∧
    setParametric (ConstantState.mk Heap.empty [] [JF.fin 1]) [JF.fin 2] () =
      .ok (ConstantState.mk Heap.empty [] [JF.fin 2]) := ⟨by simp, rfl, rfl, rfl⟩

private def expressionForwardsReferencesContract : Prop :=
  ∀ (T M R C A : Type) (ex : DynExpr.Expressions.Expression T M)
    (get : Tree T → A) (set : Tree T → C → R → A) values refs,
    getConstantsForOptimization (DynExpr.Expressions.forwardConstants get) ex = get ex.tree ∧
    setConstantsForOptimization (DynExpr.Expressions.forwardSetConstants set) ex values refs =
      set ex.tree values refs

private theorem expressionForwardsReferencesContract_holds : expressionForwardsReferencesContract := by
  intro T M R C A ex get set values refs
  exact ⟨rfl, rfl⟩

private def expressionForwardsReferencesLaw : Prop :=
  ∀ (g : DynExpr.Graph Nat) sharing fuel root values refs,
    DynExpr.Graph.NoAlias g root →
    getConstantsForOptimization (fun h => DynExpr.NodeUtils.getScalarConstants h sharing fuel root) g =
      .ok (values, refs) →
    setConstantsForOptimization DynExpr.NodeUtils.setScalarConstants g values refs = .ok g

private theorem expressionForwardsReferencesLaw_holds : expressionForwardsReferencesLaw :=
  DynExpr.NodeUtils.scalarGetterRestore_proven

private def expressionReferenceIdentity : Prop :=
  ∀ (g : DynExpr.Graph Nat) (share : Bool) (fuel root : Nat) (values : List Nat) (refs : List Addr),
    getConstantsForOptimization (fun h => DynExpr.NodeUtils.getScalarConstants h share fuel root) g =
      DynExpr.NodeUtils.getScalarConstants g share fuel root ∧
    setConstantsForOptimization DynExpr.NodeUtils.setScalarConstants g values refs =
      DynExpr.NodeUtils.setScalarConstants g values refs

def expressionForwardsReferences : Prop := expressionForwardsReferencesContract ∧
  expressionForwardsReferencesLaw ∧ expressionReferenceIdentity

/-- Legal repeated Node references need not represent independent optimizer
coordinates. The unrestricted roundtrip claim is false. -/
def scalarAliasRoundtrip : Prop :=
  ∀ (s out : ConstantState) (old values : List JF),
    getConstantsForOptimization getConstants s = .ok old → values.length = old.length →
    setConstantsForOptimization setParametric s values () = .ok out →
    getConstantsForOptimization getConstants out = .ok values

private def aliased : ConstantState :=
  ⟨(Heap.empty.alloc (JF.fin 1)).2, [0, 0], []⟩
private def aliasedOut : ConstantState :=
  (setParametric aliased [JF.fin 2, JF.fin 3] ()).toOption.getD aliased

theorem scalarAliasRoundtrip_refuted : ¬ scalarAliasRoundtrip := by
  intro h
  have bad := h aliased aliasedOut [.fin 1, .fin 1] [.fin 2, .fin 3]
    (by decide) (by decide) (by rfl)
  have unequal : getConstantsForOptimization getConstants aliasedOut ≠
      .ok [JF.fin 2, JF.fin 3] := by decide
  exact unequal bad

end SymReg.ConstOpt
