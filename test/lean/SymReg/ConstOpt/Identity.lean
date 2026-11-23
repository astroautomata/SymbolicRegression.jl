import SymReg.ConstOpt.Contracts

namespace SymReg.ConstOpt
open DynExpr
open DynExpr.ParamStruct
open SymReg.HofMig (Member)

def completeIdentity : Prop :=
  ∀ (C H R G : Type) (hooks : EntryHooks (EvalState C H) R) element
    (construct : Invocation → Nat → R →
      Effect (EvalState C H) (Evaluator C H R × GradEvaluator C H R G PrepObject))
    svc backend restarts values args (s after : EntryStore (EvalState C H) R) returned count,
    optimizeComplete hooks element construct svc backend restarts values args s =
      (.ok (returned, count), after) → returned = args.member

theorem completeIdentity_holds : completeIdentity := by
  intro C H R G hooks element construct svc backend restarts values args s after returned count h
  let inner := prepareOnStore construct svc backend restarts values
  change optimizeConstants hooks element inner args s = (_, after) at h
  cases hc : optimizeCount hooks element inner args s with
  | mk result state =>
    cases result <;> simp [optimizeConstants, hc] at h
    exact h.1.1.symm

end SymReg.ConstOpt
