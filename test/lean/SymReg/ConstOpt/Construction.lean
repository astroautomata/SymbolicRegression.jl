import SymReg.ConstOpt.Core

namespace SymReg.ConstOpt
open DynExpr

def constructedWithoutAD : Prop :=
  ∀ (C H R G : Type) set tree (refs : R) loss create allocate prep valueGradient
    (extract : G → Nat → R → Effect (EvalState C H) Nat) length broadcast (s : EvalState C H),
    (∀ error after, create 0 s = (.error error, after) →
      buildEvaluators set tree refs loss create allocate none prep valueGradient extract length broadcast s =
        (.error error, after)) ∧
    (∀ context after id allocated, create 0 s = (.ok context, after) →
      allocate context after = (.ok id, allocated) →
      ∃ f fg, buildEvaluators set tree refs loss create allocate none prep valueGradient extract length broadcast s =
          (.ok (f, fg), allocated) ∧ f.tree = tree ∧ f.refs = refs ∧ fg.evaluator = f ∧
        f.loss = loss id ∧ fg.valueGradient = valueGradient id ∧ fg.prep = none)

theorem constructedWithoutAD_holds : constructedWithoutAD := by
  intro C H R G set tree refs loss create allocate prep valueGradient extract length broadcast s
  constructor
  · intro error after hc
    simp [buildEvaluators, initialContext, hc]
  · intro context after id allocated hc ha
    refine ⟨⟨tree, refs, set, loss id⟩, ⟨⟨tree, refs, set, loss id⟩, none, none,
      valueGradient id, extract, length, broadcast⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp [buildEvaluators, initialContext, prepareGrad, hc, ha]

end SymReg.ConstOpt
