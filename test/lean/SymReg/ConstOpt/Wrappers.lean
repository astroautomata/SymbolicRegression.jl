import SymReg.ConstOpt.Core

namespace SymReg.ConstOpt
open DynExpr
open DynExpr.ParamStruct

/-- The objective writes x through the original references before any loss call.
The loss reads the resulting heap and receives the requested regularization flag. -/
def objectiveWritesFirst : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) regularization x s written value after,
    writeParameters e x s = (.ok (), written) →
    e.loss e.tree regularization
      {written with log := written.log ++ [.loss e.tree regularization]} = (.ok value, after) →
    evaluate e regularization x s = (.ok value, after)

theorem objectiveWritesFirst_holds : objectiveWritesFirst := by
  intro C H R e regularization x s written value after hw hl
  simp [evaluate, hw, callContext, hl]

def objectiveErrors : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) regularization x s,
    (∀ err after, e.set e.tree x e.refs {s with log := s.log ++ [.write e.tree x]} =
      (.error err, after) → evaluate e regularization x s = (.error err, after)) ∧
    (∀ written err after, writeParameters e x s = (.ok (), written) →
      e.loss e.tree regularization {written with log := written.log ++ [.loss e.tree regularization]} =
        (.error err, after) → evaluate e regularization x s = (.error err, after))

theorem objectiveErrors_holds : objectiveErrors := by
  intro C H R e regularization x s
  exact ⟨fun _ _ h => by simp [evaluate, writeParameters, h],
    fun _ _ _ hw hl => by simp [evaluate, hw, callContext, hl]⟩

def contextBackendSelection : Prop :=
  ∀ (S : Type) (create : Int → Effect S (Option SymReg.Loss.Context)) (s : S),
    (∀ result after, create 0 s = (result, after) →
      initialContext none create s = (result, after)) ∧
    (∀ backendId, initialContext (some backendId) create s = (.ok none, s))

theorem contextBackendSelection_holds : contextBackendSelection := by
  intro S create s
  exact ⟨fun _ _ h => h, fun _ => rfl⟩

def cachedPreparationHit : Prop :=
  ∀ (S : Type) (svc : PrepServices S) ctx backend tree task key (s : S) object,
    (svc.read s).dictionaries task key = some object →
    (svc.acceptsType ctx backend tree object s = true →
      stablePrep svc ctx backend tree task key s = (.ok object, s)) ∧
    (svc.acceptsType ctx backend tree object s = false →
      stablePrep svc ctx backend tree task key s =
        (.error (.errorException "TypeError in stable_get!"), s))

theorem cachedPreparationHit_holds : cachedPreparationHit := by
  intro S svc ctx backend tree task key s object h
  exact ⟨fun ht => by simp [stablePrep, h, ht], fun ht => by simp [stablePrep, h, ht]⟩

def cachedPreparationMiss : Prop :=
  ∀ (svc : PrepServices PrepStore) ctx backend tree task key (s : PrepStore),
    (∀ s, svc.read s = s) → (∀ p s, svc.write p s = p) →
    s.dictionaries task key = none →
    (∀ err after, svc.prepare ctx backend tree s = (.error err, after) →
      stablePrep svc ctx backend tree task key s = (.error err, after)) ∧
    (∀ object after, svc.prepare ctx backend tree s = (.ok object, after) →
      let final := (stablePrep svc ctx backend tree task key s).2
      final.dictionaries task key = some object ∧
      (∀ k, k ≠ key → final.dictionaries task k = after.dictionaries task k) ∧
      ∀ t, t ≠ task → final.dictionaries t = after.dictionaries t)

theorem cachedPreparationMiss_holds : cachedPreparationMiss := by
  intro svc ctx backend tree task key s hr hw h
  constructor
  · intro err after hp
    simp [stablePrep, hr, h, hp]
  · intro object after hp
    let updated := fun t k => if t = task ∧ k = key then some object else after.dictionaries t k
    have he : (stablePrep svc ctx backend tree task key s).2 =
        { after with dictionaries := updated } := by
      simp only [stablePrep, effect_bind, inspectEffect_apply, hr, h, hp, modifyEffect_apply,
        hw, effect_pure, updated]
      split <;> simp
    refine ⟨by simp [he, updated], ?_, ?_⟩
    · intro k hk; simp [he, updated, hk]
    · intro t ht; funext k; simp [he, updated, ht]

def prepDependsOnType : Prop :=
  ∀ (S : Type) (svc : PrepServices S) ctx backend first second key dictionary object (s after : S),
    svc.treeType first s = svc.treeType second s →
    svc.hash (ctx, backend, svc.treeType first s) s = (.ok key, after) →
    (svc.read after).taskCaches (svc.read after).task = some dictionary →
    (svc.read after).dictionaries dictionary key = some object →
    svc.acceptsType ctx backend first object after = true →
    svc.acceptsType ctx backend second object after = true →
    cachedPrep svc ctx backend first s = (.ok object, after) ∧
    cachedPrep svc ctx backend second s = (.ok object, after)

theorem prepDependsOnType_holds : prepDependsOnType := by
  intro S svc ctx backend first second key dictionary object s after ht hh hd he h₁ h₂
  exact ⟨by simp [cachedPrep, taskDictionary, stablePrep, hh, hd, he, h₁],
    by simp [cachedPrep, taskDictionary, stablePrep, ← ht, hh, hd, he, h₂]⟩

def noBackendNoPreparation : Prop :=
  ∀ (S : Type) (svc : PrepServices S) ctx tree (s : S),
    prepareGrad svc ctx tree none s = (.ok (none, none), s)

theorem noBackendNoPreparation_holds : noBackendNoPreparation := by
  intro S svc ctx tree s; rfl

def gradientIgnoresValueRequest : Prop :=
  ∀ (C H R G P : Type) (g : GradEvaluator C H R G P) first second buffer x s,
    gradient g first buffer x s = gradient g second buffer x s

theorem gradientIgnoresValueRequest_holds : gradientIgnoresValueRequest := by
  intro C H R G P g first second buffer x s; rfl

def gradientNoBuffer : Prop :=
  ∀ (C H R G P : Type) (g : GradEvaluator C H R G P) requested x s written value grad after,
    writeParameters g.evaluator x s = (.ok (), written) →
    g.valueGradient g.prep g.backend g.evaluator.tree
      {written with log := written.log ++ [.gradient g.evaluator.tree]} = (.ok (value, grad), after) →
    gradient g requested none x s = (.ok value, after)

theorem gradientNoBuffer_holds : gradientNoBuffer := by
  intro C H R G P g requested x s written value grad after hw hg
  cases grad <;> simp [gradient, hw, hg]

def gradientAbsent : Prop :=
  ∀ (C H R G P : Type) (g : GradEvaluator C H R G P) requested buffer x s written value after,
    writeParameters g.evaluator x s = (.ok (), written) →
    g.valueGradient g.prep g.backend g.evaluator.tree
      {written with log := written.log ++ [.gradient g.evaluator.tree]} = (.ok (value, none), after) →
    gradient g requested (some buffer) x s = (.ok value, after)

theorem gradientAbsent_holds : gradientAbsent := by
  intro C H R G P g requested buffer x s written value after hw hg
  simp [gradient, hw, hg]

def gradientExtractionChecked : Prop :=
  ∀ (C H R G P : Type) (g : GradEvaluator C H R G P) requested buffer x s written value grad
    afterAD source afterExtract n afterSource m afterDestination,
    writeParameters g.evaluator x s = (.ok (), written) →
    g.valueGradient g.prep g.backend g.evaluator.tree
      {written with log := written.log ++ [.gradient g.evaluator.tree]} = (.ok (value, some grad), afterAD) →
    g.extract grad g.evaluator.tree g.evaluator.refs afterAD = (.ok source, afterExtract) →
    g.length source afterExtract = (.ok n, afterSource) →
    g.length buffer afterSource = (.ok m, afterDestination) →
    (n = m → ∀ result after, g.broadcast buffer source afterDestination = (result, after) →
      gradient g requested (some buffer) x s = ((fun _ => value) <$> result, after)) ∧
    (n ≠ m → ∀ ns ss ms ts, g.length source afterDestination = (.ok ns, ss) →
      g.length buffer ss = (.ok ms, ts) →
      gradient g requested (some buffer) x s = (.error (.dimensionMismatch
        s!"extracted {ns} parameter gradients for an optimization vector of length {ms}"), ts))

theorem gradientExtractionChecked_holds : gradientExtractionChecked := by
  intro C H R G P g requested buffer x s written value grad afterAD source afterExtract n
    afterSource m afterDestination hw ha he hn hm
  constructor
  · intro hl result after hb
    cases result <;> simp [gradient, hw, ha, he, hn, hm, hl, hb]
  · intro hl ns ss ms ts hs ht
    simp [gradient, hw, ha, he, hn, hm, hl, hs, ht]

end SymReg.ConstOpt
