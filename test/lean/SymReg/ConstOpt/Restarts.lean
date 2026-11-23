import SymReg.ConstOpt.Contracts

namespace SymReg.ConstOpt
open DynExpr
open DynExpr.ParamStruct
open SymReg.HofMig (Member less)

/-- Successful restart calls in their actual order, with state from each
draw, broadcast, and Optim invocation used by the following operation. -/
inductive RestartTrace {C H : Type} (svc : RestartServices C H)
    (optimizer : Optimizer C H) (obj : Objective C H) (cfg : Config) (x0 : List C) :
    EvalState C H → List (OptimResult C) → EvalState C H → Prop
  | nil (s) : RestartTrace svc optimizer obj cfg x0 s [] s
  | cons {s typed sized drawn broadcast next final element dims eps point result results} :
      svc.eltype x0 s = (.ok element, typed) →
      svc.size x0 typed = (.ok dims, sized) →
      svc.randn cfg.rng element dims sized = (.ok eps, drawn) →
      svc.broadcast element x0 eps drawn = (.ok point, broadcast) →
      runOptimizer optimizer obj point cfg broadcast = (.ok result, next) →
      RestartTrace svc optimizer obj cfg x0 next results final →
      RestartTrace svc optimizer obj cfg x0 s (result :: results) final

def restartCertificate : Prop :=
  ∀ (C H : Type) (svc : RestartServices C H) optimizer obj cfg x0 fraction n
    (best : OptimResult C) evals (s : EvalState C H) after best' evals',
    runRestarts svc optimizer obj cfg x0 fraction n best evals s = (.ok (best', evals'), after) →
    ∃ candidates : List (OptimResult C), candidates.length = n ∧
      best' = candidates.foldl chooseResult best ∧
      evals' = candidates.foldl (fun total r => round64 (total + weightedCalls r.fCalls fraction)) evals

theorem restartCertificate_withTrace {C H : Type} (svc : RestartServices C H)
    (optimizer : Optimizer C H) (obj : Objective C H) (cfg : Config) (x0 : List C)
    (fraction : JF) (n : Nat) (best : OptimResult C) (evals : JF)
    (s after : EvalState C H) (best' : OptimResult C) (evals' : JF)
    (h : runRestarts svc optimizer obj cfg x0 fraction n best evals s =
      (.ok (best', evals'), after)) :
    ∃ candidates : List (OptimResult C), candidates.length = n ∧
      best' = candidates.foldl chooseResult best ∧
      evals' = candidates.foldl (fun total r => round64 (total + weightedCalls r.fCalls fraction)) evals ∧
      RestartTrace svc optimizer obj cfg x0 s candidates after := by
  revert best evals s after best' evals'
  induction n with
  | zero =>
    intro best evals s after best' evals' h
    simp [runRestarts] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨[], rfl, rfl, rfl, .nil _⟩
  | succ n ih =>
    intro best evals s after best' evals' h
    cases ht : svc.eltype x0 s with
    | mk out typed =>
      cases out with
      | error err => simp [runRestarts, ht] at h
      | ok element =>
        cases hs : svc.size x0 typed with
        | mk out sized =>
          cases out with
          | error err => simp [runRestarts, ht, hs] at h
          | ok dims =>
            cases hd : svc.randn cfg.rng element dims sized with
            | mk out drawn =>
              cases out with
              | error err => simp [runRestarts, ht, hs, hd] at h
              | ok eps =>
                cases hb : svc.broadcast element x0 eps drawn with
                | mk out broadcast =>
                  cases out with
                  | error err => simp [runRestarts, ht, hs, hd, hb] at h
                  | ok point =>
                    cases ho : runOptimizer optimizer obj point cfg broadcast with
                    | mk out next =>
                      cases out with
                      | error err => simp [runRestarts, ht, hs, hd, hb, ho] at h
                      | ok result =>
                        simp only [runRestarts, effect_bind, ht, hs, hd, hb, ho] at h
                        obtain ⟨results, hl, hb', hc, trace⟩ := ih _ _ next after best' evals' h
                        exact ⟨result :: results, by simp [hl], hb', hc, .cons ht hs hd hb ho trace⟩

theorem restartCertificate_holds : restartCertificate := by
  intro C H svc optimizer obj cfg x0 fraction n best evals s after best' evals' h
  obtain ⟨candidates, hl, hb, hc, _⟩ :=
    restartCertificate_withTrace svc optimizer obj cfg x0 fraction n best evals s after best' evals' h
  exact ⟨candidates, hl, hb, hc⟩

def nonpositiveRestarts : Prop :=
  ∀ (C H R : Type) (svc : OptimServices C H) (e : Evaluator C H R) fg cfg x0 member
    (s : EvalState C H) baseline afterBaseline,
    cfg.restarts ≤ 0 →
    objectiveKind cfg.algorithm cfg.backend = .value →
    evaluate e false x0 s = (.ok baseline, afterBaseline) →
    ∀ result afterOptim, runOptimizer svc.optimizer (.value (evaluate e false)) x0 cfg
      afterBaseline = (.ok result, afterOptim) →
    ∀ fraction afterFraction, datasetFraction svc.indices svc.length svc.fullCount
      afterOptim = (.ok fraction, afterFraction) →
    optimizeInner svc e fg cfg x0 member s =
      finish e svc.finish x0 baseline result (weightedCalls result.fCalls fraction) fraction
        member afterFraction

theorem nonpositiveRestarts_holds : nonpositiveRestarts := by
  intro C H R svc e fg cfg x0 member s baseline afterBaseline hc hk hb result afterOptim ho
    fraction afterFraction hf
  have hz : cfg.restarts.toNat = 0 := Int.toNat_eq_zero.mpr hc
  simp [optimizeInner, hk, hb, ho, hf, hz, runRestarts]

theorem nonpositiveRestarts_gradient {C H R : Type} (svc : OptimServices C H)
    (e : Evaluator C H R) (fg wrapped : FG C H) (cfg : Config) (x0 : List C) (member : Nat)
    (s prepared afterBaseline afterOptim afterFraction : EvalState C H) (baseline fraction : JF)
    (result : OptimResult C) (hc : cfg.restarts ≤ 0)
    (hk : objectiveKind cfg.algorithm cfg.backend = .valueGradient)
    (hw : svc.onlyFG fg s = (.ok wrapped, prepared))
    (hb : evaluate e false x0 prepared = (.ok baseline, afterBaseline))
    (ho : runOptimizer svc.optimizer (.valueGradient wrapped) x0 cfg afterBaseline =
      (.ok result, afterOptim))
    (hf : datasetFraction svc.indices svc.length svc.fullCount afterOptim =
      (.ok fraction, afterFraction)) :
    optimizeInner svc e fg cfg x0 member s =
      finish e svc.finish x0 baseline result (weightedCalls result.fCalls fraction) fraction
        member afterFraction := by
  have hz : cfg.restarts.toNat = 0 := Int.toNat_eq_zero.mpr hc
  simp [optimizeInner, hk, hw, hb, ho, hf, hz, runRestarts]

theorem onlyFG_error_first {C H R : Type} (svc : OptimServices C H)
    (e : Evaluator C H R) (fg : FG C H) (cfg : Config) (x0 : List C) (member : Nat)
    (s after : EvalState C H) (err : JlError)
    (hk : objectiveKind cfg.algorithm cfg.backend = .valueGradient)
    (hw : svc.onlyFG fg s = (.error err, after)) :
    optimizeInner svc e fg cfg x0 member s = (.error err, after) := by
  simp [optimizeInner, hk, hw]

theorem optimizerReceivesValue {C H R : Type} (svc : OptimServices C H)
    (e : Evaluator C H R) (fg : FG C H) (cfg : Config) (x0 : List C) (member : Nat)
    (s afterBaseline afterOptim : EvalState C H) (baseline : JF) (err : JlError)
    (hk : cfg.algorithm = .newton ∨ cfg.backend = none)
    (hb : evaluate e false x0 s = (.ok baseline, afterBaseline))
    (ho : svc.optimizer (.value (evaluate e false)) x0 cfg.algorithm cfg.optimizerOptions
      {afterBaseline with log := afterBaseline.log ++ [.optimizer x0 cfg.algorithm .value]} =
      (.error err, afterOptim)) :
    optimizeInner svc e fg cfg x0 member s = (.error err, afterOptim) := by
  simp [optimizeInner, (objectiveDispatch_holds _ _).mpr hk, hb, runOptimizer, Objective.kind, ho]

theorem optimizerReceivesGradient {C H R : Type} (svc : OptimServices C H)
    (e : Evaluator C H R) (fg wrapped : FG C H) (cfg : Config) (x0 : List C) (member : Nat)
    (s prepared afterBaseline afterOptim : EvalState C H) (baseline : JF) (err : JlError)
    (hk : ¬ (cfg.algorithm = .newton ∨ cfg.backend = none))
    (hw : svc.onlyFG fg s = (.ok wrapped, prepared))
    (hb : evaluate e false x0 prepared = (.ok baseline, afterBaseline))
    (ho : svc.optimizer (.valueGradient wrapped) x0 cfg.algorithm cfg.optimizerOptions
      {afterBaseline with log := afterBaseline.log ++ [.optimizer x0 cfg.algorithm .valueGradient]} =
      (.error err, afterOptim)) :
    optimizeInner svc e fg cfg x0 member s = (.error err, afterOptim) := by
  have hn : objectiveKind cfg.algorithm cfg.backend ≠ .value :=
    fun h => hk ((objectiveDispatch_holds _ _).mp h)
  simp [optimizeInner, hn, hw, hb, runOptimizer, Objective.kind, ho]

/-- Actual objective calls, separate from Optim's bookkeeping. -/
def lossCalls {C : Type} (calls : List (Call C)) : Nat :=
  (calls.filter (fun call => match call with | .loss _ _ => true | _ => false)).length

@[simp] theorem lossCalls_append {C : Type} (left right : List (Call C)) :
    lossCalls (left ++ right) = lossCalls left + lossCalls right := by
  simp [lossCalls, List.filter_append]

/-- For this property the optimizer reports exactly the number of real f calls
it performed. There is no assumption about its minimum or convergence. -/
def CountsLossCalls {C H : Type} (optimizer : Optimizer C H) (obj : Objective C H) : Prop :=
  ∀ x algorithm options (s : EvalState C H) result final,
    optimizer obj x algorithm options s = (.ok result, final) →
    lossCalls final.log = lossCalls s.log + result.fCalls

def evalAccounting : Prop :=
  ∀ (C H R : Type) (svc : OptimServices C H) (e : Evaluator C H R) fg cfg x0 member
    (s : EvalState C H) out after,
    svc.indices = none →
    CountsLossCalls svc.optimizer (.value (evaluate e false)) →
    optimizeInner svc e fg cfg x0 member s = (.ok out, after) →
    out = weightedCalls (lossCalls after.log - lossCalls s.log) (.fin 1)

private def countingEvaluator : Evaluator JF Nat Unit :=
  ⟨0, (), fun _ _ _ => pure (), fun _ _ => do
    modifyEffect fun s => {s with heap := s.heap + 1}
    pure (.fin 1)⟩

private def unusedGradient : FG JF Nat := fun _ _ _ => failEffect .boundsError

private def countedOptimizer : Optimizer JF Nat := fun obj x _ _ =>
  match obj with
  | .value value => do
    let _ ← value x
    pure ⟨x, .fin 1, 1, 0, 0, 0⟩
  | .valueGradient _ => failEffect .boundsError

private def countedServices : OptimServices JF Nat :=
  ⟨fun _ => failEffect .boundsError, countedOptimizer, none, fun _ => failEffect .boundsError,
   fun _ => 1, ⟨fun _ => failEffect .boundsError, fun _ => failEffect .boundsError,
     fun _ _ _ => failEffect .boundsError, fun _ _ _ => failEffect .boundsError⟩,
   ⟨fun _ => pure 0, fun _ _ => failEffect .boundsError, fun _ => failEffect .boundsError,
     fun _ _ => failEffect .boundsError, failEffect .boundsError, fun _ _ => failEffect .boundsError⟩⟩

private def counterConfig : Config := ⟨.configured 0, none, 0, 0, 0⟩
private def counterState : EvalState JF Nat := { heap := 0 }
private def counterAfter : EvalState JF Nat :=
  { heap := 2, log := [.write 0 [.fin 1], .loss 0 false, .optimizer [.fin 1] (.configured 0) .value,
    .write 0 [.fin 1], .loss 0 false, .write 0 [.fin 1]] }

private theorem countedOptimizer_correct : CountsLossCalls countedOptimizer
    (.value (evaluate countingEvaluator false)) := by
  intro x algorithm options s result final h
  simp [countedOptimizer, evaluate, writeParameters, callContext, countingEvaluator] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [lossCalls, List.filter_append]

theorem evalAccounting_refuted : ¬ evalAccounting := by
  intro h
  have bad := h JF Nat Unit countedServices countingEvaluator unusedGradient counterConfig
    [.fin 1] 0 counterState (weightedCalls 1 (.fin 1)) counterAfter rfl countedOptimizer_correct (by
      simp [optimizeInner, objectiveKind, counterConfig, countedServices, runOptimizer, datasetFraction,
        runRestarts, countedOptimizer, evaluate, writeParameters, callContext, countingEvaluator,
        finish, less, DynExpr.Expressions.Sampling.greater, counterState, counterAfter, Objective.kind])
  have unequal : weightedCalls 1 (.fin 1) ≠ weightedCalls 2 (.fin 1) := by
    decide +kernel
  exact unequal bad

end SymReg.ConstOpt
