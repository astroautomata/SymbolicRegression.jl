import SymReg.Backsolve.Library
import DynExpr.Registry.Types

namespace SymReg.Backsolve
open DynExpr

/-- A unit coefficient needs no multiplication node. If a term in a prepared library
already matches every finite target row, it fits at its own complexity. -/
def unit_fit_within_budget : Prop :=
  ∀ (E : FitEnv) (cfg : BacksolveCfg) (nf : Int) (target : Vec) (mask : List Bool)
    (setup : Setup) (term : Tree JF) (budget : Int),
    prepareSetup E nf cfg.maxLibrarySize 10 none = .ok setup →
    term ∈ setup.terms → E.cx term ≤ budget →
    mask = List.replicate target.length true →
    E.ev term = .ok (target.map JF.fin, true) →
    target ≠ [] → (∃ x ∈ target, x ≠ 0) → 0 < cfg.maxTerms →
    ∃ fitted, fitSparse E cfg nf none target (some mask) (some setup) none (some budget) =
      .ok (some fitted)

private def unitRows : List Row := (List.range 12).map (fun i => [.fin ((i + 1 : Nat) : Rat)])
private def unitTarget : Vec := (List.range 12).map (fun i => ((i + 1 : Nat) : Rat))

private noncomputable def unitEnv : FitEnv :=
  let bin := [Op.b .plus, Op.b .mult]
  { bin := bin,
    ev := fun t => (evalArr nanLib [[], bin] unitRows t).map (fun ys => (ys, true)),
    cx := fun t => t.size,
    hash := fun _ => 0, sq := sqC, ch := chol1 }

private noncomputable def unitSetup : Setup :=
  let cols := [List.replicate 12 (.fin 1), unitTarget.map JF.fin]
  ⟨[.const (.fin 1), .feature 1], cols, 2, gramOf (cols.map (·.map toRat)), [3, 3], 1, 2⟩

private def unitCfg : BacksolveCfg := { cfg1 with maxLibrarySize := 200 }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem unit_fit_within_budget_refuted : ¬ unit_fit_within_budget := by
  intro h
  have hsetup : prepareSetup unitEnv 1 unitCfg.maxLibrarySize 10 none = .ok unitSetup := by
    have hb : buildLibrary unitEnv.ev unitEnv.hash 1 unitCfg.maxLibrarySize 10 none =
        .ok (unitSetup.terms, unitSetup.cols, 2) := by with_unfolding_all rfl
    have hc : weightedSumCosts unitEnv.cx unitEnv.bin unitSetup.terms = .ok ([3, 3], 1, 2) := by
      simp [weightedSumCosts, wscHeader, unitEnv, unitSetup, findIdx1,
        Tree.size, bind, Except.bind, pure, Except.pure]
      rfl
    simp [prepareSetup, hb, hc, bind, Except.bind, pure, Except.pure]
    rfl
  obtain ⟨fitted, hf⟩ := h unitEnv unitCfg 1 unitTarget (List.replicate 12 true)
    unitSetup (.feature 1) 1 hsetup (by simp [unitSetup]) (by simp [unitEnv, Tree.size])
    rfl (by with_unfolding_all rfl) (by decide +kernel) ⟨1, by decide +kernel, by decide⟩ (by decide)
  have hnone : fitSparse unitEnv unitCfg 1 none unitTarget (some (List.replicate 12 true))
      (some unitSetup) none (some 1) = .ok none := by
    have hgram : fitGram (unitSetup.cols.map (·.map toRat)) (some unitSetup.gram)
        unitTarget (some (List.replicate 12 true)) none =
        ([[12, 78], [78, 650]], [78, 650], 650) := by decide +kernel
    have hcore : fitTail unitEnv unitCfg [.const (.fin 1), .feature 1]
        [[12, 78], [78, 650]] [78, 650] 650 [3, 3] 1 (some 1) = .ok none := by
      have hsel (usable : List Bool) (corr : Vec) :
          (selectBest usable [] [3, 3] 0 1 corr 2).1 = 0 := by
        simp [selectBest, List.range_succ]
      have hloop (c : GCtx) (r : Rat) (corr : Vec) (hc : c.costs = [3, 3])
          (hn : c.n = 2) : greedyLoop c 1 (GState.init r 1 corr) = GState.init r 1 corr := by
        unfold greedyLoop
        simp [GCtx.extra, GState.init, hc, hn, hsel]
      have hshape : (decide (0 < (2 : Nat)) && ([[12, 78], [78, 650]] : Mat).length == 2 &&
          ([[12, 78], [78, 650]] : Mat).all (·.length == 2)) = true := by decide
      unfold fitTail greedyGram greedyRun
      change (if (match (if !(decide (0 < (2 : Nat)) &&
          ([[12, 78], [78, 650]] : Mat).length == 2 &&
          ([[12, 78], [78, 650]] : Mat).all (·.length == 2)) then (none : Option (GCtx × GState)) else _) with
        | none => (([0, 0] : Vec), false)
        | some (ctx, st) => if st.active.isEmpty then ([0, 0], false) else _).2 then _ else _) =
        (Except.ok none : Jl (Option (Tree JF)))
      simp only [hshape, Bool.not_true, Bool.false_eq_true, ite_false, unitCfg, cfg1, Option.getD_some]
      split
      · rfl
      · rename_i _ ctx st heq
        split at heq
        · cases heq
        · simp (disch := rfl) only [show (1 : Int).toNat = 1 by rfl,
            show ([78, 650] : Vec).length = 2 by rfl, Option.getD_some, hloop] at heq
          cases heq
          rfl
    have hcut : tooFewRows (some (List.replicate 12 true)) unitTarget.length = false := by decide
    simp only [fitSparse, show hasWS unitEnv.bin = true by decide, Bool.not_true, Bool.false_eq_true,
      ite_false, hcut, pure, Except.pure, bind, Except.bind, fitAfter, extraVals, fitCosts,
      Option.map_some, Option.toList_none, List.append_nil, hgram]
    exact hcore
  rw [hnone] at hf
  cases hf

open DynExpr.Registry in
def fitPropertyEntries : List Entry := [
  { id := "bs-fit-unit-budget", juliaFile := "src/Backsolve.jl", juliaFns := ["fit_sparse_expression"],
    statement := "A basis term that equals the target on every valid row is an available fit at its own complexity.",
    preconditions := "Prepared basis, nonzero finite target, all rows valid, a positive term limit, and budget at least the exact term's complexity.",
    status := .refuted, prop := ``unit_fit_within_budget, thm := some ``unit_fit_within_budget_refuted }
]

end SymReg.Backsolve
