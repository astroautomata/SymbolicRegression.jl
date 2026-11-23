import SymReg.Search.StateProofs

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

/-- Reports are added in generation order for each population;
`src/SymbolicRegression.jl:1155`. JF preserves the source's nonfinite arithmetic. -/
def ReportAccounting (work : Nat → Nat → Reply) (p : Nat) (c : Cell) : Prop :=
  c.evaluations = ((List.range c.collected).map (fun g => (work p g).evaluations)).foldl
    JF.add (.fin 0) ∧ (c.running = true → c.pending = work p c.collected)

 theorem collect_accounting (s : OutputState) (p i : Nat) (r e : Bool)
    (work : Nat → Nat → Reply) (h : ReportAccounting work i (s.cells i)) :
    ReportAccounting work i ((collect s p r e work).cells i) := by
  unfold collect
  dsimp only
  split
  · by_cases hi : i = p
    · subst i
      have ha : (s.cells p).running = true := by simp_all
      have hp := h.2 ha
      simp only
      constructor
      · simp [List.range_succ, List.map_append, List.foldl_append, h.1, hp]
        rfl
      · intro hr
        change (decide (s.remaining > 1) && !e) = true at hr
        change (if decide (s.remaining > 1) && !e then
          work p ((s.cells p).collected + 1) else (s.cells p).pending) = _
        simp [hr]
    · simpa [hi] using h
  · exact h

 theorem visits_accounting (s : OutputState) (visits : List (Nat × Bool × Bool))
    (work : Nat → Nat → Reply) (i : Nat) (h : ReportAccounting work i (s.cells i)) :
    ReportAccounting work i ((runVisits s visits work).cells i) := by
  induction visits generalizing s with
  | nil => exact h
  | cons v vs ih => exact ih _ (collect_accounting _ _ _ _ _ _ h)

 def worker_reports_summed : Prop := ∀ (n p i : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool × Bool)),
  let cell := (runVisits (startOutput n p initial work) visits work).cells i
  cell.evaluations = ((List.range cell.collected).map (fun g => (work i g).evaluations)).foldl
    JF.add (.fin 0)
 theorem worker_reports_summed_holds : worker_reports_summed := by
  intro n p i initial work visits
  exact (visits_accounting _ visits work i (by simp [ReportAccounting, startOutput])).1

/-- While a positive budget remains every collected result is replaced by a launch;
only the very last collection avoids relaunch, `src/SymbolicRegression.jl:1210-1212`. -/
def LaunchBalance (populations : Nat) (s : OutputState) : Prop :=
  if s.remaining > 0 then s.launches = populations + s.receipts.length
  else s.launches + 1 = populations + s.receipts.length

 theorem collect_launch_balance (s : OutputState) (p : Nat) (r : Bool)
    (work : Nat → Nat → Reply) (populations : Nat) (h : LaunchBalance populations s) :
    LaunchBalance populations (collect s p r false work) := by
  unfold collect
  dsimp only
  split
  · have hz : s.remaining > 0 := by simp_all
    have hb : s.launches = populations + s.receipts.length := by
      simpa [LaunchBalance, hz] using h
    by_cases hr : s.remaining > 1 <;>
      simp [LaunchBalance, hr, show (s.remaining - 1 > 0) ↔ s.remaining > 1 by omega] <;> omega
  · exact h

 theorem visits_launch_balance (s : OutputState) (visits : List (Nat × Bool))
    (work : Nat → Nat → Reply) (populations : Nat) (h : LaunchBalance populations s) :
    LaunchBalance populations
      (runVisits s (visits.map (fun (p, ready) => (p, ready, false))) work) := by
  induction visits generalizing s with
  | nil => exact h
  | cons v vs ih => exact ih _ (collect_launch_balance _ _ _ _ _ h)

 def launch_surplus : Prop := ∀ (n p : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool)), n * p > 0 →
  let result := runVisits (startOutput n p initial work)
    (visits.map (fun (i, ready) => (i, ready, false))) work
  result.remaining = 0 → result.launches + 1 = n * p + p
 theorem launch_surplus_holds : launch_surplus := by
  intro n p initial work visits hn
  dsimp only
  intro hz
  have hb := visits_launch_balance (startOutput n p initial work) visits work p
    (by simp [LaunchBalance, startOutput, hn])
  have hc := cycle_budget_holds n p initial work
    (visits.map (fun (i, ready) => (i, ready, false))) hz
  simpa [LaunchBalance, hz, hc, Nat.add_comm] using hb
example : (1 : Nat) * 2 > 0 := by decide

end SymReg.Search
