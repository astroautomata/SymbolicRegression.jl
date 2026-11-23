import SymReg.HofMig.MigrationProofs
import DynExpr.Registry.Types

namespace SymReg.Search
open DynExpr
open SymReg.HofMig
open DynExpr.Expressions.Sampling (RNG)

-- Source: src/SymbolicRegression.jl:1191-1207
-- if options.migration
--     migrate!(
--         state.best_sub_pops[j] => cur_pop,
--         options;
--         frac=options.fraction_replaced,
--     )
-- end
-- if options.hof_migration && length(dominating) > 0
--     migrate!(dominating => cur_pop, options; frac=options.fraction_replaced_hof)
-- end
-- if !isempty(state.seed_members[j])
--     migrate!(
--         state.seed_members[j] => cur_pop,
--         options;
--         frac=options.fraction_replaced_guesses,
--     )
-- end
/-- The population passed to the next worker, with RNG and identity supplies threaded
through the individual calls to the installed migration model. -/
def migrateSearchPopulation (rt : MigrationRuntime) (crossPop hofMigration : Bool)
    (fraction fractionHof fractionGuesses : JF) (bestPops : List (List Member))
    (frontier guesses population : List Member) (fuel fresh birth : Nat) (rng : RNG) :
    Jl (List Member × Nat × Nat × RNG) := do
  let (p, f, b, r) ← if crossPop then
    migrate rt (.populations bestPops) population fraction fuel fresh birth rng
    else pure (population, fresh, birth, rng)
  let (p, f, b, r) ← if hofMigration && !frontier.isEmpty then
    migrate rt (.members frontier) p fractionHof fuel f b r else pure (p, f, b, r)
  if !guesses.isEmpty then migrate rt (.members guesses) p fractionGuesses fuel f b r
  else pure (p, f, b, r)

/-- Disabled or zero-fraction sources do not modify the population and do not use
RNG draws, even if there are migrants available from all three sources. -/
def no_migration_draws : Prop :=
  ∀ (rt : MigrationRuntime) (crossPop hofMigration : Bool) (fraction fractionHof fractionGuesses : JF)
    (bestPops : List (List Member)) (frontier guesses population : List Member)
    (fuel fresh birth : Nat) (rng : RNG),
    (crossPop = false ∨ fraction = .fin 0) →
    (hofMigration = false ∨ frontier = [] ∨ fractionHof = .fin 0) →
    (guesses = [] ∨ fractionGuesses = .fin 0) →
    migrateSearchPopulation rt crossPop hofMigration fraction fractionHof fractionGuesses bestPops
      frontier guesses population fuel fresh birth rng = .ok (population, fresh, birth, rng)

theorem no_migration_draws_holds : no_migration_draws := by
  intro rt crossPop hofMigration fraction fractionHof fractionGuesses bestPops frontier guesses
    population fuel fresh birth rng hc hh hg
  have zero (c : Candidates) (p : List Member) (f b : Nat) (r : RNG) :
      migrate rt c p (.fin 0) fuel f b r = .ok (p, f, b, r) :=
    migration_zero_fraction_holds rt c p fuel f b r
  rcases hc with hc | hc <;> rcases hh with hh | hh | hh <;> rcases hg with hg | hg <;>
    simp [migrateSearchPopulation, hc, hh, hg, zero,
      bind, Except.bind, pure, Except.pure]

example : (true = false ∨ JF.fin 0 = .fin 0) ∧ ([] : List Member) = [] := by simp

/-- A positive HOF fraction uses the Poisson result for that fraction, then
caps the number of replacements by the frontier and destination sizes. -/
def hof_migration_replacements : Prop :=
  ∀ (rt : MigrationRuntime) (frac : JF) (bestPops : List (List Member))
    (frontier population : List Member) (fuel fresh birth : Nat) (rng rng' : RNG)
    (sampled : Int),
    frontier ≠ [] → 0 ≤ sampled →
    poissonSample rt (.fin (population.length : Rat) * frac) fuel rng = .ok (sampled, rng') →
    ∃ out f b r, migrateSearchPopulation rt false true (.fin 0) frac (.fin 0) bestPops
        frontier [] population fuel fresh birth rng = .ok (out, f, b, r) ∧
      out.length = population.length ∧ b = birth + min (min sampled.toNat frontier.length) population.length

theorem hof_migration_replacements_holds : hof_migration_replacements := by
  intro rt frac bestPops frontier population fuel fresh birth rng rng' sampled hn hs hp
  obtain ⟨out, f, b, r, hm, hl, hb⟩ :=
    migration_candidate_cap_holds rt (.members frontier) population sampled fresh birth rng' hs
      (Or.inr hn)
  refine ⟨out, f, b, r, ?_, hl, hb⟩
  have h := migration_poisson_dispatch_holds rt (.members frontier) population frac fuel fresh birth rng rng' sampled hp
  simp [migrateSearchPopulation, hn, h, hm, bind, Except.bind, pure, Except.pure]

example : ([specimen (.fin 0) (.fin 1)] : List Member) ≠ [] := by decide

/-- Cross-population migration uses the flattened member bank, so availability
counts members, including repeats, rather than the number of populations. -/
def population_migration_replacements : Prop :=
  ∀ (rt : MigrationRuntime) (frac : JF) (bestPops : List (List Member))
    (frontier population : List Member) (fuel fresh birth : Nat) (rng rng' : RNG)
    (sampled : Int),
    0 ≤ sampled →
    (sampled = 0 ∨ bestPops.flatten ≠ []) →
    poissonSample rt (.fin (population.length : Rat) * frac) fuel rng = .ok (sampled, rng') →
    ∃ out f b r, migrateSearchPopulation rt true false frac (.fin 0) (.fin 0) bestPops
        frontier [] population fuel fresh birth rng = .ok (out, f, b, r) ∧
      out.length = population.length ∧
      b = birth + min (min sampled.toNat bestPops.flatten.length) population.length

theorem population_migration_replacements_holds : population_migration_replacements := by
  intro rt frac bestPops frontier population fuel fresh birth rng rng' sampled hs hpool hp
  obtain ⟨out, f, b, r, hm, hl, hb⟩ :=
    migration_candidate_cap_holds rt (.populations bestPops) population sampled fresh birth rng' hs
      hpool
  refine ⟨out, f, b, r, ?_, hl, hb⟩
  have h := migration_poisson_dispatch_holds rt (.populations bestPops) population frac fuel fresh birth rng rng' sampled hp
  simp [migrateSearchPopulation, h, hm, bind, Except.bind, pure, Except.pure]

example : let rt : MigrationRuntime := ⟨fun _ => .ok (.fin (1/4)), fun i => i⟩
    let rng : RNG := ⟨fun _ => 1/2, 0, fun n _ => ⟨0, Nat.zero_lt_succ n⟩⟩
    poissonSample rt (.fin 1) 4 rng = .ok (1, {rng with cursor := 2}) := by
  with_unfolding_all rfl

open DynExpr.Registry in
def migrationEntries : List Entry := [
  { id := "search-migration-disabled", juliaFile := "src/SymbolicRegression.jl",
    juliaFns := ["_main_search_loop!"],
    statement := "When all population, hall-of-fame and guess migration sources are disabled, empty where checked, or assigned a zero replacement fraction, the population and random stream stay unchanged.",
    preconditions := "Each source meets its disabling condition.", status := .todo,
    prop := ``no_migration_draws
    notes := "Needs observable gate decisions, disjoint migration calls in source order, and positive replacement witnesses." },
  { id := "search-hof-migration-count", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"],
    statement := "With only hall-of-fame migration, each Poisson count at the configured HOF fraction is capped by both frontier size and population size; sampling with replacement may revisit slots.",
    preconditions := "Nonempty frontier and a nonnegative completed Poisson draw.", status := .todo,
    prop := ``hof_migration_replacements
    notes := "Needs the actual draw-block order and last-write behavior for repeated sampled positions." },
  { id := "search-population-migration-count", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"],
    statement := "With only cross-population migration, each Poisson count at its configured fraction is capped by both the total number of source members and the destination population size.",
    preconditions := "Nonnegative completed Poisson draw.", status := .proven,
    prop := ``population_migration_replacements, thm := some ``population_migration_replacements_holds }
]

end SymReg.Search
