import SymReg.Population.Tournament
import SymReg.Population.Pop
import SymReg.Population.RegEvol
import DynExpr.Registry.Types

/-!
Population slice: `src/Population.jl` (constructors, `copy`, tournament selection,
`finalize_costs`, `best_sub_pop`) and `src/RegularizedEvolution.jl` (`reg_evol_cycle` and the
mutation-step middleware), SymbolicRegression.jl `upstream/master` daae84e5.
-/

namespace SymReg.Population
open DynExpr.Registry

def entries : List Entry := [
  { id := "pop-ctor-size", juliaFile := "src/Population.jl", juliaFns := ["Population", "_init_tree"]
    statement := "Population(dataset; population_size=s) (or npop=s) returns n = s and exactly s distinct new members with parent = -1; member j has the tree of the j-th _init_tree call: the plugin-provided initial tree if any, else gen_random_tree(nlength, options, nfeatures, T)."
    preconditions := "At most one plugin's init_member returns a tree per call; exactly one of population_size and npop given; trees, plugin results and the random generator arbitrary."
    status := .proven, prop := ``ctor_size, thm := some ``ctor_size_holds },
  { id := "pop-ctor-keywords", juliaFile := "src/Population.jl", juliaFns := ["Population"]
    statement := "Both Population(dataset; ...) and Population(X, y; ...) throw an AssertionError unless exactly one of population_size and npop is given."
    preconditions := "None."
    status := .proven, prop := ``ctor_keywords, thm := some ``ctor_keywords_holds },
  { id := "pop-init-tree", juliaFile := "src/Population.jl", juliaFns := ["_init_tree", "resolve_init_member"]
    statement := "_init_tree rejects mismatched tuples before calling a provider. For matching tuples it calls each provider in tuple order, preserving effects through the first exception. After successful collection it rejects multiple providers of trees, returns a sole provided tree unchanged, or calls the generator if no provider supplied a tree."
    preconditions := "Provider and random generator effects and results are arbitrary.",
    status := .proven, prop := ``member_resolution, thm := some ``member_resolution_holds },
  { id := "pop-ctor-matrix-nlength", juliaFile := "src/Population.jl", juliaFns := ["Population"]
    statement := "Population(X, y; population_size, nlength=l, options, nfeatures, plugin_states) builds every member from gen_random_tree(l, ...), the nlength it was given."
    preconditions := "No plugin provides initial trees."
    status := .refuted, prop := ``ctor_matrix_nlength, thm := some ``ctor_matrix_nlength_refuted
    notes := "Bug: the matrix constructor (src/Population.jl:144) calls Population(dataset; population_size, options, nfeatures, plugin_states) without forwarding nlength, so the dataset constructor's default nlength=3 is always used. With binary_operators=[+, *], Population(X, y; population_size=8, nlength=10, options, nfeatures=2, plugin_states) gives members with 7 nodes (3 operators) instead of 21 (10 operators)." },
  { id := "pop-without-plugins", juliaFile := "src/Population.jl", juliaFns := ["_population_without_plugins"]
    statement := "_population_without_plugins returns a one-member population (n = 1 = length(members)) whose member has parent = -1 and the gen_random_tree(nlength, ...) tree; no plugin is consulted."
    preconditions := "None; the random generator is arbitrary."
    status := .proven, prop := ``without_plugins, thm := some ``without_plugins_holds },
  { id := "pop-copy", juliaFile := "src/Population.jl", juliaFns := ["copy", "Population", "popmember_type"]
    statement := "copy(pop) returns a population of the same member type with the same n (Population(members) sets n = length), whose members are distinct newly allocated objects, none a member of the original, member i carrying the fields of original member i; the original objects are unchanged."
    preconditions := "n = length(members); the original identities were allocated before the copy."
    status := .proven, prop := ``copy_spec, thm := some ``copy_spec_holds },
  { id := "pop-sample-indices-valid", juliaFile := "src/Population.jl", juliaFns := ["_sample_indices!"]
    statement := "Whenever _sample_indices!(idxs, N, n) returns, it returns n distinct indices, all in 1:N."
    preconditions := "rand(1:N) draws lie in 1:N; any draw stream."
    status := .proven, prop := ``sample_indices_valid, thm := some ``sample_indices_valid_holds },
  { id := "pop-sample-indices-terminates", juliaFile := "src/Population.jl", juliaFns := ["_sample_indices!"]
    statement := "For n <= N, sampling on a fair in-range stream fills n distinct slots, accounts for every draw in the consumed prefix, and stops at its last accepted value. A zero-size sample consumes no draws.",
    preconditions := "n <= N (Options asserts tournament_selection_n < population_size); draws in 1:N; every value of 1:N recurs in the stream."
    status := .proven, prop := ``sample_indices_terminates, thm := some ``sample_indices_terminates_holds },
  { id := "pop-weights-geometric", juliaFile := "src/Population.jl", juliaFns := ["get_tournament_selection_weights"]
    statement := "get_tournament_selection_weights returns n weights p, p(1-p), p(1-p)^2, ..., p(1-p)^(n-1) (n = tournament_selection_n, p = tournament_selection_p) with total 1 - (1-p)^n, so place k is drawn with probability p(1-p)^(k-1) / (1 - (1-p)^n)."
    preconditions := "Exact arithmetic (no Float64 rounding); the per-task cache is keyed on (n, p)."
    status := .proven, prop := ``weights_geometric, thm := some ``weights_geometric_holds },
  { id := "pop-weights-valid", juliaFile := "src/Population.jl", juliaFns := ["get_tournament_selection_weights"]
    statement := "For 0 < p <= 1 and n >= 1 the tournament weights are nonnegative, the first equals p > 0, the total is in (0, 1], and for p < 1 the weights are strictly decreasing."
    preconditions := "0 < tournament_selection_p <= 1, tournament_selection_n >= 1; exact arithmetic."
    status := .proven, prop := ``weights_valid, thm := some ``weights_valid_holds },
  { id := "pop-place-range", juliaFile := "src/Population.jl", juliaFns := ["get_tournament_selection_weights", "_best_of_sample"]
    statement := "The tournament place StatsBase.sample(get_tournament_selection_weights(options)) is in 1:tournament_selection_n for every rand() draw in [0, 1)."
    preconditions := "0 < p <= 1, n >= 1; exact arithmetic; StatsBase.sample(rng, wv) as in StatsBase src/sampling.jl:586-605."
    status := .proven, prop := ``place_range, thm := some ``place_range_holds },
  { id := "pop-tournament-member", juliaFile := "src/Population.jl", juliaFns := ["best_of_sample", "_best_of_sample", "_sample_indices!"]
    statement := "A successful tournament returns a member at one of the original sampled indices, including when the tournament multiplier hook itself runs another tournament."
    preconditions := "The index sample was already obtained. The extension method may run a tournament on the same task."
    status := .refuted, prop := ``tournament_member_live, thm := some ``tournament_member_live_refuted,
    notes := "The nested tournament overwrites the task's scratch indices. The outer tournament returns a live population member outside its original sample. Membership holds when hooks leave the sample and member vector unchanged." },
  { id := "pop-tournament-nan", juliaFile := "src/Population.jl", juliaFns := ["_best_of_sample", "best_of_sample"]
    statement := "With tournament_selection_p == 1 (first place), a sampled member whose adjusted cost is NaN never wins when some sampled member has a non-NaN adjusted cost (the code comment at src/Population.jl:202: 'a NaN cost never does')."
    preconditions := "Distinct sampled indices in range; at least one non-NaN adjusted cost in the sample."
    status := .refuted, prop := ``tournament_nan, thm := some ``tournament_nan_refuted
    notes := "Bug: the first-place loop (src/Population.jl:203-209) starts from best_cost = adjusted_cost(1) and replaces it only when cost < best_cost; if the first sampled member's cost is NaN, every comparison with NaN is false and the NaN member wins. _best_of_sample([m_nan, m_1], [1, 2], Options(; tournament_selection_p=1.0, ...); plugin_states) returns the member with cost NaN, not the member with cost 1.0." },
  { id := "pop-tournament-first-min", juliaFile := "src/Population.jl", juliaFns := ["_best_of_sample", "best_of_sample"]
    statement := "When first place is taken (p == 1.0 or the drawn place is 1) and no sampled adjusted cost L(member.cost) * prod(multipliers) is NaN, the winner has the minimal adjusted cost of the sample and is the first sampled position with that cost."
    preconditions := "Nonempty sample with indices in range; no NaN adjusted cost (NaN is covered by pop-tournament-nan); infinities allowed."
    status := .proven, prop := ``tournament_first_min, thm := some ``tournament_first_min_holds },
  { id := "pop-tournament-rank", juliaFile := "src/Population.jl", juliaFns := ["_best_of_sample", "bottomk_fast"]
    statement := "When place k >= 2 is drawn, the winner holds the k-th place of the sample in the isless order of adjusted costs (ties in any order), as documented for tournament_selection_p ('the next fittest with probability p*(1-p), and so forth')."
    preconditions := "Distinct sampled indices in range; 2 <= k <= tournament_selection_n."
    status := .refuted, prop := ``tournament_rank, thm := some ``tournament_rank_refuted
    notes := "Bug: bottomk_fast (src/Utils.jl:97-131), used at src/Population.jl:211, initialises its buffer with (typemax(T), index 1) and inserts x[i] only when x[i] < minval[end]; costs equal to Inf (the cost of every invalid expression) or NaN never enter, so when fewer than k sampled costs are finite the k-th slot still holds the placeholder index 1. bottomk_fast([5.0, Inf], 2) returns indices [1, 1]: place 2 of the sample [5.0, Inf] goes to the cost-5.0 member (first place) instead of the Inf member; when place 2 is drawn the true second-best is never chosen." },
  { id := "pop-finalize-costs", juliaFile := "src/Population.jl", juliaFns := ["finalize_costs"]
    statement := "With batching, finalize_costs sets every member's loss to its full-data loss and cost to loss_to_cost(loss, ...), leaves every other object unchanged and returns num_evals = pop.n; without batching nothing changes and num_evals = 0."
    preconditions := "Loss evaluation and loss_to_cost arbitrary functions of the member's tree."
    status := .proven, prop := ``finalize_costs_spec, thm := some ``finalize_costs_spec_holds },
  { id := "pop-best-sub-pop", juliaFile := "src/Population.jl", juliaFns := ["best_sub_pop", "_get_cost", "Population"]
    statement := "best_sub_pop(pop; topn) returns max(0, min(topn, pop.n)) of the population's own members ranked by member.cost (_get_cost): no returned member's cost is isless-greater than a member left out (NaN costs last), and they are the members at the first positions of sortperm."
    preconditions := "sortperm meets its contract (a permutation of 1:n sorted by isless); costs arbitrary Float64 values including NaN."
    status := .proven, prop := ``best_sub_pop_spec, thm := some ``best_sub_pop_spec_holds },
  { id := "regevol-build-step", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["build_mutation_step", "_add_mutation_step_layer", "MutationStepLayer"]
    statement := "build_mutation_step(wrappers, base_step) nests the non-nothing wrappers, the first outermost: calling it on parent runs w1(parent, p -> w2(p, ... base_step)); nothing wrappers are skipped, and with none it is base_step."
    preconditions := "Wrappers and base step arbitrary functions."
    status := .proven, prop := ``build_step_spec, thm := some ``build_step_spec_holds },
  { id := "regevol-step-attempts", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["MutationStep", "reset!"]
    statement := "reset!(step) empties attempted_results and attempted_members; afterwards the k next_step calls of a pass are recorded in order with attempt_id 1..k, each with a distinct newly allocated copy of its member, and the population is untouched."
    preconditions := "Mutation middleware present (buffers allocated); next_generation outcomes arbitrary."
    status := .todo, prop := ``step_attempts
    notes := "Needs actual recorded callback return payloads and snapshots, with partial buffers when copy or tracing throws." },
  { id := "regevol-size", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "reg_evol_cycle keeps the population size constant."
    preconditions := "None; all random draws, tournament winners, mutation, middleware and crossover outcomes arbitrary."
    status := .todo, prop := ``cycle_size
    notes := "Needs population and backing-vector identity plus the scheduled passes and observable replacement writes." },
  { id := "regevol-no-alias", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle", "MutationStep"]
    statement := "Starting from a population of distinct objects, reg_evol_cycle never leaves the same object in two population slots, for every mutation and crossover outcome (best_of_sample's docstring: callers inserting the winner back must copy it)."
    preconditions := "1 <= tournament_selection_n < pop.n; distinct allocated members; tournament winners are population members; every next_generation call returns a newly allocated member (mutgen-ng-no-alias, whose handler precondition this inherits)."
    status := .todo, prop := ``no_alias
    notes := "Proved against an unfaithful model; needs re-proof through stock child constructors. Custom immediate mutations can return an existing member, which the current cycle input cannot express." },
  { id := "regevol-no-alias-fresh", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "reg_evol_cycle keeps the population made of distinct objects, all allocated before or during the cycle; with middleware the inserted baby is always a fresh copy."
    preconditions := "Distinct allocated members; next_generation returns create_child results (mutgen-ng-no-alias); middleware outcomes arbitrary."
    status := .todo, prop := ``no_alias_fresh
    notes := "Proved against an unfaithful model; needs re-proof linking the selected attempt's actual snapshot and stock crossover children to the replacement writes." },
  { id := "regevol-replace-oldest", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "A mutation pass either leaves the population unchanged or replaces exactly one slot, the first slot holding a member of minimal birth (births read after the mutation)."
    preconditions := "None; ties in birth allowed."
    status := .todo, prop := ``replace_oldest
    notes := "Needs selected child identity and direct write observation even when that identity already occupies the slot." },
  { id := "regevol-crossover-two-oldest", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "A crossover pass that inserts children (accepted, or rejected with skip_mutation_failures = false) replaces two different slots, the first slot of minimal birth and the first slot of minimal birth among the others, with two distinct newly allocated objects."
    preconditions := "pop.n >= 2 (Options asserts tournament_selection_n < population_size); distinct allocated members; births below typemax(Int); ties allowed."
    status := .todo, prop := ``crossover_two_oldest
    notes := "Needs live births after crossover and hall work, plus exact child identities and ordering of both writes." },
  { id := "regevol-skip-failures", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "With skip_mutation_failures = true, a pass whose mutation is rejected (no middleware) or whose crossover is rejected leaves the population unchanged."
    preconditions := "None."
    status := .todo, prop := ``skip_failures
    notes := "Needs preserved tournament, cache, accounting and trace effects independent of slot writes." },
  { id := "regevol-pass-evals", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle", "MutationStep"]
    statement := "Each pass adds to num_evals exactly the evaluations of its work: the crossover's, the single next_generation call's without middleware, and with middleware the sum over every next_step call made, including discarded ones."
    preconditions := "None; evaluation counts arbitrary."
    status := .todo, prop := ``pass_evals
    notes := "Needs actual wrapper invocations and Julia's Float64 sum and update order." },
  { id := "regevol-middleware-check", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "In a wrapped mutation pass, the selection check throws ArgumentError exactly when the signed attempt_id is outside the one-based range of completed attempts in that pass."
    preconditions := "Mutation middleware present."
    status := .todo, prop := ``middleware_check
    notes := "Signed validation is modeled. The range counts recorded results, even if a subsequent copy or trace failed and the wrapper caught the failure; selection and snapshot error paths need that partial state." },
  { id := "regevol-crossover-prob", juliaFile := "src/RegularizedEvolution.jl", juliaFns := ["reg_evol_cycle"]
    statement := "A pass is a crossover exactly when the rand() draw u in [0, 1) is below crossover_probability, so crossover happens with probability crossover_probability and never when it is 0."
    preconditions := "u in [0, 1), as rand() returns."
    status := .refuted, prop := ``crossover_prob, thm := some ``crossover_prob_refuted
    notes := "Bug (probability 2^-53 per pass): the test is rand() > options.crossover_probability (src/RegularizedEvolution.jl:130), so a draw equal to crossover_probability selects crossover. rand() can return exactly 0.0, so crossover_probability = 0.0 does not disable crossover: with the default RNG in a state whose next Float64 is 0.0 (Xoshiro(0, s1, s2, 0)), reg_evol_cycle with crossover_probability=0.0 runs a crossover. rand() < crossover_probability would give exactly the documented probability." }
]

end SymReg.Population
