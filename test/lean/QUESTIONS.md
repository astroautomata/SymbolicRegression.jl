# Open questions about intended behaviour

Format as in the DynamicExpressions formalization: the Julia `file:line` (SymbolicRegression.jl
`upstream/master` 103f5d42), the two readings, and the reading modelled.

## Q1. Custom complexity functions in `check_constraints`

`src/Complexity.jl:29-41`, `src/CheckConstraints.jl:66-81`. `check_constraints(ex, options, maxsize)`
immediately takes `get_tree(ex)`, and the node-level `compute_complexity` only honours a
`ComplexityMapping`; when `options.complexity_mapping` is a user function it falls back to
`count_nodes`. So without `cached_size`, the `maxsize` check uses the node count instead of the
user's complexity, and the per-operator limits always use node counts.

- Reading A: intended, since a user function takes whole expressions and cannot be applied to
  subtrees; callers pass `cached_size` for the top-level check.
- Reading B: a bug for the top-level size check.

Modelled: `constraints-accept` assumes a `ComplexityMapping` (precondition), so it is silent on this.
`cons-custom-size` models the code as written and refutes Reading B's safety expectation:
`complexity_mapping=(_ -> 10)`, `Expression(x1)` and maxsize 3 are accepted.

## Q2. `max_nesting = -1` in `nested_constraints`

`src/Options.jl:135` accepts `max_nesting >= -1`, and `flag_illegal_nests`
(`src/CheckConstraints.jl:57-59`) flags `count_max_nestedness(...) > max_nesting`. A limit of `-1`
therefore forbids the outer operator outright (every count is `>= 0 > -1`), whereas `-1` means
"unconstrained" in `op_constraints`.

- Reading A: `-1` deliberately bans the outer operator.
- Reading B: `-1` was meant to mean "unlimited", as elsewhere.

Modelled as written: `Accepts` requires the nesting count to be `<= max_nesting`, which agrees with
the code for every value including `-1`.

## Q3. Explicit indices with the default elementwise objective

`src/LossFunctions.jl:167-188`: `idx` is accepted by `eval_loss`, passed to custom
objectives, and omitted from `_eval_loss`.

- Reading A: the keyword is exclusively a compatibility interface for custom
  objectives; default losses require a `SubDataset` constructed with `batch`.
- Reading B: an explicitly supplied sample index list should select the same
  columns, targets and weights for every objective.

Modelled as written. `loss-explicit-index` refutes Reading B. A SubDataset does
select all three arrays correctly. The API accepts the explicit keyword without
warning even when the default objective ignores it.

## Q4. Baseline constant versus the documented average

`src/LossFunctions.jl:260-263`, `src/Dataset.jl:33-38`:
`update_baseline_loss!` constructs the constant `init_value(T)`, which is zero
for numeric types, while `baseline_loss` is documented as the loss of predicting
`avg_y`.

- Reading A: the baseline should be the documented constant average predictor.
- Reading B: a zero predictor is deliberately used as a generic expression
  prototype, including for ordinary numeric Expression datasets.

Modelled as written: evaluate the expression builder at zero. The property
`loss-baseline-average` compares the implementation with Reading A and is refuted.

## Q5. Weighted custom elementwise functions

`src/LossFunctions.jl:68-72`: SupervisedLoss values are multiplied by weights;
a custom function receives the weight as its third argument, and only its result
is summed.

- Reading A: custom functions must incorporate the weight themselves.
- Reading B: the framework should multiply every custom loss result by its weight.

Modelled as Reading A, matching the source and `test/unit/misc/test_losses.jl:10-32`.
Equal-weight agreement is stated for SupervisedLoss or a compatible custom function,
not arbitrary three-argument functions.

## Q6. Numeric dataset average is always absent

`src/Dataset.jl:183-191` uses `eltype(y) isa Number`, where `eltype(y)` is a type
object. For ordinary Float64 vectors the expression is false, so `avg_y` is
`nothing`, including when sample weights are supplied.

- Reading A: a numeric element type should be recognized with `eltype(y) <: Number`,
  and the documented weighted or unweighted target average should be recorded.
- Reading B: numeric target averages are deliberately unavailable.

Modelled as written for numeric datasets. `loss-dataset-average` refutes Reading A's
documented postcondition. The separate baseline-average counterexample computes the
mathematical target average directly, so it does not depend on the missing field.

## Q7. Migration count versus candidate-pool size

`src/Migration.jl:34-39` clamps the Poisson replacement count to the number of candidates, then calls `rand` twice. Both calls sample with replacement.

- Reading A: the candidate count deliberately limits assignments, even though a candidate may be drawn repeatedly.
- Reading B: the candidate-count clamp was inherited from sampling without replacement; with replacement, a single candidate should support the full sampled assignment count, capped only by destination size.

Modelled as written: both clamps apply before the two independent draw vectors. `mig-candidate-cap` refutes reading B's assignment-count guarantee. Repeated destination draws can further reduce the number of distinct changed positions, independently of the candidate clamp. The Julia reproducer counts deterministic birth resets, so it measures assignments rather than distinct positions.

## Q8. NaN ordering in hall updates and the front

`src/HallOfFame.jl:130,172,181`. An empty slot accepts a member with NaN cost, after which `< NaN` prevents replacement. The front skips NaN-loss members (line 172, PR #790) and otherwise rejects a member only when `loss >= simpler.loss`.

- Reading A: nonfinite cost and loss values are excluded before these public methods are called.
- Reading B: these methods must maintain best-member and Pareto guarantees for every well-typed member they accept, including user losses that return NaN.

Modelled as written without a finiteness restriction. `hof-nan-recovery` refutes Reading B for hall updates, with the actual default PopMember implementation; `hof-frontier-strict-all` proves Reading B for the front.

## Q9. Equal zero losses in logarithmic scores

`src/HallOfFame.jl:330-332`. Epsilon is added after `cur_loss / last_loss`. Julia's Bool multiplication gives `relu(NaN) == 0`, so equal zero losses produce `relu(-log(eps(0))/delta)`.

- Reading A: the helper is only called on a strict finite front, where two adjacent zero losses cannot occur.
- Reading B: the helper's nonnegative-loss input domain includes equal zero losses and should give zero improvement.

Modelled as written; `hof-score-zero-ratio` refutes the zero-improvement guarantee. Float64 inputs `(0.0, 0.0, 1)` produce `744.4400719213812`. The Lean refutation supplies the actual Float64 `eps(0)=2^-1074` and measured `log(eps(0))=-6548164122079683/8796093022208`. The first formatted score remains exactly zero, regardless of its loss. The strong-zero Bool rule is distinct from multiplying numeric floating zero by NaN; the latter gives NaN.

## Q10. Long equation prefixes and wrapping

`src/HallOfFame.jl:240,257-281`, `src/Utils.jl:55-59`. The equation width subtracts the prefix length even though the wrapped string already contains the prefix. A nonpositive equation width reaches `split_string` unchanged.

- Reading A: callers guarantee that statistics plus prefix leave at least one character of equation width.
- Reading B: the public rendering helper must handle arbitrary variable names and widths without dropping the equation.

Modelled as written. Negative widths can produce no chunks, silently returning an empty wrapped equation; zero width throws on nonempty strings. `hof-wrap-retains-equation` exhibits the silent-loss case.

## Hall-of-fame and migration model boundaries

Members carry abstract expression content plus separate member/expression allocation identities. Expression-copy internals are reused conceptually from the DE model rather than duplicated. The model specializes to default PopMember copying; arbitrary user-defined AbstractPopMember methods can have additional effects. Constraint checking, uncached expression complexity, scalar finite log/eps/exp, formatted unit strings and Printf/expression rendering are explicit supplied services. The supplied constraint service can be instantiated with the existing `SymReg.Constraints.checkConstraints` mirror. JF follows the shared DE arithmetic model: IEEE nonfinite rules with exact finite arithmetic, without finite rounding, overflow or signed zero. Poisson fuel expresses a finite execution bound and has an explicit exhaustion result. No theorem assumes that a stochastic fraction is deterministically rounded.

## Q11. Stale size caches

`src/CheckConstraints.jl:70-81`, `src/TemplateExpression.jl:1129-1144`.

- Reading A: `cached_size` is a caller-owned exact cache. Inconsistency is outside the intended contract.
- Reading B: The check independently guarantees maxsize even with a stale or otherwise inconsistent cache.

Modelled as written, matching Reading A. `cons-stale-cache` refutes Reading B, rather than alleging that deliberate cache trust is an unintended implementation defect. A variable weighing 2 passes maxsize 1 with cached_size 1. A template's cache replaces only its total-size computation; inner checks remain uncached.

## Q12. Cross-member sharing during population simplification

`src/SingleIteration.jl:94-109`, `src/ComposableExpression.jl:118-125`, `src/TemplateExpression.jl:1047-1067`.

- Reading A: The caller guarantees population trees do not share mutable objects with other members, templates or the hall of fame.
- Reading B: Population simplification preserves other members even if their expressions share an existing node root.

Modelled as written: no copy occurs before population simplification. `simp-shared-member` refutes Reading B with two observers of `(x1+1)+2`: the returned population expression remains equivalent, while the retained old root changes from 6 to 8 at x1=3. The simplify mutation's caller copies into separate storage (`src/Mutate.jl:397`); that copy is outside the population path and is not claimed absent there.

`simp-template-shared` checks the corresponding template path. Sharing the same `(x1+1)+2` root between inners `f` and `g` changes both returned inner values from 6 to 8 at x1=3, so the template `f(x)+g(x)` changes from 12 to 16. The individual inner trees are alias-free; the alias is between inners.

## Simplification and constraints: scope of arithmetic abstraction

DE's `JF` models exact rational finite arithmetic plus NaN and infinities, without finite rounding, overflow or signed zero. The denotation proofs use precisely DE's available scalar/rewrite contracts. Integer evaluation counts in the cycle model represent the source's Float64 counters while counts are exactly representable. User operators, user complexity functions, optimizers, plugins, evolution and hall-of-fame updates remain arbitrary callbacks rather than asserted implementations.

## Q13. Failed-crossover copies keep parent births

`src/RegularizedEvolution.jl:200-205` with `src/Crossover.jl:190`. When a crossover fails and
`skip_mutation_failures = false`, the two parents are copied with `copy(member)`, which keeps
their `birth` (`src/PopMember.jl:170-179`). A failed mutation instead inserts
`create_child(...)`, which gets a new birth (`src/Mutate.jl:475-487`).
- Reading A: deliberate; the copies stand for the unchanged parents, so they keep their age.
- Reading B: oversight; inserted copies should count as newborn, as failed mutations do.
Modelled: as written (copies keep the parents' births). No property depends on the choice.

## Q14. `best_seen` without mutation middleware

`src/RegularizedEvolution.jl:65-86,192-198` with `src/SingleIteration.jl:60`. Accepted mutation
children are offered to `best_seen` inside `reg_evol_cycle` only when mutation middleware is
present; without middleware they reach `best_seen` only through the scan of `pop.members`
after the cycle. With `tournament_selection_n = 1` (`n_evol_cycles = pop.n`) and crossovers
(two replacements per pass), an accepted mutation child can be replaced again before that
scan and never be seen by `best_seen`.
- Reading A: acceptable; `best_seen` is a per-cycle summary of survivors plus crossover children.
- Reading B: `best_seen` should see every accepted child, as it does with middleware.
Modelled: as written; no property registered on this point.

## Q15. Unvalidated `tournament_selection_p`

`src/Population.jl:224-234`, `src/Options.jl:864`. `tournament_selection_p` is not validated.
For `p = 0` every weight is 0 and `StatsBase.sample` returns place 1 (always the fittest); for
`p > 1` some weights are negative.
- Reading A: callers must pass `0 < p <= 1`.
- Reading B: `Options` should reject other values.
Modelled: properties assume `0 < p <= 1`.

## Q16. Empty populations still evaluate a first member

`src/Population.jl:77-98`. `Population(dataset; population_size=0)` still builds and evaluates
`first_member`, then discards it (empty comprehension).
- Reading A: harmless; `population_size >= 1` in practice.
- Reading B: wasted evaluation and RNG draws.
Modelled: as written (`pop-ctor-size` holds for every size, including 0).

## Q17. Checks skipped by the leaf early return of `condition_mutation_weights!`

`src/Mutate.jl:179-191` returns before the checks of lines 193-211 (`nfeatures <= 1`,
`complexity >= curmaxsize`, `should_simplify`, `condition_mutate_constant!`).

- Reading A: the early return only exists because the remaining checks are irrelevant for a leaf.
- Reading B: the remaining checks are meant for every tree; skipping them on leaves is an oversight.

Modelled: the code as written. `mutgen-cond-feature-nfeatures` and `mutgen-cond-add-maxsize`
take Reading B (both checks do apply to leaves: `mutate_feature` is a no-op with one feature,
and a leaf can reach `curmaxsize` with `complexity_of_variables > 1`) and are refuted.

## Q18. `ConstantMutation` weight on a constant leaf

`src/Mutate.jl:179-191` versus `src/Mutate.jl:197,240-243`. A tree with operators and `n`
constants gets its `ConstantMutation` weight multiplied by `min(8, n) / 8` (1/8 for one
constant), but a constant leaf, which has one constant, keeps the full weight because the
leaf branch returns before `condition_mutate_constant!`. Expression types that overload
`condition_mutate_constant!` are also never consulted for leaves.

- Reading A: intended; a constant leaf has nothing else worth mutating.
- Reading B: an oversight of the early return (as Q17).

Modelled: the code as written; no registered property takes either reading.

## Q19. `mutation_choice` passed to `create_child` on some rejection paths only

`src/Mutate.jl:476-484` (constraint/self-reported failure) and `503-512` (NaN cost) pass
`mutation_choice=mutation_choice` to `create_child`; the acceptance-draw rejection
(`536-544`) and the accepted child (`551-553`) do not. The default `create_child`
(`src/PopMember.jl:210-230`) ignores the keyword, so only custom `AbstractPopMember` types can
observe the difference.

- Reading A: deliberate (only "failed" copies are tagged with the attempted mutation).
- Reading B: the acceptance rejection should be tagged like the other rejections.

Modelled: the keyword is not represented (the default `create_child` ignores it); no property.

## Q20. Meaning of the `parent_ref` keyword of `mutate!`

The `mutate!` docstring (`src/Mutate.jl:587`) calls `parent_ref` "Reference to
`parent_member`'s parent", but `next_generation` passes `parent_ref = member.ref`
(`src/Mutate.jl:311`), the parent member's own reference, which children then record as
their `parent`.

- Reading A: the docstring is wrong; `parent_ref` is the parent's own ref.
- Reading B: the code is wrong.

Modelled: the code (children get `parent = member.ref`), as in `mutgen-ng-accept-sound`,
`mutgen-ng-reject-copy` and `mutgen-mut-do-nothing`.

## Q21. Validation in `sample_mutation` versus `_sample_mutation`

`src/MutationWeights.jl:159-164` (StatsBase) accepts negative weights and silently returns the
first mutation when all weights are zero; `_sample_mutation` (`src/Mutate.jl:247-253`) throws
`ArgumentError` in both cases, but accepts infinite weights that StatsBase rejects.

- Reading A: the two samplers are meant to agree on which weight vectors are valid.
- Reading B: `sample_mutation` is a thin legacy wrapper with StatsBase's semantics.

Modelled: each as written. `mutgen-sample-exported-zero-draw` (zero-weight choice at a 0.0
draw) and `mutgen-sample-infinite` (zero-weight choice with infinite or overflowing weights)
are refuted under the docstrings' "pick a mutation kind by weight".

## Q22. `skip_mutation_failures`

The task description mentions `skip_mutation_failures`; it is read only by
`src/RegularizedEvolution.jl:155,201`, not by `src/Mutate.jl`, so this slice does not model it.

## Q23. The `length` argument of `gen_random_tree`

`src/MutationFunctions.jl:406-421`, `src/Population.jl:47-53,63-80`. `gen_random_tree(length, ...)`
calls `append_random_op` `length` times on a one-node placeholder, so the result has exactly
`length` operator nodes and `1 + d_1 + ... + d_length` nodes (`d_j` the chosen arities). Its
callers pass `nlength` (default 3) from `Population`, and the TODO at line 417 says "This can be
larger number of nodes than length". `Options` only asserts `maxsize > 3` (`src/Options.jl:889`),
so with binary operators and `maxsize = 5` every initial member has 7 nodes.

- Reading A: `length` counts appended operators; larger trees are accepted, and oversized initial
  members are handled later by the search.
- Reading B: `length` is a node count (as `length(tree)` is in DynamicExpressions), and the result
  should have at most `length` nodes (or at most `maxsize`).

Modelled as written (Reading A): `mut-gen-random-tree` proves the operator and node counts.
`mut-gen-random-tree-length` refutes Reading B: `gen_random_tree(1, ...)` with binary operators
only has 3 nodes.

## Q24. Launched evolution jobs versus the cycle budget

`src/SymbolicRegression.jl:1021-1060,1133,1210-1260,1356-1378`.

- Reading A: `niterations * populations` limits collected results per output; extra launched jobs are acceptable.
- Reading B: the same product limits executed evolution jobs and every launched result contributes to the returned search state.

Modelled: Reading A, matching the code. Positive completed runs without external stopping launch `niterations * populations + populations - 1` jobs per output. The last `populations - 1` results are never collected. Teardown waits for threaded jobs without ingesting their populations, halls, evaluation counts or plugin reports. `search-extra-cycles` and `search-uncollected-results` refute Reading B. The serial Julia example with one iteration and two populations executes three cycles and collects two results.

## Q25. Initialization evaluations and search limits

`src/SymbolicRegression.jl:905-907,936-938,946,970,998-1005,1033-1039,1155`.

- Reading A: `num_evals` intentionally counts only collected evolution reports; initialization, restored-member rescoring and discarded evolution results are excluded.
- Reading B: evaluation accounting and `max_evals` include all full-dataset evaluations performed by the search.

Modelled: Reading A. New population initialization reports `population_size`, but warmup extracts that report and discards its evaluation field. Restored populations and halls are rescored while the restored population reports zero. `search-initial-evaluations` refutes Reading B with zero iterations: initialization worker reports total 8.0 for two four-member populations, while `num_evals` remains 0.0. Baseline and dummy-prototype evaluations are also outside these counters. The evaluation-sum theorem proves the exact collected-report contract, without claiming that it covers all actual loss calls.

## Q26. Returned state for a population whose result was never collected

`src/SymbolicRegression.jl:834,1107-1134,1152,1356-1365,1392-1393`, `src/SearchUtils.jl:412-428`.

- Reading A: return_state may contain the one-member dummy population when that population never supplied a collected result.
- Reading B: return_state contains a full initialized or evolved population for every requested population, including slower workers.

Modelled: Reading A. The per-output budget can be consumed entirely by faster populations. Waiting at teardown does not replace untouched last_pops slots. `search-return-state-pending` refutes Reading B using two threaded populations of size four: a channel delays the second population until the first supplies both budgeted collections, and the returned population sizes are [4,1]. Returning that state in a later search recreates the size-one population rather than continuing its actual initialized population.

## Q27. Meaning of early stopping and progress

`src/SearchUtils.jl:533-554,714-719,794-801,1015-1029`, `src/SymbolicRegression.jl:1210-1281,1333-1342`.

- Reading A: early_stop_condition must have a satisfying existing member in every output, and timeout/max_evals are checked at the end of a head-loop visit after possible relaunch.
- Reading B: one successful output stops the search, or limits prevent the next dispatch before it starts.

Modelled: Reading A. Numeric early stopping is strict loss < threshold; function-valued stopping receives loss and complexity. Timeout is strict elapsed > limit, while evaluation stopping is inclusive max_evals <= total. Any criterion exits the one shared loop and stops collection for every output. These are cycle-boundary checks rather than strict work caps. Reporting divides elapsed cycles by the population count, so it counts global iterations across outputs. The final population collection does not execute the progress-update branch; the progress bar is subsequently finished by finish!.

## Q28. Saved-state compatibility and changes in options

`src/SearchUtils.jl:821-844`, `src/SymbolicRegression.jl:902-910,927-979`, `src/ExpressionBuilder.jl:105-179`.

- Reading A: callers retain compatible output/population indexing and expression implementations; saved members are stripped and rescored, with wrong member counts regenerated.
- Reading B: passing any returned state validates and adapts every changed option and preserves every member field exactly.

Modelled: Reading A. Saved hall output counts must match eachindex; too few population outputs or population slots fail by indexing, while unused extra population slots are not inspected. A member-count mismatch recreates the population. Hall slot count is retained rather than resized to a new maxsize. Payload preservation during copy is proved with SymReg.HofMig, while metadata embedding/stripping is an expression service. In the default Julia implementation these transformations can allocate new members, reset births and references or complexity caches, and therefore exact identity/genealogy preservation is not asserted. Unchanged expression contents and the current dataset's recomputed costs/losses are the continuation contract.

## Search: modelling boundaries

- Every named function in both assigned source files appears in the Search registry. Data projections reuse SymReg.Loss.Basic; hall copies, constraints and per-complexity reduction reuse SymReg.HofMig. Existing DE scalar, expression and tree models are imported transitively, not duplicated.
- Evolution, optimization, custom losses, migration, metadata transformations, expression parsing/type inference, plugin hooks, logging/tracing, rendering, serialization bytes and OS actions are arbitrary supplied services. The transport model preserves typed payloads; it does not verify Julia's serializer or process runtime. The distributed mode uses the same scheduler with arbitrary readiness and latency.
- Scheduler theorems apply after ordinary warmup has launched each initial evolution job. A prelatched external stop during warmup is represented separately by the external-stop helper model; the post-warmup launch-count theorem does not apply to that execution. Zero-iteration preservation is modelled separately and performs no evolution launch.
- Counts and indices use natural numbers for nonnegative, nonoverflowing Julia Int inputs. Negative niterations, counter overflow and UInt64 worker-copy key wraparound are outside the stated input domain. UInt8 quit and trigger bytes are represented exactly.
- JF models nonfinite scalar behavior and exact finite arithmetic. Float32/Float64 rounding, signed zero and overflow are outside the common scalar model. Timeout samples, finite reporting fractions and worker evaluation reports are inputs. Resource-monitor windows must fit the recorded history; the model returns the source bounds error otherwise.
- Scheduler visit traces represent arbitrary execution prefixes. The budget theorem proves exact collected counts on reaching zero, and uniqueness/accounting invariants hold on every prefix. The lifecycle replay returns a result only after a stop or zero remaining budget; exhausting its observation list earlier produces an explicit model-fuel error. The model does not prove scheduler fairness or eventual completion for arbitrary latency.
- OS locking, actual byte-level CSV/serialization formatting, process liveness, and external callback correctness are not separately verified. Their bookkeeping and call-result flow are represented by the supplied services.

## Q29. Adaptive-parsimony exponential overflow with Float32 losses

`src/plugins/AdaptiveParsimony.jl:174-179`, `src/Population.jl:190-209`.
The multiplier is evaluated in the member's loss type. With default scaling
1040 and Float32 data, maxsize 10 starts with frequency 0.1 and produces
exp(Float32(104)) = Inf. Costs 2 and 1 both become Inf, so a first-place
tournament returns the first member (cost 2); zero cost becomes NaN.

- Reading A: the multiplier must remain finite for ordinary finite losses, so
  exponentiation should be computed/ranked without overflowing the loss type.
- Reading B: the search intentionally collapses sufficiently frequent sizes to
  infinite adjusted cost, including loss of within-size ranking.

Modelled: the source as written. `plug-tournament-finite` refutes Reading A.
The real plugin reproducer prints the format thresholds
0.08531042216545034 (Float32) and 0.6824833777821 (Float64).
`plug-parsimony-scaling-thresholds` proves the exact exponent inequalities;
finite exp is a supplied runtime service, with the counterexample's exp104
value measured in Julia rather than postulated as a new Lean axiom.

## Q30. Window shrinking can stop far above the requested total

`src/plugins/AdaptiveParsimony.jl:83-94`. The small-step break tests the amount
removed in the current step rather than the difference still remaining. The
public state constructor permits window 2 and counts [1.0000001, 3.0], for which
move_window! returns counts [1.0, 2.9999998999999997], total
3.9999998999999997. Every count starts at least one and the target is feasible.

- Reading A: the docstring's sum-to-window requirement is an exact postcondition
  for feasible states supplied through the public constructor.
- Reading B: an early exit is intentional even with a large remaining excess;
  normal search-generated states are the only intended inputs.

Modelled: the source's 1001-iteration cap and small-step exit.
`plug-window-exact-target` refutes Reading A on the public constructor input.
No claim is made that this example arises from integer-count initialization
without a caller constructing or modifying a state.

## Q31. Equal-cost annealing at the final cycle

`src/plugins/SimulatedAnnealing.jl:71,92-93`, `src/Mutate.jl:525`.
At the last cycle temperature is zero. An equal-cost mutation computes
exp(-0/0) = NaN. The engine compares NaN < rand(), obtains false and accepts.
A worsening gives multiplier zero; an improvement gives Inf.

- Reading A: an equal-cost proposal should contribute probability one, including
  at the final cycle, with a finite well-defined multiplier.
- Reading B: the NaN multiplier is acceptable because the comparison accepts the
  equal-cost proposal anyway.

Modelled: IEEE zero division as written. `plug-annealing-zero-tie` refutes
Reading A; `plug-annealing-zero-limits` proves the three actual endpoint cases.
At positive temperature the probability-range property states its supplied
exponential contract explicitly. The engine's strict comparison also allows a
zero multiplier when rand() returns exactly zero; the plugin slice does not
silently substitute a different engine comparison.

## Q32. Finite adaptive mutation weights can overflow after conditioning

`src/plugins/AdaptiveMutationWeights.jl:148-158,173-179`.
With two active mutations and adaptation_strength 1, one improving event makes
the selected exact-arithmetic multiplier 902/901. The real Float64 result is
1.0011098779134295. A finite legal base weight floatmax(Float64) then becomes
Inf during condition_mutation_weights!.

- Reading A: valid parameters and finite nonnegative base weights guarantee
  finite conditioned sampling weights.
- Reading B: callers must independently ensure enough numerical range for the
  learned multiplier, beyond finiteness/nonnegativity of each base weight.

Modelled: the source multiplication, with Float64 overflow observable.
`plug-adaptive-weights-finite` refutes Reading A using a state produced by the
real initialization and event hooks. The positive-target and active-mean
normalization theorems use exact finite arithmetic; they do not claim that
arbitrary Float64 accumulation avoids overflow or underflow.

## Q33. A zero compound probability still consumes a random draw

`src/plugins/MutationBurst.jl:60-64`. After an accepted retry result and with
compound_max_steps > 1, the while condition evaluates rand() even when
compound_probability is zero. No compound mutation runs, but the RNG advances.

- Reading A: disabling compound bursts means no extra mutation attempts; extra
  RNG consumption is allowed.
- Reading B: retry_attempts 1 and compound_probability 0 reproduce the original
  single-mutation loop's complete RNG state, as well as its returned result.

Modelled: Reading A, matching the source evaluation order. Arbitrary draw and
next-step callbacks thread all worker effects. `plug-burst-single-step` claims
complete state equality only when compound_max_steps is also 1.

## Plugins: model arithmetic and mutation-state representation

Probability-vector, LinRange and learned-multiplier equalities use exact finite
rational arithmetic, consistently with the shared JF model. They exclude
floating reduction/interpolation rounding. Positive, nonzero totals are explicit
preconditions of normalization theorems, and concrete examples establish those
preconditions. Julia's mutation-state arrays are zipped into rows with equal
lengths and preserved index order; weights and option mutation tuples share that
order. The raw-frequency, normalized-frequency and adaptive-state arrays have
independent storage, as in the built-in factories. Manually aliased state arrays
and mutable objects shared between separate plugins are outside this state
representation. Custom complexity, mutation, deepcopy and finite transcendental
operations remain supplied services. No DynamicExpressions files or shared
registry files are modified by this slice.

## Q34. Which table specifies the default mutation weights?

`src/Options.jl:472-493,1336-1350`.

- Reading A: the fifteen weights listed in the Options docstring describe what `Options()` uses.
- Reading B: `default_options` deliberately uses a separately tuned table, and the docstring lists the standalone `default_mutations()` weights.

Modelled: the constructor uses `default_options` exactly as written. `opts-doc-mutation-defaults` refutes Reading A. Ten of the fifteen weights differ. For example ConstantMutation is 0.0346 instead of 0.0353, OperatorMutation is 0.293 instead of 3.63, and RotateTreeMutation is 4.26 instead of 1.42. The Julia reproducer checks the actual docstring and constructor output. Every versioned weight table delegates omitted fields to the existing MutateGen model of `_mutation_weights`.

## Q35. Does the output-directory default describe a field or the effective save path?

`src/Options.jl:513-515,705,1166-1172`, `src/SearchUtils.jl:914-925`.

- Reading A: the constructed `Options().output_directory` field should equal the documented `"./outputs"`.
- Reading B: the constructor retains `nothing`, and `save_to_file` supplies the effective `"outputs"` base directory later, before appending the run ID.

Modelled: Reading B, matching the source. `opts-doc-output-directory` refutes the stronger constructor-field interpretation in Reading A. This is a representation difference, not evidence that saved files use the wrong default directory. The reproducer prints the field and the effective base expression. In the testing environment, an omitted directory instead calls `mktempdir`; an explicit directory is always retained.

## Q36. Are scalar range checks constructor responsibilities or caller responsibilities?

`src/Options.jl:849-892,1015,1158,1174-1178`; existing `QUESTIONS.md` Q15.

- Reading A: negative maxdepth, populations below one, negative parsimony and tournament probabilities outside `(0,1]` should fail at construction.
- Reading B: construction only checks the explicit assertions; other ranges are caller responsibilities or are handled later.

Modelled: Reading B. The complete constructor accepts arbitrary model-domain maxdepth, populations, cycles, parsimony, tournament probability, crossover probability and replacement fractions with otherwise valid defaults and successful standard constructor services. The model includes NaN and infinities through DE's JF. Population size only participates in `tournament_selection_n < population_size`; size zero with tournament size -1 is accepted. The exact rejected scalar conditions are maxsize <=3, negative or NaN warmup, tournament size >= population size, unsupported loss_scale, nonpositive print precision, unsupported batching selector, and nonpositive explicit batch_size. The Julia contract script checks these classifications, including NaN and Inf cases.

## Q37. Where is deterministic serial execution enforced?

`src/Options.jl:540-542,697,1264`, `src/Configure.jl:61-66`, `src/SymbolicRegression.jl:731-734`.

- Reading A: `Options(deterministic=true)` must receive and validate `parallelism=:serial` itself.
- Reading B: deterministic is retained by Options, while the search configuration check enforces serial execution.

Modelled: Reading B for the assigned files. Options accepts either deterministic flag and rejects `parallelism` as an unknown keyword. `test_option_configuration` explicitly rejects deterministic execution with nonserial parallelism. SRSearch reports that its caller invokes that external check only when `runtests=true`; this Options slice makes no stronger whole-search safety claim.

## Q38. What does equality of separately constructed Options mean?

`src/OptionsStruct.jl:33-38,179-266,310-327`.

- Reading A: Options defines structural `==`, so equivalent keyword calls must produce values that compare equal.
- Reading B: only ComplexityMapping has a custom `==` here; Options uses Julia's generic identity-based equality.

Modelled: Reading B. Julia reports `o == o` as true and `Options() == Options()` as false. Alias properties establish the same normalized keyword values and therefore the same downstream configuration under the same supplied constructor outcomes; they do not claim object identity between independent constructor calls. Testing-environment temporary directories and allocation identities can differ between calls. ComplexityMapping equality laws are proved for the shared integer-valued mapping specialization. Floating NaN equality is not covered by those laws.

## Q39. Does an empty operator-complexity collection need an element type?

`src/Options.jl:1005-1012`, `src/OptionsStruct.jl:68-95`.

- Reading A: any empty collection denotes no customized entries and should construct successfully.
- Reading B: Julia dictionary value types participate in promotion, so even empty inputs must carry a suitable numeric value type.

Modelled: Reading B. `Options(complexity_of_operators=[])` reaches `one(::Type{Any})` and throws MethodError. `Options(complexity_of_operators=Pair{Function,Int}[])` succeeds with `use=true`. The explicit Any-value-type branch models the eager `one(T)` failure when operators are present or a default leaf weight is needed. Other malformed type-promotion combinations are outside the integer complexity specialization, rather than assigned a successful integer result. A supplied ComplexityMapping or complexity function bypasses this builder after the conflict assertion.

## Options: model domain and reused implementations

All source functions with executable bodies in the two assigned files have mirrors and registry coverage. `default_popmember_type` at `src/Options.jl:238` is a bodyless declaration in these files, so its externally defined default method has no local implementation to prove. The default popmember type, arbitrary expression and node type metadata, objective functions, optimizer constructors, plugin hooks, ADTypes construction, helper-function installation and temporary-directory creation are represented by opaque data or supplied services with propagated exceptions. Plugin merging imports `SymReg.Plugins.mergeDefaults`. Constraint builders, nested-constraint validation, operator-key collision checking and their properties are imported from SymReg.SimpCons without duplication. Existing mutation weights and their construction are imported from SymReg.MutateGen.

Scalar-valued options use DE's JF model: exact finite rationals, NaN and infinities, without finite rounding, overflow or signed zero. Int options represent successfully converted Julia Int values. Complexity construction and equality use the existing integer `SymReg.Complexity.CMap` and `VarC`; the supplied conversion in `promotedMapping` records the field traversal, not a theorem about all Julia numeric promotion types. The explicit Any dictionary case above is additionally modelled. No source assertions are omitted in this domain. Warnings are not modelled as errors. Custom Julia callbacks and imported constructors can raise additional exceptions, represented by their supplied service results.

## Q40. NaN losses in `choose_best`

`src/MLJInterface.jl:722-729`. `argmin(losses)` treats NaN as the smallest value, and
`1.5 * minimum(losses)` is NaN as soon as one loss is NaN, which masks every row to `-Inf`.
Since PR #790, `calculate_pareto_frontier` skips NaN losses (`src/HallOfFame.jl:172`).

- Reading A: NaN losses are not expected on a frontier, so the behaviour is irrelevant.
- Reading B: selection should ignore NaN losses (threshold from the smallest non-NaN loss;
  never select a NaN row while a finite one exists).

Modelled as written. `mlj-cb-linear-nan` and `mlj-cb-log-nan` state Reading B for
`choose_best` itself and are refuted; `mlj-rep-default-nan` states it for reports and is proven
because the frontier has no NaN loss (`hof-frontier-strict-all`). `mlj-cb-log-rule` and
`mlj-rep-default-rule` prove the docstring rule under the precondition that no loss is NaN.

## Q41. One empty frontier zeroes every multitarget `best_idx`

`src/MLJInterface.jl:741` returns `fill(0, length(trees))` if any target's frontier is empty,
and `src/MLJInterface.jl:583` then returns the zero fallback for all targets.

- Reading A: intended; a multitarget model is usable only when every target has equations.
- Reading B: the other targets should keep their own `best_idx` and predictions.

Modelled as written: `mlj-rep-best-multi` and `mlj-pred-empty-multi` prove the all-zero behaviour.

## Q42. Decreasing `niterations` before a warm start

`src/MLJInterface.jl:261-263`: `update` with `m.niterations < old_fitresult.niterations`
throws `AssertionError("niterations >= 0")`. MLJ calls `update` after any hyperparameter change.

- Reading A: intended; users must refit (`fit!(mach; force=true)` or a new machine).
- Reading B: `update` should fall back to a fresh fit, as MLJ's `update` contract suggests.

Modelled as written: `mlj-update-decrease`.

## Q43. `clean!` performs no checks

`src/MLJInterface.jl:217` returns `""` for every model; the comment at line 183 defers
cleaning to `Options` and `equation_search`. A negative `niterations` therefore passes `clean!`
and fails only inside `_update` (line 263).

- Reading A: intended; `Options` validates the option fields at fit time.
- Reading B: `clean!` should warn about and correct invalid MLJ-level fields (`niterations`,
  `parallelism`) as the MLJ interface recommends.

Modelled as written: `mlj-clean-negative`.

## Q44. Feature tables with a column named `data` or `idx`

`src/MLJInterface.jl:570-576` tests any `NamedTuple` for the keys `data` and `idx` before
treating it as features.

- Reading A: `data` and `idx` are reserved column names (undocumented).
- Reading B: a feature table fitted by the model must be predictable.

`mlj-pred-feature-table` states Reading B and is refuted.

## Q45. Multitarget fallback inside the per-target loop

`src/MLJInterface.jl:547-562,599-604`: when one target's equation fails to evaluate,
`eval_tree_mlj` returns `prediction_fallback` for the whole model (a `num_targets`-column matrix,
or a table when `y` was a table), and `reduce(hcat, outs)` concatenates it with the other columns.

- Reading A: the intent was a zero column for the failed target only.
- Reading B: the intent was an all-zero prediction for every target.

Neither matches the code: `mlj-pred-width-multi` (one column per target) is refuted. For a
table target the `hcat` of a `NamedTuple` with vectors is not modelled (`predictCoreK` returns
`none` there).

## Q46. Custom complexity functions on templates
`src/TemplateExpression.jl:707-716`. Reading A: a function-valued `complexity_mapping` should receive the whole `TemplateExpression` (as `src/Complexity.jl:20-27` does for other expressions). Reading B: it is meant to be applied to each inner expression and summed. Modelled: the code (B); entry `tmpl-complexity-custom` is refuted under A.

## Q47. Crossover key choice
`src/TemplateExpression.jl:1003-1004`. Reading A: both parents should cross the same key, so subtrees stay within one function's arity. Reading B: independent keys are intended and invalid children are left to `check_constraints`. Modelled: the code (independent keys); `tmpl-crossover-valid` is refuted under A, `tmpl-crossover-same-key` proves the same-key case.

## Q48. Inner variable names after `embed_metadata`
`src/ExpressionBuilder.jl:105-109`, `src/TemplateExpression.jl:605`. Reading A: `embed_metadata` should match `create_expression(..., Val(true))`, including inner expressions' `variable_names`. Reading B: inner expressions should never carry dataset names (their features are function arguments), so `create_expression` is the odd one. Modelled: the code; `tmpl-embed-create` refuted.

## Q49. Parameter vectors passed to the constructor are aliased
`src/TemplateExpression.jl:381-385`. `ParamVector(convert(Vector{T}, p))` keeps the caller's vector, so `set_scalar_constants!` on the template mutates it (observed: caller vector became `[42.0, 43.0]`), while `parse_expression` copies (line 1382). Reading A: aliasing is intended (Julia constructor convention). Reading B: the constructor should copy. Modelled: values only (no entry depends on it).

## Q50. ParametricExpression support
`src/ExpressionBuilder.jl:84-93`. SR has no ParametricExpression methods; with `expression_type=ParametricExpression` and `expression_options=(; parameters=P, ...)` every created expression shares `P`. Reading A: unsupported since the move to template parameters. Reading B: still supported through the generic builder. Modelled: the generic builder; `tmpl-create-independent` refuted.

## Q51. Zero-length template parameters
`src/TemplateExpression.jl:1093`. `num_parameters=(p=0,)` is accepted by `TemplateStructure` and the constructor, but `mutate_constant` then throws. Reading A: zero lengths should be rejected at construction. Reading B: `mutate_constant` should skip empty vectors. Modelled: the code; `tmpl-mutconst-total` refuted.

## Q52. Counting the standalone baseline evaluation

`src/ConstantOptimization.jl:210-213,221-237` evaluates `f(x0)` before calling Optim, but initializes `num_evals` from Optim's `f_calls` alone. Restart counters and the accepted final evaluation are included.

- Reading A: `num_evals` counts all objective evaluations, scaled by `dataset_fraction`, as the surrounding search budget expects.
- Reading B: the baseline is deliberately free for budget purposes, and the counter only measures optimizer-reported work plus accepted reevaluation.

Modelled: the code as written. `copt-eval-accounting` refutes Reading A even when Optim's own counter is accurate. Real NelderMead with two restarts makes 10 actual loss calls and reports 9. A two-sample view of four samples reports 4.5 instead of 5. The discrepancy is exactly one dataset fraction. Gradient/Hessian counters and any hidden evaluations inside differentiation are also excluded unless reflected in `f_calls`.

## Q53. Equal minima and NaN barriers

`src/ConstantOptimization.jl:225-230` uses strict `<` for both restart replacement and final acceptance.

- Reading A: ties retain the earlier optimizer result, and NaN means that no improvement can be certified, even when a later restart has a finite minimum.
- Reading B: a finite restart should recover from an initial NaN optimizer minimum, and a finite candidate should recover from a NaN baseline.

Modelled: Reading A, matching the source without a finiteness precondition. `copt-restart-nan` proves that an initial NaN minimum blocks all replacements. `copt-nonfinite-comparisons` proves the NaN baseline barrier, finite improvement over positive infinity, permitted negative-infinity minima, and the impossible improvement of a negative-infinity baseline. Equality rejects and restores original parameters.

## Q54. Returning and mutating the parent object

`src/ConstantOptimization.jl:147,150,230-243`: `optimize_constants` returns the exact input member on every successful path. Accepted optimization mutates its tree, loss, cost, optional complexity cache and birth; ref/parent stay unchanged.

- Reading A: this is an explicitly in-place API, and callers that need a child must copy before calling it.
- Reading B: use by OptimizeMutation expects a new member allocation like other mutations.

Modelled: Reading A for the function itself. `copt-public-parent-identity` proves the complete public path preserves member/tree allocation identities and lineage. PR #789 takes Reading B at the call site: OptimizeMutation optimizes a `create_child` copy (`src/Mutate.jl:955-963`), so `mutgen-ng-no-alias`, `mutgen-ng-parent-unchanged` and `regevol-no-alias` are proven.

## Q55. Shared Node constants as independent optimizer coordinates

`src/ConstantOptimization.jl:88-90,118-119,231,263` delegates scalar get/set directly to DynamicExpressions. A plain Node tree may use the same constant node as two children.

- Reading A: scalar optimization requires independently writable coordinates, so callers must supply distinct constant references.
- Reading B: every legal expression, including shared plain Nodes, should round trip every exact-size optimizer vector.

Modelled: the source's ordered mutable writes. `copt-parametric-roundtrip` proves Reading A's guarantee through DE's existing reference/parameter laws. `copt-scalar-alias-roundtrip` refutes Reading B: a shared constant starts with `[1,1]`; requesting `[2,3]` reads back `[3,3]`. The final accepted loss is reevaluated after these writes, so it follows the actual expression rather than assuming Optim's reported minimum matches its flat vector.

## Q56. Preparation keys and the AutoEnzyme type test

`src/ConstantOptimization.jl:280-286,289-293` keys preparation by `hash((ctx, backend, typeof(example_tree)))`. It omits the tree value and uses the hash as the entire dictionary key. The friendly missing-Enzyme check tests the type parameter `AD isa AutoEnzyme`.

- Reading A: preparation is valid for every value of one concrete tree type, hash collisions may share preparations, and the backend's own error is acceptable when Enzyme is absent.
- Reading B: preparations depend on tree structure or collision-resistant equality, and the missing-Enzyme test was meant to recognize the AutoEnzyme backend instance.

Modelled: the code as written. Cache keys use only context, backend and concrete tree type; a hit reuses the stored object. A Julia type object is not an AutoEnzyme instance, so the type-parameter test is false. Backend/preparation failures remain explicit throwing services. No theorem assumes that an arbitrary external differentiation preparation is valid for every cached expression.

## Q57. Fresh scores and nonfinite accepted reevaluation

`src/ConstantOptimization.jl:205-210,230-240,251-265` compares Optim's minimum against an unregularized fresh baseline, then reevaluates accepted constants with regularization enabled. It does not check the final value for finiteness, compare final regularized loss against stored loss, or refresh scores on rejection/early return.

- Reading A: deterministic, expression-read-only loss functions and coherent initial member scores are caller obligations; regularization can change the final score and need not preserve the ordering used for acceptance.
- Reading B: optimization promises an unconditional decrease of the stored regularized loss and unconditional fresh scores, even for stale members or stateful custom losses.

Modelled: Reading A. Accepted scores equal a fresh regularized evaluation under the explicit read-only/deterministic service contract, including NaN or infinities. The rejection and no-parameter paths preserve old scores exactly. Optim is an arbitrary function returning minimizer, minimum and all counters; no convergence or truthful-minimum condition is silently assumed.

## Constant optimization: model boundaries and source coverage

Every function in the 307-line `src/ConstantOptimization.jl` at SR upstream/master daae84e5 is represented by the registered source names. There is no function named `dispatch_optimize_constants` in that file. The present dispatch is the single-real-parameter Newton choice and `_optimize_constants_inner`'s f versus only_fg! choice. Compatibility hooks and context-aware optimizable-parameter hooks are included.

Population mask generation is reused from `simp-optimizer-selections`; `copt-population-enabled` adds the `should_optimize_constants` conjunction using the existing SimpCons per-member model. DE owns expression/node/reference/parametric scalar operations. `copt-template-roundtrip` imports the Templates slice's scalar laws through a ParameterHooks adapter. Its domain has independent outer parameter arrays; arbitrary replacement vectors additionally require distinct constant-node references within and across inner expressions. Restoring the original vector permits shared nodes. Custom combiner parameter-selection overrides remain arbitrary hooks.

Finite JF arithmetic is exact and excludes floating rounding, overflow and signed zero. Evaluation counters use Rat as the other SR slices do. Sample ratios are mathematical ratios; Float64 rounding of ratios and accumulated counters is outside the model. Successful call effects are threaded explicitly through expression storage and the loss context. Exceptions propagate as Jl errors; post-exception partial mutations are outside the successful-return claims. External optimization, automatic differentiation, custom parameter hooks and loss evaluation remain arbitrary callbacks.

## Q58. Raw string_tree drops remaining keywords

`src/InterfaceDynamicExpressions.jl:226-244,247-272`: the raw branch accepts `kws...` but does not pass them to DE, whereas both pretty branches forward them.

- Reading A: DE printing keywords, such as `f_constant`, should work regardless of pretty mode.
- Reading B: raw rendering intentionally disables every additional printing keyword without warning.

Modelled as written. `ide-raw-keyword-forward` refutes Reading A: a constant 1.0 with `f_constant=(_ -> "CUSTOM")` prints `1.0` instead of `CUSTOM`. The direct DE call honors the keyword.

## Q59. print_tree bypasses SR pretty formatting

`src/InterfaceDynamicExpressions.jl:282-286,332-344`: SR string_tree uses subscripted default variable names in pretty mode, but both print_tree methods delegate directly to DE and therefore use DE's plain default names. Precision, display-variable names and unit support also take the DE route.

- Reading A: printing an equation with the same options and pretty=true should append one newline to SR string_tree's result.
- Reading B: SR print_tree deliberately provides DE formatting rather than SR's option-aware formatting.

Modelled as written. `ide-print-pretty-consistency` refutes Reading A with the variable x1: string_tree returns `x₁`, while print_tree writes `x1\n`.

## Q60. Mixed element types fail SR's output assertion

`src/InterfaceDynamicExpressions.jl:91,110,115-123`: the expected output array uses X's scalar type and ignores the tree's scalar type. DE promotes mixed scalar types before evaluation.

- Reading A: SR wrappers should accept the same valid mixed Float32/Float64 input as DE and preserve its promoted result.
- Reading B: SR intentionally requires equal tree/data scalar types even though the public wrapper has no such signature restriction.

Modelled as written. `ide-mixed-type-eval` refutes Reading A: `Node(Float64;val=1.0)` with `ones(Float32,1,2)` evaluates in DE to `Float64[1,1]`, but SR throws `TypeError`, expecting `Vector{Float32}`. The Lean model reuses DE's `NodeBase.Elt` and `promoteElt`.

## Q61. Data-type hook support and documentation signatures

`src/InterfaceDataTypes.jl:7-14,23-30,33-39`: sample_value's docstring omits the required RNG positional argument. Number dispatch delegates to randn(rng,T), so numeric types without a randn method can throw. Generic initialization/sampling/mutation are documented extension points that throw until a type supplies its own overload.

- Reading A: the documentation summarizes hook intent; supported Number types are those implementing zero/randn, and custom types must add overloads.
- Reading B: every Number type should always receive a successful, requested-type sample, and the two-argument documented sample_value signature should be callable.

Modelled as Reading A. Runtime zero/randn services are arbitrary typed results, including exceptions. No unsupported type is silently converted. Existing `mut-mutate-value` owns numeric ConstantMutation range and RNG-consumption properties; `idt-constant-mutation` reuses its model, retaining temperature and both mutation fields.

## Q62. Dataset overloads absent in the target source

`src/InterfaceDynamicExpressions.jl:17,80-87,226-234`: Dataset is imported but there is no Dataset-argument evaluation or string method in this file.

- Reading A: callers supply `dataset.X` and `variable_names=dataset.variable_names` explicitly.
- Reading B: wrappers should provide a Dataset convenience overload.

Modelled as Reading A, matching all methods present. Names supplied from a dataset are ordinary variable-name lists, and Loss.Dataset/getX already own dataset view selection. No nonexistent Dataset dispatch was added to the model.

## Interface slice: model boundaries and source coverage

**Files already fully covered by other slices.** None. Both target files receive new entries. Numeric mutate_value's actual implementation is in `MutationFunctions.jl` and is already covered by `mut-mutate-value`; the InterfaceDataTypes fallback is newly covered here.

**Model reuse and scope.** Reuses DE `Expressions.Expression`, `Expressions.get_tree`, `Expressions.get_operators`, `OpEnum`, `Eval.EvalContext`, `JMat`, `JVec`, `Heap`, `StringsParse.Scalar`, `RenderConfig`, `stringTree`, `printTree` and `printTreeIO`; SR `Loss.Options`, `Loss.Reply`, `Loss.dispatchReply`, `Loss.at1`, `Options.inverseOpmap` and `Mutations.mutateValue`/`mutateValue'`.

DE is modeled at its API boundary: arbitrary evaluation callbacks retain array values and errors, and a separate `assertOutput` mirror models the concrete output-type check with DE's existing scalar types/promotion. Custom AbstractOptions operator selection remains an arbitrary resolved service. Printf, DynamicQuantities text, zero and randn remain external services. GraphNode preparation reuses DE's heap conversion algorithm and proves conversion occurs only for raw graph rendering; pretty graphs retain their root and heap. Distributed fallback AST hygiene is outside value-level semantics.

## Q63. Structural symbolic roundtrip versus dependency canonicalization

`ext/SymbolicRegressionSymbolicUtilsExt.jl:16-67` forwards conversion to DynamicExpressions and SymbolicUtils. The SR extension contains no implementation of constant conversion, variable naming, operator matching or symbolic canonicalization.

- Reading A: conversion roundtrip means structural equality of every input tree, including operator association and constant representation.
- Reading B: roundtrip preserves whatever equality the underlying converter promises; symbolic canonicalization can change tree structure.

Modelled: unconditional equality between the SR wrapper composition and the dependency composition, plus conditional structural roundtrip when the dependency has a right-inverse law for those operators and keywords. No global SymbolicUtils inverse law is invented. All constants, feature/operator indices and keyword values reach the dependency unchanged. The identity-converter witness shows the conditional theorem is satisfiable.

## Q64. Gradient tangent shape in Mooncake

`ext/SymbolicRegressionMooncakeExt.jl:10-37` allocates count_scalar_constants(ex) slots, zips tree and parameter tangents with primal fields, and performs unchecked sequential packing without a final count assertion.

- Reading A: Mooncake tangents have the matching structure and scalar count required by the expression; malformed tangents are outside the integration contract.
- Reading B: arbitrary hand-constructed tangents should be rejected safely rather than returning uninitialized output or writing beyond the buffer.

Modelled Reading A for the fully initialized gradient theorem. The mirror retains zip truncation, NoTangent assertions, uninitialized suffix slots and undefined behavior on overrun. No malformed-tangent bug is registered without evidence that supported Mooncake differentiation produces one.

## Ext slice: model boundaries and source coverage

**Already-covered files.** None. All six assigned files have registry entries.

**Coverage boundaries and non-checkable code.**

- Enzyme: models shadow preparation, exact zero/remake callback routing, output/adjoint seeds, loss selection, optional gradient buffer and returned tree-shadow component. External AD remains arbitrary. No theorem asserts that Enzyme computes derivatives correctly. Numeric scalar storage uses the shared JF model. The concrete TemplateOptimizableRefs failure uses actual built-in template optimizer references, rather than a deliberately incompatible user hook.
- Mooncake: models template and composable extraction, tree-first/parameter-second order, NoTangent assertions and zip behavior. External inner-gradient extraction remains arbitrary. The packing model covers numeric scalar coordinates; external custom scalar packing is not assigned an invented law.
- SymbolicUtils: all eight overloads are represented. Tree and operator models reuse DynamicExpressions; complete keyword tuples are arbitrary values. Variables, operators and constants are preserved at the SR-to-dependency boundary. Any stronger converter correctness claim is explicitly conditional on an external inverse law.
- JSON: json_write forwards the whole trace, not a chosen field list, with allownan=true. The file framing model proves append/write/newline behavior on successful file I/O and serializer-error propagation. It does not assert undocumented JSON serialization rules or claim file rollback after an I/O/serialization error. File open/close and device I/O semantics belong to Base.
- Tables: all seven methods are covered. Columns/names/matrix/materializer services remain arbitrary; Symbol-convertible names retain order. The singleton Val(:Tables) argument is represented by Unit.
- PythonCall: this extension implements no Python conversions. Lines 6-39 only request precompilation of conversion rules implemented in PythonCall; those signatures have no conversion result to formalize. The runtime function pysr_shaped_workload and its default operator order are modelled. Lines 65-70 run two fixed precompilation workloads under output redirection; these zero-input initialization effects are not registered as universally quantified conversion properties. No PythonCall dependency is added.

**Dependencies.** Enzyme is added to repro/Project.toml solely for the real ext-enzyme-optimizable-hooks refutation. No Mooncake, SymbolicUtils, JSON, Tables or PythonCall dependency is needed for refutations.

## Q65. Gamma pole handling and library exceptions

`src/Operators.jl:14-17`. The wrapper changes infinite SpecialFunctions.gamma results to NaN. In Julia 1.12, gamma(-1.0) and gamma(-2.0) throw DomainError before the infinity test, gamma(0.0) returns NaN, and gamma(-Inf) throws.

- Reading A: gamma should be a safe real-valued operator that returns NaN for poles.
- Reading B: only infinite successful results should be sanitized, and library exceptions are intentional.

Modelled as written, with arbitrary exception-valued library callbacks and a concrete confirmed gamma(-1.0) runtime fact. `ops-gamma-total` refutes Reading A's safety expectation; the zero pole already follows that convention.

## Q66. Strong-zero conditional and rectifier semantics

`src/Operators.jl:101-124`. Julia Bool multiplication has a strong zero: false*NaN returns 0.0. Consequently relu(NaN)=0.0 and cond(-1.0,NaN)=0.0, while comparisons with NaN return numeric zero.

- Reading A: these are masking/selecting operators; an inactive value is intentionally discarded.
- Reading B: relu should agree with max(x,0), including NaN propagation, and conditional operators should propagate invalid operands.

Modelled Reading A because the implementation explicitly multiplies a Boolean and no docs/src page or operator docstring states a NaN-propagation promise. This is a proven runtime convention, not a registered bug. JF merges the two zero signs; Julia returns -0.0 for relu(-1.0) and relu(-Inf).

## Q67. Different pole conventions in guarded unary methods

`src/Operators.jl:50-76`. safe_log(0.0) and safe_log1p(-1.0) return NaN, although Base gives -Inf. safe_atanh(1.0) returns Inf and safe_atanh(-1.0) returns -Inf.

- Reading A: the explicit source inequalities define each operator independently, allowing some infinite endpoint values.
- Reading B: every singular endpoint should have a common NaN convention.

Modelled Reading A. No operator documentation in docs/src or docstrings promises uniform pole handling, so this is a question rather than a claimed bug.

## Q68. atanh_clip's comment uses remainder instead of modulo

`src/Operators.jl:19-20`. Execution uses mod(x+1,2), while the adjacent mathematical comment writes (x+1)%2. In Julia percent means rem, and the two differ when x+1 is negative.

- Reading A: execution's mod is the intended periodic wrapping into [-1,1).
- Reading B: the comment's Julia percent/rem expression specifies the intended function.

Modelled Reading A, preserving the actual mod call. The source comment's stated equivalence is refuted by `ops-atanh-comment`: at x=-2.0 execution returns 0.0, while the percent/rem expression throws DomainError. Julia gives mod(-1,2)=1, rem(-1,2)=-1, atanh(0)=0, and atanh(-2) throws. This is a documentation mismatch; no operator docstring or docs/src explanation resolves intent.

## Operators slice: model boundaries and source coverage

**Existing coverage and scope.** No Julia file skipped. `src/Operators.jl` is covered by this slice. Existing Options.Core opmap/inverseOpmap uses the same function identities and covers Options normalization; this slice imports and reuses it for get_safe_op rather than defining a second identity system. No pre-existing registry entry covered safe operator scalar evaluation. Shared IEEE comparison implementations from DE Expressions.Sampling and SR HofMig and isZero from MutateGen are reused.

Transcendental values, Base power/modulo, SpecialFunctions.gamma, promoted scalar conversion and generic dispatch results are external exception-valued callbacks. JF's finite values are exact rationals and omit rounding, overflow and signed zero. Quantity dimensions and Dual derivatives stay in the external services; scalar guards and specialized-vs-generic dispatch are covered. For dimensionless quantities, 2^2=4, 0^-2=NaN and (-2)^0.5=NaN. Dimensioned examples give safe_pow(4m,0.5)=2m^(1/2), safe_pow(-4m,0.5)=NaN and safe_pow(1m,1m) raises DimensionError, matching test/integration/ext/dynamicquantities_units/test_units.jl:183-187. No extra Julia dependency was needed. The Units slice covers the WildcardQuantity dimensional-analysis path. The JF scalar model leaves dimensioned DynamicQuantities runtime behaviour external.

Documentation check: docs/src/*.md contains no operator-specific relu/gamma/safe_* definitions or NaN promises; Operators.jl has no operator docstrings. Source inequalities and formulas are therefore the modelled reading, with ambiguous pole/masking conventions listed above.

## Q69. Dataset weights shape omitted by configuration validation

`src/Configure.jl:99-125`, `src/Dataset.jl:170-191`. The configuration error text promises that weights have shape `[rows]`, but its condition checks only X and y. Ordinary numeric Dataset construction also accepts a weight vector with a different length.

- Reading A: the configuration validator enforces all three shapes mentioned by its diagnostic.
- Reading B: callers must separately guarantee the weight shape, despite the diagnostic.

Modelled as written. `cfg-weights-shape` refutes Reading A: three columns and targets with one weight are accepted. The reproducer uses the ordinary public Dataset constructor and the real validator.

## Q70. Numeric operator validation is a finite sample

`src/Configure.jl:36-57`. Numeric operators are tested on 99 range values from -100 to 100. Complex values use matching real and imaginary coordinates, producing only a diagonal. NaN and infinities are not test inputs, and successful NaN/Inf outputs of the correct type are allowed.

- Reading A: “well-defined” means successful same-type execution on exactly this finite test set.
- Reading B: passing validation proves an operator works everywhere on the real line or complex plane.

Modelled as Reading A, matching the implementation and its explicit safe-log NaN advice. There is no global-domain soundness claim.

## Q71. Narrow progress display widths

`src/ProgressBars.jl:42-46`. Multiline formatting computes a repeated-space prefix with exponent `width-length("  <label>:  ")`, without clipping a negative result.

- Reading A: any positive progress-bar width should remain renderable.
- Reading B: callers guarantee the bar width is at least every label margin.

Modelled as written. `pbar-narrow-multiline` tests Reading A with label `label`, value `a\nb`, and width 3. Character repetition has exponent -7 and throws `ArgumentError("can't repeat a character -7 times")`. No such width precondition appears on this helper.

## Q72. Invalid precompilation mode diagnostic

`src/precompile.jl:26,41`. The invalid-mode branches concatenate a string with `show(mode)`. Julia's one-argument `show` prints the mode and returns `nothing`, so string multiplication raises `MethodError` before `error(...)` can build the intended diagnostic.

- Reading A: invalid modes should raise `ErrorException` with the explicit `Invalid value for mode` message.
- Reading B: any exception suffices for unsupported modes.

Modelled as written. `pre-invalid-mode-diagnostic` refutes Reading A with `do_precompilation(Val(:invalid))`, which prints `:invalid` and throws `MethodError(*(String, Nothing))` without running the workload.

## Infra slice: model boundaries and source coverage

**Boundaries and reuse.** - All six requested Julia source files have entries. No whole Julia file is already fully covered by another slice.
- `score_func` in `src/deprecates.jl:31-39` is already completely covered by `loss-score-deprecated`, using `SymReg.Loss.scoreFunc` and `SymReg.Loss.score_deprecated_holds`. Infra imports the existing definitions rather than reproducing its loss model.
- Deprecated Options keyword renaming belongs to existing `opts-alias-precedence`, `opts-alias-autodiff-ignored`, `opts-population-alias-precedence`, `opts-return-state-order`, and `opts-weight-creation`. Infra imports `SymReg.Options.Properties`; the aliases are not recreated.
- `EquationSearch(...;multithreaded=...)` preserves the deprecated keyword unchanged. `equation_search` rejects non-nothing values at `src/SymbolicRegression.jl:616-620`. It does not map a Boolean to a parallelism symbol. This is deliberate removal behavior, not an Infra forwarding bug.
- Data reuse: `SymReg.Loss.Basic`, `DynExpr.JF`, `DynExpr.Jl/JlError`, `SymReg.Search.Parallelism`, and `SymReg.HofMig.Member`, `copyMember`, and `calculatePareto`.
- Int counters/ref keys model values before machine overflow. Finite Rat arithmetic excludes floating rounding/overflow/signed zero, following the shared scalar model. Operator range rounding/conversion, log10/eps/extrema, callable reflection, distribution, I/O, ProgressMeter updates, and compilation services are explicit external inputs.
- Logging callback frequency uses the current source's zero-based first log and mandatory positive-interval terminal log. Nonpositive intervals disable logging. Calls that throw during payload or emission do not reach the increment.
- Geometry proofs apply to finite coordinates. Hull execution is an inductive certificate of the actual loop, avoiding an artificial fuel cutoff. The theorem proves input-vertex membership for terminating runs; it does not claim totality for NaN geometry or prove every hull is a minimal convex hull.
- Source tracing uses dictionary entries keyed by decimal member ref. The model uses integer keys because decimal rendering is injective. Reused references preserve the first snapshot. Times are external observations. Parent/member copies reuse the existing allocation model. Arbitrary post-snapshot trace dictionary mutations outside the package schema are outside the model.
- `src/scripts/fromfile_to_modules.sh` is a historical one-off source migration relying on external `vims` and destructive filesystem rewriting, not loaded by the package. It has no callable SR runtime semantics and no in-scope stable replacement specification.
- `src/scripts/apply_deprecates.py` is a historical one-off migration targeting nonexistent uppercase `src/Deprecates.jl` and one-line macro declarations, while the current source is lowercase and multiline. It is not loaded by the package. Its external filesystem rewrite is excluded rather than treating an obsolete developer script as a runtime API.

## Q73. NaNs and sentinel values in fast selection

`src/Utils.jl:106-143`.

- Reading A: fast selection is intended only for finite losses strictly below typemax(T).
- Reading B: the documented bottom-k and findmin operations should retain Base ordering and return actual input indices for every legal floating input, including NaN and Inf.

Modelled as written, with Reading B's total selection contract refuted: findmin_fast([1.0,NaN,0.0]) returns (0.0,3) instead of Base's (NaN,2), and bottomk_fast([0.0,Inf],2) returns indices [1,1] for values [0.0,Inf]. Neither public function documents a finite-only precondition.

## Q74. Tiny positive Poisson rates

`src/Utils.jl:146-153`.

- Reading A: a positive finite Poisson rate always has a nonnegative integer sample.
- Reading B: the zero guard is sufficient even when exp(-lambda) rounds to exactly one.

Modelled as written. The support guarantee is refuted because lambda=1e-20 has exp(-lambda)==1.0 and the initial while guard is false, returning -1. The result does not depend on the random stream.

## Q75. Type-only safe_call caching

`src/Utils.jl:234-250`.

- Reading A: only method applicability is cached; an internal, value-dependent MethodError must not suppress later valid inputs of the same types.
- Reading B: every MethodError permanently marks the function/tuple type pair Bad within the task, regardless of where it arose.

Modelled as Reading B because the catch checks only isa(e,MethodError). Reading A's safe-call guarantee is refuted with f(0) raising an internal MethodError and f(1)==2, after which safe_call(f,(1,),-99) incorrectly returns (-99,false).

## Q76. Single-entry crossover weights

`src/Crossover.jl:120-127`.

- Reading A: the singleton list deliberately bypasses sampling and weight validation to avoid RNG draws.
- Reading B: a zero or invalid singleton weight should prevent selection as in the multi-entry sampler.

Modelled as Reading A, matching the source comment. The theorem quantifies over the full JF weight domain, including negative and NaN values, without classifying this intentional shortcut as another bug.

## CrossMut slice: model boundaries and source coverage

**Existing coverage reused.** - `src/MutationFunctions.jl`: crossover_trees is already `crossover-swap` (Crossover and Crossover* heap models). CrossMut models only dispatch and generation, leaving subtree swapping to that entry. Remaining mutation functions remain the existing Mutations slice.
- `src/Mutate.jl`: mutate! interface and handler behavior already covered by `mutgen-mut-tree`, `mutgen-mut-add-node`, `mutgen-mut-do-nothing`, `mutgen-mut-unknown`, `mutgen-bs-success`, `mutgen-bs-restore` and SimpCons's simplification handler entries. No duplicate engine/handler model is introduced.
- `src/MutationWeights.jl`: full conversion, field ordering and keyword defaults already `mutgen-weights-fields` and `mutgen-weights-kw`; CrossMut imports those definitions. New proofs add completeness and uniqueness across builtin/default/weight-field tables.
- No entire assigned Julia file is skipped as already covered: Crossover.jl, Crossovers.jl, Mutations.jl and Utils.jl all receive entries.

**Files without executable properties.** - `src/Core.jl:1-130` only declares an empty create_expression generic, includes modules, and imports bindings. Its include/import dependency graph is statically inspectable, but has no additional algorithm or method body to prove. Implementations of imported functions belong to their owning slices. No fake universally quantified input was added to a constant include-order fact.
- `src/ProgramConstants.jl:1-9` only defines TraceType=Dict{String,Any}, MaybeTrace=Union{Nothing,TraceType}, DATA_TYPE=Any and LOSS_TYPE=Real. Those four aliases are statically checkable Julia declarations; they have no executable behavior or input-quantified correctness property. No registry entry is fabricated for them.
- The annotated-string aliases in `src/Utils.jl:254-264` choose the Base types on Julia 1.12, already the environment used by every reproducer. The @ignore macro is covered as a function of its arbitrary syntax arguments by util-ignore-syntax.

**Model scope.** - Reuses HofMig.Member and HofMig.poissonSample/poissonLoop/MigrationRuntime, MutateGen.Kind/defaultMutations/builtinKinds/fieldNames/documentedKind/mutationFromSymbol and sampleMutationR, plus DE JF/Jl/RNG. Mutable callback effects are threaded through arbitrary H for crossover constraint and scoring calls.
- Crossovers use opaque expression identities; the actual tree operation is the existing heap-based crossover-swap theorem. Default PopMember construction stores caller-supplied births and references independently. Custom create_child implementations remain arbitrary external callbacks, as their user code is outside the assigned files.
- Counters use exact Rat as in the existing slices. General Float64 accumulation rounding, signed zero, integer overflow and non-isbits MutableTuple pointer layouts are excluded explicitly. The Poisson refutation retains Float64 exponential rounding through an explicit runtime input confirmed in Julia.
- String proofs operate on decoded Unicode character sequences. Chunk width is n=width+1, so positive chunk sizes include every legal positive input. Decimal subscript formatting operates on Julia digits' nonnegative decimal digit output.
- MutableTuple list storage represents Julia's homogeneous isbits NTuple allocation; unsafe invalid indices return the shared undefinedBehavior error rather than invented values.

## Q77. `^` on dimensioned bases with integer exponents (src/DimensionalAnalysis.jl:92-103)

`Base.:^(::WildcardQuantity, ::WildcardQuantity)` accepts only a dimensionless-or-wildcard base and power, so `x1^2.0` with `x1` in metres is a violation even though m^2 is physically meaningful for an integer power.
- Reading A: deliberate; the comment "Require both base and power to be dimensionless" states the rule (use `square`/`cube` for dimensioned powers).
- Reading B: integer constant powers of a dimensioned base should yield the base's dimensions to that power.
- Modelled: Reading A (`specRule .pow` requires both dimensionless), because the comment states it explicitly and the tests list `1.0 * (x1^(Node(; val=3.2)))` as bad.

## Q78. Value dependence of the dimensional check (src/DimensionalAnalysis.jl:142-145)

`degn_eval` marks a node as violating whenever any argument value on the first data row (`X[:, 1]`, features scaled by their unit factors, e.g. km -> 1000 m) is nonfinite. For `x1 * inv(x1)` with `X[1,1] = 0`, `violates_dimensional_constraints(inv(x1)*x1, ...)` returns `true`.
- Reading A: intended; a nonfinite value means the expression is invalid anyway, and normal evaluation also fails on that row.
- Reading B: the dimensional check should depend only on units.
- Modelled: as written (Reading A); recorded as the proven behaviour `units-degn-guard`, and `units-complete-arith` assumes finite first-row subexpressions.

## Q79. `safe_call` cache inside `@maybe_return_call` (src/Utils.jl:234-251, src/DimensionalAnalysis.jl:20-32)

`safe_call` caches per `(F, argument types)` whether the first call threw `MethodError`. After a `Good` entry a later `MethodError` is no longer caught (and `@maybe_return_call` rethrows it); after a `Bad` entry the method is never called again.
- Reading A: methods are assumed to depend on types only, so the cache is transparent.
- Reading B: a user operator whose `MethodError` depends on values would make the check history-dependent or throw.
- Modelled: uncached `safe_call` (Reading A); exact for every built-in operator, whose method applicability depends only on argument types.

## Units slice: model boundaries and source coverage

**(c) Files judged already covered / out of scope.**

- None of the two in-scope files was already covered; both appear as `juliaFile` of Units entries.
- Related but outside this slice: the dimensional penalty that calls the check (`dimensional_regularization`, src/LossFunctions.jl) is covered by `loss-dimension-no-units`, `loss-dimension-penalty`, `loss-dimension-satisfied`, `loss-dimension-empty`; the `[?]` unit prefix of the hall of fame by `hof-prefix`; MLJ unit unwrapping by `mlj-units-*`. Unit pretty-printing (`format_dimensions`) lives in src/InterfaceDynamicExpressions.jl and the TemplateExpression override of `violates_dimensional_constraints` in src/TemplateExpression.jl; neither is in this slice.
- `DimensionalAnalysis.jl` and `Dataset.jl` both rely on DynamicQuantities `FixedRational{Int32,25200}` exponents; Int32 numerator overflow (exponents above 85217) is outside the model.

## Q80. What a valid row of `eval_inverse_tree_array_masked` promises

`src/EvaluateInverse.jl:102-120`. The docstring says row `i` is valid "only if" every inversion step and every sibling value is finite. The code marks a row valid exactly when that holds. Finite steps do not imply that the rewritten tree reproduces the target: `Fix2(/, 0)` inverts `y` to `y * 0 = 0`, so for `x1 / x2` with `x2 = 0` the row is valid with value 0 although `0 / 0 = NaN`.

- Reading A: valid only means "all steps finite"; reproduction is not promised.
- Reading B: a valid row is a row whose inverted value reproduces the target (the purpose of the inversion, `src/EvaluateInverse.jl:68-79`, and of feeding the targets to the backsolve fit).

Modelled Reading B for `einv-mask-sound` (refuted). `einv-masked-row-spec` proves the code matches Reading A, and `einv-right-inverse-reproduces` proves Reading B for operators that are right inverses wherever finite.

## Q81. Inverse of `Fix2(safe_pow, a)` on negative bases

`src/InverseFunctions.jl:139`. `approx_inverse(Fix2(safe_pow, a)) = Fix2(safe_pow, inv(a))` returns NaN on every negative target, including `safe_pow(-2.0, 3.0) = -8.0`.

- Reading A: only the principal (nonnegative) branch is intended; NaN masks the row, which is safe.
- Reading B: for odd integer `a` the real root exists and should be returned.

Modelled Reading B for `inv-pow-complete` (refuted). The behaviour is incomplete, not unsound: the rows are masked out.

## Q82. Scale invariance of greedy forward selection

`src/Backsolve.jl:184-187,264`. The docstring says the selection "is invariant to the scale of y and of the individual columns". The column choice is, but `success = any(abs.(coefficients) .> tol * 100)` and the stopping floor are absolute, so a fit of `y = 2e-15 * x1` fails while `y = 2 * x1` succeeds.

- Reading A: the claim covers only which columns are chosen.
- Reading B: the whole fit, including success, is scale invariant.

Modelled Reading B for `bs-greedy-scale` (refuted).

## Q83. Uniqueness of `PopMember.ref`

`src/PopMember.jl:23` documents `ref::Int` as "Unique reference ID". `generate_reference` returns `abs(rand(Int))` from the task-local RNG with no collision check, and constructors accept an explicit `ref` from the caller.

- Reading A: uniqueness is probabilistic (a collision has probability about 2^-64 per pair), and an explicit `ref` is the caller's responsibility.
- Reading B: SR guarantees distinct refs.

Modelled Reading A: no refutation is claimed. Properties state what the code does: generated refs come from `abs(rand(Int))`, and constructors and `copy` keep or assign `ref`/`parent` as documented.

## Backsolve slice: model boundaries and source coverage

**Already covered elsewhere.**

- `src/MutationFunctions.jl` `backsolve_rewrite_random_node`: `mut-backsolve-rewrite`.
- `src/Mutate.jl` `mutate!(..., ::BacksolveMutation, ...)`: `mutgen-bs-success`, `mutgen-bs-restore`.
- `BacksolveMutation` constructor fields: `mutiface-config-fields`.

**Modelling boundary.** Exact rationals (no rounding, overflow, signed zero); `Complex` element types of `STLSQ_DATA_TYPE` and node degrees above 2 are outside the model; `sqrt`, Cholesky, `eval_tree_array`, `compute_complexity` and `hash` are arbitrary functions with stated hypotheses.
