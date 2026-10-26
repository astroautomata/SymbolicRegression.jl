# Migrating from v1 to v2

SymbolicRegression.jl v2 restructures the internals around a composable
plugin interface, first-class mutation types, and customizable crossover
operations. Almost all v1 code still runs without modification: the
breaking surface is behavioral rather than syntactic. This page lists what
to check when upgrading from v1.13.

## Behavioral changes

Your code will run unchanged, but search results will differ:

- **Adaptive mutation weights are now on by default.** Mutation weights
  adapt over the course of the search via `AdaptiveMutationWeightsPlugin`.
  To recover static v1 weights, choose the default plugin set explicitly:

  ```julia
  Options(;
      default_plugins=(SimulatedAnnealingPlugin(; alpha=3.17), AdaptiveParsimonyPlugin())
  )
  ```

- **`batching` now defaults to `:auto`.** Large datasets are evaluated in
  batches automatically, with `batch_size` chosen for you when not set.
  Restore v1 behavior with `batching=false, batch_size=50`.

- **`crossover_probability` now defaults to `0.20`** (was `0.0259`).

- **Simplification recomputes cost.** After a tree is simplified, its cost
  is recomputed from scratch, so `PopMember.cost` can differ from v1 for an
  equivalent expression.

- **Constant-optimization restarts can now escape zero-valued constants,**
  so optimization trajectories (and therefore results) differ from v1.

All other defaults are unchanged from v1.13.

## Renames (deprecated shims in place)

These still work but emit deprecation warnings:

- `eval_options=` is now `eval_context=` in evaluation entry points.
- `use_recorder`/`recorder_file` are now `use_tracing`/`tracing_file`;
  recorder output is streamed as JSONL traces.
- `PopMember.score` is now `PopMember.cost`.
- camelCase keyword arguments (`mutationWeights`, `useFrequency`,
  `shouldOptimizeConstants`, ...) are deprecated in favor of snake_case.

## Removed

- **`ParametricExpression`** is removed. Use `TemplateExpression` with
  optimizable parameters instead.
- **`Options`, `SearchState`, and `TemplateExpressionSpec` gained type
  parameters**, which changes their concrete type arity. `SearchState`
  also replaces `all_running_search_statistics` with `plugin_states`.
- The internal mutation helpers `delete_random_op!` and `_random_op` were
  generalized to n-ary operators. This only affects code that defines
  custom mutations against internals.

## v1 keyword arguments that still work

These are converted automatically to the new plugin/mutation
configuration, and need no changes:

- `mutation_weights` (including a plain vector via the deprecated
  `mutationWeights` spelling) is converted to weighted first-class
  mutations.
- `annealing` / `alpha` inject a `SimulatedAnnealingPlugin`.
- `use_frequency` / `use_frequency_in_tournament` configure the
  `AdaptiveParsimonyPlugin`.
- `perturbation_factor` / `probability_flip_constant_sign` are applied to the
  default `ConstantMutation`. The deprecated `probability_negate_constant`
  (and `probability_negate` in `ConstantMutation`) still work and mean
  `1 - probability_flip_constant_sign`.

## New APIs

- **Plugins**: `Options(; plugins=(MyPlugin(),))` composes search
  behaviors. See the [Plugins](plugins.md) page for the hook set and a
  worked example.
- **First-class mutations**: pass `mutations=[MutateConstant() => 1.0, ...]`
  or subtype `AbstractMutation`; see [Customization](customization.md).
- **Custom crossovers**: subtype `AbstractCrossover` and pass
  `crossovers=[MyCrossover() => 1.0, ...]`.
- **MLJ-free interface**: `machine`, `fit!`, `predict`, and `report` work
  without loading MLJ.
