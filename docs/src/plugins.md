# Plugins

Plugins let you hook into the search loop without modifying SymbolicRegression.jl itself.
A plugin is a small struct that opts into lifecycle hooks: observing mutations,
biasing selection, injecting initial population members, or tracking statistics
across generations.

## How the search works

The search maintains multiple **populations** of candidate expressions, evolved
in parallel. Each population runs on a **worker** (a thread or process);
a single **head node** coordinates them.

A **cycle** is one round of evolution on a single population. Within a cycle,
the engine runs many steps: each step picks a random member via **tournament
selection** (sample a few members, keep the one with the lowest cost), mutates
it, and decides whether to accept the result. The **cost** used in tournament
selection combines the raw loss with a complexity penalty.

After a cycle finishes, the worker sends its updated population back to the
head node. The head node merges results, updates the hall of fame, and
dispatches the next cycle. Plugins can hook into any of these stages. Note:
`on_generation_end!` fires on the head when a completed cycle is received
(not per inner step), while `on_cycle_end!` fires on the worker at the end
of its cycle.

## Using a plugin

Pass plugin instances to `Options` via the `plugins` keyword:

```julia
using SymbolicRegression

options = Options(;
    binary_operators=[+, -, *, /],
    unary_operators=[cos],
    plugins=(AdaptiveParsimonyPlugin(; tournament=true, mutation_acceptance=true),),
)
```

Multiple plugins compose. The engine iterates the tuple at each lifecycle point
and dispatches the appropriate hook on each plugin type.

[`AdaptiveParsimonyPlugin`](@ref) ships with the package and is enabled by
default. It biases tournament selection and mutation acceptance away from
over-represented complexities, using a sliding window of recent equation
frequencies.

[`AdaptiveMutationWeightsPlugin`](@ref) is also enabled by default. It learns
relative mutation weights from successful search moves, with the learned
multipliers regularized halfway toward the configured weights in log space.
Pass `default_plugins=()` to `Options` to disable automatic plugins.

## Writing a custom plugin

Define a struct that subtypes [`AbstractPlugin`](@ref), then override whichever
hooks you need. The struct holds immutable configuration; mutable runtime state
lives in a separate object returned by [`init_plugin_state`](@ref).

See the [Writing a Custom Plugin](examples/plugin_tutorial.md) tutorial for a
complete walkthrough that builds a plugin from scratch.

## Lifecycle hooks

Every hook dispatches on your plugin type. Default implementations are no-ops
(or return `1.0` for multipliers, `nothing` for factories). Override only what
you need.

Hooks fall into four categories:

| Category    | Name shape                 | Contract                                            |
| ----------- | -------------------------- | --------------------------------------------------- |
| Observer    | `on_X_start!`, `on_X_end!` | Engine fires, plugin reacts. Return value ignored.  |
| Multiplier  | `X_multiplier`             | Returns a `Real`. Plugins compose multiplicatively. |
| Conditioner | `condition_X!`             | Mutates a passed struct in place.                   |
| Factory     | `init_X`                   | Called once per (plugin, output) at startup.        |

### Initialization and teardown

```@docs
init_plugin_state
fork_plugin_state
refresh_worker_plugin_state
on_search_start!
on_search_end!
```

### Per-generation and per-cycle

```@docs
on_generation_end!
on_cycle_start!
on_cycle_end!
on_mutation_end!
MutationEvent
```

### Selection and acceptance biases

```@docs
tournament_cost_multiplier
mutation_acceptance_multiplier
```

### Mutation conditioning

```@docs
prepare_mutation_context
condition_mutation!
```

[`condition_mutation_weights!`](@ref) is a related hook that modifies the
mutation weight vector before sampling. See the [Customization](customization.md)
page for its full docstring.

### Operation defaults

Plugins may contribute weighted mutation and crossover defaults. Explicit
entries in `Options(; mutations=..., crossovers=...)` take precedence.

```@docs
plugin_mutations
plugin_crossovers
```

### Population seeding

```@docs
init_member
```

## Thread and process safety

- `on_generation_end!` runs serially on the head node. Safe to mutate state.
- `on_cycle_end!` and `on_mutation_end!` run on workers against per-dispatch
  copies built by `fork_plugin_state`. Cross-worker communication requires
  `Channel` / `RemoteChannel`.
- `init_member` reads head-node state. In multithreading mode, multiple
  population-creation tasks may call it concurrently, so keep it read-only
  or thread-safe.

## Dispatching on mutation type

`on_mutation_end!` receives the mutation as a typed argument. You can write
specific methods for individual mutation types:

```julia
function SymbolicRegression.on_mutation_end!(
    state::MyState,
    ::MyPlugin,
    ::ConstantMutation,
    event::MutationEvent,
    dataset,
    options,
)
    # handle constant mutations specifically
end
```

Available mutation types: `ConstantMutation`, `OperatorMutation`,
`FeatureMutation`, `SwapOperandsMutation`, `AddNodeMutation`,
`InsertNodeMutation`, `DeleteNodeMutation`, `FormConnectionMutation`,
`BreakConnectionMutation`, `RotateTreeMutation`, `BacksolveMutation`,
`SimplifyMutation`, `RandomizeMutation`, `OptimizeMutation`,
`DoNothingMutation`.

## Built-in plugins

```@docs
AdaptiveParsimonyPlugin
AdaptiveMutationWeightsPlugin
SimulatedAnnealingPlugin
MutationBurstPlugin
```

## Abstract type

```@docs
AbstractPlugin
```
