module PluginModule

using DispatchDoctor: @unstable

"""
    AbstractPlugin

Abstract type for a plugin's *configuration*. A plugin instance is an immutable
struct whose fields are the user-tunable settings of the plugin. Mutable
runtime data is held separately in an [`AbstractPluginState`](@ref) returned by
[`init_plugin_state`](@ref).

A search may have **any number of plugins active simultaneously**, supplied
via the `plugins = (Plugin1(), Plugin2(), ...)` keyword on `Options`. The
engine iterates the tuple at each lifecycle point and dispatches the
appropriate hook on the plugin type.

!!! warning "Experimental"
    The plugin interface is experimental. Hook signatures may change in minor
    releases until validated by multiple in-tree plugins.
"""
abstract type AbstractPlugin end

"""
    AbstractPluginState

Abstract type for mutable per-worker plugin state.

Each plugin gets its own state instance per worker via [`init_plugin_state`](@ref).
States hold the mutable runtime data the engine doesn't need to know about
(counters, channels, concept databases, etc.).

**Thread / Multiprocessing Safety**:
- `on_generation_complete!` runs serially on the head node — safe to mutate.
- `on_population_evaluated!` and `on_mutation_evaluated!` run on workers
  concurrently in multithreading mode. Each `(plugin, worker)` slot has its
  own state, so no cross-slot races occur. Cross-worker communication must
  use `Channel` / `RemoteChannel`.
- `init_member` uses the head node's states during initial population
  creation. In multithreading mode, multiple population-creation tasks may
  call it concurrently — keep it read-only or thread-safe.
- In multiprocessing mode, plugin config is serialized to workers (via
  `options.plugins`); worker state is initialized lazily on each worker
  process.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
abstract type AbstractPluginState end

"""
    NoPluginState <: AbstractPluginState

Default no-op plugin state, returned by the fallback `init_plugin_state` when
a plugin doesn't override it.
"""
struct NoPluginState <: AbstractPluginState end

"""
    init_plugin_state(plugin::AbstractPlugin, options, datasets) -> AbstractPluginState

Create the mutable per-worker state for `plugin`. Called once on the head node
(with the full `datasets` vector) and once per worker (with a single-element
tuple `(dataset,)`).

Override by dispatching on your plugin type:

```julia
SymbolicRegression.init_plugin_state(p::MyPlugin, options, datasets) =
    MyPluginState(p.config)
```

If your implementation uses `datasets`, note the type difference: the head
node receives a `Vector{<:Dataset}` while each worker receives a
`Tuple{<:Dataset}`.

Default returns `NoPluginState()`.

!!! warning "Experimental"
"""
function init_plugin_state(::AbstractPlugin, options, datasets)
    return NoPluginState()
end

"""
    init_plugin_states(plugins::Tuple, options, datasets) -> Tuple

Build the parallel tuple of plugin states matching `options.plugins`. The
returned tuple has one entry per plugin, in the same order as
`options.plugins`. Type-stable when the plugin tuple is concretely typed.

Override this only if you need bulk initialization logic that can't be
expressed by per-plugin `init_plugin_state` methods.
"""
@inline function init_plugin_states(plugins::Tuple, options, datasets)
    return map(p -> init_plugin_state(p, options, datasets), plugins)
end

"""
    on_search_start!(plugin, state, datasets, options, ropt)

Lifecycle hook called on the head node after initialization, before warmup
and the main search loop. Called once per plugin, in the order
`options.plugins` was constructed.

Override by dispatching on your plugin type:

```julia
SymbolicRegression.on_search_start!(p::MyPlugin, s::MyPluginState, datasets, options, ropt) = ...
```

Default is a no-op.

!!! warning "Experimental"
"""
function on_search_start!(::AbstractPlugin, ::AbstractPluginState, datasets, options, ropt)
    return nothing
end

"""
    on_search_end!(plugin, state, search_state, datasets, options, ropt)

Lifecycle hook called on the head node after all workers have completed,
before tearing down processes/threads. Called once per plugin.

Override by dispatching on your plugin type. Default is a no-op.

!!! warning "Experimental"
"""
function on_search_end!(
    ::AbstractPlugin, ::AbstractPluginState, search_state, datasets, options, ropt
)
    return nothing
end

"""
    on_generation_complete!(plugin, state, search_state, datasets, options, ropt)

Lifecycle hook called on the HEAD NODE after each generation completes
(after HoF update + migration). Runs serially; safe to mutate plugin state,
update concept databases, drain feedback channels, etc. Called once per
plugin per generation.

Override by dispatching on your plugin type. Default is a no-op.

!!! warning "Experimental"
"""
function on_generation_complete!(
    ::AbstractPlugin, ::AbstractPluginState, search_state, datasets, options, ropt
)
    return nothing
end

"""
    on_population_evaluated!(plugin, state, pop, dataset, hof, options)

Lifecycle hook called on the WORKER after each s_r_cycle finishes. May run
concurrently across workers. Use only worker-local state, or use `Channel` /
`RemoteChannel` for cross-worker communication. Called once per plugin per
worker cycle.

Override by dispatching on your plugin type. Default is a no-op.

!!! warning "Experimental"
"""
function on_population_evaluated!(
    ::AbstractPlugin, ::AbstractPluginState, pop, dataset, hof, options
)
    return nothing
end

"""
    MutationEvent

Bundle of per-mutation observations passed to [`on_mutation_evaluated!`](@ref)
once the accept/reject decision has been made inside `next_generation`.

# Fields

- `mutation_type::Symbol`: the `Symbol` identifying which mutation was
  attempted (e.g. `:mutate_constant`, `:add_node`).
- `accepted::Bool`: `true` if the mutation was accepted (via
  `return_immediately` or annealing/fitness acceptance); `false` if rejected
  (constraint failure, NaN loss, or annealing/frequency rejection).
- `before_loss::Float64`: loss of the parent member before mutation. Always
  finite (members with NaN loss are never propagated into the population).
- `after_loss::Float64`: loss after mutation. `NaN` if no valid evaluation
  occurred (constraint failure or NaN loss). Finite if the mutated tree was
  successfully evaluated — including annealing rejections, where the tree
  was evaluated but the proposal was stochastically rejected. May be `NaN`
  even when `accepted=true` in the `return_immediately` path if the
  returned member has a NaN loss.

`accepted` and `after_loss` carry independent information: annealing
rejection has a finite `after_loss` but `accepted=false`. A plugin can
distinguish "valid tree, probabilistically rejected" from "invalid tree,
never evaluated" by checking `isnan(after_loss)`.

!!! warning "Experimental"
    Fields may be added in minor releases (never removed or renamed).
"""
struct MutationEvent
    mutation_type::Symbol
    accepted::Bool
    before_loss::Float64
    after_loss::Float64
end

"""
    on_mutation_evaluated!(plugin, state, event::MutationEvent, dataset, options)

Lifecycle hook called on the WORKER immediately before each return from
`next_generation`, after the final accept/reject decision for a mutation.
Called once per plugin per mutation.

Use this hook to track per-mutation improvement rates, adapt mutation
weights, or log mutation outcomes.

Override by dispatching on your plugin type:

```julia
SymbolicRegression.on_mutation_evaluated!(
    p::MyPlugin, s::MyPluginState, ev::MutationEvent, dataset, opts,
) = ...
```

Default is a no-op.

!!! warning "Experimental"
"""
function on_mutation_evaluated!(
    ::AbstractPlugin, ::AbstractPluginState, ::MutationEvent, dataset, options
)
    return nothing
end

"""
    tournament_cost_multiplier(plugin, state, member, running_search_statistics, options) -> Real

Per-plugin multiplier applied to a candidate's `member.cost` during tournament
selection in `_best_of_sample`. Plugins compose multiplicatively: the
adjusted cost is `member.cost * ∏ tournament_cost_multiplier(p, s, ...)`
across all plugins in tuple order. Default returns `1.0` (no adjustment).

The shipped `AdaptiveParsimonyPlugin` is the canonical example.

!!! warning "Experimental"
"""
function tournament_cost_multiplier(
    ::AbstractPlugin, ::AbstractPluginState, member, running_search_statistics, options
)
    return 1.0
end

"""
    mutation_acceptance_multiplier(plugin, state, parent_member, new_tree, running_search_statistics, options) -> Real

Per-plugin multiplier applied to `probChange` inside `next_generation`, after
the annealing factor (if any) is folded in. Plugins compose multiplicatively;
defaults to `1.0` (no adjustment).

!!! warning "Experimental"
"""
function mutation_acceptance_multiplier(
    ::AbstractPlugin,
    ::AbstractPluginState,
    parent_member,
    new_tree,
    running_search_statistics,
    options,
)
    return 1.0
end

"""
    init_member(plugin, state, dataset, options)

Called when initializing each population member's tree during **initial
population creation only**. Called per plugin; the first plugin whose hook
returns a non-`nothing` value wins. If all plugins return `nothing`, the
engine falls through to `gen_random_tree`.

Override by dispatching on your plugin type. Default returns `nothing`.

!!! note "State used"
    `init_member` is called with the **head node's** state instance, not a
    per-worker copy. In `:multithreading` mode, multiple population-creation
    tasks may call it concurrently — ensure your implementation is
    thread-safe or limit it to read-only access of the state.

!!! warning "Experimental"
"""
function init_member(::AbstractPlugin, ::AbstractPluginState, dataset, options)
    return nothing
end

@inline invoke_init_member(::Tuple{}, ::Tuple{}, dataset, options) = nothing
@inline function invoke_init_member(plugins::Tuple, states::Tuple, dataset, options)
    candidate = init_member(plugins[1], states[1], dataset, options)
    return if candidate === nothing
        invoke_init_member(Base.tail(plugins), Base.tail(states), dataset, options)
    else
        candidate
    end
end

# Each kwarg → plugin migration gets one forward-declared injector here.
# The plugin module that owns the migration provides the only method
# (necessary because plugin modules live above Core in the include order, so
# Options.jl can't name their plugin types directly). The plugin module
# always loads before any Options is constructed at runtime.
function _inject_adaptive_parsimony_plugin end

end  # module PluginModule
