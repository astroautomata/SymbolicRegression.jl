module PluginModule

using DispatchDoctor: @unstable
using ..MutationsModule: AbstractMutation

# ────────────────────────────────────────────────────────────────────────────
# Hook naming taxonomy
# ────────────────────────────────────────────────────────────────────────────
#
# All plugin hooks belong to one of six categories. The name's verb/suffix
# tells you the contract; the docstring tells you the semantics.
#
#   `on_X_start!` / `on_X_end!`   — Observer. Engine fires; plugin reacts.
#                                   Return value ignored. `!` because state
#                                   may mutate. Composes by iteration.
#
#   `X_multiplier`                — Multiplier. Returns a `Real` the engine
#                                   multiplies into a base value. Reads like
#                                   a Julia getter (`length`, `size`). Plugins
#                                   compose multiplicatively in tuple order.
#
#   `condition_X!`                — Conditioner. Mutates a passed struct in
#                                   place. Engine layers plugin conditioning
#                                   on top of its own. Composes by sequential
#                                   in-place mutation in tuple order.
#
#   `decide_X`                    — Decider. Returns a `Symbol` / enum the
#                                   engine acts on. Composes by precedence:
#                                   first non-default response in tuple order
#                                   wins. Use for control-flow forks.
#
#   `init_X`                      — Factory (one-time). Called once per
#                                   (plugin, output) at startup. Returns a
#                                   new instance.
#
#   `prepare_X`                   — Factory (per-context). Called per dispatch
#                                   with the dataset. Returns a new instance
#                                   for the worker.
#
# When adding a new hook: pick a category, follow the verb shape. If the name
# feels ambiguous, the contract probably isn't one of these six — rethink
# whether you need a new category or are forcing the feature into the wrong
# shape.
#
# ── Hook argument-order convention ──────────────────────────────────────────
#
# All hooks follow the same positional convention:
#
#     (mutated_thing_if_any, state, plugin, ...other_context)
#
# - For `!` functions that mutate one specific thing (e.g.
#   `condition_X!(X, ...)`), the mutated thing is the FIRST arg, then
#   `state`, then `plugin`.
# - For observer `on_X_end!` hooks, the state is the mutated thing, so
#   ordering is `(state, plugin, ...)`.
# - For non-`!` hooks that read state without mutating (`*_multiplier`,
#   `init_member`, etc.), ordering is still `(state, plugin, ...)`.
# - For constructor hooks that *create* a state (`init_plugin_state`) — no
#   state exists yet, so plugin is the dispatch key and goes first.
#
# The verb/suffix in the name + this ordering rule together ARE the contract.
# ────────────────────────────────────────────────────────────────────────────

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

Abstract type for mutable per-output plugin state.

Each (plugin, output) pair gets its own state instance via
[`init_plugin_state`](@ref). States hold the mutable runtime data the engine
doesn't need to know about (counters, channels, concept databases, etc.).

**Thread / Multiprocessing Safety**:
- `on_generation_end!` runs serially on the head node — safe to mutate.
- `on_cycle_end!` and `on_mutation_end!` run on workers, against per-dispatch
  copies built by [`fork_worker_state`](@ref). Cross-worker
  communication must use `Channel` / `RemoteChannel`.
- `init_member` reads the head node's per-output state during initial
  population creation. In multithreading mode, multiple population-creation
  tasks may call it concurrently — keep it read-only or thread-safe.
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
    init_plugin_state(plugin::AbstractPlugin, options, dataset) -> AbstractPluginState

Create the mutable per-output state for `plugin`. Called once per
(plugin, output) pair at search start.

Override by dispatching on your plugin type:

```julia
SymbolicRegression.init_plugin_state(p::MyPlugin, options, dataset) =
    MyPluginState(p.config)
```

Default returns `NoPluginState()`.

!!! warning "Experimental"
"""
function init_plugin_state(::AbstractPlugin, options, dataset)
    return NoPluginState()
end

"""
    on_search_start!(plugin, state, dataset, options, ropt)

Lifecycle hook called on the head node after initialization, before warmup
and the main search loop. Called once per (plugin, output) pair.

Override by dispatching on your plugin type:

```julia
SymbolicRegression.on_search_start!(p::MyPlugin, s::MyPluginState, dataset, options, ropt) = ...
```

Default is a no-op.

!!! warning "Experimental"
"""
function on_search_start!(::AbstractPluginState, ::AbstractPlugin, dataset, options, ropt)
    return nothing
end

"""
    on_search_end!(plugin, state, search_state, dataset, options, ropt)

Lifecycle hook called on the head node after all workers have completed,
before tearing down processes/threads. Called once per (plugin, output) pair.

Override by dispatching on your plugin type. Default is a no-op.

!!! warning "Experimental"
"""
function on_search_end!(
    ::AbstractPluginState, ::AbstractPlugin, search_state, dataset, options, ropt
)
    return nothing
end

"""
    on_generation_end!(plugin, state, search_state, dataset, options, ropt, returned_pop)

Lifecycle hook called on the HEAD NODE after each cycle's result has been
received from a worker. Runs serially; safe to mutate plugin state, update
concept databases, drain feedback channels, etc. Called once per (plugin,
output) pair per cycle. `state` is this output's state; `returned_pop` is
the population the worker produced.

Override by dispatching on your plugin type. Default is a no-op.

!!! warning "Experimental"
"""
function on_generation_end!(
    ::AbstractPluginState,
    ::AbstractPlugin,
    search_state,
    dataset,
    options,
    ropt,
    returned_pop,
)
    return nothing
end

"""
    on_cycle_end!(plugin, state, pop, dataset, hof, options)

Lifecycle hook called on the WORKER after each s_r_cycle finishes. May run
concurrently across workers. Use only worker-local state, or use `Channel` /
`RemoteChannel` for cross-worker communication. Called once per plugin per
worker cycle.

Override by dispatching on your plugin type. Default is a no-op.

!!! warning "Experimental"
"""
function on_cycle_end!(::AbstractPluginState, ::AbstractPlugin, pop, dataset, hof, options)
    return nothing
end

"""
    MutationEvent

Bundle of per-mutation observations passed to [`on_mutation_end!`](@ref)
once the accept/reject decision has been made inside `next_generation`.

# Fields

- `accepted::Bool`: `true` if the mutation was accepted (via
  `return_immediately` or annealing/fitness acceptance); `false` if rejected
  (constraint failure, NaN loss, or annealing/frequency rejection).
- `before_loss::L`: loss of the parent member before mutation.
- `after_loss::L`: loss after mutation. `NaN` if no valid evaluation
  occurred (constraint failure or NaN loss).

`L` is the dataset's loss type (e.g. `Float32` or `Float64`).

The mutation kind itself is passed as a separate dispatch arg to
[`on_mutation_end!`](@ref), not stored on the event — that way plugin
authors can write type-specific methods.

!!! warning "Experimental"
"""
struct MutationEvent{L<:Real}
    accepted::Bool
    before_loss::L
    after_loss::L
end

"""
    on_mutation_end!(plugin, state, mutation::AbstractMutation, event::MutationEvent, dataset, options)

Lifecycle hook called on the WORKER immediately before each return from
`next_generation`, after the final accept/reject decision for a mutation.
Called once per plugin per mutation. Plugins can dispatch on the mutation
type (e.g. `::MutateConstant`) for type-specific handling, or
`::AbstractMutation` for a generic catch-all.

Default is a no-op.

!!! warning "Experimental"
"""
function on_mutation_end!(
    ::AbstractPluginState,
    ::AbstractPlugin,
    ::AbstractMutation,
    ::MutationEvent,
    dataset,
    options,
)
    return nothing
end

"""
    tournament_cost_multiplier(state, plugin, member, options) -> Real

Per-plugin multiplier applied to a candidate's `member.cost` during tournament
selection in `_best_of_sample`. Plugins compose multiplicatively: the
adjusted cost is `member.cost * ∏ tournament_cost_multiplier(s, p, ...)`
across all plugins in tuple order. Default returns `1.0` (no adjustment).

The shipped `AdaptiveParsimonyPlugin` is the canonical example; it reads
frequency statistics from its own state, not from an engine-passed arg.

!!! warning "Experimental"
"""
function tournament_cost_multiplier(
    ::AbstractPluginState, ::AbstractPlugin, member, options
)
    return 1.0
end

"""
    mutation_acceptance_multiplier(state, plugin, parent_member, new_tree, options) -> Real

Per-plugin multiplier applied to `probChange` inside `next_generation`, after
the annealing factor (if any) is folded in. Plugins compose multiplicatively;
defaults to `1.0` (no adjustment).

!!! warning "Experimental"
"""
function mutation_acceptance_multiplier(
    ::AbstractPluginState, ::AbstractPlugin, parent_member, new_tree, options
)
    return 1.0
end

"""
    fork_worker_state(head_state, plugin, dataset) -> AbstractPluginState

Build the worker-side plugin state for one cycle's dispatch, given the head
node's current plugin state for this output and the dataset the worker will
operate on. Called once per (plugin, output) pair per cycle dispatch.

Default returns `deepcopy(head_state)` (full snapshot).

!!! warning "Experimental"
"""
function fork_worker_state(head_state::AbstractPluginState, ::AbstractPlugin, dataset)
    return deepcopy(head_state)
end

"""
    init_member(state, plugin, dataset, options)

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
function init_member(::AbstractPluginState, ::AbstractPlugin, dataset, options)
    return nothing
end

# `Base.tail` recursion (vs a `for` loop) so heterogeneous tuples are walked
# type-stably with early exit on the first non-`nothing` candidate.
@inline invoke_init_member(::Tuple{}, ::Tuple{}, dataset, options) = nothing
@inline function invoke_init_member(states::Tuple, plugins::Tuple, dataset, options)
    candidate = init_member(states[1], plugins[1], dataset, options)
    return if candidate === nothing
        invoke_init_member(Base.tail(states), Base.tail(plugins), dataset, options)
    else
        candidate
    end
end

"""
    wrap_mutation_step(state, plugin, parent_member, next_step) -> (member, accepted, num_evals)

Middleware-style hook around `next_generation`. The engine builds a thunk
`next_step(parent) -> (member, accepted, num_evals)` that runs one call to
`next_generation` against `parent`. The plugin may call `next_step` zero,
one, or many times — with the original parent (retry), with the previous
result (chain), with a different member (ensemble), or skip it entirely.
It returns the final tuple to its caller.

Plugins compose as nested middleware in `options.plugins` order:
plugin 1's `wrap` wraps plugin 2's wrap wraps... wraps `next_generation`.
Plugin 1 sees the composed behavior of plugins 2+ as `next_step`. Use this
shape for retry, compound bursts, MCMC-style acceptance criteria,
ensemble voting, or any control-flow extension that needs to call
`next_generation` more than once per cycle.

Default is a single pass-through: `next_step(parent_member)`.

!!! warning "Experimental"
"""
@unstable function wrap_mutation_step(
    ::AbstractPluginState, ::AbstractPlugin, parent_member, next_step::F
) where {F}
    return next_step(parent_member)
end

# Forward-declared per kwarg→plugin migration. Plugin modules (loaded above
# Core) provide the only method. Each returns either a plugin instance or
# `nothing` (when the legacy kwarg is off).
function default_adaptive_parsimony_plugin end
function default_adaptive_mutation_weights_plugin end
function default_mutation_retry_plugin end
function default_compound_mutation_plugin end

# Append defaults whose type isn't already in the user tuple. Each default
# may be `nothing` (auto-injected plugin disabled by the legacy kwarg) and
# is filtered out.
@unstable function _merge_with_default_plugins(
    @nospecialize(user_plugins::Tuple), @nospecialize(default_plugins...)
)
    actual_defaults = filter(!isnothing, default_plugins)
    novel = filter(dp -> !any(p -> p isa typeof(dp), user_plugins), actual_defaults)
    return (user_plugins..., novel...)
end

end  # module PluginModule
