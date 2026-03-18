module PluginModule

using ..OptionsStructModule: AbstractOptions

"""
    AbstractPluginState

Abstract type for mutable per-worker plugin state.

`AbstractPluginState` holds mutable runtime data (concept databases, counters, etc.).
Each worker gets its own instance via `init_plugin_state`. See the
[Plugin Development Guide](@ref) for a full walkthrough.

**Thread / Multiprocessing Safety**:
- `on_generation_complete!` runs serially on the head node — safe to mutate.
- `on_population_evaluated!` runs on workers concurrently in multithreading mode.
  Each `(output, population)` slot has its own state Ref, so no cross-slot races occur.
  Cross-worker communication must use `Channel`.
- `init_member` uses the head node's state during initial population creation.
  In multithreading mode, multiple slots are created concurrently — keep it read-only or thread-safe.
- In multiprocessing mode, plugin config is serialized to workers (via options);
  worker state is initialized lazily on each worker process.

!!! warning "Experimental"
    The plugin interface is experimental. Design is subject to change until validated
    in practice by multiple plugin packages.
"""
abstract type AbstractPluginState end

"""
    NoPluginState <: AbstractPluginState

Default no-op plugin state, used when no plugin is active.
"""
struct NoPluginState <: AbstractPluginState end

"""
    init_plugin_state(options::AbstractOptions, datasets) -> AbstractPluginState

Create mutable plugin state. Called once on the head node (with the full `datasets`
vector) and once per worker (with a single-element tuple `(dataset,)`).

Override by dispatching on your custom options type:

```julia
SymbolicRegression.init_plugin_state(opts::MyOptions, datasets) =
    MyPluginState(opts.config)
```

If your implementation uses `datasets`, note the type difference: the head node
receives a `Vector{<:Dataset}` while each worker receives a `Tuple{<:Dataset}`.

Default returns `NoPluginState()`.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function init_plugin_state(::AbstractOptions, datasets)
    return NoPluginState()
end

"""
    on_search_start!(plugin_state, datasets, options, ropt)

Lifecycle hook called on the head node after initialization, before warmup and the main search loop.

Override by dispatching on your `AbstractPluginState` subtype:

```julia
SymbolicRegression.on_search_start!(s::MyPluginState, datasets, options, ropt) = ...
```

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_search_start!(::AbstractPluginState, datasets, options, ropt)
    return nothing
end

"""
    on_search_end!(plugin_state, search_state, datasets, options, ropt)

Lifecycle hook called on the head node after all workers have completed,
before tearing down processes/threads.

Override by dispatching on your `AbstractPluginState` subtype.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_search_end!(::AbstractPluginState, search_state, datasets, options, ropt)
    return nothing
end

"""
    on_generation_complete!(plugin_state, search_state, datasets, options, ropt)

Lifecycle hook called on the HEAD NODE after each generation completes
(after HoF update + migration). Runs serially; safe to mutate plugin state,
update concept databases, drain feedback channels, etc.

Override by dispatching on your `AbstractPluginState` subtype.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_generation_complete!(::AbstractPluginState, search_state, datasets, options, ropt)
    return nothing
end

"""
    on_population_evaluated!(plugin_state, pop, dataset, hof, options)

Lifecycle hook called on the WORKER after each s_r_cycle finishes.
May run concurrently across workers. Use only worker-local state, or use
`Channel` / `RemoteChannel` for cross-worker communication.

Override by dispatching on your `AbstractPluginState` subtype.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_population_evaluated!(::AbstractPluginState, pop, dataset, hof, options)
    return nothing
end

"""
    init_member(plugin_state, dataset, options)

Called when initializing each population member's tree during **initial population creation only**.

Override by dispatching on your `AbstractPluginState` subtype.

Return an expression tree to override `gen_random_tree`, or `nothing` to use
the default random tree generation.

!!! note "State used"
    `init_member` is called with the **head node's** `AbstractPluginState` instance,
    not a per-worker copy. In `:multithreading` mode, multiple population-creation
    tasks may call it concurrently — ensure your implementation is thread-safe or
    limit it to read-only access of the state.

Default returns `nothing` (falls through to default random tree generation).

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function init_member(::AbstractPluginState, dataset, options)
    return nothing
end

end  # module PluginModule
