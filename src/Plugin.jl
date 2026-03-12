module PluginModule

using ..OptionsStructModule: AbstractOptions

"""
    AbstractPlugin

Abstract type for plugin objects that extend SymbolicRegression.jl behavior.

A plugin is a serializable configuration object. Plugins are stored in an
`AbstractOptions` subtype and retrieved via `get_plugin(options)`. Plugin state
is managed by `AbstractPluginState`, initialized per-worker via `init_plugin_state`.

Plugins provide two layers of extension:

**Layer 1: Algorithm Override via Multiple Dispatch**

Override any exported SR.jl function with `options::AbstractOptions` in its signature
by subclassing `AbstractOptions`:

```julia
# Custom complexity plugin:
function SymbolicRegression.compute_complexity(member, opts::MyOptions)
    return my_complexity_metric(member.tree)
end
```

**Layer 2: Lifecycle Hooks + Persistent State**

For post-generation callbacks, search-level init/teardown, and cross-generation state,
use `AbstractPlugin` + `AbstractPluginState`:

```julia
struct MyPlugin <: AbstractPlugin
    config::Float64
end

mutable struct MyPluginState <: AbstractPluginState
    concept_db::ConceptDB
end

SymbolicRegression.get_plugin(o::MyOptions) = o.plugin
SymbolicRegression.init_plugin_state(p::MyPlugin, datasets, options) =
    MyPluginState(ConceptDB())

function SymbolicRegression.on_generation_complete!(
    p::MyPlugin, state::MyPluginState, search_state, datasets, options, ropt
)
    evolve_concepts!(state.concept_db, search_state.halls_of_fame)
end
```

!!! warning "Experimental"
    The plugin interface is experimental. Design is subject to change until validated
    in practice by multiple plugin packages.
"""
abstract type AbstractPlugin end

"""
    AbstractPluginState

Abstract type for mutable per-worker plugin state.

Unlike `AbstractPlugin` (a stateless config), `AbstractPluginState` holds
mutable runtime data like concept databases or accumulated statistics.
Each worker initializes its own state via `init_plugin_state`.

**Thread / Multiprocessing Safety**:
- `on_generation_complete!` runs serially on the head node — safe to mutate.
- `on_population_evaluated!` and `init_member` run on workers concurrently.
  In multithreading mode, each `(output, population)` slot has its own state Ref,
  so no cross-slot races occur. Cross-worker communication must use `Channel`.
- In multiprocessing mode, plugin config is serialized to workers; worker state
  is initialized lazily on each worker process.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
abstract type AbstractPluginState end

"""
    NoPlugin <: AbstractPlugin

Default no-op plugin. All dispatch paths through `NoPlugin` compile away.
"""
struct NoPlugin <: AbstractPlugin end

"""
    NoPluginState <: AbstractPluginState

Default no-op plugin state, used when no plugin is active.
"""
struct NoPluginState <: AbstractPluginState end

"""
    get_plugin(options::AbstractOptions) -> AbstractPlugin

Retrieve the plugin from an options object. Plugin packages override this
for their custom options type:

```julia
SymbolicRegression.get_plugin(o::MyOptions) = o.plugin
```

Default returns `NoPlugin()`.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
get_plugin(::AbstractOptions) = NoPlugin()

"""
    init_plugin_state(plugin::AbstractPlugin, datasets, options) -> AbstractPluginState

Create mutable plugin state. Called once per worker before search begins.

Override for custom plugins:
```julia
init_plugin_state(p::MyPlugin, datasets, options) = MyPluginState(ConceptDB())
```

Default returns `NoPluginState()`.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function init_plugin_state(::AbstractPlugin, datasets, options)
    return NoPluginState()
end

"""
    on_search_start!(plugin, plugin_state, datasets, options, ropt)

Lifecycle hook called on the head node after initialization, before the main search loop.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_search_start!(
    ::AbstractPlugin, ::AbstractPluginState, datasets, options, ropt
)
    return nothing
end

"""
    on_search_end!(plugin, plugin_state, search_state, datasets, options, ropt)

Lifecycle hook called on the head node before tearing down workers.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_search_end!(
    ::AbstractPlugin, ::AbstractPluginState, search_state, datasets, options, ropt
)
    return nothing
end

"""
    on_generation_complete!(plugin, plugin_state, search_state, datasets, options, ropt)

Lifecycle hook called on the HEAD NODE after each generation completes
(after HoF update + migration). Runs serially; safe to mutate plugin state,
update concept databases, drain feedback channels, etc.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_generation_complete!(
    ::AbstractPlugin, ::AbstractPluginState, search_state, datasets, options, ropt
)
    return nothing
end

"""
    on_population_evaluated!(plugin, plugin_state, pop, dataset, hof, options)

Lifecycle hook called on the WORKER after each s_r_cycle finishes.
May run concurrently across workers. Use only worker-local state, or use
`Channel` / `RemoteChannel` for cross-worker communication.

Default is a no-op.

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function on_population_evaluated!(
    ::AbstractPlugin, ::AbstractPluginState, pop, dataset, hof, options
)
    return nothing
end

"""
    init_member(plugin, plugin_state, dataset, options)

Called when initializing each population member's tree.

Return an expression tree to override `gen_random_tree`, or `nothing` to use
the default random tree generation.

Default returns `nothing` (falls through to default random tree generation).

!!! warning "Experimental"
    The plugin interface is experimental.
"""
function init_member(::AbstractPlugin, ::AbstractPluginState, dataset, options)
    return nothing
end

end  # module PluginModule
