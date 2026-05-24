module AdaptiveParsimonyPluginModule

using DispatchDoctor: @unstable
using ..CoreModule: AbstractPlugin, AbstractPluginState, AbstractOptions
using ..ComplexityModule: compute_complexity
using ..AdaptiveParsimonyModule:
    RunningSearchStatistics,
    update_frequencies!,
    move_window!,
    normalize_frequencies!
import ..CoreModule:
    init_plugin_state,
    prepare_dispatch_state,
    tournament_cost_multiplier,
    mutation_acceptance_multiplier,
    on_generation_end!,
    _inject_adaptive_parsimony_plugin

"""
    AdaptiveParsimonyPlugin <: AbstractPlugin

Frequency-weighted parsimony adjustments at two engine decision points:

- `tournament`: when `true`, multiplies tournament-selection cost by
  `exp(adaptive_parsimony_scaling * f)`, where `f` is the recent relative
  frequency of equations at this complexity. Biases selection against
  over-represented complexities.
- `mutation_acceptance`: when `true`, multiplies the mutation acceptance
  probability by `old_freq / new_freq`. Biases mutation acceptance away
  from over-represented complexities.

Both default to `true`. Frequency statistics are tracked **per output**
(per dataset in multi-target regression), so different outputs don't
interfere with each other's complexity distributions. Equivalent to the
legacy `Options(; use_frequency_in_tournament=true, use_frequency=true)`
flags, which are auto-translated into this plugin during `Options`
construction.

!!! warning "Experimental"
    Part of the experimental plugin interface.
"""
Base.@kwdef struct AdaptiveParsimonyPlugin <: AbstractPlugin
    tournament::Bool = true
    mutation_acceptance::Bool = true
end

"""
    AdaptiveParsimonyState <: AbstractPluginState

Mutable per-plugin state for [`AdaptiveParsimonyPlugin`](@ref). Holds a
vector of `RunningSearchStatistics` instances, one per output.

On the head node, `rss` has length `nout` (one slot per dataset). On a
worker, after [`prepare_dispatch_state`](@ref) extracts the relevant
slice, `rss` has length 1 — the worker only ever needs its own output's
statistics.
"""
mutable struct AdaptiveParsimonyState <: AbstractPluginState
    rss::Vector{RunningSearchStatistics}
end

function init_plugin_state(::AdaptiveParsimonyPlugin, options, datasets)
    return AdaptiveParsimonyState([
        RunningSearchStatistics(; options=options) for _ in 1:length(datasets)
    ])
end

@unstable function prepare_dispatch_state(
    ::AdaptiveParsimonyPlugin,
    head_state::AdaptiveParsimonyState,
    output_index::Int,
    dataset,
)
    snapshot = deepcopy(head_state.rss[output_index])
    normalize_frequencies!(snapshot)
    return AdaptiveParsimonyState([snapshot])
end

function tournament_cost_multiplier(
    p::AdaptiveParsimonyPlugin,
    s::AdaptiveParsimonyState,
    member,
    options::AbstractOptions,
)
    p.tournament || return 1.0
    rss = s.rss[1]
    size = compute_complexity(member, options)
    frequency = if (0 < size <= options.maxsize)
        Float64(rss.normalized_frequencies[size])
    else
        0.0
    end
    return exp(Float64(options.adaptive_parsimony_scaling) * frequency)
end

function mutation_acceptance_multiplier(
    p::AdaptiveParsimonyPlugin,
    s::AdaptiveParsimonyState,
    parent_member,
    new_tree,
    options::AbstractOptions,
)
    p.mutation_acceptance || return 1.0
    rss = s.rss[1]
    old_size = compute_complexity(parent_member, options)
    new_size = compute_complexity(new_tree, options)
    old_frequency = if (0 < old_size <= options.maxsize)
        Float64(rss.normalized_frequencies[old_size])
    else
        1e-6
    end
    new_frequency = if (0 < new_size <= options.maxsize)
        Float64(rss.normalized_frequencies[new_size])
    else
        1e-6
    end
    return old_frequency / new_frequency
end

# Head-side per-cycle hook: update frequencies for the returned population's
# output, then slide the window to keep memory bounded.
function on_generation_end!(
    ::AdaptiveParsimonyPlugin,
    s::AdaptiveParsimonyState,
    search_state,
    datasets,
    options,
    ropt,
    output_index::Int,
    returned_pop,
)
    rss = s.rss[output_index]
    for member in returned_pop.members
        size = compute_complexity(member, options)
        update_frequencies!(rss; size=size)
    end
    move_window!(rss)
    return nothing
end

@unstable function _inject_adaptive_parsimony_plugin(
    plugins::Tuple, use_frequency::Bool, use_frequency_in_tournament::Bool
)
    (use_frequency || use_frequency_in_tournament) || return plugins
    any(p -> p isa AdaptiveParsimonyPlugin, plugins) && return plugins
    return (
        plugins...,
        AdaptiveParsimonyPlugin(;
            tournament=use_frequency_in_tournament, mutation_acceptance=use_frequency
        ),
    )
end

export AdaptiveParsimonyPlugin

end  # module AdaptiveParsimonyPluginModule
