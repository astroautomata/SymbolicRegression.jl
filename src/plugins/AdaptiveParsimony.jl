module AdaptiveParsimonyPluginModule

using DispatchDoctor: @unstable
using ..CoreModule: AbstractPlugin, AbstractPluginState, AbstractOptions
using ..ComplexityModule: compute_complexity
import ..CoreModule:
    tournament_cost_multiplier,
    mutation_acceptance_multiplier,
    _inject_adaptive_parsimony_plugin

"""
    AdaptiveParsimonyPlugin <: AbstractPlugin

Frequency-weighted parsimony adjustments at two engine decision points:

- `tournament`: when `true`, multiplies tournament-selection cost by
  `exp(adaptive_parsimony_scaling * f)`, where `f` is the recent relative
  frequency of equations at this complexity (tracked by
  `RunningSearchStatistics`). Biases selection against over-represented
  complexities.
- `mutation_acceptance`: when `true`, multiplies the mutation acceptance
  probability by `old_freq / new_freq`. Biases mutation acceptance away
  from over-represented complexities.

Both default to `true`. Equivalent to the legacy
`Options(; use_frequency_in_tournament=true, use_frequency=true)` flags,
which are auto-translated into this plugin during `Options` construction.

!!! warning "Experimental"
    Part of the experimental plugin interface.
"""
Base.@kwdef struct AdaptiveParsimonyPlugin <: AbstractPlugin
    tournament::Bool = true
    mutation_acceptance::Bool = true
end

function tournament_cost_multiplier(
    p::AdaptiveParsimonyPlugin,
    ::AbstractPluginState,
    member,
    running_search_statistics,
    options::AbstractOptions,
)
    p.tournament || return 1.0
    size = compute_complexity(member, options)
    frequency = if (0 < size <= options.maxsize)
        Float64(running_search_statistics.normalized_frequencies[size])
    else
        0.0
    end
    return exp(Float64(options.adaptive_parsimony_scaling) * frequency)
end

function mutation_acceptance_multiplier(
    p::AdaptiveParsimonyPlugin,
    ::AbstractPluginState,
    parent_member,
    new_tree,
    running_search_statistics,
    options::AbstractOptions,
)
    p.mutation_acceptance || return 1.0
    old_size = compute_complexity(parent_member, options)
    new_size = compute_complexity(new_tree, options)
    old_frequency = if (0 < old_size <= options.maxsize)
        Float64(running_search_statistics.normalized_frequencies[old_size])
    else
        1e-6
    end
    new_frequency = if (0 < new_size <= options.maxsize)
        Float64(running_search_statistics.normalized_frequencies[new_size])
    else
        1e-6
    end
    return old_frequency / new_frequency
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
