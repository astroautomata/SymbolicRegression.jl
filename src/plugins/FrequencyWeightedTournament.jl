module FrequencyWeightedTournamentModule

using ..CoreModule: AbstractPlugin, AbstractPluginState, AbstractOptions
using ..ComplexityModule: compute_complexity
import ..CoreModule: tournament_cost_multiplier, _legacy_plugin_for

"""
    FrequencyWeightedTournamentPlugin <: AbstractPlugin

Multiplies each tournament candidate's `member.cost` by
`exp(adaptive_parsimony_scaling * f)`, where `f` is the relative frequency
of equations at that complexity in the recent search history (tracked by
`RunningSearchStatistics`). Biases tournament selection against
complexities that are over-represented in the current population,
encouraging coverage across the complexity axis.

Equivalent to the legacy `Options(; use_frequency_in_tournament=true)`
flag, which is auto-translated into `plugins = (..., FrequencyWeightedTournamentPlugin(), ...)`
during `Options` construction. Both forms work; passing the plugin
explicitly is preferred going forward.

# Composition

This plugin contributes one multiplicative factor to the tournament cost.
Other plugins (e.g. an age-regularisation plugin) can stack their own
`tournament_cost_multiplier` overloads — factors multiply across plugins
in tuple order.

!!! warning "Experimental"
    Part of the experimental plugin interface.
"""
struct FrequencyWeightedTournamentPlugin <: AbstractPlugin end

function tournament_cost_multiplier(
    ::FrequencyWeightedTournamentPlugin,
    ::AbstractPluginState,
    member,
    running_search_statistics,
    options::AbstractOptions,
)
    size = compute_complexity(member, options)
    frequency = if (0 < size <= options.maxsize)
        Float64(running_search_statistics.normalized_frequencies[size])
    else
        0.0
    end
    return exp(Float64(options.adaptive_parsimony_scaling) * frequency)
end

function _legacy_plugin_for(::Val{:use_frequency_in_tournament})
    FrequencyWeightedTournamentPlugin()
end

export FrequencyWeightedTournamentPlugin

end  # module FrequencyWeightedTournamentModule
