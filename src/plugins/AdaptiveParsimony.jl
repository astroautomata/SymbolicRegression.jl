module AdaptiveParsimonyModule

using DispatchDoctor: @stable
using ..CoreModule: AbstractPlugin, AbstractPluginState, AbstractOptions
using ..ComplexityModule: compute_complexity
using ..PopMemberModule: AbstractPopMember
import ..CoreModule:
    init_plugin_state,
    prepare_dispatch_state,
    tournament_cost_multiplier,
    mutation_acceptance_multiplier,
    on_generation_end!,
    default_adaptive_parsimony_plugins

"""
    RunningSearchStatistics

A struct to keep track of various running averages of the search and discovered
equations, for use in adaptive losses and parsimony.

# Fields

- `window_size::Int`: After this many equations are seen, the frequencies are reduced
    by 1, averaged over all complexities, each time a new equation is seen.
- `frequencies::Vector{Float64}`: The number of equations seen at this complexity,
    given by the index.
- `normalized_frequencies::Vector{Float64}`: This is the same as `frequencies`, but
    normalized to sum to 1.0. This is updated once in a while.
"""
struct RunningSearchStatistics
    window_size::Int
    frequencies::Vector{Float64}
    normalized_frequencies::Vector{Float64}  # Stores `frequencies`, but normalized (updated once in a while)
end

function RunningSearchStatistics(; options::AbstractOptions, window_size::Int=100000)
    init_frequencies = ones(Float64, options.maxsize)

    return RunningSearchStatistics(
        window_size, init_frequencies, copy(init_frequencies) / sum(init_frequencies)
    )
end

"""
    update_frequencies!(running_search_statistics::RunningSearchStatistics; size=nothing)

Update the frequencies in `running_search_statistics` by adding 1 to the frequency
for an equation at size `size`.
"""
@inline function update_frequencies!(
    running_search_statistics::RunningSearchStatistics; size=nothing
)
    if 0 < size <= length(running_search_statistics.frequencies)
        running_search_statistics.frequencies[size] += 1
    end
    return nothing
end

"""
    move_window!(running_search_statistics::RunningSearchStatistics)

Reduce `running_search_statistics.frequencies` until it sums to
`window_size`.
"""
function move_window!(running_search_statistics::RunningSearchStatistics)
    smallest_frequency_allowed = 1
    max_loops = 1000

    frequencies = running_search_statistics.frequencies
    window_size = running_search_statistics.window_size

    cur_size_frequency_complexities = sum(frequencies)
    if cur_size_frequency_complexities > window_size
        difference_in_size = cur_size_frequency_complexities - window_size
        # We need frequencyComplexities to be positive, but also sum to a number.
        num_loops = 0
        # TODO: Clean this code up. Should not have to have
        # loop catching.
        while difference_in_size > 0
            indices_to_subtract = findall(frequencies .> smallest_frequency_allowed)
            num_remaining = size(indices_to_subtract, 1)
            amount_to_subtract = min(
                difference_in_size / num_remaining,
                min(frequencies[indices_to_subtract]...) - smallest_frequency_allowed,
            )
            frequencies[indices_to_subtract] .-= amount_to_subtract
            total_amount_to_subtract = amount_to_subtract * num_remaining
            difference_in_size -= total_amount_to_subtract
            num_loops += 1
            if num_loops > max_loops || total_amount_to_subtract < 1e-6
                # Sometimes, total_amount_to_subtract can be a very very small number.
                break
            end
        end
    end
    return nothing
end

function normalize_frequencies!(running_search_statistics::RunningSearchStatistics)
    running_search_statistics.normalized_frequencies .=
        running_search_statistics.frequencies ./ sum(running_search_statistics.frequencies)
    return nothing
end

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

function prepare_dispatch_state(
    head_state::AdaptiveParsimonyState,
    ::AdaptiveParsimonyPlugin,
    output_index::Int,
    dataset,
)
    snapshot = deepcopy(head_state.rss[output_index])::RunningSearchStatistics
    normalize_frequencies!(snapshot)
    return AdaptiveParsimonyState([snapshot])
end

function tournament_cost_multiplier(
    s::AdaptiveParsimonyState,
    p::AdaptiveParsimonyPlugin,
    member::AbstractPopMember{T,L,N},
    options::AbstractOptions,
) where {T,L,N}
    p.tournament || return one(L)
    rss = s.rss[1]
    sz = compute_complexity(member, options)
    frequency = if (0 < sz <= options.maxsize)
        L(rss.normalized_frequencies[sz])
    else
        zero(L)
    end
    return exp(L(options.adaptive_parsimony_scaling) * frequency)
end

function mutation_acceptance_multiplier(
    s::AdaptiveParsimonyState,
    p::AdaptiveParsimonyPlugin,
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
    s::AdaptiveParsimonyState,
    ::AdaptiveParsimonyPlugin,
    search_state,
    datasets,
    options,
    ropt,
    output_index::Int,
    returned_pop,
)
    rss = s.rss[output_index]
    for member in returned_pop.members
        sz = compute_complexity(member, options)
        update_frequencies!(rss; size=sz)
    end
    move_window!(rss)
    return nothing
end

@stable(
    default_union_limit = 2,
    function default_adaptive_parsimony_plugins(;
        use_frequency::Bool, use_frequency_in_tournament::Bool
    )
        (use_frequency || use_frequency_in_tournament) || return ()
        return (
            AdaptiveParsimonyPlugin(;
                tournament=use_frequency_in_tournament, mutation_acceptance=use_frequency,
            ),
        )
    end
)

end  # module AdaptiveParsimonyModule
