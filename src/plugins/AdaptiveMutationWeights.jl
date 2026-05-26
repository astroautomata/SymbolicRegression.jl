module AdaptiveMutationWeightsModule

using DispatchDoctor: @stable
using ..CoreModule:
    AbstractPlugin,
    AbstractPluginState,
    AbstractOptions,
    AbstractMutation,
    Simplify,
    DoNothing,
    MutationEvent
import ..CoreModule:
    init_plugin_state,
    fork_worker_state,
    on_mutation_end!,
    default_adaptive_mutation_weights_plugin
import ..MutateModule: condition_mutation_weights!, _scale_weight!

"""
    AdaptiveMutationWeightsPlugin <: AbstractPlugin

Online-adapt per-mutation weights from the search's own success statistics.
For each mutation kind, the plugin tracks attempts and "strictly improving"
successes (`accepted && after_loss < before_loss`) and adjusts a
multiplicative factor applied to that mutation's base weight, updated each
mutation via an EMA over the smoothed success-ratio with a floor clamp.

Statistics are local to one worker dispatch — no cross-population
aggregation.

# Fields
- `smoothing::Float64 = 0.02`: EMA factor for the multiplier update.
- `floor::Float64 = 0.05`: clamp range for a single mutation's target
  multiplier (`[floor, 1/floor]`). Prevents necessary rare ops from being
  starved.

Mutation kinds excluded from accounting are declared by dispatch on
[`skip_in_adaptive_weights`](@ref); by default `Simplify` and `DoNothing`
are skipped. Define `skip_in_adaptive_weights(::MyMutation) = true` to add
your own.

!!! warning "Experimental"
"""
Base.@kwdef struct AdaptiveMutationWeightsPlugin <: AbstractPlugin
    smoothing::Float64 = 0.02
    floor::Float64 = 0.05
end

"""
    skip_in_adaptive_weights(::AbstractMutation) -> Bool

Whether [`AdaptiveMutationWeightsPlugin`](@ref) should exclude a mutation
kind from its success/attempt accounting. Default `false`. Overridden to
`true` for `Simplify` and `DoNothing` (they accept trivially / don't
represent real search moves).

Extend by dispatch:

```julia
SymbolicRegression.skip_in_adaptive_weights(::MyMutation) = true
```
"""
skip_in_adaptive_weights(::AbstractMutation) = false
skip_in_adaptive_weights(::Simplify) = true
skip_in_adaptive_weights(::DoNothing) = true

"""
    AdaptiveMutationWeightsState <: AbstractPluginState

Per-dispatch (per-worker) mutable counters and multipliers, parallel to
`options.mutations`. Reset at each `fork_worker_state` call.
"""
mutable struct AdaptiveMutationWeightsState <: AbstractPluginState
    attempts::Vector{Float64}
    successes::Vector{Float64}
    multipliers::Vector{Float64}
end

function init_plugin_state(::AdaptiveMutationWeightsPlugin, options, dataset)
    n = length(options.mutations)
    return AdaptiveMutationWeightsState(zeros(n), zeros(n), ones(n))
end

# Fresh stats per worker dispatch (per-population locality; no cross-pop merge).
function fork_worker_state(
    head_state::AdaptiveMutationWeightsState,
    ::AdaptiveMutationWeightsPlugin,
    dataset,
)
    n = length(head_state.multipliers)
    return AdaptiveMutationWeightsState(zeros(n), zeros(n), ones(n))
end

function on_mutation_end!(
    s::AdaptiveMutationWeightsState,
    p::AdaptiveMutationWeightsPlugin,
    mutation::AbstractMutation,
    event::MutationEvent,
    dataset,
    options::AbstractOptions,
)
    skip_in_adaptive_weights(mutation) && return nothing
    mutations = options.mutations
    idx = findfirst(pair -> typeof(pair.first) === typeof(mutation), mutations)
    idx === nothing && return nothing
    s.attempts[idx] += 1.0
    if event.accepted && event.after_loss < event.before_loss
        s.successes[idx] += 1.0
    end
    # Recompute multipliers from current rates.
    rates = (s.successes .+ 1.0) ./ (s.attempts .+ 2.0)
    mean_rate = sum(s.successes .+ 1.0) / sum(s.attempts .+ 2.0)
    f = p.floor
    upper = f > 0 ? inv(f) : Inf
    @inbounds for i in eachindex(s.multipliers)
        target = clamp(rates[i] / mean_rate, f, upper)
        s.multipliers[i] = (1 - p.smoothing) * s.multipliers[i] + p.smoothing * target
    end
    return nothing
end

function condition_mutation_weights!(
    weights::AbstractVector,
    s::AdaptiveMutationWeightsState,
    ::AdaptiveMutationWeightsPlugin,
    member,
    options::AbstractOptions,
    curmaxsize,
    nfeatures,
)
    mutations = options.mutations
    @inbounds for i in eachindex(mutations)
        m, w = weights[i]
        weights[i] = m => w * s.multipliers[i]
    end
    return nothing
end

@stable(
    default_union_limit = 2,
    function default_adaptive_mutation_weights_plugin(;
        adaptive_mutation_weights::Bool,
        adaptive_mutation_smoothing::Real,
        adaptive_mutation_floor::Real,
    )
        adaptive_mutation_weights || return nothing
        return AdaptiveMutationWeightsPlugin(;
            smoothing=Float64(adaptive_mutation_smoothing),
            floor=Float64(adaptive_mutation_floor),
        )
    end
)

end  # module AdaptiveMutationWeightsModule
