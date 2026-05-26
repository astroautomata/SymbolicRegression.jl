module SimulatedAnnealingModule

using DispatchDoctor: @stable, @unstable
using ..CoreModule:
    AbstractPlugin,
    AbstractPluginState,
    AbstractOptions,
    MutateConstant,
    MutateConstantContext
import ..CoreModule:
    init_plugin_state,
    on_cycle_start!,
    condition_mutation!,
    mutation_acceptance_multiplier,
    default_simulated_annealing_plugin

"""
    SimulatedAnnealingPlugin(; alpha=0.1)

Couple the search's mutation pipeline to a temperature schedule that
sweeps linearly from `1.0` at the first cycle of an iteration to `0.0` at
the last. The plugin uses its current temperature for two things:

1. **Constant-perturbation magnitude**: via [`condition_mutation!`](@ref)
   on [`MutateConstantContext`](@ref), the plugin scales the per-call
   `perturbation_factor` by the current temperature, so constants are
   perturbed less near the end of an iteration.
2. **Mutation acceptance**: via [`mutation_acceptance_multiplier`](@ref),
   the plugin contributes `exp(-(after_cost - before_cost) / (T * alpha))`
   to the engine's combined accept probability — multiple plugins'
   multipliers compose against a single rand draw so the legacy
   `annealing × frequency_parsimony` semantics are preserved.

The "temperature" concept is entirely local to this plugin's mutable
state; nothing else in the engine references it.

!!! warning "Experimental"
"""
Base.@kwdef struct SimulatedAnnealingPlugin <: AbstractPlugin
    alpha::Float64 = 0.1
end

"""
    SimulatedAnnealingState

Per-output mutable state for [`SimulatedAnnealingPlugin`](@ref). `temperature`
is recomputed each cycle by [`on_cycle_start!`](@ref) and read by the
plugin's other hooks.
"""
mutable struct SimulatedAnnealingState <: AbstractPluginState
    temperature::Float64
end

init_plugin_state(::SimulatedAnnealingPlugin, options, dataset) =
    SimulatedAnnealingState(1.0)

function on_cycle_start!(
    s::SimulatedAnnealingState,
    ::SimulatedAnnealingPlugin,
    cycle_idx::Int,
    options::AbstractOptions,
)
    n = options.ncycles_per_iteration
    s.temperature = n > 1 ? (n - cycle_idx) / (n - 1) : 1.0
    return nothing
end

function condition_mutation!(
    ctx::MutateConstantContext,
    s::SimulatedAnnealingState,
    ::SimulatedAnnealingPlugin,
    ::MutateConstant,
    options::AbstractOptions,
)
    ctx.perturbation_factor *= s.temperature
    return nothing
end

function mutation_acceptance_multiplier(
    s::SimulatedAnnealingState,
    p::SimulatedAnnealingPlugin,
    parent_member,
    new_tree,
    before_cost,
    after_cost,
    options::AbstractOptions,
)
    delta = after_cost - before_cost
    return exp(-delta / (s.temperature * p.alpha))
end

@stable(
    default_union_limit = 2,
    function default_simulated_annealing_plugin(; annealing::Bool, alpha::Real)
        annealing || return nothing
        return SimulatedAnnealingPlugin(; alpha=Float64(alpha))
    end
)

end  # module SimulatedAnnealingModule
