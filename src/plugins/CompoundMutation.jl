module CompoundMutationModule

using DispatchDoctor: @unstable
using ..CoreModule: AbstractPlugin, AbstractPluginState
import ..CoreModule: wrap_mutation_step

"""
    CompoundMutationPlugin(; probability=0.25, max_steps=2)

After a successful mutation, with probability `probability` run another
ordinary mutation step on the resulting tree (matches PySR p108: compound
mutation burst). Total mutation steps in one generation are bounded by
`max_steps`.

Implemented as middleware on [`wrap_mutation_step`](@ref) — after an
accepted result, calls the inner thunk again (using the result as new
parent) while a probability roll passes and `max_steps` isn't reached.

`probability = 0` reproduces upstream single-step behavior.

!!! warning "Experimental"
"""
Base.@kwdef struct CompoundMutationPlugin <: AbstractPlugin
    probability::Float64 = 0.25
    max_steps::Int = 2
end

@unstable function wrap_mutation_step(
    ::AbstractPluginState, p::CompoundMutationPlugin, parent_member, next_step::F
) where {F}
    member, accepted, num_evals = next_step(parent_member)
    steps = 1
    while accepted && steps < p.max_steps && rand() < p.probability
        chained, chain_accepted, chain_evals = next_step(member)
        num_evals += chain_evals
        chain_accepted || break
        member = chained
        steps += 1
    end
    return member, accepted, num_evals
end

end  # module CompoundMutationModule
