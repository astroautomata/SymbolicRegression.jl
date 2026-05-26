module MutationRetryModule

using DispatchDoctor: @unstable
using ..CoreModule: AbstractPlugin, AbstractPluginState
import ..CoreModule: wrap_mutation_step

"""
    MutationRetryPlugin(; attempts=4)

Retry the per-cycle `next_generation` call up to `attempts` total times
when the previous attempt was rejected (matches PySR p026: bounded
mutation retry). Each retry re-samples the mutation kind against the
**original** parent.

Implemented as middleware on [`wrap_mutation_step`](@ref) — runs the inner
thunk up to `attempts` times, breaking on the first accepted result.

`attempts = 1` reproduces upstream behavior.

!!! warning "Experimental"
"""
Base.@kwdef struct MutationRetryPlugin <: AbstractPlugin
    attempts::Int = 4
end

@unstable function wrap_mutation_step(
    ::AbstractPluginState, p::MutationRetryPlugin, parent_member, next_step::F
) where {F}
    member, accepted, num_evals = next_step(parent_member)
    for _ in 2:(p.attempts)
        accepted && break
        new_member, new_accepted, new_evals = next_step(parent_member)
        num_evals += new_evals
        member, accepted = new_member, new_accepted
    end
    return member, accepted, num_evals
end

end  # module MutationRetryModule
