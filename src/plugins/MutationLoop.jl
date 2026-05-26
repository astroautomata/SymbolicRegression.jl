module MutationLoopModule

using DispatchDoctor: @stable, @unstable
using ..CoreModule: AbstractPlugin, AbstractPluginState
import ..CoreModule: wrap_mutation_step, default_mutation_loop_plugin

"""
    MutationLoopPlugin(; retry_attempts=4, compound_probability=0.25, compound_max_steps=2)

Per-cycle local-search extensions to the basic single-mutation loop:

- **Retry** (outer): if the engine rejects a mutation, re-run
  `next_generation` against the original parent up to `retry_attempts`
  total times. Break on the first accepted result.
- **Compound burst** (inner): after an accepted mutation, with probability
  `compound_probability` chain another mutation step on the result, up to
  `compound_max_steps` total accepted mutations.

`retry_attempts = 1` disables retry; `compound_probability = 0` disables
compound bursts; the combination reproduces the upstream single-mutation
loop.

Plugin tuple order matters: this plugin should sit OUTSIDE any wrappers
that should fire per next_generation call (e.g. nothing else uses
`wrap_mutation_step` today). The nesting structure intentionally mirrors
PySR's accepted p108 stack: retry is outer, compound is inner.

!!! warning "Extra experimental"
    The retry/compound mechanisms and their composition were validated on
    a single benchmark suite — they may change behavior, defaults, or
    config-knob names in minor releases until exercised more broadly.
"""
Base.@kwdef struct MutationLoopPlugin <: AbstractPlugin
    retry_attempts::Int = 4
    compound_probability::Float64 = 0.25
    compound_max_steps::Int = 2
end

@unstable function wrap_mutation_step(
    ::AbstractPluginState, p::MutationLoopPlugin, parent_member, next_step::F
) where {F}
    # Retry outer.
    member, accepted, num_evals = next_step(parent_member)
    for _ in 2:(p.retry_attempts)
        accepted && break
        m, a, n = next_step(parent_member)
        member, accepted = m, a
        num_evals += n
    end
    accepted || return member, accepted, num_evals
    # Compound inner — only after an accepted retry result.
    n_steps = 1
    while n_steps < p.compound_max_steps && rand() < p.compound_probability
        m, a, n = next_step(member)
        num_evals += n
        a || break
        member = m
        n_steps += 1
    end
    return member, true, num_evals
end

@stable(
    default_union_limit = 2,
    function default_mutation_loop_plugin(;
        mutation_retry_attempts::Int,
        compound_mutation_probability::Real,
        compound_mutation_max_steps::Int,
    )
        if mutation_retry_attempts <= 1 && compound_mutation_probability <= 0
            return nothing
        end
        return MutationLoopPlugin(;
            retry_attempts=mutation_retry_attempts,
            compound_probability=Float64(compound_mutation_probability),
            compound_max_steps=compound_mutation_max_steps,
        )
    end
)

end  # module MutationLoopModule
