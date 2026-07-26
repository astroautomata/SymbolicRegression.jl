using Base: @deprecate

import .LossFunctionsModule: score_func
import .HallOfFameModule: calculate_pareto_frontier
import .MutationFunctionsModule: gen_random_tree, gen_random_tree_fixed_size
import .MutateModule: next_generation
import .PopulationModule: best_of_sample
using .AdaptiveParsimonyModule: AdaptiveParsimonyState, RunningSearchStatistics

@deprecate(
    next_generation(
        dataset,
        member,
        temperature,
        curmaxsize::Int,
        running_search_statistics::RunningSearchStatistics,
        options::AbstractOptions;
        tmp_recorder::RecordType,
        population_for_backsolve=nothing,
    ),
    next_generation(
        dataset,
        member,
        temperature,
        curmaxsize,
        options;
        tmp_recorder,
        plugin_states=(AdaptiveParsimonyState(running_search_statistics),),
        population_for_backsolve,
    ),
)
@deprecate(
    best_of_sample(
        pop::Population,
        running_search_statistics::RunningSearchStatistics,
        options::AbstractOptions,
    ),
    best_of_sample(
        pop, options; plugin_states=(AdaptiveParsimonyState(running_search_statistics),)
    ),
)

@deprecate(
    score_func(
        dataset::Dataset{T,L},
        member,
        options::AbstractOptions;
        complexity::Union{Int,Nothing}=nothing,
    ) where {T<:DATA_TYPE,L<:LOSS_TYPE},
    eval_cost(dataset, member, options; complexity),
)
@deprecate(
    calculate_pareto_frontier(X, y, hallOfFame, options; weights=nothing),
    calculate_pareto_frontier(hallOfFame)
)
@deprecate(
    calculate_pareto_frontier(dataset, hallOfFame, options),
    calculate_pareto_frontier(hallOfFame)
)

@deprecate(
    EquationSearch(X::AbstractMatrix{T1}, y::AbstractMatrix{T2}; kw...) where {T1,T2},
    equation_search(X, y; kw...)
)

@deprecate(
    EquationSearch(X::AbstractMatrix{T1}, y::AbstractVector{T2}; kw...) where {T1,T2},
    equation_search(X, y; kw...)
)

@deprecate(EquationSearch(dataset::Dataset; kws...), equation_search(dataset; kws...),)

@deprecate(
    EquationSearch(
        X::AbstractMatrix{T},
        y::AbstractMatrix{T};
        niterations::Int=10,
        weights::Union{AbstractMatrix{T},AbstractVector{T},Nothing}=nothing,
        variable_names::Union{Vector{String},Nothing}=nothing,
        options::AbstractOptions=Options(),
        parallelism=:multithreading,
        numprocs::Union{Int,Nothing}=nothing,
        procs::Union{Vector{Int},Nothing}=nothing,
        addprocs_function::Union{Function,Nothing}=nothing,
        runtests::Bool=true,
        saved_state=nothing,
        loss_type::Type=Nothing,
        # Deprecated:
        multithreaded=nothing,
    ) where {T<:DATA_TYPE},
    equation_search(
        X,
        y;
        niterations,
        weights,
        variable_names,
        options,
        parallelism,
        numprocs,
        procs,
        addprocs_function,
        runtests,
        saved_state,
        loss_type,
        multithreaded,
    )
)

@deprecate(
    EquationSearch(
        datasets::Vector{D};
        niterations::Int=10,
        options::AbstractOptions=Options(),
        parallelism=:multithreading,
        numprocs::Union{Int,Nothing}=nothing,
        procs::Union{Vector{Int},Nothing}=nothing,
        addprocs_function::Union{Function,Nothing}=nothing,
        runtests::Bool=true,
        saved_state=nothing,
    ) where {T<:DATA_TYPE,L<:LOSS_TYPE,D<:Dataset{T,L}},
    equation_search(
        datasets;
        niterations,
        options,
        parallelism,
        numprocs,
        procs,
        addprocs_function,
        runtests,
        saved_state,
    )
)
