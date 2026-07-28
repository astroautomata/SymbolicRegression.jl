@testitem "Logger receives terminal search state" begin
    using SymbolicRegression

    mutable struct CapturingLogger <: SymbolicRegression.AbstractSRLogger
        cycles_remaining::Vector{Vector{Int}}
    end

    function SymbolicRegression.logging_callback!(logger::CapturingLogger; state, kws...)
        push!(logger.cycles_remaining, copy(state.cycles_remaining))
        return nothing
    end

    X = reshape(Float32.(1:8), 1, :)
    y = @. X[1, :]^2
    options = Options(;
        binary_operators=(+, *),
        populations=1,
        population_size=5,
        ncycles_per_iteration=1,
        tournament_selection_n=2,
        maxsize=5,
        should_optimize_constants=false,
        deterministic=true,
        seed=0,
        verbosity=0,
        progress=false,
    )
    logger = CapturingLogger(Vector{Int}[])

    equation_search(X, y; niterations=1, options, parallelism=:serial, logger)

    @test logger.cycles_remaining == [[0]]

    multi_output_logger = CapturingLogger(Vector{Int}[])
    multi_output_y = vcat(reshape((@. X[1, :]^2), 1, :), reshape((@. X[1, :]^3), 1, :))

    equation_search(
        X,
        multi_output_y;
        niterations=1,
        options,
        parallelism=:serial,
        logger=multi_output_logger,
    )

    @test length(multi_output_logger.cycles_remaining) == 2
    @test sum(first(multi_output_logger.cycles_remaining)) == 1
    @test last(multi_output_logger.cycles_remaining) == [0, 0]
    @test count(all ∘ iszero, multi_output_logger.cycles_remaining) == 1
end

@testitem "SRLogger always emits normal terminal state" begin
    using Logging: SimpleLogger
    using SymbolicRegression

    function count_search_records(io)
        return length(collect(eachmatch(r"search\s*\n\s*│\s*data\s*=", String(take!(io)))))
    end

    X = reshape(Float32.(1:8), 1, :)
    y = @. X[1, :]^2
    options = Options(;
        binary_operators=(+, *),
        populations=1,
        population_size=5,
        ncycles_per_iteration=1,
        tournament_selection_n=2,
        maxsize=5,
        should_optimize_constants=false,
        deterministic=true,
        seed=0,
        verbosity=0,
        progress=false,
    )

    unaligned_io = IOBuffer()
    unaligned_logger = SRLogger(; logger=SimpleLogger(unaligned_io), log_interval=100)
    equation_search(
        X, y; niterations=2, options, parallelism=:serial, logger=unaligned_logger
    )
    @test count_search_records(unaligned_io) == 2

    aligned_io = IOBuffer()
    aligned_logger = SRLogger(; logger=SimpleLogger(aligned_io), log_interval=2)
    equation_search(
        X, y; niterations=3, options, parallelism=:serial, logger=aligned_logger
    )
    @test count_search_records(aligned_io) == 2

    disabled_io = IOBuffer()
    disabled_logger = SRLogger(; logger=SimpleLogger(disabled_io), log_interval=0)
    equation_search(
        X, y; niterations=1, options, parallelism=:serial, logger=disabled_logger
    )
    @test count_search_records(disabled_io) == 0
end
