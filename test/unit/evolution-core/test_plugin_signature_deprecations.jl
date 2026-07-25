@testitem "Deprecated plugin interface signatures forward to current methods" begin
    using SymbolicRegression
    using SymbolicRegression: Dataset, RecordType
    using SymbolicRegression.AdaptiveParsimonyModule:
        AdaptiveParsimonyState, RunningSearchStatistics
    using SymbolicRegression.MutateModule: next_generation
    using SymbolicRegression.PopulationModule: best_of_sample
    using Random
    using Test

    options = Options(;
        binary_operators=(+, *),
        mutation_weights=(; do_nothing=1e30),
        tournament_selection_n=1,
    )
    dataset = Dataset(randn(2, 16), randn(16))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=false)
    population = Population([member])
    statistics = RunningSearchStatistics(; options)
    plugin_states = (AdaptiveParsimonyState(statistics),)

    Random.seed!(0)
    current_best = best_of_sample(population, options; plugin_states)
    Random.seed!(0)
    deprecated_best = @test_deprecated best_of_sample(population, statistics, options)
    @test deprecated_best.tree == current_best.tree

    Random.seed!(0)
    current_generation = next_generation(
        dataset,
        member,
        1.0,
        options.maxsize,
        options;
        tmp_recorder=RecordType(),
        plugin_states,
    )
    Random.seed!(0)
    deprecated_generation = @test_deprecated next_generation(
        dataset,
        member,
        1.0,
        options.maxsize,
        statistics,
        options;
        tmp_recorder=RecordType(),
    )
    @test deprecated_generation[1].tree == current_generation[1].tree
    @test deprecated_generation[2:3] == current_generation[2:3]
end
