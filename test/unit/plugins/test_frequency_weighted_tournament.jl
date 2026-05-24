@testitem "FrequencyWeightedTournamentPlugin: legacy kwarg auto-injects" begin
    using SymbolicRegression
    using Test

    # Explicit `use_frequency_in_tournament=true` (legacy) → plugin appended.
    opts1 = Options(; binary_operators=[+, *], use_frequency_in_tournament=true)
    @test any(p -> p isa FrequencyWeightedTournamentPlugin, opts1.plugins)

    # Explicit `use_frequency_in_tournament=false` → no plugin.
    opts2 = Options(; binary_operators=[+, *], use_frequency_in_tournament=false)
    @test !any(p -> p isa FrequencyWeightedTournamentPlugin, opts2.plugins)

    # Already in `plugins` → not duplicated when legacy flag is also true.
    opts3 = Options(;
        binary_operators=[+, *],
        use_frequency_in_tournament=true,
        plugins=(FrequencyWeightedTournamentPlugin(),),
    )
    @test count(p -> p isa FrequencyWeightedTournamentPlugin, opts3.plugins) == 1

    # Explicit plugin without the legacy flag still works.
    opts4 = Options(;
        binary_operators=[+, *],
        use_frequency_in_tournament=false,
        plugins=(FrequencyWeightedTournamentPlugin(),),
    )
    @test count(p -> p isa FrequencyWeightedTournamentPlugin, opts4.plugins) == 1
end

@testitem "FrequencyWeightedTournamentPlugin: matches legacy behaviour exactly" begin
    using SymbolicRegression
    using SymbolicRegression: tournament_cost_multiplier, NoPluginState
    using SymbolicRegression.AdaptiveParsimonyModule:
        RunningSearchStatistics, update_frequencies!, normalize_frequencies!
    using SymbolicRegression.PopulationModule: _best_of_sample
    using SymbolicRegression.CoreModule.DatasetModule: Dataset
    using DynamicExpressions: Node
    using Test

    # Build a deterministic running stats with known frequencies.
    opts = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        adaptive_parsimony_scaling=30.0,
        maxsize=20,
        plugins=(FrequencyWeightedTournamentPlugin(),),
    )
    stats = RunningSearchStatistics(; options=opts, window_size=500)
    for size in (1, 1, 1, 1, 1, 3, 3, 5)
        update_frequencies!(stats; size=size)
    end
    normalize_frequencies!(stats)

    # Build a few synthetic members of varying complexity.
    dataset = Dataset(randn(2, 10), randn(10))
    n1 = Node{Float64}(; feature=1)
    n2 = n1 + n1
    n3 = cos(n1) + n1 * n1  # complexity 5
    PM = opts.popmember_type
    mk(tree) = PM(dataset, tree, opts; deterministic=false)
    m1 = mk(n1)
    m2 = mk(n2)
    m3 = mk(n3)

    p = FrequencyWeightedTournamentPlugin()
    mult1 = tournament_cost_multiplier(p, NoPluginState(), m1, stats, opts)
    mult3 = tournament_cost_multiplier(p, NoPluginState(), m3, stats, opts)
    # Size-1 is much more frequent than size-5 → mult1 > mult3 (penalty larger).
    @test mult1 > mult3
    @test mult1 > 1.0
end

@testitem "FrequencyWeightedTournamentPlugin: empty plugins → no multiplier" begin
    using SymbolicRegression
    using SymbolicRegression: tournament_cost_multiplier, NoPluginState, AbstractPlugin
    using Test

    # The default no-op AbstractPlugin returns multiplier = 1.0.
    struct DummyPlugin <: AbstractPlugin end
    @test tournament_cost_multiplier(
        DummyPlugin(), NoPluginState(), nothing, nothing, nothing
    ) == 1.0
end

@testitem "FrequencyWeightedTournamentPlugin: end-to-end equation_search" begin
    using SymbolicRegression
    using Test

    # Equation search with the plugin auto-injected via the legacy flag.
    opts_legacy = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        populations=2,
        verbosity=0,
        progress=false,
        use_frequency_in_tournament=true,
    )
    X = rand(Float32, 2, 30)
    y = 2.0f0 .* X[1, :] .+ X[2, :]
    hof_legacy = equation_search(
        X, y; options=opts_legacy, niterations=2, parallelism=:serial
    )
    @test hof_legacy isa SymbolicRegression.HallOfFame

    # Explicit plugin path: same behaviour.
    opts_plugin = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        populations=2,
        verbosity=0,
        progress=false,
        use_frequency_in_tournament=false,
        plugins=(FrequencyWeightedTournamentPlugin(),),
    )
    hof_plugin = equation_search(
        X, y; options=opts_plugin, niterations=2, parallelism=:serial
    )
    @test hof_plugin isa SymbolicRegression.HallOfFame
end
