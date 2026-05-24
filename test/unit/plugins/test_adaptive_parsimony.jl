@testitem "AdaptiveParsimonyPlugin: legacy kwargs auto-inject" begin
    using SymbolicRegression
    using Test

    # Both legacy kwargs default to true in master → plugin gets injected
    # with both modes on.
    opts_default = Options(; binary_operators=[+, *])
    plugins = collect(opts_default.plugins)
    @test count(p -> p isa AdaptiveParsimonyPlugin, plugins) == 1
    p = plugins[findfirst(p -> p isa AdaptiveParsimonyPlugin, plugins)]
    @test p.tournament == true
    @test p.mutation_acceptance == true

    # Only one of the two flags on → plugin still injected, only that mode on.
    opts_t = Options(;
        binary_operators=[+, *], use_frequency=false, use_frequency_in_tournament=true
    )
    pt = first(p for p in opts_t.plugins if p isa AdaptiveParsimonyPlugin)
    @test pt.tournament == true
    @test pt.mutation_acceptance == false

    opts_m = Options(;
        binary_operators=[+, *], use_frequency=true, use_frequency_in_tournament=false
    )
    pm = first(p for p in opts_m.plugins if p isa AdaptiveParsimonyPlugin)
    @test pm.tournament == false
    @test pm.mutation_acceptance == true

    # Both off → no plugin injected.
    opts_off = Options(;
        binary_operators=[+, *], use_frequency=false, use_frequency_in_tournament=false
    )
    @test !any(p -> p isa AdaptiveParsimonyPlugin, opts_off.plugins)

    # Explicit plugin passed → not duplicated by legacy injection.
    opts_explicit = Options(;
        binary_operators=[+, *],
        plugins=(AdaptiveParsimonyPlugin(; tournament=false, mutation_acceptance=false),),
        use_frequency=true,
        use_frequency_in_tournament=true,
    )
    plugs = collect(opts_explicit.plugins)
    @test count(p -> p isa AdaptiveParsimonyPlugin, plugs) == 1
    px = plugs[findfirst(p -> p isa AdaptiveParsimonyPlugin, plugs)]
    @test px.tournament == false  # user's instance wins
end

@testitem "AdaptiveParsimonyPlugin: tournament multiplier matches legacy formula" begin
    using SymbolicRegression
    using SymbolicRegression: tournament_cost_multiplier, NoPluginState
    using SymbolicRegression.AdaptiveParsimonyModule:
        RunningSearchStatistics, update_frequencies!, normalize_frequencies!
    using SymbolicRegression.CoreModule.DatasetModule: Dataset
    using DynamicExpressions: Node
    using Test

    opts = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        adaptive_parsimony_scaling=30.0,
        maxsize=20,
        use_frequency=false,
        use_frequency_in_tournament=false,
        plugins=(AdaptiveParsimonyPlugin(; tournament=true, mutation_acceptance=false),),
    )
    stats = RunningSearchStatistics(; options=opts, window_size=500)
    for size in (1, 1, 1, 1, 1, 3, 3, 5)
        update_frequencies!(stats; size=size)
    end
    normalize_frequencies!(stats)

    dataset = Dataset(randn(2, 10), randn(10))
    n1 = Node{Float64}(; feature=1)
    n3 = cos(n1) + n1 * n1  # complexity 5
    PM = opts.popmember_type
    mk(tree) = PM(dataset, tree, opts; deterministic=false)
    m1 = mk(n1)
    m3 = mk(n3)

    p = AdaptiveParsimonyPlugin(; tournament=true, mutation_acceptance=false)
    mult1 = tournament_cost_multiplier(p, NoPluginState(), m1, stats, opts)
    mult3 = tournament_cost_multiplier(p, NoPluginState(), m3, stats, opts)
    @test mult1 > mult3
    @test mult1 > 1.0

    # tournament=false → identity
    p_off = AdaptiveParsimonyPlugin(; tournament=false, mutation_acceptance=false)
    @test tournament_cost_multiplier(p_off, NoPluginState(), m1, stats, opts) == 1.0
end

@testitem "AdaptiveParsimonyPlugin: mutation_acceptance multiplier matches legacy formula" begin
    using SymbolicRegression
    using SymbolicRegression: mutation_acceptance_multiplier, NoPluginState
    using SymbolicRegression.AdaptiveParsimonyModule:
        RunningSearchStatistics, update_frequencies!, normalize_frequencies!
    using SymbolicRegression.CoreModule.DatasetModule: Dataset
    using DynamicExpressions: Node
    using Test

    opts = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        maxsize=20,
        use_frequency=false,
        use_frequency_in_tournament=false,
        plugins=(AdaptiveParsimonyPlugin(; tournament=false, mutation_acceptance=true),),
    )
    stats = RunningSearchStatistics(; options=opts, window_size=500)
    for size in (1, 1, 1, 1, 1, 3, 3, 5)
        update_frequencies!(stats; size=size)
    end
    normalize_frequencies!(stats)

    dataset = Dataset(randn(2, 10), randn(10))
    n1 = Node{Float64}(; feature=1)
    n3 = cos(n1) + n1 * n1  # complexity 5
    PM = opts.popmember_type
    mk(tree) = PM(dataset, tree, opts; deterministic=false)
    parent_small = mk(n1)
    new_big = n3

    p = AdaptiveParsimonyPlugin(; tournament=false, mutation_acceptance=true)
    # Parent has size 1 (frequent → high old_freq); new tree has size 5 (rare → low new_freq).
    # Multiplier = old_freq / new_freq should be > 1.
    mult = mutation_acceptance_multiplier(p, NoPluginState(), parent_small, new_big, stats, opts)
    @test mult > 1.0

    # mutation_acceptance=false → identity
    p_off = AdaptiveParsimonyPlugin(; tournament=false, mutation_acceptance=false)
    @test mutation_acceptance_multiplier(p_off, NoPluginState(), parent_small, new_big, stats, opts) == 1.0
end

@testitem "AdaptiveParsimonyPlugin: end-to-end equation_search" begin
    using SymbolicRegression
    using Test

    # Legacy form (auto-injected).
    opts_legacy = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        populations=2,
        verbosity=0,
        progress=false,
    )
    X = rand(Float32, 2, 30)
    y = 2.0f0 .* X[1, :] .+ X[2, :]
    hof_legacy = equation_search(
        X, y; options=opts_legacy, niterations=2, parallelism=:serial
    )
    @test hof_legacy isa SymbolicRegression.HallOfFame

    # Explicit plugin form, no legacy flags.
    opts_plugin = Options(;
        binary_operators=[+, *],
        unary_operators=[cos],
        populations=2,
        verbosity=0,
        progress=false,
        use_frequency=false,
        use_frequency_in_tournament=false,
        plugins=(AdaptiveParsimonyPlugin(),),
    )
    hof_plugin = equation_search(
        X, y; options=opts_plugin, niterations=2, parallelism=:serial
    )
    @test hof_plugin isa SymbolicRegression.HallOfFame
end
