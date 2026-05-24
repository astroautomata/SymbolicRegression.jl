@testitem "AdaptiveParsimonyPlugin: legacy kwargs auto-inject" begin
    using SymbolicRegression
    using Test

    opts_default = Options(; binary_operators=[+, *])
    plugins = collect(opts_default.plugins)
    @test count(p -> p isa AdaptiveParsimonyPlugin, plugins) == 1
    p = plugins[findfirst(p -> p isa AdaptiveParsimonyPlugin, plugins)]
    @test p.tournament == true
    @test p.mutation_acceptance == true

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

    opts_off = Options(;
        binary_operators=[+, *], use_frequency=false, use_frequency_in_tournament=false
    )
    @test !any(p -> p isa AdaptiveParsimonyPlugin, opts_off.plugins)

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

@testitem "AdaptiveParsimonyPlugin: state owns RSS, multipliers read from it" begin
    using SymbolicRegression
    using SymbolicRegression:
        tournament_cost_multiplier,
        mutation_acceptance_multiplier,
        init_plugin_state,
        prepare_dispatch_state
    using SymbolicRegression.AdaptiveParsimonyModule:
        update_frequencies!, normalize_frequencies!
    using SymbolicRegression.AdaptiveParsimonyPluginModule: AdaptiveParsimonyState
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
        plugins=(AdaptiveParsimonyPlugin(),),
    )
    dataset = Dataset(randn(2, 10), randn(10))
    plugin = first(p for p in opts.plugins if p isa AdaptiveParsimonyPlugin)

    # Init head-side state, populate frequencies for known complexities.
    head_state = init_plugin_state(plugin, opts, [dataset])::AdaptiveParsimonyState
    @test length(head_state.rss) == 1
    rss_head = head_state.rss[1]
    for size in (1, 1, 1, 1, 1, 3, 3, 5)
        update_frequencies!(rss_head; size=size)
    end

    # prepare_dispatch_state should normalize and extract the slice for output 1.
    worker_state = prepare_dispatch_state(plugin, head_state, 1, dataset)::AdaptiveParsimonyState
    @test length(worker_state.rss) == 1
    @test sum(worker_state.rss[1].normalized_frequencies) ≈ 1.0  atol=1e-9
    # worker holds a distinct object from head (deepcopy)
    @test worker_state.rss[1] !== rss_head
    # head's raw frequency counts reflect the updates we made above
    @test rss_head.frequencies[1] >= 1.0
    @test rss_head.frequencies[3] >= 1.0
    @test rss_head.frequencies[5] >= 1.0

    # Build a couple of members of differing complexity.
    n1 = Node{Float64}(; feature=1)
    n3 = cos(n1) + n1 * n1  # complexity 5
    PM = opts.popmember_type
    mk(tree) = PM(dataset, tree, opts; deterministic=false)
    m1 = mk(n1)
    m3 = mk(n3)

    # tournament multiplier: size-1 (frequent) gets larger multiplier than size-5 (rare).
    mult1 = tournament_cost_multiplier(plugin, worker_state, m1, opts)
    mult3 = tournament_cost_multiplier(plugin, worker_state, m3, opts)
    @test mult1 > mult3
    @test mult1 > 1.0

    # mutation_acceptance multiplier: parent small (high old_freq) → big (low new_freq)
    # → multiplier > 1 (encourages diversification).
    mult_mut = mutation_acceptance_multiplier(plugin, worker_state, m1, n3, opts)
    @test mult_mut > 1.0

    # With both flags off, both multipliers are identity.
    p_off = AdaptiveParsimonyPlugin(; tournament=false, mutation_acceptance=false)
    @test tournament_cost_multiplier(p_off, worker_state, m1, opts) == 1.0
    @test mutation_acceptance_multiplier(p_off, worker_state, m1, n3, opts) == 1.0
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
