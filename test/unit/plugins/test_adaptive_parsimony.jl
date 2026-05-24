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

@testitem "AdaptiveParsimonyPlugin: hook outputs match the legacy formula" begin
    using SymbolicRegression
    using SymbolicRegression:
        tournament_cost_multiplier,
        mutation_acceptance_multiplier,
        init_plugin_state,
        prepare_dispatch_state
    using SymbolicRegression.AdaptiveParsimonyModule: update_frequencies!
    using SymbolicRegression.CoreModule.DatasetModule: Dataset
    using DynamicExpressions: Node
    using Test

    # Public-API setup: configure plugin via Options, build state via init_plugin_state.
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

    head_state = init_plugin_state(plugin, opts, [dataset])
    # Inject known frequency history via the public RunningSearchStatistics API.
    rss = head_state.rss[1]
    for size in (1, 1, 1, 1, 1, 3, 3, 5)
        update_frequencies!(rss; size=size)
    end

    # prepare_dispatch_state normalizes + extracts the slice for the given output.
    worker_state = prepare_dispatch_state(plugin, head_state, 1, dataset)
    @test length(worker_state.rss) == 1
    @test sum(worker_state.rss[1].normalized_frequencies) ≈ 1.0  atol = 1e-9
    @test worker_state.rss[1] !== rss  # snapshot is independent of head

    # Build members of two complexities (1 vs 5) via the popmember_type from Options.
    PM = opts.popmember_type
    n1 = Node{Float64}(; feature=1)
    n5 = cos(n1) + n1 * n1
    m1 = PM(dataset, n1, opts; deterministic=false)
    m5 = PM(dataset, n5, opts; deterministic=false)

    # Frequent complexity (1) gets a larger multiplier than the rare one (5).
    mult1 = tournament_cost_multiplier(plugin, worker_state, m1, opts)
    mult5 = tournament_cost_multiplier(plugin, worker_state, m5, opts)
    @test mult1 > mult5
    @test mult1 > 1.0

    # mutation_acceptance: small parent (high old_freq), big new (low new_freq) → >1.
    mult_mut = mutation_acceptance_multiplier(plugin, worker_state, m1, n5, opts)
    @test mult_mut > 1.0

    # Flag toggles produce identity multipliers when off.
    p_tournament_off = AdaptiveParsimonyPlugin(;
        tournament=false, mutation_acceptance=true
    )
    p_mut_off = AdaptiveParsimonyPlugin(; tournament=true, mutation_acceptance=false)
    @test tournament_cost_multiplier(p_tournament_off, worker_state, m1, opts) == 1.0
    @test mutation_acceptance_multiplier(p_mut_off, worker_state, m1, n5, opts) == 1.0

    # Out-of-range complexity (size > maxsize) → frequency = 0 → tournament multiplier
    # = exp(scaling * 0) = 1.0. Hits the "size out of range" branch.
    big_tree = foldl((acc, _) -> acc + n1, 1:30; init=Node{Float64}(; val=1.0))
    m_huge = PM(dataset, big_tree, opts; deterministic=false)
    @test tournament_cost_multiplier(plugin, worker_state, m_huge, opts) == 1.0
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
