@testitem "Plugin interface: types and defaults" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin,
        AbstractPluginState,
        NoPluginState,
        init_plugin_state,
        fork_worker_state,
        on_search_start!,
        on_search_end!,
        on_generation_end!,
        on_cycle_end!,
        on_mutation_end!,
        init_member,
        tournament_cost_multiplier,
        mutation_acceptance_multiplier,
        condition_mutation_weights!,
        MutationEvent,
        MutationWeights
    using Test

    @test NoPluginState() isa AbstractPluginState

    # No-plugin Options (legacy adaptive parsimony off, no auto-inject).
    opts = Options(;
        binary_operators=[+, *], use_frequency=false, use_frequency_in_tournament=false
    )
    @test opts.plugins isa Tuple{}

    # Dummy plugin exercises every default hook contract.
    struct DummyPlugin <: AbstractPlugin end
    p = DummyPlugin()
    @test init_plugin_state(p, opts, nothing) isa NoPluginState
    s = NoPluginState()

    # Observers default to no-op (return nothing). Hooks follow the convention
    # (state, plugin, ...) so the mutated `state` is first.
    @test on_search_start!(s, p, nothing, opts, nothing) === nothing
    @test on_search_end!(s, p, nothing, nothing, opts, nothing) === nothing
    @test on_generation_end!(s, p, nothing, nothing, opts, nothing, nothing) === nothing
    @test on_cycle_end!(s, p, nothing, nothing, nothing, opts) === nothing
    @test on_mutation_end!(
        s, p, MutateConstant(), MutationEvent(true, 0.5, 0.4), nothing, opts
    ) === nothing

    # Factory defaults: init_member returns nothing, fork_worker_state
    # deepcopies the head state. (NoPluginState is an empty singleton, so
    # `===` returns true after deepcopy — we just check the type.)
    @test init_member(s, p, nothing, opts) === nothing
    head = NoPluginState()
    snap = fork_worker_state(head, p, nothing)
    @test snap isa NoPluginState

    # Modifier defaults return 1.0 (multiplicative identity).
    @test tournament_cost_multiplier(s, p, nothing, opts) == 1.0
    @test mutation_acceptance_multiplier(s, p, nothing, nothing, opts) == 1.0

    # Conditioner default leaves weights untouched. `weights` is the mutated
    # arg → first; then state, then plugin.
    w = deepcopy(opts.mutations)
    before = deepcopy(w)
    @test condition_mutation_weights!(w, s, p, nothing, opts, 20, 2) === nothing
    @test w == before
end

@testitem "Plugin interface: lifecycle hooks called for each plugin" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin,
        AbstractPluginState,
        init_plugin_state,
        fork_worker_state,
        on_search_start!,
        on_search_end!,
        on_generation_end!,
        on_cycle_end!
    using Test

    # Use a channel to safely count from multiple threads/tasks.
    counter_ch = Channel{Symbol}(1000)

    struct LifecyclePlugin <: AbstractPlugin
        counter_ch::Channel{Symbol}
    end
    mutable struct LifecyclePluginState <: AbstractPluginState
        counter_ch::Channel{Symbol}
    end

    SymbolicRegression.init_plugin_state(p::LifecyclePlugin, options, datasets) = LifecyclePluginState(
        p.counter_ch
    )
    # Share the head state's channel with workers (default fork deepcopies,
    # which would isolate the channel and lose worker-side events).
    SymbolicRegression.fork_worker_state(
        head::LifecyclePluginState, ::LifecyclePlugin, dataset
    ) = head
    SymbolicRegression.on_search_start!(
        s::LifecyclePluginState, ::LifecyclePlugin, d, o, r
    ) = (put!(s.counter_ch, :start); nothing)
    SymbolicRegression.on_search_end!(
        s::LifecyclePluginState, ::LifecyclePlugin, ss, d, o, r
    ) = (put!(s.counter_ch, :end); nothing)
    SymbolicRegression.on_generation_end!(
        s::LifecyclePluginState, ::LifecyclePlugin, ss, d, o, r, rp
    ) = (put!(s.counter_ch, :gen); nothing)
    SymbolicRegression.on_cycle_end!(
        s::LifecyclePluginState, ::LifecyclePlugin, pop, d, h, o
    ) = (put!(s.counter_ch, :pop); nothing)

    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        verbosity=0,
        progress=false,
        plugins=(LifecyclePlugin(counter_ch),),
    )
    X = rand(Float32, 2, 30)
    y = 2.0f0 .* X[1, :] .+ X[2, :]

    equation_search(X, y; options=opts, niterations=3, parallelism=:serial)

    close(counter_ch)
    counts = Dict{Symbol,Int}()
    for s in counter_ch
        counts[s] = get(counts, s, 0) + 1
    end

    @test get(counts, :start, 0) == 1
    @test get(counts, :end, 0) == 1
    @test get(counts, :gen, 0) > 0
    @test get(counts, :pop, 0) > 0
end

@testitem "Plugin interface: multiple plugins all fire" begin
    using SymbolicRegression
    import SymbolicRegression: AbstractPlugin, AbstractPluginState
    using Test

    a_calls = Ref(0)
    b_calls = Ref(0)

    struct PluginA <: AbstractPlugin
        calls::Base.RefValue{Int}
    end
    struct PluginB <: AbstractPlugin
        calls::Base.RefValue{Int}
    end
    mutable struct PluginAState <: AbstractPluginState
        calls::Base.RefValue{Int}
    end
    mutable struct PluginBState <: AbstractPluginState
        calls::Base.RefValue{Int}
    end

    SymbolicRegression.init_plugin_state(p::PluginA, o, d) = PluginAState(p.calls)
    SymbolicRegression.init_plugin_state(p::PluginB, o, d) = PluginBState(p.calls)
    SymbolicRegression.on_generation_end!(s::PluginAState, ::PluginA, ss, d, o, r, rp) =
        (s.calls[] += 1; nothing)
    SymbolicRegression.on_generation_end!(s::PluginBState, ::PluginB, ss, d, o, r, rp) =
        (s.calls[] += 1; nothing)

    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        verbosity=0,
        progress=false,
        plugins=(PluginA(a_calls), PluginB(b_calls)),
    )
    X = rand(Float32, 2, 30)
    y = 2.0f0 .* X[1, :] .+ X[2, :]
    equation_search(X, y; options=opts, niterations=2, parallelism=:serial)

    @test a_calls[] > 0
    @test b_calls[] > 0
end

@testitem "Plugin interface: init_member hook" begin
    using SymbolicRegression
    import SymbolicRegression: AbstractPlugin, AbstractPluginState, init_member
    using SymbolicRegression.MutationFunctionsModule: gen_random_tree
    using Test

    init_count = Ref(0)

    struct InitMemberPlugin <: AbstractPlugin
        calls::Base.RefValue{Int}
    end
    mutable struct InitMemberPluginState <: AbstractPluginState
        calls::Base.RefValue{Int}
    end

    SymbolicRegression.init_plugin_state(p::InitMemberPlugin, o, d) = InitMemberPluginState(
        p.calls
    )
    # Return nothing to fall through to gen_random_tree, but count calls
    SymbolicRegression.init_member(
        s::InitMemberPluginState, ::InitMemberPlugin, dataset, options
    ) = (s.calls[] += 1; nothing)

    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        verbosity=0,
        progress=false,
        plugins=(InitMemberPlugin(init_count),),
    )
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]

    equation_search(X, y; options=opts, niterations=2, parallelism=:serial)

    @test init_count[] > 0
end

@testitem "Plugin interface: init_member that returns a tree is consumed" begin
    using SymbolicRegression
    import SymbolicRegression: AbstractPlugin, AbstractPluginState
    using SymbolicRegression.MutationFunctionsModule: gen_random_tree
    using Test

    # Plugin always returns a real tree of the canonical type via gen_random_tree.
    # Exercises the non-nothing branch of `invoke_init_member` AND the
    # `candidate::typeof(fallback)` type assertion in `_init_tree`.
    seeded_calls = Ref(0)

    struct SeedingPlugin <: AbstractPlugin
        calls::Base.RefValue{Int}
    end
    mutable struct SeedingPluginState <: AbstractPluginState
        calls::Base.RefValue{Int}
    end
    SymbolicRegression.init_plugin_state(p::SeedingPlugin, o, d) = SeedingPluginState(
        p.calls
    )
    function SymbolicRegression.init_member(
        s::SeedingPluginState, ::SeedingPlugin, dataset, options
    )
        s.calls[] += 1
        nlength = 3
        nfeatures = size(dataset.X, 1)
        T = eltype(dataset.X)
        return gen_random_tree(nlength, options, nfeatures, T)
    end

    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        verbosity=0,
        progress=false,
        plugins=(SeedingPlugin(seeded_calls),),
    )
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]

    hof = equation_search(X, y; options=opts, niterations=2, parallelism=:serial)
    @test seeded_calls[] > 0
    @test hof isa SymbolicRegression.HallOfFame
end

@testitem "Plugin interface: on_mutation_end! fires with correct args" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin, AbstractPluginState, MutationEvent, on_mutation_end!
    using Test

    # Collect MutationEvent values via a Channel
    events_ch = Channel{MutationEvent{Float32}}(10_000)

    struct MutEvalPlugin <: AbstractPlugin
        events_ch::Channel{MutationEvent{Float32}}
    end
    mutable struct MutEvalPluginState <: AbstractPluginState
        events_ch::Channel{MutationEvent{Float32}}
    end
    SymbolicRegression.init_plugin_state(p::MutEvalPlugin, o, d) = MutEvalPluginState(
        p.events_ch
    )
    # Share the channel with workers (default fork deepcopies → events lost).
    SymbolicRegression.fork_worker_state(
        head::MutEvalPluginState, ::MutEvalPlugin, dataset
    ) = head
    function SymbolicRegression.on_mutation_end!(
        state::MutEvalPluginState,
        ::MutEvalPlugin,
        ::SymbolicRegression.AbstractMutation,
        event::MutationEvent,
        dataset,
        opts,
    )
        put!(state.events_ch, event)
        return nothing
    end

    # maxsize=5 ensures add_node frequently hits the constraint limit,
    # producing NaN after_loss events reliably.
    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        verbosity=0,
        progress=false,
        maxsize=5,
        plugins=(MutEvalPlugin(events_ch),),
    )
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]

    equation_search(X, y; options=opts, niterations=3, parallelism=:serial)

    close(events_ch)
    events = collect(events_ch)

    # Hook fired at all
    @test length(events) > 0

    for ev in events
        @test ev isa MutationEvent
        @test ev.accepted isa Bool
        @test ev.before_loss isa Float32
        @test ev.after_loss isa Float32
        @test isfinite(ev.before_loss)
    end

    # Both accepted and rejected mutations should appear (over many calls)
    @test any(ev.accepted for ev in events)
    @test any(!ev.accepted for ev in events)

    # Some events should have finite after_loss (valid evaluations occurred)
    @test any(isfinite(ev.after_loss) for ev in events)

    # Some events should have NaN after_loss (constraint failure or NaN eval)
    @test any(isnan(ev.after_loss) for ev in events)
end

@testitem "Plugin interface: condition_mutation_weights! plugin-dispatched" begin
    using SymbolicRegression
    using SymbolicRegression: AbstractPlugin, AbstractPluginState
    using Test

    # Plugin that zeroes out `mutate_constant` from its dispatched method.
    # Verifies the engine layers plugin conditioning on top of its own.
    struct ZeroConstPlugin <: AbstractPlugin end
    mutable struct ZeroConstState <: AbstractPluginState end
    SymbolicRegression.init_plugin_state(::ZeroConstPlugin, o, d) = ZeroConstState()
    function SymbolicRegression.condition_mutation_weights!(
        weights::SymbolicRegression.AbstractMutationWeights,
        ::ZeroConstState,
        ::ZeroConstPlugin,
        member,
        options,
        curmaxsize,
        nfeatures,
    )
        weights.mutate_constant = 0.0
        return nothing
    end

    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        verbosity=0,
        progress=false,
        use_frequency=false,
        use_frequency_in_tournament=false,
        plugins=(ZeroConstPlugin(),),
    )
    X = rand(Float32, 2, 20)
    y = X[1, :] .+ X[2, :]
    hof = equation_search(X, y; options=opts, niterations=2, parallelism=:serial)
    @test hof isa SymbolicRegression.HallOfFame
end
