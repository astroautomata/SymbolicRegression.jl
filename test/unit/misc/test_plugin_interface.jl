@testitem "Plugin interface: types and defaults" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin,
        AbstractPluginState,
        NoPluginState,
        init_plugin_state,
        init_plugin_states,
        on_search_start!,
        on_search_end!,
        on_generation_complete!,
        on_population_evaluated!,
        init_member
    using Test

    # Default types exist
    @test NoPluginState() isa AbstractPluginState

    # An options with no plugins (and the legacy `use_frequency_in_tournament`
    # auto-injection disabled) has an empty tuple.
    opts = Options(binary_operators=[+, *], use_frequency_in_tournament=false)
    @test opts.plugins isa Tuple{}
    @test init_plugin_states(opts.plugins, opts, []) isa Tuple{}

    # A dummy plugin's default init returns NoPluginState
    struct DummyPlugin <: AbstractPlugin end
    p = DummyPlugin()
    @test init_plugin_state(p, opts, []) isa NoPluginState

    # Default hooks return nothing
    s = NoPluginState()
    @test on_search_start!(p, s, [], opts, nothing) === nothing
    @test on_search_end!(p, s, nothing, [], opts, nothing) === nothing
    @test on_generation_complete!(p, s, nothing, [], opts, nothing) === nothing
    @test on_population_evaluated!(p, s, nothing, nothing, nothing, opts) === nothing
    @test init_member(p, s, nothing, opts) === nothing
end

@testitem "Plugin interface: lifecycle hooks called for each plugin" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin,
        AbstractPluginState,
        init_plugin_state,
        on_search_start!,
        on_search_end!,
        on_generation_complete!,
        on_population_evaluated!
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
    SymbolicRegression.on_search_start!(
        ::LifecyclePlugin, s::LifecyclePluginState, d, o, r
    ) = (put!(s.counter_ch, :start); nothing)
    SymbolicRegression.on_search_end!(
        ::LifecyclePlugin, s::LifecyclePluginState, ss, d, o, r
    ) = (put!(s.counter_ch, :end); nothing)
    SymbolicRegression.on_generation_complete!(
        ::LifecyclePlugin, s::LifecyclePluginState, ss, d, o, r
    ) = (put!(s.counter_ch, :gen); nothing)
    SymbolicRegression.on_population_evaluated!(
        ::LifecyclePlugin, s::LifecyclePluginState, pop, d, h, o
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
    SymbolicRegression.on_generation_complete!(::PluginA, s::PluginAState, ss, d, o, r) =
        (s.calls[] += 1; nothing)
    SymbolicRegression.on_generation_complete!(::PluginB, s::PluginBState, ss, d, o, r) =
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
        ::InitMemberPlugin, s::InitMemberPluginState, dataset, options
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

@testitem "Plugin interface: on_mutation_evaluated! fires with correct args" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin, AbstractPluginState, MutationEvent, on_mutation_evaluated!
    using Test

    # Collect MutationEvent values via a Channel
    events_ch = Channel{MutationEvent}(10_000)

    struct MutEvalPlugin <: AbstractPlugin
        events_ch::Channel{MutationEvent}
    end
    mutable struct MutEvalPluginState <: AbstractPluginState
        events_ch::Channel{MutationEvent}
    end
    SymbolicRegression.init_plugin_state(p::MutEvalPlugin, o, d) = MutEvalPluginState(
        p.events_ch
    )
    function SymbolicRegression.on_mutation_evaluated!(
        ::MutEvalPlugin, state::MutEvalPluginState, event::MutationEvent, dataset, opts
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

    # All mutation types are valid Symbols (fields of MutationWeights)
    valid_mutations = Set(fieldnames(MutationWeights))
    for ev in events
        @test ev isa MutationEvent
        @test ev.mutation_type in valid_mutations
        @test ev.accepted isa Bool
        @test ev.before_loss isa Float64
        @test ev.after_loss isa Float64
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

@testitem "Plugin interface: @extend_mutation_weights macro" begin
    using SymbolicRegression
    import SymbolicRegression: sample_mutation, MutationWeights
    using Test

    @extend_mutation_weights TestWeights begin
        my_mutation::Float64 = 2.0
    end

    w = TestWeights()

    # All standard fields present with correct defaults
    @test w.mutate_constant == MutationWeights().mutate_constant
    @test w.my_mutation == 2.0
    @test length(fieldnames(TestWeights)) == length(fieldnames(MutationWeights)) + 1

    # copy produces an equal but independent object
    w2 = copy(w)
    @test w2.my_mutation == w.my_mutation
    @test w2 !== w
    w2.my_mutation = 99.0
    @test w.my_mutation == 2.0  # original unchanged

    # sample_mutation dispatches to the generated method and returns a valid field
    s = sample_mutation(w)
    @test s isa Symbol
    @test s in fieldnames(TestWeights)

    # With all weight on my_mutation, it should always be sampled
    w_biased = TestWeights(;
        mutate_constant=0.0,
        mutate_operator=0.0,
        mutate_feature=0.0,
        swap_operands=0.0,
        rotate_tree=0.0,
        add_node=0.0,
        insert_node=0.0,
        delete_node=0.0,
        simplify=0.0,
        randomize=0.0,
        do_nothing=0.0,
        optimize=0.0,
        form_connection=0.0,
        break_connection=0.0,
        my_mutation=1.0,
    )
    @test all(sample_mutation(w_biased) === :my_mutation for _ in 1:20)
end

@testitem "Plugin interface: @extend_mutation_weights rejects non-Float64 fields" begin
    using SymbolicRegression
    using Test

    @test_throws ErrorException @macroexpand @extend_mutation_weights BadWeights begin
        my_count::Int = 0
    end
end
