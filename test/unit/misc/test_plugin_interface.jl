@testitem "Plugin interface: types and defaults" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPluginState,
        NoPluginState,
        init_plugin_state,
        on_search_start!,
        on_search_end!,
        on_generation_complete!,
        on_population_evaluated!,
        init_member
    using Test

    # Default types exist
    @test NoPluginState() isa AbstractPluginState

    # Default init_plugin_state returns NoPluginState
    opts = Options(binary_operators=[+, *])
    state = init_plugin_state(opts, [])
    @test state isa NoPluginState

    # Default hooks return nothing
    @test on_search_start!(state, [], opts, nothing) === nothing
    @test on_search_end!(state, nothing, [], opts, nothing) === nothing
    @test on_generation_complete!(state, nothing, [], opts, nothing) === nothing
    @test on_population_evaluated!(state, nothing, nothing, nothing, opts) === nothing
    @test init_member(state, nothing, opts) === nothing
end

@testitem "Plugin interface: lifecycle hooks called" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPluginState,
        AbstractOptions,
        init_plugin_state,
        on_search_start!,
        on_search_end!,
        on_generation_complete!,
        on_population_evaluated!
    using Test

    # Use a channel to safely count from multiple threads/tasks
    counter_ch = Channel{Symbol}(1000)

    mutable struct LifecyclePluginState <: AbstractPluginState
        counter_ch::Channel{Symbol}
    end
    struct LifecycleOptions{O} <: AbstractOptions
        base::O
        counter_ch::Channel{Symbol}
    end
    Base.getproperty(o::LifecycleOptions, k::Symbol) =
        k === :counter_ch ? getfield(o, :counter_ch) : getproperty(getfield(o, :base), k)
    SymbolicRegression.init_plugin_state(opts::LifecycleOptions, datasets) =
        LifecyclePluginState(opts.counter_ch)
    SymbolicRegression.on_search_start!(s::LifecyclePluginState, d, o, r) =
        (put!(s.counter_ch, :start); nothing)
    SymbolicRegression.on_search_end!(s::LifecyclePluginState, ss, d, o, r) =
        (put!(s.counter_ch, :end); nothing)
    SymbolicRegression.on_generation_complete!(s::LifecyclePluginState, ss, d, o, r) =
        (put!(s.counter_ch, :gen); nothing)
    SymbolicRegression.on_population_evaluated!(s::LifecyclePluginState, pop, d, h, o) =
        (put!(s.counter_ch, :pop); nothing)

    base_opts = Options(binary_operators=[+, *], populations=2, verbosity=0, progress=false)
    opts = LifecycleOptions(base_opts, counter_ch)
    X = rand(Float32, 2, 30)
    y = 2f0 .* X[1, :] .+ X[2, :]

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

@testitem "Plugin interface: init_member hook" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPluginState, AbstractOptions, init_plugin_state, init_member
    using Test

    init_count = Ref(0)

    mutable struct InitMemberPluginState <: AbstractPluginState end
    struct InitMemberOptions{O} <: AbstractOptions
        base::O
    end
    Base.getproperty(o::InitMemberOptions, k::Symbol) =
        getproperty(getfield(o, :base), k)
    SymbolicRegression.init_plugin_state(::InitMemberOptions, datasets) =
        InitMemberPluginState()
    # Return nothing to fall through to gen_random_tree, but count calls
    SymbolicRegression.init_member(::InitMemberPluginState, dataset, options) =
        (init_count[] += 1; nothing)

    base_opts = Options(binary_operators=[+, *], populations=2, verbosity=0, progress=false)
    opts = InitMemberOptions(base_opts)
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]

    equation_search(X, y; options=opts, niterations=2, parallelism=:serial)

    @test init_count[] > 0
end

@testitem "Plugin interface: on_mutation_evaluated! fires with correct args" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPluginState, AbstractOptions,
        init_plugin_state, on_mutation_evaluated!
    using Test

    # Collect (mutation_type, accepted, delta_loss) triples via a Channel
    events_ch = Channel{Tuple{Symbol,Bool,Float64}}(10_000)

    mutable struct MutEvalPluginState <: AbstractPluginState
        events_ch::Channel{Tuple{Symbol,Bool,Float64}}
    end
    struct MutEvalOptions{O} <: AbstractOptions
        base::O
        events_ch::Channel{Tuple{Symbol,Bool,Float64}}
    end
    Base.getproperty(o::MutEvalOptions, k::Symbol) =
        k === :events_ch ? getfield(o, :events_ch) : getproperty(getfield(o, :base), k)
    SymbolicRegression.init_plugin_state(opts::MutEvalOptions, datasets) =
        MutEvalPluginState(opts.events_ch)
    function SymbolicRegression.on_mutation_evaluated!(
        state::MutEvalPluginState, mutation_type::Symbol, accepted::Bool,
        delta_loss::Float64, dataset, opts::MutEvalOptions
    )
        put!(state.events_ch, (mutation_type, accepted, delta_loss))
        return nothing
    end

    base_opts = Options(binary_operators=[+, *], populations=2, verbosity=0, progress=false)
    opts = MutEvalOptions(base_opts, events_ch)
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]

    equation_search(X, y; options=opts, niterations=3, parallelism=:serial)

    close(events_ch)
    events = collect(events_ch)

    # Hook fired at all
    @test length(events) > 0

    # All mutation types are valid Symbols (fields of MutationWeights)
    valid_mutations = Set(fieldnames(MutationWeights))
    for (mt, acc, dl) in events
        @test mt isa Symbol
        @test mt in valid_mutations
        @test acc isa Bool
        @test dl isa Float64
    end

    # Both accepted and rejected mutations should appear (over many calls)
    @test any(acc for (_, acc, _) in events)
    @test any(!acc for (_, acc, _) in events)

    # Some events should have finite delta_loss (valid evaluations occurred)
    @test any(isfinite(dl) for (_, _, dl) in events)
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
        mutate_constant=0.0, mutate_operator=0.0, mutate_feature=0.0,
        swap_operands=0.0, rotate_tree=0.0, add_node=0.0, insert_node=0.0,
        delete_node=0.0, simplify=0.0, randomize=0.0, do_nothing=0.0,
        optimize=0.0, form_connection=0.0, break_connection=0.0,
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
