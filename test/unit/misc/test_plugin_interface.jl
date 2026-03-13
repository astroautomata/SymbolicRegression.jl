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

    const init_count = Ref(0)

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
