@testitem "Plugin interface: types and defaults" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin,
        AbstractPluginState,
        NoPlugin,
        NoPluginState,
        get_plugin,
        init_plugin_state,
        on_search_start!,
        on_search_end!,
        on_generation_complete!,
        on_population_evaluated!,
        init_member
    using Test

    # Default types exist
    @test NoPlugin() isa AbstractPlugin
    @test NoPluginState() isa AbstractPluginState

    # Default hooks return nothing
    opts = Options(binary_operators=[+, *])
    plugin = get_plugin(opts)
    @test plugin isa NoPlugin

    state = init_plugin_state(plugin, [], opts)
    @test state isa NoPluginState

    @test on_search_start!(plugin, state, [], opts, nothing) === nothing
    @test on_search_end!(plugin, state, nothing, [], opts, nothing) === nothing
    @test on_generation_complete!(plugin, state, nothing, [], opts, nothing) === nothing
    @test on_population_evaluated!(plugin, state, nothing, nothing, nothing, opts) === nothing
    @test init_member(plugin, state, nothing, opts) === nothing
end

@testitem "Plugin interface: lifecycle hooks called" begin
    using SymbolicRegression
    import SymbolicRegression:
        AbstractPlugin,
        AbstractPluginState,
        AbstractOptions,
        get_plugin,
        init_plugin_state,
        on_search_start!,
        on_search_end!,
        on_generation_complete!,
        on_population_evaluated!
    using Test

    # Use a channel to safely count from multiple threads/tasks
    counter_ch = Channel{Symbol}(1000)

    mutable struct LifecyclePluginState <: AbstractPluginState end
    struct LifecyclePlugin <: AbstractPlugin
        counter_ch::Channel{Symbol}
    end
    struct LifecycleOptions{O} <: AbstractOptions
        base::O
        plugin::LifecyclePlugin
    end
    Base.getproperty(o::LifecycleOptions, k::Symbol) =
        k === :plugin ? getfield(o, :plugin) : getproperty(getfield(o, :base), k)
    SymbolicRegression.get_plugin(o::LifecycleOptions) = o.plugin
    SymbolicRegression.init_plugin_state(::LifecyclePlugin, datasets, options) =
        LifecyclePluginState()
    SymbolicRegression.on_search_start!(p::LifecyclePlugin, ::LifecyclePluginState, d, o, r) =
        (put!(p.counter_ch, :start); nothing)
    SymbolicRegression.on_search_end!(
        p::LifecyclePlugin, ::LifecyclePluginState, ss, d, o, r
    ) = (put!(p.counter_ch, :end); nothing)
    SymbolicRegression.on_generation_complete!(
        p::LifecyclePlugin, ::LifecyclePluginState, ss, d, o, r
    ) = (put!(p.counter_ch, :gen); nothing)
    SymbolicRegression.on_population_evaluated!(
        p::LifecyclePlugin, ::LifecyclePluginState, pop, d, h, o
    ) = (put!(p.counter_ch, :pop); nothing)

    base_opts = Options(binary_operators=[+, *], populations=2, verbosity=0, progress=false)
    opts = LifecycleOptions(base_opts, LifecyclePlugin(counter_ch))
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
        AbstractPlugin, AbstractPluginState, AbstractOptions, get_plugin, init_plugin_state,
        init_member
    using Test

    const init_count = Ref(0)

    mutable struct InitMemberPluginState <: AbstractPluginState end
    struct InitMemberPlugin <: AbstractPlugin end
    struct InitMemberOptions{O} <: AbstractOptions
        base::O
        plugin::InitMemberPlugin
    end
    Base.getproperty(o::InitMemberOptions, k::Symbol) =
        k === :plugin ? getfield(o, :plugin) : getproperty(getfield(o, :base), k)
    SymbolicRegression.get_plugin(o::InitMemberOptions) = o.plugin
    SymbolicRegression.init_plugin_state(::InitMemberPlugin, datasets, options) =
        InitMemberPluginState()
    # Return nothing to fall through to gen_random_tree, but count calls
    SymbolicRegression.init_member(::InitMemberPlugin, ::InitMemberPluginState, dataset, options) =
        (init_count[] += 1; nothing)

    base_opts = Options(binary_operators=[+, *], populations=2, verbosity=0, progress=false)
    opts = InitMemberOptions(base_opts, InitMemberPlugin())
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]

    equation_search(X, y; options=opts, niterations=2, parallelism=:serial)

    @test init_count[] > 0
end
