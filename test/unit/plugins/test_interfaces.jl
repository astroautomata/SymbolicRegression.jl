@testitem "PluginInterface validates declared hooks" begin
    using Interfaces: Interfaces, Arguments, @implements, implements, test
    using SymbolicRegression
    using SymbolicRegression:
        Dataset,
        AbstractPlugin,
        AbstractMutation,
        MutationEvent,
        PluginInterface,
        condition_mutation_weights!,
        init_plugin_state,
        on_mutation_end!

    mutable struct ValidPluginState
        observations::Int
    end
    struct ValidPlugin <: AbstractPlugin end

    SymbolicRegression.init_plugin_state(::ValidPlugin, options, dataset) = ValidPluginState(
        0
    )
    function SymbolicRegression.on_mutation_end!(
        state::ValidPluginState,
        ::ValidPlugin,
        ::AbstractMutation,
        ::MutationEvent,
        dataset,
        options,
    )
        state.observations += 1
        return nothing
    end
    function SymbolicRegression.condition_mutation_weights!(
        weights::AbstractVector,
        state::ValidPluginState,
        ::ValidPlugin,
        member,
        options,
        curmaxsize,
        nfeatures,
    )
        return nothing
    end

    plugin = ValidPlugin()
    options = Options(;
        binary_operators=(+, *),
        plugins=(plugin,),
        default_plugins=(),
        default_mutations=(),
        mutations=(DoNothingMutation() => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(; plugin, options, dataset, member, mutation=DoNothingMutation())

    @implements(PluginInterface, ValidPlugin, [arguments],)

    @test implements(PluginInterface, ValidPlugin)
    @test test(PluginInterface, ValidPlugin; show=false)
end

@testitem "PluginInterface accepts default hook implementations" begin
    using Interfaces: Arguments, test
    using SymbolicRegression
    using SymbolicRegression: AbstractPlugin, Dataset, PluginInterface

    struct DefaultOnlyPlugin <: AbstractPlugin end

    plugin = DefaultOnlyPlugin()
    options = Options(;
        binary_operators=(+, *),
        plugins=(plugin,),
        default_plugins=(),
        default_mutations=(),
        mutations=(DoNothingMutation() => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(; plugin, options, dataset, member, mutation=DoNothingMutation())

    @test test(PluginInterface, DefaultOnlyPlugin, [arguments]; show=false)
end

@testitem "PluginInterface accepts narrower hook dispatch" begin
    using Interfaces: Arguments, test
    using SymbolicRegression
    using SymbolicRegression:
        AbstractPlugin, Dataset, MutationEvent, OptimizeMutation, PluginInterface

    struct NarrowHookPlugin <: AbstractPlugin end
    function SymbolicRegression.on_mutation_end!(
        ::Nothing, ::NarrowHookPlugin, ::OptimizeMutation, ::MutationEvent, dataset, options
    )
        return nothing
    end

    plugin = NarrowHookPlugin()
    options = Options(;
        binary_operators=(+, *),
        plugins=(plugin,),
        default_plugins=(),
        default_mutations=(),
        mutations=(DoNothingMutation() => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(; plugin, options, dataset, member, mutation=DoNothingMutation())

    @test test(PluginInterface, NarrowHookPlugin, [arguments]; show=false)
end

@testitem "PluginInterface rejects incompatible plugin state dispatch" begin
    using Interfaces: Arguments, test
    using SymbolicRegression
    using SymbolicRegression:
        AbstractPlugin, AbstractMutation, Dataset, MutationEvent, PluginInterface

    struct ActualPluginState end
    struct ExpectedPluginState end
    struct StateMismatchPlugin <: AbstractPlugin end

    SymbolicRegression.init_plugin_state(::StateMismatchPlugin, options, dataset) = ActualPluginState()
    function SymbolicRegression.on_mutation_end!(
        ::ExpectedPluginState,
        ::StateMismatchPlugin,
        ::AbstractMutation,
        ::MutationEvent,
        dataset,
        options,
    )
        return nothing
    end

    plugin = StateMismatchPlugin()
    options = Options(;
        binary_operators=(+, *),
        plugins=(plugin,),
        default_plugins=(),
        default_mutations=(),
        mutations=(DoNothingMutation() => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(; plugin, options, dataset, member, mutation=DoNothingMutation())

    @test !test(PluginInterface, StateMismatchPlugin, [arguments]; show=false)
end

@testitem "Built-in plugins implement PluginInterface" begin
    using Interfaces: Interfaces, test
    using SymbolicRegression
    using SymbolicRegression: PluginInterface

    @test isempty(Interfaces.optional_keys(PluginInterface))
    for plugin in (
        AdaptiveParsimonyPlugin(),
        AdaptiveMutationWeightsPlugin(),
        MutationBurstPlugin(),
        SimulatedAnnealingPlugin(),
    )
        @test test(PluginInterface, typeof(plugin); show=false)
    end
end
