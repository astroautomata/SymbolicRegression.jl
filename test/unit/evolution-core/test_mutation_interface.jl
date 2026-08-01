@testitem "MutationInterface validates custom mutations" begin
    using Interfaces: Interfaces, Arguments, @implements, implements, test
    using SymbolicRegression
    using SymbolicRegression:
        AbstractMutation, Dataset, MutationInterface, MutationResult, RecordType

    struct ValidMutation <: AbstractMutation end
    function SymbolicRegression.mutate!(
        tree::N, ::P, ::ValidMutation, options; kws...
    ) where {N,P}
        return MutationResult{N,P}(; tree)
    end

    mutation = ValidMutation()
    options = Options(;
        binary_operators=(+, *),
        default_plugins=(),
        default_mutations=(),
        mutations=(mutation => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(;
        mutation,
        new_tree=copy(member.tree),
        parent_member=member,
        options,
        recorder=RecordType(),
        context=nothing,
        dataset,
        cost=member.cost,
        loss=member.loss,
        parent_ref=member.ref,
        curmaxsize=options.maxsize,
        nfeatures=2,
        plugin_states=(),
        population_for_backsolve=nothing,
    )

    @implements MutationInterface ValidMutation [arguments]

    @test implements(MutationInterface, ValidMutation)
    @test test(MutationInterface, ValidMutation; show=false)
end

@testitem "MutationInterface rejects a missing mutate! implementation" begin
    using Interfaces: Arguments, test
    using SymbolicRegression
    using SymbolicRegression: AbstractMutation, Dataset, MutationInterface, RecordType

    struct MissingMutationImplementation <: AbstractMutation end

    mutation = MissingMutationImplementation()
    options = Options(;
        binary_operators=(+, *),
        default_plugins=(),
        default_mutations=(),
        mutations=(mutation => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(;
        mutation,
        new_tree=copy(member.tree),
        parent_member=member,
        options,
        recorder=RecordType(),
        context=nothing,
        dataset,
        cost=member.cost,
        loss=member.loss,
        parent_ref=member.ref,
        curmaxsize=options.maxsize,
        nfeatures=2,
        plugin_states=(),
        population_for_backsolve=nothing,
    )

    @test !test(MutationInterface, MissingMutationImplementation, [arguments]; show=false)
end

@testitem "MutationInterface rejects an invalid mutation context" begin
    using Interfaces: Arguments, test
    using SymbolicRegression
    using SymbolicRegression:
        AbstractMutation, Dataset, MutationInterface, MutationResult, RecordType

    struct InvalidMutationContext <: AbstractMutation end
    function SymbolicRegression.mutate!(
        tree::N, ::P, ::InvalidMutationContext, options; kws...
    ) where {N,P}
        return MutationResult{N,P}(; tree)
    end
    SymbolicRegression.prepare_mutation_context(::InvalidMutationContext) = 1

    mutation = InvalidMutationContext()
    options = Options(;
        binary_operators=(+, *),
        default_plugins=(),
        default_mutations=(),
        mutations=(mutation => 1.0,),
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    arguments = Arguments(;
        mutation,
        new_tree=copy(member.tree),
        parent_member=member,
        options,
        recorder=RecordType(),
        context=nothing,
        dataset,
        cost=member.cost,
        loss=member.loss,
        parent_ref=member.ref,
        curmaxsize=options.maxsize,
        nfeatures=2,
        plugin_states=(),
        population_for_backsolve=nothing,
    )

    @test !test(MutationInterface, InvalidMutationContext, [arguments]; show=false)
end

@testitem "Built-in mutations implement MutationInterface" begin
    using Interfaces: Interfaces, test
    using SymbolicRegression
    using SymbolicRegression: MutationInterface

    @test isempty(Interfaces.optional_keys(MutationInterface))
    for mutation_type in (
        ConstantMutation,
        OperatorMutation,
        FeatureMutation,
        SwapOperandsMutation,
        AddNodeMutation,
        InsertNodeMutation,
        DeleteNodeMutation,
        FormConnectionMutation,
        BreakConnectionMutation,
        RotateTreeMutation,
        BacksolveMutation,
        SimplifyMutation,
        RandomizeMutation,
        OptimizeMutation,
        DoNothingMutation,
    )
        @test test(MutationInterface, mutation_type; show=false)
    end
end
