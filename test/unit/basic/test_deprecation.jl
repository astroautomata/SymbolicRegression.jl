@testitem "Test deprecated options" begin
    using SymbolicRegression

    weights = @test_deprecated MutationWeights()
    @test convert(Vector, weights) == last.(default_mutations())
    options = Options(; mutation_weights=weights)
    @test last.(options.mutations) == convert(Vector, weights)
    @test_throws ArgumentError MutationWeights(; invalid=1.0)

    # Deprecated kwargs should still work:
    options = Options(;
        mutationWeights=MutationWeights(; mutate_constant=0.0),
        fractionReplacedHof=0.01f0,
        shouldOptimizeConstants=true,
        loss=L2DistLoss(),
    )

    @test only(
        weight for (mutation, weight) in options.mutations if mutation isa ConstantMutation
    ) == 0.0
    @test options.fraction_replaced_hof == 0.01f0
    @test options.should_optimize_constants == true
    @test options.elementwise_loss == L2DistLoss()

    recorder_options = @test_deprecated Options(; use_recorder=true)
    @test recorder_options.use_tracing == Val(true)

    recorder_file_options = @test_deprecated Options(; recorder_file="legacy_trace.json")
    @test recorder_file_options.tracing_file == "legacy_trace.json"

    options = Options(; mutationWeights=[1.0 for i in 1:8])
    @test only(
        weight for (mutation, weight) in options.mutations if mutation isa AddNodeMutation
    ) == 1.0

    # Test score_func deprecation
    X = randn(3, 5)
    y = randn(5)
    dataset = Dataset(X, y)
    options = Options()
    tree = Node(; val=1.0)

    using SymbolicRegression: score_func, eval_cost

    @test_deprecated score_func(dataset, tree, options) == eval_cost(dataset, tree, options)

    # Test PopMember score deprecation warnings
    X = randn(3, 5)
    y = randn(5)
    dataset = Dataset(X, y)
    options = Options()
    tree = Node(; val=1.0)
    member = PopMember(dataset, tree, options; deterministic=true)

    # Test that accessing .score triggers deprecation warning
    @test_deprecated member.score
    @test (@test_deprecated member.score) == member.cost

    # Test that setting .score triggers deprecation warning
    @test_deprecated member.score = 0.5
    @test member.cost == 0.5
end

@testitem "Deprecated constant sign probability names" begin
    using SymbolicRegression

    constant_mutation(options) = only(
        first(p) for p in options.mutations if first(p) isa ConstantMutation
    )
    new = Options(; probability_flip_constant_sign=0.75)
    for old in (
        @test_deprecated(Options(; probability_negate_constant=0.25)),
        @test_deprecated(Options(; probNegate=0.25)),
    )
        @test old.probability_flip_constant_sign == new.probability_flip_constant_sign
        @test constant_mutation(old) == constant_mutation(new)
    end
    @test (@test_deprecated ConstantMutation(; probability_negate=0.25)) ==
        ConstantMutation(; probability_flip_sign=0.75)
    @test (@test_deprecated ConstantMutation(; probability_flip_sign=0.75).probability_negate) ==
        0.25

    @test_throws ArgumentError Options(;
        probability_negate_constant=0.25, probability_flip_constant_sign=0.75
    )
    @test_throws ArgumentError ConstantMutation(;
        probability_negate=0.25, probability_flip_sign=0.75
    )
end

@testitem "Test deprecated evaluation context names" begin
    using SymbolicRegression
    using SymbolicRegression: eval_cost, eval_loss

    operators = OperatorEnum(; binary_operators=(+,))
    options = Options(; operators)
    X = reshape([1.0, 2.0, 3.0], 1, :)
    dataset = Dataset(X, copy(vec(X)))
    tree = Node{Float64}(; feature=1)
    eval_options = EvalOptions(; early_exit=false)

    @test (@test_deprecated eval_tree_array(tree, X, options; eval_options)) ==
        eval_tree_array(tree, X, options; eval_context=eval_options)
    @test (@test_deprecated eval_loss(tree, dataset, options; eval_options)) ==
        eval_loss(tree, dataset, options; eval_context=eval_options)
    @test (@test_deprecated eval_cost(dataset, tree, options; eval_options)) ==
        eval_cost(dataset, tree, options; eval_context=eval_options)
    @test_throws MethodError eval_loss(tree, dataset, options; eval_contex=eval_options)
    @test_throws MethodError eval_cost(dataset, tree, options; eval_contex=eval_options)

    f = @test_deprecated ComposableExpression(tree; operators, eval_options)
    @test get_metadata(f).eval_context === eval_options
    @test_throws ArgumentError ComposableExpression(tree; operators, invalid=true)

    structure = TemplateStructure{(:f,)}(((; f), (x1,)) -> f(x1))
    expression = TemplateExpression((; f); structure, operators)
    @test (@test_deprecated eval_tree_array(expression, X, operators; eval_options)) ==
        eval_tree_array(expression, X, operators; eval_context=eval_options)

    spec = TemplateExpressionSpec(; structure)
    parsed = @test_deprecated parse_expression(
        (; f="#1"); expression_spec=spec, operators, eval_options
    )
    @test get_metadata(get_contents(parsed).f).eval_context === eval_options

    @test_throws AssertionError eval_tree_array(
        tree, X, options; eval_context=eval_options, eval_options
    )
end
