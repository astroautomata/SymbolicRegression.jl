@testitem "Test backsolve mutation" tags = [:part1] begin
    using SymbolicRegression
    using SymbolicRegression.InverseFunctionsModule: approx_inverse
    using SymbolicRegression.EvaluateInverseModule:
        eval_inverse_tree_array, eval_inverse_tree_array_masked, _eval_inverse_tree_array
    using SymbolicRegression.MutationFunctionsModule: backsolve_rewrite_random_node
    using DynamicExpressions:
        Node,
        OperatorEnum,
        count_nodes,
        Expression,
        get_child,
        eval_tree_array,
        EvalContext,
        ArrayBuffer
    using StableRNGs: StableRNG

    rng = StableRNG(0)
    options_with_backsolve(; kws...) = Options(;
        default_mutations=(), mutations=(BacksolveMutation() => 1.0,), kws...
    )

    @testset "InverseFunctions - Unary operators" begin
        inverse_pairs = (
            sin => SymbolicRegression.CoreModule.safe_asin,
            SymbolicRegression.CoreModule.safe_asin => sin,
            cos => SymbolicRegression.CoreModule.safe_acos,
            SymbolicRegression.CoreModule.safe_acos => cos,
            tan => atan,
            atan => tan,
            cosh => SymbolicRegression.CoreModule.safe_acosh,
            SymbolicRegression.CoreModule.safe_acosh => cosh,
            tanh => SymbolicRegression.CoreModule.atanh_clip,
            SymbolicRegression.CoreModule.atanh_clip => tanh,
            SymbolicRegression.CoreModule.square => SymbolicRegression.CoreModule.safe_sqrt,
            exp => SymbolicRegression.CoreModule.safe_log,
            SymbolicRegression.CoreModule.safe_log => exp,
            SymbolicRegression.CoreModule.safe_log2 => exp2,
            exp2 => SymbolicRegression.CoreModule.safe_log2,
            SymbolicRegression.CoreModule.safe_log10 => exp10,
            exp10 => SymbolicRegression.CoreModule.safe_log10,
            SymbolicRegression.CoreModule.safe_sqrt => SymbolicRegression.CoreModule.square,
            SymbolicRegression.CoreModule.cube => cbrt,
            cbrt => SymbolicRegression.CoreModule.cube,
            SymbolicRegression.CoreModule.neg => SymbolicRegression.CoreModule.neg,
        )
        for (f, inv_f) in inverse_pairs
            @test approx_inverse(f) == inv_f
        end
        @test isapprox(
            approx_inverse(SymbolicRegression.CoreModule.safe_log1p)(1.0), exp(1.0) - 1.0
        )
        @test approx_inverse(approx_inverse(SymbolicRegression.CoreModule.safe_log1p)) ==
            SymbolicRegression.CoreModule.safe_log1p
        for f in (abs, SymbolicRegression.CoreModule.relu)
            @test approx_inverse(f) === nothing
        end
    end

    @testset "InverseFunctions - Binary operators" begin
        f_mul_2 = Base.Fix2(*, 2.0)
        inv_f = approx_inverse(f_mul_2)
        @test inv_f isa Base.Fix2{typeof(/)}
        @test inv_f.x == 2.0

        f_2_pow = Base.Fix1(SymbolicRegression.CoreModule.safe_pow, 2.0)
        inv_f = approx_inverse(f_2_pow)
        @test inv_f isa Function
        @test isapprox(inv_f(8.0), 3.0)

        f_pow_2 = Base.Fix2(SymbolicRegression.CoreModule.safe_pow, 2.0)
        inv_f = approx_inverse(f_pow_2)
        @test inv_f isa Base.Fix2{typeof(SymbolicRegression.CoreModule.safe_pow)}
        @test inv_f.x == 0.5

        for f in (Base.Fix1(mod, 2), Base.Fix2(mod, 2))
            @test approx_inverse(f) === nothing
        end
    end

    @testset "EvaluateInverse - Simple unary tree" begin
        operators = OperatorEnum(; binary_operators=[+, *], unary_operators=[sin])
        x_node = Node(Float64; feature=1)
        tree = Node(1, x_node)

        X = reshape([1.0], 1, 1)
        y = [0.5]

        inverted, success = eval_inverse_tree_array(tree, X, operators, x_node, y)

        @test success
        @test length(inverted) == 1
        @test isapprox(inverted[1], asin(0.5); atol=1e-10)
    end

    @testset "EvaluateInverse - Binary tree" begin
        operators = OperatorEnum(; binary_operators=[+, *], unary_operators=[sin])
        x_node = Node(Float64; feature=1)
        const_node = Node(Float64; val=2.0)
        tree = Node(1, x_node, const_node)

        X = reshape([1.0], 1, 1)
        y = [5.0]

        inverted, success = eval_inverse_tree_array(tree, X, operators, x_node, y)

        @test success
        @test length(inverted) == 1
        @test isapprox(inverted[1], 3.0; atol=1e-10)
    end

    @testset "EvaluateInverse - Complex tree" begin
        operators = OperatorEnum(; binary_operators=[+, *], unary_operators=[sin])
        x_node = Node(Float64; feature=1)
        const_node = Node(Float64; val=2.0)
        mul_node = Node(2, x_node, const_node)
        tree = Node(1, mul_node)

        X = reshape([1.0], 1, 1)
        y = [0.5]

        inverted, success = eval_inverse_tree_array(tree, X, operators, x_node, y)

        @test success
        @test length(inverted) == 1
        @test isapprox(inverted[1], asin(0.5) / 2.0; atol=1e-10)
    end

    @testset "EvaluateInverse - Multiple data points" begin
        operators = OperatorEnum(; binary_operators=[+, *], unary_operators=[sin])
        x_node = Node(Float64; feature=1)
        const_node = Node(Float64; val=1.0)
        tree = Node(1, x_node, const_node)

        X = reshape([1.0, 2.0, 3.0], 1, 3)
        y = [2.0, 3.0, 4.0]

        inverted, success = eval_inverse_tree_array(tree, X, operators, x_node, y)

        @test success
        @test length(inverted) == 3
        @test isapprox(inverted, [1.0, 2.0, 3.0]; atol=1e-10)
    end

    @testset "EvaluateInverse - Masked sibling with evaluation buffer" begin
        operators = OperatorEnum(; binary_operators=[+, /])
        x_node = Node(Float64; feature=1)
        sibling_1 = Node(2, Node(Float64; val=1.0), Node(Float64; feature=2))
        sibling_2 = Node(2, Node(Float64; val=2.0), Node(Float64; feature=2))
        tree = Node(1, Node(1, x_node, sibling_1), sibling_2)

        X = Float64[0.0 0.0 0.0; 0.0 1.0 2.0]
        y = fill(20.0, 3)
        buffer = ArrayBuffer(zeros(1, length(y)), Ref(0))
        eval_context = EvalContext(; buffer)

        inverted, valid = eval_inverse_tree_array_masked(
            tree, X, operators, x_node, y; eval_context
        )

        @test valid == BitVector([false, true, true])
        @test inverted[2:3] ≈ [17.0, 18.5]

        before_reuse = copy(inverted)
        buffer.index[] = 0
        eval_tree_array(sibling_1, X, operators; eval_context)
        @test inverted == before_reuse
    end

    @testset "EvaluateInverse - Target node not found" begin
        operators = OperatorEnum(; binary_operators=[+, *], unary_operators=[sin])
        tree = Node(Float64; feature=1)
        other = Node(Float64; feature=1)

        X = reshape([1.0], 1, 1)
        y = [1.0]

        inverted, success = eval_inverse_tree_array(tree, X, operators, other, y)

        @test !success
        @test inverted == y
    end

    @testset "backsolve_rewrite_random_node - Basic mutation" begin
        X = reshape(Float64[1.0, 2.0, 3.0], 1, 3)
        y = Float64[2.0, 3.0, 4.0]
        dataset = Dataset(X, y)

        options = options_with_backsolve(;
            binary_operators=[+, *, -, /], unary_operators=[sin, cos]
        )

        x_node = Node(Float64; feature=1)
        sin_node = Node(1, x_node)
        const_node = Node(Float64; val=2.0)
        tree = Node(1, sin_node, const_node)

        mutated_tree = backsolve_rewrite_random_node(tree, dataset, options, rng)

        @test mutated_tree !== nothing
        @test count_nodes(mutated_tree) >= 1
    end

    @testset "backsolve_rewrite_random_node - Handles single node" begin
        # Single node tree should return unchanged
        X = reshape(Float64[1.0], 1, 1)
        y = Float64[1.0]
        dataset = Dataset(X, y)

        options = options_with_backsolve(; binary_operators=[+], unary_operators=[sin])

        tree = Node(Float64; val=1.0)
        mutated_tree = backsolve_rewrite_random_node(tree, dataset, options, rng)

        @test mutated_tree === tree
    end

    @testset "backsolve_rewrite_random_node - Handles invalid inversion" begin
        X = reshape(Float64[1.0, 2.0], 1, 2)
        y = Float64[10.0, 20.0]
        dataset = Dataset(X, y)

        operators = OperatorEnum(; binary_operators=[+, *], unary_operators=[sin])
        options = options_with_backsolve(; binary_operators=[+, *], unary_operators=[sin])

        x_node = Node(Float64; feature=1)
        tree = Node(1, x_node)

        mutated_tree = backsolve_rewrite_random_node(tree, dataset, options, rng)

        @test mutated_tree !== nothing
    end

    @testset "backsolve_rewrite_random_node - Complex constant fallback" begin
        X = reshape(ComplexF64[1 + im, 2 - im, 3 + 2im], 1, 3)
        y = ComplexF64[2 + 2im, 3 - im, 4 + 0im]
        dataset = Dataset(X, y)

        options = options_with_backsolve(; binary_operators=(+,), unary_operators=())

        tree = Node(1, Node(ComplexF64; feature=1), Node(ComplexF64; val=1 + 0im))
        mutated_tree = backsolve_rewrite_random_node(tree, dataset, options, rng)

        @test mutated_tree !== nothing
    end

    @testset "MutationWeights - backsolve field" begin
        weights = MutationWeights()
        @test hasfield(typeof(weights), :backsolve)
        @test weights.backsolve == 0.0

        weights_on = MutationWeights(; backsolve=0.5)
        @test weights_on.backsolve == 0.5
    end

    @testset "Helpful errors" begin
        operators3 = OperatorEnum(1 => (sin,), 2 => (+, *), 3 => ((a, b, c) -> a + b + c,))
        x1 = Node{Float64,3}(; feature=1)
        x2 = Node{Float64,3}(; feature=2)
        x3 = Node{Float64,3}(; feature=3)
        ternary_tree = Node{Float64,3}(; op=1, children=(x1, x2, x3))
        X3 = reshape(Float64[1.0, 2.0, 3.0], 3, 1)
        y3 = Float64[6.0]

        @test_throws(
            "eval_inverse_tree_array only supports AbstractExpressionNode{T,2}",
            eval_inverse_tree_array(ternary_tree, X3, operators3, x1, y3)
        )
        @test !hasmethod(
            _eval_inverse_tree_array,
            Tuple{
                typeof(ternary_tree),
                typeof(X3),
                typeof(operators3),
                typeof(x1),
                typeof(y3),
                NamedTuple{(),Tuple{}},
            },
        )
        @test_throws(
            "backsolve_rewrite_random_node only supports AbstractExpressionNode{T,2}",
            backsolve_rewrite_random_node(
                ternary_tree,
                Dataset(X3, y3),
                options_with_backsolve(; binary_operators=(+, *), unary_operators=(sin,)),
                rng,
            )
        )

        operators_no_unary = OperatorEnum(1 => (), 2 => (+,))
        unary_tree_without_operator = Node(
            Float64; op=1, children=(Node(Float64; feature=1),)
        )
        X_unary = reshape(Float64[1.0], 1, 1)
        y_unary = Float64[1.0]
        @test_throws(
            "eval_inverse_tree_array cannot invert node degree 1 with the configured operators",
            _eval_inverse_tree_array(
                unary_tree_without_operator,
                X_unary,
                operators_no_unary,
                get_child(unary_tree_without_operator, 1),
                copy(y_unary),
                (;),
            )
        )

        shared_options = Options(; binary_operators=(+, *), unary_operators=(sin,))
        shared_x = GraphNode(Float64; feature=1)
        shared_branch = shared_x + 1.0
        shared_tree = sin(shared_branch) + shared_branch
        X_shared = reshape(Float64[1.0], 1, 1)
        y_shared = Float64[sin(2.0) + 2.0]

        @test_throws(
            "eval_inverse_tree_array does not currently support shared-node expressions",
            eval_inverse_tree_array(
                shared_tree, X_shared, shared_options.operators, shared_x, y_shared
            )
        )

        string_tree = Node{String}(; val="x")
        string_dataset = Dataset(reshape(["x"], 1, 1), ["x"], Float64)
        string_options = options_with_backsolve(; binary_operators=(+,), unary_operators=())

        @test_throws(
            "backsolve_rewrite_random_node only supports floating-point scalar types",
            backsolve_rewrite_random_node(string_tree, string_dataset, string_options, rng)
        )

        int_tree = Node(Int; val=1)
        int_dataset = Dataset(reshape(Int[1], 1, 1), Int[1], Float64)
        int_options = options_with_backsolve(; binary_operators=(+,), unary_operators=())

        @test_throws(
            "backsolve_rewrite_random_node only supports floating-point scalar types",
            backsolve_rewrite_random_node(int_tree, int_dataset, int_options, rng)
        )

        template_dataset = Dataset(reshape(Float32[1.0, 2.0], 1, 2), Float32[1.0, 2.0])

        template_spec = @template_spec(expressions = (f,)) do x1
            f(x1)
        end
        template_options = options_with_backsolve(;
            binary_operators=(*,), unary_operators=(), expression_spec=template_spec
        )
        template_expr = parse_expression(
            (; f="#1"); expression_spec=template_spec, operators=template_options.operators
        )

        @test_throws(
            "expression wrapper types must opt in explicitly",
            backsolve_rewrite_random_node(
                template_expr, template_dataset, template_options, rng
            )
        )
    end

    @testset "Integration - backsolve in mutation pipeline" begin
        using SymbolicRegression.MutateModule: mutate!

        X = reshape(Float64[1.0, 2.0, 3.0], 1, 3)
        y = Float64[2.0, 4.0, 6.0]
        dataset = Dataset(X, y)

        options = Options(; binary_operators=[+, *], unary_operators=[sin])

        x_node = Node(Float64; feature=1)
        const_node = Node(Float64; val=1.0)
        tree = Node(1, x_node, const_node)

        ex = Expression(tree; operators=options.operators)
        member = PopMember(dataset, tree, options; deterministic=true)

        result = mutate!(
            ex,
            member,
            BacksolveMutation(),
            options;
            trace=Dict{String,Any}(),
            dataset=dataset,
        )

        @test result isa SymbolicRegression.MutateModule.MutationResult
        @test result.tree !== nothing || result.member !== nothing
    end

    @testset "Integration - backsolve in equation_search" begin
        X = reshape(Float64[1.0, 2.0, 3.0, 4.0], 1, 4)
        y = 2 .* vec(X) .+ 1

        options = Options(;
            binary_operators=(+, *, -),
            unary_operators=(sin,),
            default_mutations=(),
            mutations=(BacksolveMutation() => 1.0,),
            population_size=20,
            populations=1,
            ncycles_per_iteration=20,
            maxsize=10,
            deterministic=true,
            crossover_probability=0.0,
            progress=false,
            verbosity=0,
        )

        hall_of_fame = equation_search(
            X, y; niterations=1, options, parallelism=:serial, guesses=["x1 + 1.0"]
        )

        @test !isempty(hall_of_fame.members)
        @test any(member -> isfinite(member.loss), hall_of_fame.members)
    end
end
