@testitem "Test options" begin
    using SymbolicRegression
    using Optim: Optim

    # testing types
    op = Options(; optimizer_options=(iterations=16, f_calls_limit=100, x_abstol=1e-16))
    @test isa(op.optimizer_options, Optim.Options)

    op = Options(;
        optimizer_options=Dict(:iterations => 32, :g_calls_limit => 50, :f_reltol => 1e-16)
    )
    @test isa(op.optimizer_options, Optim.Options)

    optim_op = Optim.Options(; iterations=16)
    op = Options(; optimizer_options=optim_op)
    @test isa(op.optimizer_options, Optim.Options)

    # testing loss_scale parameter
    op_log = Options(; loss_scale=:log)
    @test op_log.loss_scale == :log

    op_linear = Options(; loss_scale=:linear)
    @test op_linear.loss_scale == :linear

    # test that invalid loss_scale values are caught
    @test_throws AssertionError Options(; loss_scale=:invalid)
    @test_throws AssertionError Options(; loss_scale=:cubic)
end

@testitem "Test versioned default profile selection" begin
    using SymbolicRegression
    using Optim: Optim
    using SymbolicRegression.CoreModule.OptionsModule: default_options

    pre_v2_defaults = default_options(v"1.0.0")
    v2_defaults = default_options(v"2.0.0-alpha")
    current_defaults = default_options()

    changed_fields = (
        :populations,
        :population_size,
        :ncycles_per_iteration,
        :adaptive_parsimony_scaling,
        :use_frequency,
        :use_frequency_in_tournament,
        :optimizer_nrestarts,
        :optimizer_probability,
        :optimizer_iterations,
        :optimizer_f_calls_limit,
        :tournament_selection_n,
        :tournament_selection_p,
        :fraction_replaced_hof,
    )

    for field in changed_fields
        @test getproperty(current_defaults, field) == getproperty(v2_defaults, field)
    end
    for field in changed_fields
        @test getproperty(pre_v2_defaults, field) != getproperty(v2_defaults, field)
    end

    current_mutation_weights = convert(Vector, current_defaults.mutation_weights)
    @test current_mutation_weights == convert(Vector, v2_defaults.mutation_weights)
    @test current_mutation_weights == convert(Vector, MutationWeights())
    @test current_mutation_weights != convert(Vector, pre_v2_defaults.mutation_weights)

    # These used to be hardcoded constructor defaults, so this checks the
    # versioned bundle is not silently masked before OptionsStruct construction.
    for (version, defaults) in ((v"1.0.0", pre_v2_defaults), (v"2.0.0-alpha", v2_defaults))
        options = Options(; defaults=version)
        @test options.use_frequency == defaults.use_frequency
        @test options.use_frequency_in_tournament == defaults.use_frequency_in_tournament
        @test options.optimizer_nrestarts == defaults.optimizer_nrestarts
        @test options.optimizer_probability ≈ Float32(defaults.optimizer_probability)
        @test options.optimizer_options.iterations == defaults.optimizer_iterations
        @test options.optimizer_options.f_calls_limit == defaults.optimizer_f_calls_limit
    end

    user_optimizer_options = Optim.Options(; iterations=16)
    overridden = Options(;
        defaults=v"2.0.0-alpha",
        use_frequency=true,
        use_frequency_in_tournament=true,
        optimizer_nrestarts=7,
        optimizer_probability=0.05,
        optimizer_options=user_optimizer_options,
    )
    @test overridden.use_frequency
    @test overridden.use_frequency_in_tournament
    @test overridden.optimizer_nrestarts == 7
    @test overridden.optimizer_probability ≈ Float32(0.05)
    @test overridden.optimizer_options === user_optimizer_options

    @test_throws AssertionError Options(;
        optimizer_options=user_optimizer_options, optimizer_iterations=10
    )
end

@testitem "Test backsolve options" begin
    using SymbolicRegression

    @test Options().backsolve == BacksolveOptions()
    @test Options(; backsolve=nothing).backsolve == BacksolveOptions()
    @test Options(; backsolve=BacksolveOptions(; lambda=0.2)).backsolve.lambda == 0.2
end

@testitem "Test operators parameter conflicts" begin
    using SymbolicRegression
    using DynamicExpressions: OperatorEnum

    # Test that when operators is provided, we can't also provide individual sets
    operators = OperatorEnum(1 => (sin, cos), 2 => (+, *, -))
    @test_throws AssertionError Options(; operators, binary_operators=(+, *))
    @test_throws AssertionError Options(; operators, unary_operators=(sin,))

    # Test that when operators is provided, operator_enum_constructor should be nothing
    @test_throws AssertionError Options(; operators, operator_enum_constructor=OperatorEnum)

    # Test that providing operators alone works fine (should not throw)
    @test_nowarn Options(; operators)
end

@testitem "Test operators stored globally" begin
    using SymbolicRegression
    using DynamicExpressions.OperatorEnumConstructionModule: LATEST_OPERATORS

    operators = OperatorEnum(1 => [sin, cos], 2 => [+, -, *], 3 => [fma], 5 => [max])
    options = Options(; operators)

    @test LATEST_OPERATORS[] == operators
end

@testitem "Test with_max_degree_from_context" begin
    using SymbolicRegression

    operators = OperatorEnum(1 => (sin, cos), 2 => (+, *, -))
    @test Options(; node_type=GraphNode, operators).node_type <: GraphNode{<:Any,2}
    @test Options(; node_type=Node, operators).node_type <: Node{<:Any,2}

    operators = OperatorEnum(1 => (sin, cos), 2 => ())
    @test Options(; node_type=Node{<:Any,1}, operators).node_type <: Node{<:Any,1}

    @test Options().node_type <: Node{<:Any,2}

    operators = OperatorEnum(1 => (sin, cos), 2 => (+, *, -), 3 => (fma, max))
    options = Options(; operators)
    @test options.node_type <: Node{<:Any,3}
    @test options.op_constraints ==
        ([-1, -1], [(-1, -1), (-1, -1), (-1, -1)], [(-1, -1, -1), (-1, -1, -1)])
    @test options.nops == (2, 3, 2)
end

@testitem "Test operator appears in multiple degrees error" begin
    using SymbolicRegression

    operators = OperatorEnum(1 => (+, sin), 2 => (+, *))  # + appears in both degrees

    @test_throws(
        "Operator + appears in multiple degrees. You can't use nested constraints.",
        Options(; operators, nested_constraints=[(+) => [(+) => 0]])
    )

    @test_throws(
        "Operator + appears in multiple degrees. You can't use constraints.",
        Options(; operators, constraints=[(+) => -1])
    )
end

@testitem "Test build_constraints with pre-processed vector format" begin
    using SymbolicRegression
    using SymbolicRegression.CoreModule.OptionsModule: build_constraints
    using DynamicExpressions: OperatorEnum

    operators = OperatorEnum(1 => (sin, cos), 2 => (+, *, -), 5 => (max,))

    constraints_processed = (
        [-1, -1], [(-1, -1), (-1, -1), (-1, -1)], nothing, nothing, [(-1, -1, -1, -1, -1)]
    )

    result = build_constraints(;
        constraints=constraints_processed, operators_by_degree=operators.ops
    )

    # Verify the result matches expected format (fills empty slots with default values)
    @test result == (
        [-1, -1],
        [(-1, -1), (-1, -1), (-1, -1)],
        NTuple{3,Int}[],
        NTuple{4,Int}[],
        [(-1, -1, -1, -1, -1)],
    )
end
