@testitem "HallOfFame API accessors" tags = [:part3] begin
    using SymbolicRegression
    using DynamicExpressions: Node, Expression
    using SymbolicRegression.HallOfFameModule:
        defined_members, dominates, dominating_members, update_hall_of_fame!
    using SymbolicRegression.SearchUtilsModule: check_for_loss_threshold

    options = Options(; binary_operators=[+], unary_operators=[], maxsize=10)

    X = [1.0 2.0 3.0]
    y = [1.0, 2.0, 3.0]
    dataset = Dataset(X, y)

    to_hof_expression(ex) = Expression(ex.tree; operators=nothing, variable_names=nothing)

    ex1 = to_hof_expression(
        @parse_expression(
            x, operators=options.operators, variable_names=[:x], node_type=Node{Float64},
        ),
    )
    ex3 = to_hof_expression(
        @parse_expression(
            x + 1.0,
            operators=options.operators,
            variable_names=[:x],
            node_type=Node{Float64},
        ),
    )
    ex5 = to_hof_expression(
        @parse_expression(
            x + x + 1.0,
            operators=options.operators,
            variable_names=[:x],
            node_type=Node{Float64},
        ),
    )

    m1 = PopMember(ex1, 1.0, 5.0, options, 1; deterministic=true)
    m3 = PopMember(ex3, 1.0, 6.0, options, 3; deterministic=true)
    m5 = PopMember(ex5, 1.0, 4.0, options, 5; deterministic=true)

    hof = HallOfFame(options, dataset)
    update_hall_of_fame!(hof, [m1, m3, m5], options)

    members = collect(defined_members(hof))
    @test length(members) == 3
    @test length(defined_members(hof)) == 3

    dom = dominating_members(hof)
    dom2 = calculate_pareto_frontier(hof)
    @test [m.loss for m in dom] == [m.loss for m in dom2]

    # (complexity=1, loss=5) should be kept (no simpler competitor)
    # (complexity=3, loss=6) is dominated by complexity=1
    # (complexity=5, loss=4) should be kept (beats all simpler on loss)
    @test length(dom) == 2
    @test dom[1].loss == 5.0
    @test dom[2].loss == 4.0

    @test dominates(1, 5.0, 3, 5.0)
    @test !dominates(3, 5.0, 1, 5.0)

    options_stop = Options(;
        binary_operators=[+],
        unary_operators=[],
        maxsize=10,
        early_stop_condition=((loss, complexity) -> loss < 4.5),
    )
    options_no_stop = Options(;
        binary_operators=[+],
        unary_operators=[],
        maxsize=10,
        early_stop_condition=((loss, complexity) -> loss < 3.5),
    )
    @test check_for_loss_threshold([hof], options_stop)
    @test !check_for_loss_threshold([hof], options_no_stop)

    # Ensure update supports iterables (not just vectors)
    hof2 = HallOfFame(options, dataset)
    update_hall_of_fame!(hof2, defined_members(hof), options)
    @test length(collect(defined_members(hof2))) == 3
end
