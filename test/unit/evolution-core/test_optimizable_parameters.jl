@testitem "Optimizable parameter hooks aggregate constants and template parameters" begin
    using DynamicExpressions
    using SymbolicRegression

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+, *))
    variable_names = ["x1"]

    expr = parse_expression("x1 + 2.0"; operators, variable_names)
    flat = SymbolicRegression.get_optimizable_parameters(expr)[1]
    @test flat == [2.0]
    @test SymbolicRegression.count_optimizable_parameters(expr) == 1

    structure = TemplateStructure{(:f,),(:p,)}(
        ((; f), (; p), (x,)) -> f(x) * p[1]; num_parameters=(; p=1)
    )
    template = TemplateExpression(
        (; f=ComposableExpression(Node{Float64}(; val=3.0); operators, variable_names));
        structure,
        operators,
        variable_names,
        parameters=(; p=[2.0]),
    )

    params, refs = SymbolicRegression.get_optimizable_parameters(template)
    @test params == [3.0, 2.0]
    @test SymbolicRegression.count_optimizable_parameters(template) == 2

    SymbolicRegression.set_optimizable_parameters!(template, [4.0, 5.0], refs)
    @test SymbolicRegression.get_optimizable_parameters(template)[1] == [4.0, 5.0]
end
