using SymbolicRegression
using DynamicExpressions
using Enzyme
using SymbolicRegression.ConstantOptimizationModule:
    Evaluator, EvaluatorContext, GradEvaluator

operators = OperatorEnum(; binary_operators=(+, *))
options = Options(; operators)
structure = TemplateStructure{(:f,),(:p,)}(
    ((; f), (; p), (x,)) -> f(x) * p[1]; num_parameters=(; p=1)
)
ex = TemplateExpression(
    (; f=ComposableExpression(Node{Float64}(; val=3.0); operators));
    structure,
    operators,
    parameters=(; p=[2.0]),
)
x, refs = SymbolicRegression.get_optimizable_parameters(ex, options)
dataset = Dataset(reshape([1.0, 2.0], 1, :), [0.0, 0.0])
e = Evaluator(ex, refs, EvaluatorContext(dataset, options, nothing))
expected = e([4.0, 5.0])
@assert expected == 400.0
SymbolicRegression.set_optimizable_parameters!(ex, x, refs)
ext = Base.get_extension(SymbolicRegression, :SymbolicRegressionEnzymeExt)
g = GradEvaluator(e, ext.AutoEnzyme())
actual = try
    g(nothing, zeros(2), [4.0, 5.0])
catch error
    error
end
println("non-extension loss = ", expected, "; Enzyme result = ", actual)
@assert actual isa MethodError
@assert actual.f === iterate
@assert first(actual.args) === refs
println("REPRODUCED ext-enzyme-optimizable-hooks")
