using SymbolicRegression
using DynamicExpressions: Node, Expression

options = SymbolicRegression.Options(; binary_operators=[+], complexity_mapping=(_ -> 10))
ex = Expression(Node(Float64; feature=1); operators=options.operators)
complexity = SymbolicRegression.compute_complexity(ex, options)
accepted = SymbolicRegression.CheckConstraintsModule.check_constraints(ex, options, 3)
println("custom complexity=", complexity, "; maxsize=3, accepted=", accepted)
if complexity == 10 && accepted
    println("REPRODUCED cons-custom-size")
end
