# Reproducer for registry entry `tmpl-composable-scalar-call` (SymReg/Templates/Composable.lean).
# A ComposableExpression called on numbers returns the value of an incomplete evaluation
# (src/ComposableExpression.jl:203-209), while the one-sample vector call maps it to NaN
# (src/ComposableExpression.jl:186-202).
using SymbolicRegression
using SymbolicRegression: ComposableExpression
using DynamicExpressions: Node, OperatorEnum

operators = OperatorEnum(1 => (inv, -), 2 => (+, /))
x1 = Node{Float64}(; feature=1)
f = ComposableExpression(
    Node{Float64}(; op=2, children=(Node{Float64}(; op=1, children=(x1,)),)); operators
)

scalar = f(0.0)
vector = f([0.0])
println("f = -(inv(x1))")
println("scalar call f(0.0)   = ", scalar, "  (expected the vector call's value)")
println("vector call f([0.0]) = ", vector)
if scalar == Inf && length(vector) == 1 && isnan(only(vector))
    println("REPRODUCED tmpl-composable-scalar-call")
end
