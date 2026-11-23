using SymbolicRegression
using DynamicExpressions: Expression, get_scalar_constants
using SymbolicRegression.ConstantOptimizationModule:
    get_optimizable_parameters, set_optimizable_parameters!

options = Options(; binary_operators=[+])
shared = Node(Float64; val=1.0)
ex = Expression(Node(Float64; op=1, l=shared, r=shared))
original, refs = get_optimizable_parameters(ex, options)
requested = [2.0, 3.0]
set_optimizable_parameters!(ex, requested, refs)
actual = first(get_scalar_constants(ex))
println(
    "original = ",
    original,
    "; requested optimizer vector = ",
    requested,
    "; actual getter vector = ",
    actual,
    "; shared node = ",
    shared.val,
)
@assert original == [1.0, 1.0]
@assert actual == [3.0, 3.0]
if actual != requested
    println("REPRODUCED copt-scalar-alias-roundtrip")
end
