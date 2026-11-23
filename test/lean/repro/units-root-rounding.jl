using SymbolicRegression
using SymbolicRegression: Dataset
using SymbolicRegression.DimensionalAnalysisModule: violates_dimensional_constraints
using DynamicQuantities

# (s5 * s5) / s4 with s4 = x1^(1/16), s5 = x1^(1/32) is dimensionless.
options = Options(; binary_operators=[*, /], unary_operators=[sqrt])
dataset = Dataset(reshape([1.0, 2.0], 1, :), [1.0, 2.0]; X_units=["m"], y_units="1")
x1 = Node(Float64; feature=1)
s(t) = sqrt(t)
s4 = s(s(s(s(x1))))
s5 = s(s4)
tree = (s5 * s5) / s4
println("dimension(u\"m\")^(1//32) = ", dimension(u"m")^(1 // 32))
println("violates(s4 / s4) = ", violates_dimensional_constraints(s4 / s4, dataset, options))
println(
    "violates((s5 * s5) / s4) = ", violates_dimensional_constraints(tree, dataset, options)
)
if violates_dimensional_constraints(tree, dataset, options) &&
    !violates_dimensional_constraints(s4 / s4, dataset, options)
    println("REPRODUCED units-root-rounding")
end
