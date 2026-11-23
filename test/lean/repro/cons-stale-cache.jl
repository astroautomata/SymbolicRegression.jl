using SymbolicRegression
using DynamicExpressions: Node

options = SymbolicRegression.Options(; binary_operators=[+], complexity_of_variables=2)
tree = Node(Float64; feature=1)
fresh = SymbolicRegression.CheckConstraintsModule.check_constraints(tree, options, 1)
cached = SymbolicRegression.CheckConstraintsModule.check_constraints(tree, options, 1, 1)
println("complexity=2, maxsize=1: uncached=", fresh, ", stale cached_size=1 -> ", cached)
if !fresh && cached
    println("REPRODUCED cons-stale-cache")
end
