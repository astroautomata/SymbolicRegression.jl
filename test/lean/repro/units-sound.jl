using SymbolicRegression
using SymbolicRegression.DimensionalAnalysisModule:
    violates_dimensional_constraints, violates_dimensional_constraints_dispatch
using SymbolicRegression: Dataset

options = Options(; node_type=GraphNode, binary_operators=[/])
dataset = Dataset([1.0 2.0], [1.0, 1.0]; X_units=["1"], y_units="m")
c = GraphNode(Float64; val=2.0)
tree = GraphNode(; op=1, children=(c, c))
shared = tree.l === tree.r
result = violates_dimensional_constraints_dispatch(
    tree, dataset.X_units, view(dataset.X, :, 1), options.operators, true
)
violates = violates_dimensional_constraints(tree, dataset, options)
println("shared = ", shared, ", wildcard = ", result.wildcard, ", violates = ", violates)
if shared && result.wildcard && !violates
    println("REPRODUCED units-sound")
    println("REPRODUCED units-wildcard-any")
end
