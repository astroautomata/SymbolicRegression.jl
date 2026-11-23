using SymbolicRegression
using SymbolicRegression: Dataset
using SymbolicRegression.CoreModule.OperatorsModule: greater, less
using SymbolicRegression.DimensionalAnalysisModule: violates_dimensional_constraints

# Comparing a quantity with itself is dimensionally consistent and gives a dimensionless 0/1.
options = Options(; binary_operators=[+, *, greater, less])
ops = options.operators
bi(f) = findfirst(==(f), ops.binops)
dataset = Dataset([1.0 2.0; 3.0 4.0], [1.0, 2.0]; X_units=["m", "1"], y_units="1")
x1 = Node(Float64; feature=1)
x2 = Node(Float64; feature=2)
trees = (
    greater_x1=Node(; op=bi(greater), children=(x1, x1)),
    less_x1=Node(; op=bi(less), children=(x1, x1)),
    greater_x2=Node(; op=bi(greater), children=(x2, x2)),
)
results = map(t -> violates_dimensional_constraints(t, dataset, options), trees)
println("violates = ", results)
if all(values(results))
    println("REPRODUCED units-compare")
end
