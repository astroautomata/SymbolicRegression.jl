using SymbolicRegression
using SymbolicRegression: Dataset
using SymbolicRegression.CoreModule.OperatorsModule: neg, relu
using SymbolicRegression.DimensionalAnalysisModule: violates_dimensional_constraints

# x1 is in metres and so is the target: neg(x1) and relu(x1) are consistent.
options = Options(; binary_operators=[+, *], unary_operators=[neg, relu])
ops = options.operators
un(f) = findfirst(==(f), ops.unaops)
bi(f) = findfirst(==(f), ops.binops)
dataset = Dataset([1.0 2.0; 3.0 4.0], [1.0, 2.0]; X_units=["m", "1"], y_units="m")
x1 = Node(Float64; feature=1)
c = Node(Float64; val=2.0)
trees = (
    neg=Node(; op=un(neg), children=(x1,)),
    relu=Node(; op=un(relu), children=(x1,)),
    neg_cx1=Node(; op=un(neg), children=(Node(; op=bi(*), children=(c, x1)),)),
)
results = map(t -> violates_dimensional_constraints(t, dataset, options), trees)
println("violates(x1) = ", violates_dimensional_constraints(x1, dataset, options))
println("violates = ", results)
if all(values(results)) && !violates_dimensional_constraints(x1, dataset, options)
    println("REPRODUCED units-neg-preserve")
end
