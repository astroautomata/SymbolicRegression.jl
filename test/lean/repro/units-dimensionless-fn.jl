using SymbolicRegression
using SymbolicRegression: Dataset
using SymbolicRegression.CoreModule.OperatorsModule: safe_log
using SymbolicRegression.DimensionalAnalysisModule: violates_dimensional_constraints

# x2 is dimensionless ("1") and so is the target: cos(x2), exp(x2), log(x2) are consistent.
options = Options(; binary_operators=[+, *], unary_operators=[cos, exp, log])
ops = options.operators
un(f) = findfirst(==(f), ops.unaops)
dataset = Dataset([1.0 2.0; 3.0 4.0], [1.0, 2.0]; X_units=["m", "1"], y_units="1")
x2 = Node(Float64; feature=2)
results = Dict(
    f => violates_dimensional_constraints(
        Node(; op=un(f), children=(x2,)), dataset, options
    ) for f in (cos, exp, safe_log)
)
println("violates(x2) = ", violates_dimensional_constraints(x2, dataset, options))
println("violates(f(x2)) = ", results)
if all(values(results)) && !violates_dimensional_constraints(x2, dataset, options)
    println("REPRODUCED units-dimensionless-fn")
end
