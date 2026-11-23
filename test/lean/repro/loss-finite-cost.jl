using SymbolicRegression: Options
using SymbolicRegression.LossFunctionsModule: loss_to_cost

loss = floatmax(Float64)
options = Options(; parsimony=0.0)
cost = loss_to_cost(loss, false, 1.0, nothing, options, 1)
@assert isfinite(loss) && cost == Inf
println("loss = ", loss, "; cost = ", cost)
println("REPRODUCED loss-finite-cost")
