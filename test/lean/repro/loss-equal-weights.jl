using SymbolicRegression.LossFunctionsModule: _loss, _weighted_loss
using LossFunctions: L1DistLoss

loss = L1DistLoss()
x, y = [0.0, 0.0], [1.0, 1.0]
unweighted = _loss(x, y, loss)
weighted = _weighted_loss(x, y, fill(floatmax(Float64), length(x)), loss)
@assert unweighted == 1.0 && isnan(weighted)
println("unweighted = ", unweighted, "; weighted = ", weighted)
println("REPRODUCED loss-equal-weights")
