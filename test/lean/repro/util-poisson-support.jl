using SymbolicRegression
using SymbolicRegression.CoreModule.UtilsModule: poisson_sample
using Random: MersenneTwister
lambda = 1.0e-20
actual = poisson_sample(MersenneTwister(1), lambda)
println(
    "lambda=",
    lambda,
    " exp(-lambda)=",
    exp(-lambda),
    " sample=",
    actual,
    " expected nonnegative integer",
)
@assert lambda > 0
@assert exp(-lambda) == 1.0
@assert actual == -1
println("REPRODUCED util-poisson-support")
