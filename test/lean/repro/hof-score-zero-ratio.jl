using SymbolicRegression
hall = SymbolicRegression.HallOfFameModule
score = hall.compute_zero_centered_score(0.0, 0.0, 1)
println("compute_zero_centered_score(0.0, 0.0, 1)=", score)
println("log(eps(0.0)) exact Float64 rational=", rationalize(BigInt, log(eps(0.0)); tol=0))
println(
    "relu(NaN)=",
    SymbolicRegression.relu(NaN),
    ", relu(-Inf)=",
    SymbolicRegression.relu(-Inf),
)
if isfinite(score) && score > 0.0
    println("REPRODUCED hof-score-zero-ratio")
end
