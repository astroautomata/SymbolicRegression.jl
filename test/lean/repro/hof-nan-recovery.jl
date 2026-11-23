using SymbolicRegression
options = Options(; binary_operators=[+], maxsize=5, deterministic=true)
dataset = Dataset(zeros(1, 2), zeros(2))
hof = HallOfFame(options, dataset)
bad = copy(hof.members[1])
bad.cost = NaN
bad.loss = 1.0
good = copy(hof.members[1])
good.cost = 1.0
good.loss = 1.0
SymbolicRegression.update_hall_of_fame!(hof, bad, options)
SymbolicRegression.update_hall_of_fame!(hof, good, options)
println("NaN incumbent followed by finite challenger: cost=", hof.members[1].cost)
if hof.exists[1] && isnan(hof.members[1].cost) && hof.members[1] !== bad
    println("REPRODUCED hof-nan-recovery")
end
