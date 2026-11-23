# Reproducer for registry entry `mut-mutate-factor-negate` (SymReg/Mutations/Refute.lean).
# ConstantMutation's probability_negate is documented as "the chance of flipping the
# constant's sign" (src/Mutations.jl:38), but mutate_factor negates when
# rand(rng) > m.probability_negate (src/MutationFunctions.jl:181), i.e. with probability
# 1 - probability_negate.
using SymbolicRegression, Random
using SymbolicRegression.MutationFunctionsModule: mutate_factor, mutate_value
using SymbolicRegression.CoreModule: ConstantMutation

m = ConstantMutation()  # probability_negate = 0.01
rng = Xoshiro(0)
n = 10_000
negated = count(_ -> mutate_factor(Float64, 1.0, m, rng) < 0, 1:n)
flipped = count(_ -> mutate_value(rng, 2.5, 1.0, m) < 0, 1:n)
println("probability_negate = ", m.probability_negate)
println("fraction of negative factors: ", negated / n)
println("fraction of sign flips of 2.5 by mutate_value: ", flipped / n)
if negated / n > 0.5 && flipped / n > 0.5
    println("REPRODUCED mut-mutate-factor-negate")
end
