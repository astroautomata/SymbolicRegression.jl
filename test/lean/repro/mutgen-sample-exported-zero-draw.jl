# Reproducer for registry entry `mutgen-sample-exported-zero-draw` (SymReg/MutateGen/SampleProps.lean).
# sample_mutation (src/MutationWeights.jl:159-164) uses StatsBase.sample, whose scan
# `while cw < t` stops at index 1 when the draw is exactly 0.0 (a legal rand() value), so a
# zero-weight first mutation is returned. The task-local Xoshiro state below makes the next
# rand() return 0.0.
using SymbolicRegression
using Random

copy!(Random.default_rng(), Random.Xoshiro(0x0, 0x1, 0x2, 0x0))
choice = SymbolicRegression.sample_mutation([
    OperatorMutation() => 0.0, ConstantMutation() => 1.0
])
copy!(Random.default_rng(), Random.Xoshiro(0x0, 0x1, 0x2, 0x0))
draw = rand()
println(
    "next rand() = ",
    draw,
    "; sample_mutation([OperatorMutation() => 0.0, ConstantMutation() => 1.0]) = ",
    choice,
)
if draw == 0.0 && choice isa OperatorMutation
    println("REPRODUCED mutgen-sample-exported-zero-draw")
end
