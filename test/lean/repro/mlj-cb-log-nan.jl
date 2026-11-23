# Reproducer for registry entry `mlj-cb-log-nan` (SymReg/MLJ/SelectProps.lean).
# choose_best (src/MLJInterface.jl:715-730) computes `1.5 * minimum(losses)`; one NaN loss
# makes the threshold NaN, so every row is masked to -Inf and argmax returns 1.
using SymbolicRegression
using SymbolicRegression.MLJInterfaceModule: choose_best

losses = [2.0, 1.0, NaN]
scores = [0.0, 1.0, 0.0]
idx = choose_best(;
    trees=nothing, losses, scores, complexities=[1, 2, 3], options=Options()
)
println("losses = $losses, scores = $scores: choose_best = $idx (expected 2)")
if idx == 1
    println("REPRODUCED mlj-cb-log-nan")
end
