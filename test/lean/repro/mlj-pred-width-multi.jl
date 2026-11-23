# Reproducer for registry entry `mlj-pred-width-multi` (SymReg/MLJ/PredictProps.lean).
# In multitarget `_predict` (src/MLJInterface.jl:599-604), a target whose equation fails to
# evaluate contributes `prediction_fallback(...)`, which is a whole n x num_targets matrix,
# so `reduce(hcat, outs)` has more columns than targets.
using SymbolicRegression
using SymbolicRegression: machine, fit!, predict
using SymbolicRegression.MLJInterfaceModule: MultitargetSRTestRegressor
using DynamicExpressions: with_contents
using Random

Random.seed!(0)
Xm = randn(30, 2)
Y = hcat(Xm[:, 1], Xm[:, 2] .+ 1)
model = MultitargetSRTestRegressor(;
    binary_operators=[+, *],
    populations=1,
    population_size=20,
    ncycles_per_iteration=10,
    parallelism=:serial,
)
mach = machine(model, Xm, Y)
fit!(mach; verbosity=0)
# Keep one known equation per target: x1 * 1.0 for target 1, the constant 2.0 for target 2.
hofs = mach.fitresult.state[2]
function only_slot!(hof, c, tree)
    fill!(hof.exists, false)
    m = hof.members[c]
    m.tree = with_contents(m.tree, tree)
    setfield!(m, :complexity, c)
    m.loss = 1.0
    m.cost = 1.0
    hof.exists[c] = true
    return nothing
end
only_slot!(hofs[1], 3, Node(2, Node{Float64}(; feature=1), Node{Float64}(; val=1.0)))
only_slot!(hofs[2], 1, Node{Float64}(; val=2.0))
Xnew = hcat(fill(NaN, 4), zeros(4))  # target 1 evaluates to NaN, target 2 to 2.0
out = predict(mach, Xnew)
println("num_targets = 2, predict output size = ", size(out))
display(out)
println()
if size(out, 2) != 2
    println("REPRODUCED mlj-pred-width-multi")
end
