# Reproducer for registry entry `mut-mutate-operator-changes` (SymReg/Mutations/Refute.lean).
# mutate_operator draws the new operator from all operators of the node's degree, including
# the current one (src/MutationFunctions.jl:118), so it often leaves the tree unchanged.
using SymbolicRegression, DynamicExpressions, Random
using SymbolicRegression.MutationFunctionsModule: mutate_operator

options = Options(; binary_operators=[+, *], unary_operators=[cos])
x1 = Node(Float64; feature=1)
kept = 0
for seed in 1:1000
    tree = Node(1, x1, copy(x1))  # x1 + x1
    out = mutate_operator(tree, options, Xoshiro(seed))
    global kept += (out.degree == 2 && out.op == 1)
end
println("mutations that kept operator + out of 1000: ", kept)
if kept > 0
    println("REPRODUCED mut-mutate-operator-changes")
end
