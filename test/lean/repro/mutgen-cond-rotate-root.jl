# Reproducer for registry entry `mutgen-cond-rotate-root` (SymReg/MutateGen/ConditionProps.lean).
# condition_mutation_weights! never zeroes RotateTreeMutation, but randomly_rotate_tree!
# returns the tree unchanged when no node is a valid rotation root
# (src/MutationFunctions.jl:617-630), e.g. on every leaf.
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.MutateModule: condition_mutation_weights!
using SymbolicRegression.MutationFunctionsModule: randomly_rotate_tree!
using DynamicExpressions: Node

X = randn(2, 20)
dataset = Dataset(X, X[1, :] .+ 1)
options = Options(; binary_operators=[+, *])
member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=false)

weights = copy(options.mutations)
condition_mutation_weights!(weights, member, options, 10, 2)
w = only(p.second for p in weights if p.first isa RotateTreeMutation)
rotated = randomly_rotate_tree!(copy(member.tree))
println(
    "leaf ",
    member.tree,
    ": conditioned RotateTreeMutation weight = ",
    w,
    "; randomly_rotate_tree! gives ",
    rotated,
)
if w > 0 && string(rotated) == string(member.tree)
    println("REPRODUCED mutgen-cond-rotate-root")
end
