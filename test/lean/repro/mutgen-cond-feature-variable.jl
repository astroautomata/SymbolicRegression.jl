# Reproducer for registry entry `mutgen-cond-feature-variable` (SymReg/MutateGen/ConditionProps.lean).
# condition_mutation_weights! zeroes FeatureMutation on a constant leaf (src/Mutate.jl:187-189)
# but never on an operator tree without variables, where mutate_feature also returns the tree
# unchanged (src/MutationFunctions.jl:201).
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.MutateModule: condition_mutation_weights!
using SymbolicRegression.MutationFunctionsModule: mutate_feature
using DynamicExpressions: Node

X = randn(2, 20)
dataset = Dataset(X, X[1, :] .+ 1)
options = Options(; binary_operators=[+, *])
tree = Node{Float64,2}(;
    op=1, children=(Node{Float64,2}(; val=1.0), Node{Float64,2}(; val=2.0))
)
member = PopMember(dataset, tree, options; deterministic=false)

weights = copy(options.mutations)
condition_mutation_weights!(weights, member, options, 10, 2)
w = only(p.second for p in weights if p.first isa FeatureMutation)
mutated = mutate_feature(copy(member.tree), 2)
println(
    "tree ",
    member.tree,
    ", nfeatures = 2: conditioned FeatureMutation weight = ",
    w,
    "; mutate_feature gives ",
    mutated,
)
if w > 0 && string(mutated) == string(member.tree)
    println("REPRODUCED mutgen-cond-feature-variable")
end
