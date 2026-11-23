# Reproducer for registry entry `mutgen-cond-feature-nfeatures` (SymReg/MutateGen/ConditionProps.lean).
# condition_mutation_weights! returns early for a leaf (src/Mutate.jl:179-191), before the
# `nfeatures <= 1` check that zeroes FeatureMutation (src/Mutate.jl:199-201). On a variable
# leaf with one feature, FeatureMutation keeps its weight although mutate_feature returns
# the tree unchanged (src/MutationFunctions.jl:200).
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.MutateModule: condition_mutation_weights!
using SymbolicRegression.MutationFunctionsModule: mutate_feature
using DynamicExpressions: Node

X = randn(1, 20)
dataset = Dataset(X, X[1, :] .+ 1)
options = Options(; binary_operators=[+, *])
member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=false)

weights = copy(options.mutations)
condition_mutation_weights!(weights, member, options, 10, 1)
w = only(p.second for p in weights if p.first isa FeatureMutation)
mutated = mutate_feature(copy(member.tree), 1)
println(
    "leaf ",
    member.tree,
    ", nfeatures = 1: conditioned FeatureMutation weight = ",
    w,
    "; mutate_feature gives ",
    mutated,
)
if w > 0 && string(mutated) == string(member.tree)
    println("REPRODUCED mutgen-cond-feature-nfeatures")
end

include("mutgen-cond-add-maxsize.jl")
