# Reproducer for registry entry `mutgen-cond-add-maxsize` (SymReg/MutateGen/ConditionProps.lean).
# condition_mutation_weights! returns early for a leaf (src/Mutate.jl:179-191), before the
# `complexity >= curmaxsize` check that zeroes AddNodeMutation and InsertNodeMutation
# (src/Mutate.jl:203-207). With complexity_of_variables = 3 a variable leaf already has
# complexity 3 = curmaxsize, yet both growth mutations keep their weights.
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember, compute_complexity
using SymbolicRegression.MutateModule: condition_mutation_weights!
using DynamicExpressions: Node

X = randn(2, 20)
dataset = Dataset(X, X[1, :] .+ 1)
options = Options(; binary_operators=[+, *], complexity_of_variables=3)
member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=false)
curmaxsize = 3

weights = copy(options.mutations)
condition_mutation_weights!(weights, member, options, curmaxsize, 2)
c = compute_complexity(member, options)
add = only(p.second for p in weights if p.first isa AddNodeMutation)
ins = only(p.second for p in weights if p.first isa InsertNodeMutation)
println(
    "leaf complexity = ",
    c,
    ", curmaxsize = ",
    curmaxsize,
    ": conditioned AddNode weight = ",
    add,
    ", InsertNode weight = ",
    ins,
)
if c >= curmaxsize && add > 0 && ins > 0
    println("REPRODUCED mutgen-cond-add-maxsize")
end
