# Reproducer for registry entry `mutgen-cond-optimize-constant` (SymReg/MutateGen/ConditionProps.lean).
# condition_mutation_weights! zeroes OptimizeMutation on a variable leaf (src/Mutate.jl:184-186)
# but never on an operator tree without constants, where optimize_constants returns the member
# unchanged with zero evaluations (src/ConstantOptimization.jl:148-150).
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember, optimize_constants
using SymbolicRegression.MutateModule: condition_mutation_weights!
using DynamicExpressions: Node

X = randn(2, 20)
dataset = Dataset(X, X[1, :] .+ 1)
options = Options(; binary_operators=[+, *], mutations=[OptimizeMutation() => 0.1])
x1, x2 = Node(Float64; feature=1), Node(Float64; feature=2)
member = PopMember(dataset, x1 + x2, options; deterministic=false)

weights = copy(options.mutations)
condition_mutation_weights!(weights, member, options, 10, 2)
w = only(p.second for p in weights if p.first isa OptimizeMutation)
result, evals = optimize_constants(dataset, member, options)
println(
    "tree ",
    member.tree,
    ": conditioned OptimizeMutation weight = ",
    w,
    "; optimize_constants returns the same member: ",
    result === member,
    ", evals = ",
    evals,
)
if w > 0 && result === member && evals == 0
    println("REPRODUCED mutgen-cond-optimize-constant")
end
