# Reproducer for registry entry `mutgen-cond-swap-arity` (SymReg/MutateGen/ConditionProps.lean).
# condition_mutation_weights! zeroes SwapOperandsMutation unless some node has degree == 2
# (src/Mutate.jl:193-195), but swap_operands swaps two children of any node with degree > 1
# (src/MutationFunctions.jl:88-101). On a tree whose only operator is ternary the swap is
# disabled although it applies.
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.MutateModule: condition_mutation_weights!
using SymbolicRegression.MutationFunctionsModule: swap_operands
using DynamicExpressions: Node, OperatorEnum
using Random

X = randn(3, 20)
dataset = Dataset(X, X[1, :])
options = Options(; operators=OperatorEnum(1 => (cos,), 2 => (+,), 3 => (fma,)))
leaf(i) = Node{Float64,3}(; feature=i)
tree = Node{Float64,3}(; op=1, children=(leaf(1), leaf(2), leaf(3)))
member = PopMember(dataset, tree, options; deterministic=false)

weights = copy(options.mutations)
condition_mutation_weights!(weights, member, options, 10, 3)
before = only(p.second for p in options.mutations if p.first isa SwapOperandsMutation)
after = only(p.second for p in weights if p.first isa SwapOperandsMutation)
Random.seed!(0)
swapped = swap_operands(copy(member.tree))
changed = string(swapped) != string(member.tree)
println("tree: ", member.tree, "  swap_operands gives: ", swapped)
println("SwapOperandsMutation weight: options ", before, ", conditioned ", after)
if before > 0 && after == 0 && changed
    println("REPRODUCED mutgen-cond-swap-arity")
end
