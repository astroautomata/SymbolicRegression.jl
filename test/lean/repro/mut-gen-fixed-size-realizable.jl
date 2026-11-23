# Reproducer for registry entry `mut-gen-fixed-size-realizable` (SymReg/Mutations/Refute.lean).
# gen_random_tree_fixed_size (src/MutationFunctions.jl:464-494) grows the tree greedily: with
# binary and ternary operators only (nops == (0, 1, 1)) and node_count = 4, the first arity is 2
# or 3 with equal probability; after arity 2 one node remains, no unary operator exists, and the
# loop stops at 3 nodes, although a ternary root over three leaves has exactly 4.
using SymbolicRegression, DynamicExpressions, Random
using SymbolicRegression.MutationFunctionsModule: gen_random_tree_fixed_size

options = Options(; operators=OperatorEnum(1 => (), 2 => (+,), 3 => (fma,)))
println("nops = ", options.nops)
sizes = [
    count_nodes(gen_random_tree_fixed_size(4, options, 1, Float64, Xoshiro(seed))) for
    seed in 1:200
]
println(
    "sizes for node_count = 4 over 200 seeds: ",
    sort(unique(sizes)),
    ", count of size 4: ",
    count(==(4), sizes),
    ", count of size 3: ",
    count(==(3), sizes),
)
if any(!=(4), sizes)
    println("REPRODUCED mut-gen-fixed-size-realizable")
end
