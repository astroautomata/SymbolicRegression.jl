# Reproducer for registry entry `mut-rotate-graph-acyclic` (SymReg/Mutations/Refute.lean).
# randomly_rotate_tree! (src/MutationFunctions.jl:626-656) on a GraphNode whose root holds the
# same pivot object in two slots: set_child!(root, grand_child, pivot_idx) replaces only one of
# them, then set_child!(pivot, root, grand_child_idx) makes the pivot point back to the root,
# which still points to the pivot through its other slot: a cycle.
using SymbolicRegression, DynamicExpressions, Random
using SymbolicRegression.MutationFunctionsModule: randomly_rotate_tree!
using DynamicExpressions: get_child

function has_cycle(n, onpath=IdDict{Any,Bool}())
    haskey(onpath, n) && return true
    onpath[n] = true
    for i in 1:(n.degree)
        has_cycle(get_child(n, i), onpath) && return true
    end
    delete!(onpath, n)
    return false
end

cycles = 0
for seed in 1:100
    x = GraphNode(Float64; feature=1)
    p = GraphNode(1, x)        # sin(x1)
    tree = GraphNode(1, p, p)  # sin(x1) + sin(x1), one shared object
    @assert !has_cycle(tree)
    out = randomly_rotate_tree!(tree, Xoshiro(seed))
    has_cycle(out) && (global cycles += 1)
end
println("rotations of p + p (p shared) that produced a cycle, out of 100 seeds: ", cycles)
if cycles > 0
    println("REPRODUCED mut-rotate-graph-acyclic")
end
