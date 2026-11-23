using SymbolicRegression
using DynamicExpressions: Node, get_tree, count_nodes

options = SymbolicRegression.Options(;
    binary_operators=[+],
    should_simplify=true,
    should_optimize_constants=false,
    complexity_mapping=(ex -> 20 - count_nodes(get_tree(ex))),
)
dataset = SymbolicRegression.Dataset(reshape([0.0], 1, :), [3.0])
tree = Node(1, Node(Float64; val=1.0), Node(Float64; val=2.0))
parent = SymbolicRegression.PopMember(dataset, tree, options; deterministic=false)
before = SymbolicRegression.compute_complexity(parent.tree, options)
result = SymbolicRegression.MutateModule.mutate!(
    copy(parent.tree),
    parent,
    SymbolicRegression.SimplifyMutation(),
    options;
    trace=nothing,
    dataset,
    parent_ref=parent.ref,
    curmaxsize=18,
)
after = SymbolicRegression.compute_complexity(result.member.tree, options)
accepted = result.return_immediately && result.success
println(
    "custom complexity=20-count_nodes: before=",
    before,
    ", after=",
    after,
    ", curmaxsize=18, immediate acceptance=",
    accepted,
)
if before == 17 && after == 19 && accepted
    println("REPRODUCED simp-custom-maxsize")
end
