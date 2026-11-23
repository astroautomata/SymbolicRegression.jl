using SymbolicRegression
using SymbolicRegression: Dataset, Node, PopMember, get_tree
using SymbolicRegression.ComplexityModule: compute_complexity
using SymbolicRegression.ConstantOptimizationModule: optimize_constants
using SymbolicRegression.LossFunctionsModule: loss_to_cost

mapping(ex) = get_tree(ex).val < 2.0 ? 1 : 3
objective(ex, _, _) = abs2(get_tree(ex).val - 3.0)
options = Options(;
    binary_operators=[+],
    complexity_mapping=mapping,
    parsimony=0.125,
    deterministic=true,
    optimizer_nrestarts=0,
    autodiff_backend=nothing,
    loss_function_expression=objective,
)
dataset = Dataset(zeros(1, 4), fill(3.0, 4))
member = PopMember(dataset, Node(Float64; val=1.0), options; deterministic=true)
old_loss = member.loss
old_complexity = compute_complexity(member, options)
returned, _ = optimize_constants(dataset, member, options)
actual_complexity = compute_complexity(returned, options)
fresh_complexity = compute_complexity(returned.tree, options)
fresh_cost = loss_to_cost(
    returned.loss,
    dataset.use_baseline,
    dataset.baseline_loss,
    returned,
    options,
    fresh_complexity,
)
println(
    "complexity: before=$old_complexity cached=$actual_complexity fresh=$fresh_complexity"
)
println("cost: stored=$(returned.cost) fresh=$fresh_cost")
if returned === member &&
    returned.loss < old_loss &&
    old_complexity == actual_complexity &&
    actual_complexity != fresh_complexity &&
    returned.cost != fresh_cost
    println("REPRODUCED copt-accepted-scores-fresh")
end
