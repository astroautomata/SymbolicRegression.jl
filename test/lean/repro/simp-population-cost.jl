using SymbolicRegression
using DynamicExpressions: Node

options = SymbolicRegression.Options(;
    binary_operators=[+],
    should_simplify=true,
    should_optimize_constants=false,
    batching=false,
    parsimony=1.0,
)
dataset = SymbolicRegression.Dataset(reshape([0.0], 1, :), [3.0])
tree = Node(1, Node(Float64; val=1.0), Node(Float64; val=2.0))
member = SymbolicRegression.PopMember(dataset, tree, options; deterministic=false)
pop = SymbolicRegression.Population([member])
before = member.cost
SymbolicRegression.SingleIterationModule.optimize_and_simplify_population(
    dataset, pop, options, options.maxsize, nothing
)
stored = member.cost
expected, _ = SymbolicRegression.LossFunctionsModule.eval_cost(dataset, member, options)
println(
    "1+2 -> 3 with parsimony=1: previous cost=",
    before,
    ", stored cost=",
    stored,
    ", recomputed cost=",
    expected,
)
if before == 3.0 && stored == 3.0 && expected == 1.0
    println("REPRODUCED simp-population-cost")
end
