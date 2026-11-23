using SymbolicRegression
using SymbolicRegression: Dataset, eval_loss, create_expression
using SymbolicRegression.CoreModule: batch

options = Options(; binary_operators=[+], parsimony=0.0)
dataset = Dataset(reshape([1.0, 3.0], 1, :), [0.0, 0.0]; weights=[1.0, 3.0])
tree = create_expression(Node(Float64; feature=1), options, dataset)
with_idx = eval_loss(tree, dataset, options; idx=[1])
with_view = eval_loss(tree, batch(dataset, [1]), options)
println("eval_loss(idx=[1])=", with_idx, " eval_loss(batch([1]))=", with_view)
if with_idx == 7.0 && with_view == 1.0
    println("REPRODUCED loss-explicit-index")
end
