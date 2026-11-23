using SymbolicRegression: Options, Dataset, Node, eval_loss

options = Options(; elementwise_loss=(target, prediction) -> target)
dataset = Dataset(reshape([2.0], 1, 1), [7.0])
actual = eval_loss(Node(Float64; feature=1), dataset, options)
@assert actual == 2.0 && actual != 7.0
println("expected 7.0; got ", actual)
println("REPRODUCED loss-unweighted-mean")

weighted_options = Options(;
    elementwise_loss=(target, prediction, weight) -> weight * target
)
weighted_dataset = Dataset(reshape([2.0], 1, 1), [7.0]; weights=[3.0])
weighted = eval_loss(Node(Float64; feature=1), weighted_dataset, weighted_options)
@assert weighted == 2.0 && weighted != 7.0
println("weighted: expected 7.0; got ", weighted)
println("REPRODUCED loss-custom-weighted-sum")
