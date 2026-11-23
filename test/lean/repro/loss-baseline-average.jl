using SymbolicRegression
using SymbolicRegression:
    Dataset, update_baseline_loss!, eval_loss, eval_cost, create_expression
using SymbolicRegression: MutationAcceptanceContext, mutation_acceptance_multiplier
using SymbolicRegression.SimulatedAnnealingModule:
    SimulatedAnnealingPlugin, SimulatedAnnealingState
using DynamicExpressions
using Random

println("Julia ", VERSION, "; DynamicExpressions ", pkgversion(DynamicExpressions))

options = Options(; binary_operators=[+])
dataset = Dataset(reshape(Float32[1, 2], 1, :), Float32[99, 101])
update_baseline_loss!(dataset, options)
average = sum(dataset.y) / length(dataset.y)
mean_tree = create_expression(average, options, dataset)
expected = eval_loss(mean_tree, dataset, options)
cost, raw_loss = eval_cost(dataset, mean_tree, options)
println(
    "avg_y=",
    dataset.avg_y,
    " target_average=",
    average,
    " baseline_loss=",
    dataset.baseline_loss,
    " loss_at_average=",
    expected,
    " use_baseline=",
    dataset.use_baseline,
)
println(
    "mean predictor: raw loss=",
    raw_loss,
    ", actual cost=",
    cost,
    ", cost with mean baseline=",
    raw_loss / expected + options.parsimony,
)

# Hold the proposed change in raw loss fixed so only the normalization differs.
centered = Dataset(dataset.X, dataset.y .- average)
update_baseline_loss!(centered, options)
annealing = only(p for p in options.plugins if p isa SimulatedAnnealingPlugin)
temperature = SimulatedAnnealingState(1.0)
function multiplier(delta)
    mutation_acceptance_multiplier(
        temperature,
        annealing,
        MutationAcceptanceContext(nothing, nothing, zero(delta), delta),
        options,
    )
end
actual_multiplier = multiplier(1 / dataset.baseline_loss)
expected_multiplier = multiplier(1 / centered.baseline_loss)
draws = rand(Xoshiro(42), 10_000)
println(
    "At T=1, alpha=",
    annealing.alpha,
    ", raw loss increase=1: ",
    "acceptance probability (offset vs centered) ",
    actual_multiplier,
    " vs ",
    expected_multiplier,
    "; accepted out of 10000 identical seeded draws: ",
    count(<=(actual_multiplier), draws),
    " vs ",
    count(<=(expected_multiplier), draws),
)
if average == 100 &&
    dataset.baseline_loss == 10001 &&
    expected == raw_loss == 1 &&
    dataset.use_baseline &&
    cost ≈ 1.0f0 / 10001.0f0 + Float32(options.parsimony)
    println("REPRODUCED loss-baseline-average")
end
