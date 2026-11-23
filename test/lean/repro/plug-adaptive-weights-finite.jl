using SymbolicRegression
using SymbolicRegression:
    AbstractMutation,
    ConstantMutation,
    OperatorMutation,
    MutationEvent,
    init_plugin_state,
    on_mutation_end!
using SymbolicRegression.AdaptiveMutationWeightsModule:
    AdaptiveMutationWeightsPlugin, condition_mutation_weights!

p = AdaptiveMutationWeightsPlugin(; adaptation_strength=1.0)
options = Options(;
    binary_operators=[+, *],
    plugins=(p,),
    default_plugins=(),
    default_mutations=(),
    mutations=(ConstantMutation() => floatmax(Float64), OperatorMutation() => 1.0),
)
s = init_plugin_state(p, options, nothing)
idx = findfirst(x -> first(x) isa ConstantMutation, options.mutations)
event = MutationEvent(true, 2.0, 1.0, 2.0, 1.0, idx)
on_mutation_end!(s, p, ConstantMutation(), event, nothing, options)
weights = Pair{AbstractMutation,Float64}[m => w for (m, w) in options.mutations]
println(
    "after one improving mutation: multipliers = ",
    s.multipliers,
    "; all finite and nonnegative = ",
    all(x -> isfinite(x) && x >= 0, s.multipliers),
)
println("base weights = ", last.(weights))
condition_mutation_weights!(weights, s, p, nothing, options, options.maxsize, 1)
println("adjusted weights = ", last.(weights), "; expected finite nonnegative weights")
@assert all(x -> isfinite(x) && x >= 0, s.multipliers)
@assert isinf(last(weights[idx]))
println("REPRODUCED plug-adaptive-weights-finite")
