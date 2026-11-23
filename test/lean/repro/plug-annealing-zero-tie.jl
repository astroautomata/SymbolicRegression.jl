using SymbolicRegression
using SymbolicRegression:
    Dataset,
    PopMember,
    MutationAcceptanceContext,
    mutation_acceptance_multiplier,
    init_plugin_state,
    on_cycle_start!
using SymbolicRegression.SimulatedAnnealingModule: SimulatedAnnealingPlugin

p = SimulatedAnnealingPlugin()
options = Options(; binary_operators=[+, *], plugins=(p,), default_plugins=())
X = reshape([1.0, 2.0, 3.0], 1, :)
dataset = Dataset(X, vec(X))
m = PopMember(dataset, Node{Float64}(; feature=1), options; deterministic=false)
s = init_plugin_state(p, options, dataset)
on_cycle_start!(s, p, 2, 2, options)
probabilities = map((2.0, 1.0, 0.0)) do after
    ctx = MutationAcceptanceContext(m, m.tree, 1.0, after)
    mutation_acceptance_multiplier(s, p, ctx, options)
end
println("last-cycle temperature = ", s.temperature)
println(
    "worse/equal/better costs give multipliers = ",
    probabilities,
    "; expected equal-cost multiplier = 1.0",
)
println("engine accepts equal-cost NaN multiplier at draw .5 = ", !(probabilities[2] < 0.5))
@assert probabilities[1] == 0.0 && isnan(probabilities[2]) && isinf(probabilities[3])
println("REPRODUCED plug-annealing-zero-tie")
