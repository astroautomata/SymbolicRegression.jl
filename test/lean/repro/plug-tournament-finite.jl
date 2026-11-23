using SymbolicRegression
using SymbolicRegression: Dataset, PopMember, tournament_cost_multiplier, compute_complexity
using SymbolicRegression.AdaptiveParsimonyModule: AdaptiveParsimonyPlugin, init_plugin_state
using SymbolicRegression.PopulationModule: _best_of_sample

p = AdaptiveParsimonyPlugin()
options = Options(;
    binary_operators=[+, *],
    plugins=(p,),
    default_plugins=(),
    maxsize=10,
    tournament_selection_n=2,
    population_size=10,
    tournament_selection_p=1.0,
)
X = reshape(Float32[1, 2, 3, 4], 1, :)
dataset = Dataset(X, vec(X))
s = init_plugin_state(p, options, dataset)
members = [
    PopMember(dataset, Node{Float32}(; feature=1), options; deterministic=false) for
    _ in 1:2
]
@assert typeof(members[1].cost) === Float32
members[1].cost = 2.0f0
members[2].cost = 1.0f0
f = s.rss.normalized_frequencies[compute_complexity(members[1], options)]
multiplier = tournament_cost_multiplier(s, p, members[1], options)
adjusted = [m.cost * tournament_cost_multiplier(s, p, m, options) for m in members]
winner = _best_of_sample(members, [1, 2], options; plugin_states=(s,))
zero_adjusted = 0.0f0 * multiplier
println(
    "Float32 data; default scaling = ",
    options.adaptive_parsimony_scaling,
    "; normalized frequency = ",
    f,
)
println(
    "Float32 threshold log(floatmax)/scaling = ",
    log(Float64(floatmax(Float32))) / options.adaptive_parsimony_scaling,
)
println(
    "Float64 threshold log(floatmax)/scaling = ",
    log(floatmax(Float64)) / options.adaptive_parsimony_scaling,
)
println(
    "plugin multiplier = ", multiplier, "; expected finite multiplier for finite inputs"
)
println(
    "costs = ",
    [m.cost for m in members],
    "; adjusted costs = ",
    adjusted,
    "; zero adjusted cost = ",
    zero_adjusted,
)
println("winner cost = ", winner.cost, "; expected lower cost = ", members[2].cost)
@assert isinf(multiplier) && all(isinf, adjusted) && isnan(zero_adjusted)
@assert winner === members[1]
println("REPRODUCED plug-tournament-finite")
