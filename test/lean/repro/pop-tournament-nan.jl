# Reproducer for registry entry `pop-tournament-nan` (SymReg/Population/Tournament.lean).
# With tournament_selection_p = 1.0 the first-place loop (src/Population.jl:203-209) starts from
# the first sampled member; a NaN cost there is never beaten, although the comment says a NaN
# cost never wins.
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.PopulationModule: _best_of_sample
using Random

Random.seed!(0)
options = Options(;
    binary_operators=[+, *],
    default_plugins=(),
    tournament_selection_p=1.0,
    tournament_selection_n=2,
    population_size=10,
)
X = randn(1, 20)
dataset = Dataset(X, X[1, :])
function member_with_cost(c)
    m = PopMember(dataset, Node{Float64}(; feature=1), options; deterministic=false)
    m.cost = c
    return m
end
members = [member_with_cost(NaN), member_with_cost(1.0)]
winner = _best_of_sample(members, [1, 2], options; plugin_states=())
println("sample costs [NaN, 1.0], p = 1.0: winner cost = ", winner.cost, " (expected 1.0)")
if isnan(winner.cost)
    println("REPRODUCED pop-tournament-nan")
end
