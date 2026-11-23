# Reproducer for registry entry `pop-tournament-rank` (SymReg/Population/Tournament.lean).
# bottomk_fast (src/Utils.jl:97-131) never inserts costs equal to Inf (or NaN), so place 2 of the
# sample [5.0, Inf] goes to the place-1 member. With p = 0.5 and n = 2 place 2 is drawn with
# probability 1/3, yet the Inf-cost member is never selected.
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.PopulationModule: _best_of_sample
using SymbolicRegression.UtilsModule: bottomk_fast
using Random

Random.seed!(0)
options = Options(;
    binary_operators=[+, *],
    default_plugins=(),
    tournament_selection_p=0.5,
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
println("bottomk_fast([5.0, Inf], 2) = ", bottomk_fast([5.0, Inf], 2))
members = [member_with_cost(5.0), member_with_cost(Inf)]
trials = 3000
second = count(
    _ -> _best_of_sample(members, [1, 2], options; plugin_states=()) === members[2],
    1:trials,
)
println(
    "Inf-cost member chosen in ",
    second,
    " of ",
    trials,
    " tournaments (expected about ",
    trials ÷ 3,
    ")",
)
if bottomk_fast([5.0, Inf], 2)[2][end] == 1 && second == 0
    println("REPRODUCED pop-tournament-rank")
end

include("util-bottomk-sentinel.jl")
