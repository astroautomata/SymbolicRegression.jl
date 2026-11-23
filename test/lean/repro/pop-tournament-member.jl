using Random
using SymbolicRegression
using SymbolicRegression:
    AbstractOptions, AbstractPlugin, AbstractPopMember, Dataset, PopMember
using SymbolicRegression.PopulationModule: Population, best_of_sample

struct NestedTournament <: AbstractPlugin end
struct NestedTournamentState{P,O}
    pop::P
    options::O
    sampled::Ref{Int}
end

function SymbolicRegression.tournament_cost_multiplier(
    state::NestedTournamentState,
    ::NestedTournament,
    member::AbstractPopMember,
    options::AbstractOptions,
)
    state.sampled[] = findfirst(m -> m === member, state.pop.members)
    best_of_sample(state.pop, state.options; plugin_states=())
    return one(member.cost)
end

common = (;
    default_plugins=(),
    population_size=2,
    tournament_selection_n=1,
    tournament_selection_p=1.0,
)
inner = Options(; common...)
outer = Options(; common..., plugins=(NestedTournament(),))
X = reshape([1.0, 2.0], 1, :)
dataset = Dataset(X, X[1, :])
pop = Population([
    PopMember(dataset, Node{Float64}(; feature=1), inner; deterministic=false) for _ in 1:2
])
state = NestedTournamentState(pop, inner, Ref(0))
for seed in 0:127
    Random.seed!(seed)
    winner = best_of_sample(pop, outer; plugin_states=(state,))
    slot = findfirst(m -> m === winner, pop.members)
    if slot !== nothing && slot != state.sampled[]
        println(
            "Original sample slot: ", state.sampled[], "; returned population slot: ", slot
        )
        println("REPRODUCED pop-tournament-member")
        break
    end
end
