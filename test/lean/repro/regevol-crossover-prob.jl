# Reproducer for registry entry `regevol-crossover-prob` (SymReg/Population/RegEvol.lean).
# The branch test is rand() > crossover_probability (src/RegularizedEvolution.jl:130). rand()
# can return exactly 0.0, so crossover_probability = 0.0 still runs a crossover. The default
# RNG is put in a state whose next Float64 is 0.0 (Xoshiro256++ output rotl(s0 + s3, 23) + s0
# is 0 when s0 = s3 = 0); every mutation fails and is skipped, so any change of the population
# comes from a crossover.
using SymbolicRegression
using SymbolicRegression: Dataset, HallOfFame, MutationResult
using SymbolicRegression.RegularizedEvolutionModule: reg_evol_cycle
using Random

struct FailingMutation <: SymbolicRegression.AbstractMutation end
function SymbolicRegression.mutate!(
    tree::N, ::P, ::FailingMutation, options; kws...
) where {N,P}
    return MutationResult{N,P}(; tree, success=false)
end

Random.seed!(0)
X = randn(2, 50)
y = X[1, :] .+ 1
dataset = Dataset(X, y)
options = Options(;
    binary_operators=[+, *],
    default_mutations=(),
    mutations=(FailingMutation() => 1.0,),
    crossover_probability=0.0,
    skip_mutation_failures=true,
    population_size=2,
    tournament_selection_n=1,
)
plugin_states = SymbolicRegression.init_plugin_states(options, dataset)

function replaced_after_cycle(rng_state)
    pop = Population(
        dataset; population_size=2, nlength=3, options, nfeatures=2, plugin_states
    )
    before = copy(pop.members)  # the member objects
    best_seen = HallOfFame(options, dataset)
    # No RNG draw happens between this point and the `rand()` at src/RegularizedEvolution.jl:130.
    copy!(Random.default_rng(), rng_state)
    reg_evol_cycle(
        dataset, pop, options.maxsize, options, nothing; plugin_states, best_seen
    )
    return count(i -> pop.members[i] !== before[i], 1:pop.n)
end

probe = Xoshiro(
    0x0000000000000000, 0x0123456789abcdef, 0x0fedcba987654321, 0x0000000000000000
)
println("first rand() from the crafted state: ", rand(copy(probe)))
control = sum(s -> replaced_after_cycle(Xoshiro(s)), 1:20)
println(
    "control (20 ordinary seeds): members replaced = ", control, " (mutations always fail)"
)
replaced = replaced_after_cycle(probe)
println(
    "crossover_probability = 0.0, first rand() = 0.0: members replaced = ",
    replaced,
    " (expected 0)",
)
if control == 0 && replaced > 0
    println("REPRODUCED regevol-crossover-prob")
end
