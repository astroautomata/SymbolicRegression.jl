# Reproducer for registry entry `pop-ctor-matrix-nlength` (SymReg/Population/Pop.lean).
# Population(X, y; nlength) does not forward nlength (src/Population.jl:144), so the trees are
# built with the default nlength=3. With only binary operators, gen_random_tree(l, ...) yields
# exactly l operators, i.e. 2l + 1 nodes.
using SymbolicRegression
using SymbolicRegression: Dataset
using DynamicExpressions: count_nodes
using Random

Random.seed!(0)
options = Options(; binary_operators=[+, *], population_size=10, tournament_selection_n=2)
X = randn(2, 50)
y = X[1, :] .+ 1
plugin_states = SymbolicRegression.init_plugin_states(options, Dataset(X, y))
pop = Population(X, y; population_size=8, nlength=10, options, nfeatures=2, plugin_states)
sizes = [count_nodes(m.tree) for m in pop.members]
println("node counts with nlength=10: ", sizes, " (expected 21 each)")
if all(==(7), sizes)
    println("REPRODUCED pop-ctor-matrix-nlength")
end
