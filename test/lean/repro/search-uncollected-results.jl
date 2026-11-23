using SymbolicRegression

struct SearchReceiptProbe <: SymbolicRegression.AbstractPlugin
    cycles::Base.RefValue{Int}
    collections::Base.RefValue{Int}
end
function SymbolicRegression.on_cycle_end!(_, p::SearchReceiptProbe, pop, data, hof, options)
    (p.cycles[] += 1; nothing)
end
function SymbolicRegression.on_generation_end!(
    _, p::SearchReceiptProbe, state, data, options, ropt, pop
)
    (p.collections[] += 1; nothing)
end

probe = SearchReceiptProbe(Ref(0), Ref(0))
options = Options(;
    binary_operators=[+],
    populations=2,
    population_size=4,
    tournament_selection_n=1,
    ncycles_per_iteration=1,
    should_optimize_constants=false,
    should_simplify=false,
    save_to_file=false,
    input_stream=devnull,
    plugins=(probe,),
    verbosity=0,
    progress=false,
    seed=123,
)
X = reshape(Float64[1, 2, 3, 4], 1, :)
y = Float64[2, 4, 6, 8]
equation_search(X, y; options, niterations=1, parallelism=:serial, runtests=false)
actual = probe.collections[]
expected = probe.cycles[]
println("collected results actual=$actual expected=$expected (one per executed dispatch)")
@assert actual == 2
@assert expected == 3
println("REPRODUCED search-uncollected-results")
