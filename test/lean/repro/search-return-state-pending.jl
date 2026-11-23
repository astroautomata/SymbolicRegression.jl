using SymbolicRegression

mutable struct PendingReturnProbe <: SymbolicRegression.AbstractPlugin
    forks::Int
    collections::Int
    release::Channel{Nothing}
end
struct PendingReturnState
    worker::Int
end
function SymbolicRegression.init_plugin_state(::PendingReturnProbe, options, data)
    PendingReturnState(0)
end
function SymbolicRegression.fork_plugin_state(
    head::PendingReturnState, p::PendingReturnProbe, data
)
    p.forks += 1
    return PendingReturnState(p.forks)
end
function SymbolicRegression.on_cycle_start!(
    state::PendingReturnState, p::PendingReturnProbe, cycle::Int, ncycles::Int, options
)
    state.worker == 2 && take!(p.release)
    return nothing
end
function SymbolicRegression.on_generation_end!(
    ::PendingReturnState, p::PendingReturnProbe, ss, data, options, ropt, pop
)
    p.collections += 1
    p.collections == 2 && put!(p.release, nothing)
    return nothing
end

probe = PendingReturnProbe(0, 0, Channel{Nothing}(1))
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
saved, hof = equation_search(
    X,
    y;
    options,
    niterations=1,
    parallelism=:multithreading,
    return_state=true,
    runtests=false,
)
actual = sort([length(p.members) for p in only(saved)])
expected = fill(options.population_size, options.populations)
println("returned population member counts actual=$actual expected=$expected")
@assert probe.collections == 2
@assert actual == [1, 4]
@assert actual != expected
println("REPRODUCED search-return-state-pending")
