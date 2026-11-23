using SymbolicRegression
using SymbolicRegression.CoreModule:
    WarmStartIncompatibleError, check_warm_start_compatibility

function search_options(maxsize)
    return Options(;
        binary_operators=[+, *],
        maxsize,
        populations=1,
        population_size=4,
        maxdepth=3,
        tournament_selection_n=2,
        should_optimize_constants=false,
        deterministic=true,
        seed=12,
        input_stream=devnull,
        save_to_file=false,
    )
end

x = collect(1.0:8.0)
X = reshape(x, 1, :)
y = x .+ x .^ 2
old, new = search_options(7), search_options(4)
params = (; niterations=0, parallelism=:serial, verbosity=0, progress=false)
saved = equation_search(
    X, y; params..., options=old, return_state=true, guesses=["x1 + x1 * x1"]
)

compatibility_error = try
    check_warm_start_compatibility(old, new)
    nothing
catch err
    err isa WarmStartIncompatibleError || rethrow()
    err
end
@assert compatibility_error isa WarmStartIncompatibleError
@assert compatibility_error.fields == [:maxsize]
@assert saved[2].exists[5] && saved[2].members[5].loss == 0.0

resumed = equation_search(X, y; params..., options=new, saved_state=saved)
frontier = calculate_pareto_frontier(resumed)
if resumed.exists[5] && any(m -> m.loss == 0.0 && compute_complexity(m, new) == 5, frontier)
    println("maxsize=4; resumed frontier still contains complexity=5, loss=0.0")
    println("REPRODUCED search-warm-start-incompatible")
else
    error("No out-of-budget perfect equation survived the warm start")
end
