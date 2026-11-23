using SymbolicRegression
const SR = SymbolicRegression

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
    verbosity=0,
    progress=false,
)
X = reshape(Float64[1, 2, 3, 4], 1, :)
datasets = [Dataset(X, Float64[2, 4, 6, 8])]
ropt = SR.SearchUtilsModule.RuntimeOptions(;
    niterations=0,
    nout=1,
    parallelism=:serial,
    runtests=false,
    verbosity=0,
    progress=false,
    return_state=true,
)
SR._validate_options(datasets, ropt, options)
state = SR._create_workers(datasets, ropt, options)
SR._initialize_search!(state, datasets, ropt, options, nothing, nothing)
initial_reports = sum(reply[4] for row in state.worker_output for reply in row)
SR._warmup_search!(state, datasets, ropt, options)
SR._main_search_loop!(state, datasets, ropt, options)
SR._tear_down!(state, datasets, ropt, options)
actual = sum(sum, state.num_evals)
expected = initial_reports
println(
    "recorded initialization evaluations actual=$actual expected=$expected (worker reports)"
)
@assert initial_reports == options.population_size * options.populations == 8
@assert actual == 0
println("REPRODUCED search-initial-evaluations")
