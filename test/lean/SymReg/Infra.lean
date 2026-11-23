import SymReg.Infra.Configure
import SymReg.Infra.Workers
import SymReg.Infra.Tracing
import SymReg.Infra.Logging
import SymReg.Infra.Compatibility
import SymReg.Infra.Precompile
import DynExpr.Registry.Types

namespace SymReg.Infra
open DynExpr.Registry

private def pe (id file : String) (fns : List String) (statement preconditions : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, preconditions,
    status := .proven, prop, thm := some thm }

private def cfg := "src/Configure.jl"
private def log := "src/Logging.jl"
private def trace := "src/Tracing.jl"
private def pbar := "src/ProgressBars.jl"
private def depr := "src/deprecates.jl"
private def pre := "src/precompile.jl"

def entries : List Entry := [
  pe "cfg-operator-acceptance" cfg ["test_operator"]
    "The test calls the operator with x alone when y is absent and with x and y otherwise; same-type output succeeds, wrong types and thrown errors produce their respective diagnostics."
    "Value identities are separate from rendering; operator results and type observations are supplied." ``operatorAcceptance ``operatorAcceptance_holds,
  pe "cfg-operator-nonfinite" cfg ["test_operator"]
    "Same-type operator outputs are accepted independently of their value, including NaN and either infinity."
    "None; uses the shared JF scalar model." ``operatorNonfinite ``operatorNonfinite_holds,
  pe "cfg-operator-diagnostics" cfg ["test_operator"]
    "Thrown operators and mismatched output types raise distinct errors with exact wording, including unary or binary inputs, the applicable domain and thrown exception, or the actual and expected types."
    "Runtime text rendering and exception type naming supplied as arbitrary services." ``operatorDiagnostics ``operatorDiagnostics_holds,
  { id := "cfg-input-grid", juliaFile := cfg, juliaFns := ["get_test_inputs"],
    statement := "Successful numeric conversion returns 99 values in range order from -100 to 100, feeding equal real and imaginary coordinates to complex conversion.",
    preconditions := "Numeric dispatch; conversion may fail.", status := .proven, prop := ``numericInputShape,
    thm := some ``numericInputShape_holds },
  pe "cfg-custom-input-count" cfg ["get_test_inputs"]
    "Custom sampling initializes MersenneTwister at seed zero, then samples 100 times in RNG order with the supplied type and options, stopping at the first error."
    "Nonnumeric dispatch; seed initialization and sampling are runtime services." ``customInputCount ``customInputCount_holds,
  { id := "cfg-operator-test-count", juliaFile := cfg, juliaFns := ["assert_operators_well_defined"],
    statement := "The ordered Cartesian schedule has one call per binary input pair and operator, followed by one call per unary input and operator, in nested loop order.",
    preconditions := "Finite input and operator lists, including repeated entries.",
    status := .proven, prop := ``operatorTestCount, thm := some ``operatorTestCount_holds },
  { id := "cfg-operator-test-completeness", juliaFile := cfg, juliaFns := ["assert_operators_well_defined"],
    statement := "The operator traversal accepts exactly when every Cartesian call succeeds and propagates the first failure without running later callbacks.",
    preconditions := "Input generation succeeds; tests may fail and retain effects.",
    status := .proven, prop := ``operatorTestsAccept, thm := some ``operatorTestsAccept_holds },
  { id := "cfg-dataset-acceptance", juliaFile := cfg, juliaFns := ["test_dataset_configuration"],
    statement := "Successful validation requires one X column, one y value if y is present, and one weight if weights are present per sample, plus a three-argument method for weighted custom losses.",
    preconditions := "Method nargs observations include the function itself; sample layout reuses Loss.Basic.",
    status := .refuted, prop := ``datasetAcceptance, thm := some ``datasetAcceptance_refuted,
    notes := "The configuration accepts three samples with a single weight; see cfg-weights-shape." },
  pe "cfg-dataset-warning" cfg ["test_dataset_configuration"]
    "With valid X and y shape, validation attempts the oversized dataset warning with maxlog=1 before checking loss arity, exactly when n exceeds 50,000 and verbosity is positive."
    "X and any y match the stored sample count. Logger-owned suppression is external." ``datasetWarningBoundary ``datasetWarningBoundary_holds,
  { id := "cfg-weights-shape", juliaFile := cfg, juliaFns := ["test_dataset_configuration"],
    statement := "A successfully checked weighted dataset should have one weight per sample, as the shape diagnostic describes.",
    preconditions := "Ordinary numeric data, supervised loss, constructor succeeds.",
    status := .refuted, prop := ``datasetWeightsShape, thm := some ``datasetWeightsShape_refuted,
    notes := "Dataset(reshape([1.,2.,3.],1,:),zeros(3);weights=[1.]) is accepted by test_dataset_configuration, despite n=3 and one weight. The validator omits the weights shape check." },
  pe "cfg-deterministic-serial" cfg ["test_option_configuration"]
    "Deterministic mode rejects both nonserial execution modes before warnings, anonymity checks or operator calls, regardless of their outcomes."
    "Execution mode is not serial; witness in Configure.lean." ``deterministicSerial ``deterministicSerial_holds,
  { id := "cfg-operator-check-order", juliaFile := cfg, juliaFns := ["test_option_configuration"],
    statement := "A failing operator test after earlier checks propagates before the unary/binary intersection check.",
    preconditions := "Any earlier warning and anonymity checks succeed.",
    status := .proven, prop := ``optionOperatorOrder, thm := some ``optionOperatorOrder_holds },
  pe "cfg-worker-fetch-success" cfg ["fetch_all", "test_function_on_workers"]
    "After fetching every future, fetch_all returns nothing exactly when all futures succeeded; successful result values are discarded."
    "The supplied result list retains process enumeration order; fetching runs concurrently." ``workerFetchSuccess ``workerFetchSuccess_holds,
  pe "cfg-worker-first-failure" cfg ["fetch_all"]
    "Among concurrently fetched results, the first failure by input order is thrown, regardless of completion order."
    "Prefix futures succeeded; errors and suffix results arbitrary." ``workerFirstFailure ``workerFirstFailure_holds,
  pe "cfg-worker-copy-gate" cfg ["move_functions_to_workers"]
    "Retest the original function and arguments after a successful first probe or a successful copy for captured UndefVarError. Copy receives the original processes, options and verbosity; other failures stop before retesting, retaining prior effects."
    "Probe, inspection and copy are stateful exception-valued services." ``workerCopyGate ``workerCopyGate_holds,
  pe "cfg-worker-method-order" cfg ["copy_definition_to_workers"]
    "Remote evaluation declares the function on the original processes, then visits each reflected method in order; if a step fails, the trace ends at that step."
    "The observation service records original process arguments and can fail at the declaration or a selected method." ``workerMethodsOrder ``workerMethodsOrder_holds,
  { id := "cfg-worker-function-arguments", juliaFile := cfg, juliaFns := ["move_functions_to_workers"],
    statement := "The transfer groups unary, binary, custom loss, early stop, expression definitions, node loss, expression loss and complexity in that order with their indicated example arguments.",
    preconditions := "Options and make_example_inputs supply the active families.",
    status := .todo, prop := ``workerFunctionArguments,
    notes := "The plan includes the definitions and skipped families. Need operation callbacks for creating examples and probing the workers with their actual values." },
  { id := "cfg-worker-import-order", juliaFile := cfg, juliaFns := ["import_module_on_workers"],
    statement := "Choose the local or package route, list loaded supported extensions in fixed order and append user imports when provided.",
    preconditions := "The head loaded-module list and optional imports are supplied.",
    status := .proven, prop := ``workerImportOrder, thm := some ``workerImportOrder_holds },
  { id := "cfg-worker-pipeline-arguments", juliaFile := cfg,
    juliaFns := ["test_module_on_workers", "test_entire_pipeline", "activate_env_on_workers"],
    statement := "Every module test uses length 3, five features and Float32. The pipeline uses 20 members of initial length 3, cycles at 5/5 with separate head and worker plugin states, and optimizes at options.maxsize with no trace. Environment activation forwards the project path.",
    preconditions := "Worker list and external pipeline and environment services are supplied.",
    status := .todo, prop := ``workerPipelineArguments,
    notes := "Module arguments are checked per process; need execution with actual population and cycle results, and an observable remote activation call." },
  { id := "cfg-worker-setup-create", juliaFile := "src/Configure.jl", juliaFns := ["configure_workers"],
    statement := "Absent workers trigger addprocs with lazy=false, module import, function transfer, then both optional smoke tests; the result marks workers as owned.", preconditions := "The creation service's process list is supplied; no Pkg activation occurs here.",
    status := .proven, prop := ``workerSetupCreate, thm := some ``workerSetupCreate_holds },
  pe "cfg-worker-setup-reuse" cfg ["configure_workers"]
    "Supplied workers are reused without creation or module import, functions are still moved, and optional module/pipeline tests remain ordered."
    "None; explicit worker list, including an empty list." ``workerSetupReuse ``workerSetupReuse_holds,
  pe "log-interval" log ["SRLogger", "should_log", "logging_callback!"]
    "A nonterminal callback with a payload attempts logger setup exactly when the live step is a multiple of a positive interval; it then attempts Info only if setup succeeds."
    "Payload construction succeeds and the callback is nonterminal; mathematical Int before overflow." ``loggerInterval ``loggerInterval_holds,
  pe "log-periodicity" log ["should_log", "increment_log_step!"]
    "For a positive interval, intermediate logging is due at zero, not due at positive steps below one interval, and unchanged by adding an interval."
    "Positive interval; mathematical Int before machine overflow." ``loggerPeriodicity ``loggerPeriodicity_holds,
  pe "log-first-terminal" log ["logging_callback!"]
    "After successful payload construction, a positive interval causes one logger setup attempt on the first or terminal callback, even when both coincide, followed by one Info attempt if setup succeeds."
    "Step zero or all-zero cycle counts; Info delivery and errors belong to the underlying logger." ``loggerFirstTerminal ``loggerFirstTerminal_holds,
  pe "log-disabled" log ["logging_callback!"]
    "A nonpositive interval skips payload construction and Info for all cycle lists and writes the old step plus one to the same counter."
    "Nonpositive interval; mathematical Int before overflow." ``loggerDisabled ``loggerDisabled_holds,
  pe "log-underlying-forwarding" log ["SRLogger", "get_logger", "with_logger", "increment_log_step!"]
    "The zero-argument callback runs under the original logger after successful setup; setup errors prevent invocation. Incrementing writes old step plus one to the same counter and retains that logger."
    "Counter before machine overflow; underlying logger and counter represented by identity." ``loggerForwarding ``loggerForwarding_holds,
  { id := "log-payload-shape", juliaFile := log, juliaFns := ["log_payload"],
    statement := "One output is flattened; otherwise every output occupies its exact one-based output key, with num_evals the nested Float64 sum.",
    preconditions := "Scalar payloads in matching dataset and hall order.", status := .todo, prop := ``loggerPayloadShape,
    notes := "Prove indexed payload shape and rounded nested reduction correspondence; model Julia's ArgumentError for an empty outer mapped sum." },
  { id := "log-scalar-contents", juliaFile := log, juliaFns := ["_log_scalars"],
    statement := "Population diagnostics retain member order; equations use the last matching copied frontier member for each complexity; an empty frontier attempts conversion of Inf and preserves failure.",
    preconditions := "Frontier copies reuse HofMig; complexity, renderer, conversion and volume are delegated.", status := .todo,
    prop := ``loggerScalarContents,
    notes := "Need the installed cache-hit/miss model and last-write dictionary proof; the prior proof used a pure complexity service." },
  pe "log-orientation" log ["isleftof"]
    "For exact rational coordinates, the strict orientation determinant decides left-of, and common translation preserves the verdict."
    "Finite rational coordinates; excludes floating rounding and nonfinite values." ``geometryOrientation ``geometryOrientation_holds,
  pe "log-hull-area-nonnegative" log ["convex_hull_area"]
    "The empty hull has area zero; a nonempty hull has nonnegative area equal to half the absolute cyclic cross-product sum, including the closing edge."
    "Finite exact rational coordinates; excludes floating overflow and rounding." ``hullAreaNonnegative ``hullAreaNonnegative_holds,
  pe "log-hull-input-vertices" log ["convex_hull"]
    "Every vertex in a terminating gift-wrapping execution belongs to the input point collection."
    "Nonempty points; starting/current vertices in input; explicit terminating HullRun certificate. Witness in Logging.lean." ``hullVerticesInput ``hullVerticesInput_holds,
  { id := "log-volume-preprocessing", juliaFile := log, juliaFns := ["pareto_volume"],
    statement := "Empty losses return 0.0 without geometry; nonempty successful preprocessing passes the transformed points followed by the minimum-loss/largest-size and maximum-coordinate closure points, where extrema include the inserted point.",
    preconditions := "Matching lengths and successful log transforms for the nonempty clause; geometry and extrema delegated.", status := .todo,
    prop := ``volumeEmptyAndShape, notes := "Need list-append/zip proof and typed cat promotion at the geometry boundary." },
  pe "trace-enable-and-identity" trace ["new_trace", "new_step_trace", "new_traced_steps", "reset_traced_steps!", "trace_mutation_type!", "trace_mutation_result!", "trace_identity_mutation!"]
    "Enabled trace and vector allocations start empty at fresh identities; disabled allocation and mutation do nothing; enabled identity sets three literal fields and reset clears the original vector."
    "Monotone supply beyond all live identities; string result/reason values." ``traceEnabled ``traceEnabled_holds,
  pe "trace-step-copies" trace ["trace_mutation_step!"]
    "Enabled attempts append unchanged payloads with fresh, distinct member and tree identities, retaining the step's trace and vector; disabled attempts make no writes or allocations."
    "Monotone supply beyond all live identities; default PopMember copy." ``traceStepCopies ``traceStepCopies_holds,
  pe "trace-first-reference-wins" trace ["_trace_member!"]
    "An existing mutation record at a member reference is preserved without replacing its snapshot or events."
    "Reference already present, witnessed in Tracing.lean." ``traceMemberFirstWins ``traceMemberFirstWins_holds,
  pe "trace-insert-reference" trace ["_trace_member!"]
    "A new reference stores the member's rendered tree, cost, loss and parent, starting with no events."
    "Reference absent, witnessed in Tracing.lean." ``traceMemberInserted ``traceMemberInserted_holds,
  pe "trace-population-links" trace ["_trace_population"]
    "Every population snapshot retains member ref and parent links in population order."
    "Renderer and complexity services arbitrary." ``tracePopulationLinks ``tracePopulationLinks_holds,
  pe "trace-iteration-schema" trace ["trace_iteration_start!", "next_trace_iteration"]
    "Iteration records use schema version 1, carry output/population/iteration, start with empty mutations, and advance the next iteration by one."
    "next_trace_iteration reads an existing iteration field; mathematical Int before overflow." ``traceIterationSchema ``traceIterationSchema_holds,
  pe "trace-write-forwarding" trace ["initialize_trace!", "write_trace"]
    "Disabled tracing performs no writes; enabled writes forward the append flag and retain service errors."
    "I/O callback arbitrary." ``traceWriteForwarding ``traceWriteForwarding_holds,
  { id := "trace-event-links", juliaFile := trace, juliaFns := ["trace_mutation_attempts!", "trace_crossover!"],
    statement := "Mutation and crossover events carry exact child and parent links. Each history preserves earlier events and appends every event for its reference in source order, including repeated references, selected-attempt flags and replacement deaths.", preconditions := "One attempt without replacement; the parent has an existing record and differs in reference from the child.",
    status := .todo, prop := ``traceEventLinks, thm := none, notes := "Original mutation and crossover schemas preserved; missing proof of full dictionary update order for arbitrary attempts, initial absence, repeated references and replacement." },
  { id := "trace-optimization-links", juliaFile := trace, juliaFns := ["trace_optimization!"],
    statement := "Insert the current member if missing; append tuning and then death to the old event vector, or allocate one from the first matching snapshot. Failed old-reference lookup retains prior insertion.",
    preconditions := "Enabled initialized iteration trace and successful rendering; both optimization flags are arbitrary.", status := .todo,
    prop := ``traceOptimizationLinks, notes := "Need the full case proof including reference reuse and binding events to the shared vector heap." },
  pe "trace-initialization" trace ["initialize_trace!", "next_trace_iteration"]
    "Initialization writes the populated original dictionary once with append=false and clears it only on success. Options rendering failure preserves the first three writes and skips I/O; write failure preserves the full header. Disabled iteration returns zero; missing enabled iteration raises KeyError."
    "Delegated options rendering and I/O may fail." ``traceInitialization ``traceInitialization_holds,
  pe "pbar-constructor-and-width" pbar ["WrappedProgressBar", "barlen"]
    "The wrapper retains its total, starts with an empty postfix, selects devnull only for the exact test-env string true, and uses stored width before stdout fallback."
    "ProgressMeter and terminal dimensions are external services." ``progressConstructor ``progressConstructor_holds,
  pe "pbar-absolute-update" pbar ["manually_iterate!"]
    "With an empty postfix, select width first, then update the original bar once at the requested absolute count with no showvalues and valuecolor=none; a width error prevents update."
    "ProgressMeter and terminal-size service results arbitrary." ``progressAbsoluteValue ``progressAbsoluteValue_holds,
  pe "pbar-formatted-update" pbar ["manually_iterate!"]
    "After successful width selection and formatting, update the original bar once at the requested absolute count with the complete ordered, styled, display-width-formatted postfix and valuecolor=none."
    "Successful width selection; multiline labels leave a nonnegative padding width. Julia character display widths are supplied." ``progressFormattedUpdate ``progressFormattedUpdate_holds,
  pe "pbar-finish-forwarding" pbar ["finish!"]
    "finish! calls the underlying ProgressMeter finish once, discards its successful result, and propagates errors."
    "Finish service arbitrary." ``progressFinishForwarding ``progressFinishForwarding_holds,
  pe "pbar-padding-retains" pbar ["newlines_to_spaces"]
    "Split on newlines, retain all original characters and their annotations, append exactly enough spaces per short line to reach the target display width, and join without separators."
    "Julia character display widths are supplied." ``progressPaddingRetains ``progressPaddingRetains_holds,
  pe "pbar-single-line" pbar ["format_for_meter", "newlines_to_spaces"]
    "A postfix value without newlines is returned unchanged, regardless of width."
    "No newline, witnessed in Compatibility.lean; annotations are external metadata." ``progressSingleLine ``progressSingleLine_holds,
  { id := "pbar-narrow-multiline", juliaFile := pbar,
    juliaFns := ["format_for_meter", "newlines_to_spaces"],
    statement := "Formatting a progress postfix should succeed for every positive bar width, including a multiline value.",
    preconditions := "Positive width; ordinary string label/value.", status := .refuted,
    prop := ``progressNarrowMultiline, thm := some ``progressNarrowMultiline_refuted,
    notes := "format_for_meter((\"label\",\"a\\nb\"),3) throws ArgumentError because width minus the 10-character label margin is -7; a positive narrow terminal width should still render." },
  pe "depr-search-forwarding" depr ["EquationSearch"]
    "Every EquationSearch replacement receives the original positional arguments and keyword payload; same-type matrix and dataset-vector overloads preserve their legacy niterations=10 default and all explicitly listed keywords."
    "Dispatch has selected the corresponding Julia overload; replacements arbitrary, including errors." ``deprecationForwarding ``deprecationForwarding_holds,
  pe "depr-plugin-states" depr ["best_of_sample"]
    "Deprecated best_of_sample forwards population/options and one plugin state per plugin, wrapping the supplied statistics only for adaptive-parsimony plugins."
    "Default AdaptiveParsimonyState constructor; plugin order retained." ``deprecationPluginMapping ``deprecationPluginMapping_holds,
  { id := "depr-pareto-and-context", juliaFile := depr, juliaFns := ["calculate_pareto_frontier", "EvalOptions"],
    statement := "Each deprecated frontier overload calls the replacement once with the original hall's backing arrays and preserves its result or error and resulting state. EvalOptions resolves to the EvalContext binding.",
    preconditions := "Successful deprecation dispatch.", status := .proven,
    prop := ``deprecationDiscardedArguments, thm := some ``deprecationDiscardedArguments_holds },
  { id := "pre-type-preference", juliaFile := pre, juliaFns := ["PRECOMPILE_TYPES", "do_precompilation"],
    statement := "A completed direct run begins only Float32 if the preference is false; otherwise it begins Float32 then Float64, including when the preference is absent.",
    preconditions := "Direct compile mode and normal completion with default options and search keywords, without serialization.", status := .proven,
    prop := ``precompilePreference, thm := some ``precompilePreference_holds },
  pe "pre-mode-forwarding" pre ["@maybe_setup_workload", "@maybe_compile_workload"]
    "Compile mode invokes the body once directly; precompile mode evaluates the designated setup or compile expansion with the unchanged body and preserves its result or error."
    "PrecompileTools controls whether it invokes the body." ``precompileModeForwarding ``precompileModeForwarding_holds,
  { id := "pre-invalid-mode-diagnostic", juliaFile := pre,
    juliaFns := ["@maybe_setup_workload", "@maybe_compile_workload", "do_precompilation"],
    statement := "An unsupported precompilation mode should raise the explicit Invalid value for mode ErrorException.",
    preconditions := "Mode differs from compile and precompile; no workload is executed.",
    status := .refuted, prop := ``precompileInvalidDiagnostic,
    thm := some ``precompileInvalidDiagnostic_refuted,
    notes := "do_precompilation(Val(:invalid)) prints :invalid then throws MethodError from string * nothing, because show(mode) returns nothing; intended error diagnostic is never constructed." },
  { id := "pre-workload-shapes", juliaFile := pre, juliaFns := ["do_precompilation"],
    statement := "Each completed type draws 3x30 data and a length-30 target, builds the configured options, makes two searches with merged keywords and state forwarding, then optionally serializes options before the first search state.",
    preconditions := "Direct mode and successful run; random arrays, search results and file buffers represented by identities.", status := .todo,
    prop := ``precompileShapes, notes := "Need the full merged-keyword trace, a HallOfFame return-type assertion, and fresh serialization buffers for each value." }
]

end SymReg.Infra
