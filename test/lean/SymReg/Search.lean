import SymReg.Search.Constructors
import DynExpr.Registry.Types

/-!
Search bookkeeping for SymbolicRegression.jl upstream/master daae84e5.
`Scheduler` models arbitrary ready-result visits after warmup. `Lifecycle` cycles a fixed
shuffled order and applies a global stop after collection/relaunch. `StateData` models
construction and returned-state loading. Population evolution, loss evaluation, migration,
metadata operations, plugins, tracing, IO, serialization bytes and OS timing are supplied
services; these implementations remain in their existing slices. Numeric arithmetic uses
DE's JF with exact finite values, without Float32/Float64 rounding, overflow or signed zero.
Natural counts represent nonnegative, nonoverflowing Julia counters. Distributed execution
uses the same head scheduler with arbitrary latency, not a proof of OS/process reliability.
Finite execution prefixes need not terminate; the cycle-count theorem states the result of
reaching a zero budget. Questions and the precise boundaries are in questions-search.md.
-/

namespace SymReg.Search
open DynExpr.Registry

def local_modes : Prop := serial_workers ∧ local_assignment
theorem local_modes_holds : local_modes := ⟨serial_workers_holds, local_assignment_holds⟩
def idle_finished : Prop := idle_preserves ∧ finished_preserves
theorem idle_finished_holds : idle_finished := ⟨idle_preserves_holds, finished_preserves_holds⟩
def threshold_modes : Prop := stop_outputs ∧ stop_float
theorem threshold_modes_holds : threshold_modes := ⟨stop_outputs_holds, stop_float_holds⟩
def timeout_conditions : Prop := timeout_exact
theorem timeout_conditions_holds : timeout_conditions := timeout_exact_holds
def global_stopping : Prop :=
  stop_disjunction ∧ global_stop_all ∧ global_stop_persistent ∧ loop_returns_terminal
theorem global_stopping_holds : global_stopping :=
  ⟨stop_disjunction_holds, global_stop_all_holds, global_stop_persistent_holds,
    loop_returns_terminal_holds⟩
def format_shapes : Prop := state_format ∧ vector_format
theorem format_shapes_holds : format_shapes := ⟨state_format_holds, vector_format_holds⟩
def population_roundtrip : Prop := state_population_roundtrip ∧ legacy_population_shape
theorem population_roundtrip_holds : population_roundtrip :=
  ⟨state_population_roundtrip_holds, legacy_population_shape_holds⟩
def saved_shapes : Prop := saved_population_bounds ∧ saved_hall_shape
theorem saved_shapes_holds : saved_shapes := ⟨saved_population_bounds_holds, saved_hall_shape_holds⟩
def dataset_rows : Prop := dataset_single ∧ weighted_dataset_rows
theorem dataset_rows_holds : dataset_rows := ⟨dataset_single_holds, weighted_dataset_rows_holds⟩
def name_modes : Prop := dataset_names ∧ dataset_multi_names
theorem name_modes_holds : name_modes := ⟨dataset_names_holds, dataset_multi_names_holds⟩
def stdin_conditions : Prop := reader_safety ∧ shared_stream
theorem stdin_conditions_holds : stdin_conditions := ⟨reader_safety_holds, shared_stream_holds⟩
def external_conditions : Prop := external_latched ∧ external_trigger
theorem external_conditions_holds : external_conditions := ⟨external_latched_holds, external_trigger_holds⟩
def save_conditions : Prop := final_saves ∧ file_backups
theorem save_conditions_holds : save_conditions := ⟨final_saves_holds, file_backups_holds⟩
def guess_conditions : Prop := guess_shape ∧ guess_oversize_retained ∧ template_guess_guard
theorem guess_conditions_holds : guess_conditions :=
  ⟨guess_shape_holds, guess_oversize_retained_holds, template_guess_guard_holds⟩
def runtime_conditions : Prop := runtime_defaults ∧ run_id_prefix ∧ runtime_projection
theorem runtime_conditions_holds : runtime_conditions :=
  ⟨runtime_defaults_holds, run_id_prefix_holds, runtime_projection_holds⟩
def dispatch_counts : Prop := dispatch_unbatched ∧ dispatch_batched
theorem dispatch_counts_holds : dispatch_counts := ⟨dispatch_unbatched_holds, dispatch_batched_holds⟩
def frontier_cache_correct : Prop := frontier_no_repeat ∧ frontier_changes
theorem frontier_cache_correct_holds : frontier_cache_correct :=
  ⟨frontier_no_repeat_holds, frontier_changes_holds⟩
def hall_merging : Prop := merge_best_per_complexity ∧ hall_output_frame
theorem hall_merging_holds : hall_merging :=
  ⟨merge_best_per_complexity_holds, hall_output_frame_holds⟩

def constructor_storage : Prop := initial_dimensions ∧ dummy_storage_shape
theorem constructor_storage_holds : constructor_storage :=
  ⟨initial_dimensions_holds, dummy_storage_shape_holds⟩
def result_typing : Prop := result_type_paths ∧ inferred_type_stability
theorem result_typing_holds : result_typing :=
  ⟨result_type_paths_holds, inferred_type_stability_holds⟩

def entries : List Entry := [
  { id := "search-validation", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_validate_options", "equation_search"]
    statement := "Validation succeeds exactly for nonempty outputs, positive populations, compatible dim_out and progress settings."
    preconditions := "External dataset/option tests succeed; this property concerns the explicit shape/progress checks."
    status := .proven, prop := ``validate_exact, thm := some ``validate_exact_holds },
  { id := "search-storage", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_create_workers", "SearchState", "init_dummy_pops"]
    statement := "Storage has a distinct empty capacity-one channel per output/population, zero evaluation counters, each task key in the shuffled order, and niterations*populations remaining cycles per output. Both dummy banks have one member per slot."
    preconditions := "Nonnegative nonoverflowing dimensions; constructor supplies one-member prototypes; shuffle permutes its input."
    status := .todo, prop := ``constructor_storage
    notes := "The storage law now pins the exact result of shuffle. Still needs both dummy-bank calls wired into createWorkers through the installed one-member constructor." },
  { id := "search-local-workers", juliaFile := "src/SearchUtils.jl", juliaFns := ["assign_next_worker!", "WorkerAssignments"]
    statement := "Serial and threaded modes allocate no process list and return worker index zero without altering assignments."
    preconditions := "Mode is serial or multithreading."
    status := .proven, prop := ``local_modes, thm := some ``local_modes_holds },
  { id := "search-worker-result", juliaFile := "src/SearchUtils.jl", juliaFns := ["get_worker_output_type", "worker_result_type", "extract_from_worker", "infer_popmember_type"]
    statement := "Serial replies are direct tuples; thread/process replies are tasks whose extraction preserves all five reply fields."
    preconditions := "Successful type inference and fetch; concrete population/expression type construction is an external service."
    status := .proven, prop := ``result_typing, thm := some ``result_typing_holds },
  { id := "search-worker-sticky", juliaFile := "src/SearchUtils.jl", juliaFns := ["assign_next_worker!"]
    statement := "A population with an existing process assignment keeps that worker, irrespective of later load."
    preconditions := "An assignment for the requested output/population exists."
    status := .proven, prop := ``worker_sticky, thm := some ``worker_sticky_holds },
  { id := "search-worker-minimum", juliaFile := "src/SearchUtils.jl", juliaFns := ["next_worker"]
    statement := "A successful new-worker selection is a provided worker with minimal assigned-job count."
    preconditions := "The call succeeds; empty worker lists and assignments to absent workers fail."
    status := .proven, prop := ``least_busy_worker, thm := some ``least_busy_worker_holds },
  { id := "search-cycle-budget", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"]
    statement := "A run reaching zero remaining cycles has collected exactly niterations*populations results per output, regardless of readiness and population order."
    preconditions := "Nonnegative nonoverflowing counts; warmup has launched each initial evolution job; the execution prefix reaches zero."
    status := .todo, prop := ``cycle_budget
    notes := "Needs actual successful consumption and processing events, including failure before the debit." },
  { id := "search-launch-surplus", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_warmup_search!", "_main_search_loop!"]
    statement := "A completed positive-budget run without external stop launches niterations*populations+populations-1 evolution jobs per output."
    preconditions := "Positive nonoverflowing cycle budget; normal warmup; completed run; no external stop."
    status := .todo, prop := ``launch_surplus
    notes := "Needs actual keyed dispatch events from warmup and relaunch, rather than an independent counter." },
  { id := "search-extra-cycles", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_warmup_search!", "_main_search_loop!"]
    statement := "A completed run executes exactly niterations*populations evolution jobs per output."
    preconditions := "Positive niterations and populations; no early stop; all launched jobs finish."
    status := .refuted, prop := ``exact_launched_cycles, thm := some ``exact_launched_cycles_refuted
    notes := "src/SymbolicRegression.jl:1021-1060 launches P jobs, then :1210-1260 relaunches after C-1 collections. With niterations=1 and populations=2, serial execution runs 3 jobs and collects 2." },
  { id := "search-uncollected-results", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!", "_tear_down!"]
    statement := "Every launched evolution result is collected exactly once by final teardown."
    preconditions := "Normal warmup; completed budget; launched jobs return successfully."
    status := .refuted, prop := ``every_launch_collected, thm := some ``every_launch_collected_refuted
    notes := "src/SymbolicRegression.jl:1133 refuses results after an output budget reaches zero; :1356-1378 only waits. The serial 1-iteration/2-population run collects 2 of 3 executed results." },
  { id := "search-one-inflight", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_warmup_search!", "_main_search_loop!"]
    statement := "Each population's launches equal its collections plus zero or one in-flight job; a relaunch follows collection."
    preconditions := "Normal warmup; arbitrary successful worker results and channel timing."
    status := .todo, prop := ``population_one_inflight
    notes := "Needs ordered dispatch/publish/receive events with completed unread results counted as outstanding." },
  { id := "search-receipt-unique", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"]
    statement := "In the scheduler projection, no output/population dispatch identity is received twice."
    preconditions := "Normal warmup; generation counters do not overflow."
    status := .todo, prop := ``no_duplicate_collection
    notes := "Dispatch now stamps its pending result before collection. Needs the listener publication and serial slot-read paths tied to the same identities." },
  { id := "search-idle-finished", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"]
    statement := "An unready visit or a visit to an output with zero budget preserves the scheduler state."
    preconditions := "None."
    status := .todo, prop := ``idle_finished
    notes := "Needs one live-loop visit including readiness monitoring, failure handling, yields and stop checks." },
  { id := "search-population-frame", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"]
    statement := "Collecting one population never changes another population's pending result, last population or evaluation counter."
    preconditions := "Distinct population indices; plugin/migration effects on the next evolution reply are arbitrary external inputs."
    status := .todo, prop := ``output_isolation
    notes := "Needs direct head writes distinguished from hook writes and asynchronous publication." },
  { id := "search-teardown", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_tear_down!"]
    statement := "Waiting for workers during teardown does not ingest a pending reply or update saved populations."
    preconditions := "Worker waits succeed; end hooks and OS/process cleanup are external services."
    status := .todo, prop := ``teardown_no_collection
    notes := "Needs mode-specific waits, process timeout, hook calls, resource cleanup and external notification draining." },
  { id := "search-evaluation-sum", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"]
    statement := "Every population's num_evals is the ordered sum of exactly its collected worker reports, including fractional and nonfinite reports."
    preconditions := "Normal warmup; JF scalar semantics; finite rounding is outside the shared scalar model."
    status := .todo, prop := ``worker_reports_summed
    notes := "Needs actual consumed reports and Float64 accumulation, with hook writes distinguished." },
  { id := "search-initial-evaluations", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_initialize_search!", "_warmup_search!", "_preserve_loaded_state!"]
    statement := "Initialization worker evaluation reports are included in the returned search evaluation counters."
    preconditions := "Successful initialization; niterations=0 is supported."
    status := .refuted, prop := ``initialization_evaluations_counted, thm := some ``initialization_evaluations_counted_refuted
    notes := "src/SymbolicRegression.jl:970 reports population_size, but :998-1005 and :1033-1039 discard that field. With two populations of four, initial worker reports total 8.0 and num_evals remains 0.0." },
  { id := "search-dispatch-evaluations", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_dispatch_s_r_cycle"]
    statement := "Dispatch sums evolution and optimization reports; batching adds one full-data evaluation for each existing best-seen slot through maxsize."
    preconditions := "Arbitrary successful evolution and optimization reports; the batched counting fact uses finite JF reports."
    status := .proven, prop := ``dispatch_counts, thm := some ``dispatch_counts_holds },
  { id := "search-stop-disabled", juliaFile := "src/SearchUtils.jl", juliaFns := ["check_for_loss_threshold", "_check_for_loss_threshold"]
    statement := "An absent early_stop_condition never requests a loss stop, even for an empty hall list."
    preconditions := "None."
    status := .proven, prop := ``stop_disabled, thm := some ``stop_disabled_holds },
  { id := "search-stop-all-outputs", juliaFile := "src/SearchUtils.jl", juliaFns := ["check_for_loss_threshold", "_check_for_loss_threshold"]
    statement := "Loss stopping requires a satisfying existing member in every output; numeric thresholds are strict loss<threshold and ignore complexity."
    preconditions := "Arbitrary Bool-valued user predicate and complexity service; numeric threshold converted as in src/Options.jl:1034-1039."
    status := .proven, prop := ``threshold_modes, thm := some ``threshold_modes_holds },
  { id := "search-timeout", juliaFile := "src/SearchUtils.jl", juliaFns := ["check_for_timeout"]
    statement := "With no timeout return false without reading the clock. A timeout reads once and returns false at equality with the computed Float64 difference. For finite elapsed time and limit, the test is strict."
    preconditions := "Clock samples and timeout seconds are Julia Float64 values represented as JF."
    status := .proven, prop := ``timeout_conditions, thm := some ``timeout_conditions_holds },
  { id := "search-max-evals", juliaFile := "src/SearchUtils.jl", juliaFns := ["check_max_evals"]
    statement := "If max_evals is absent, the check skips both the second limit read and the reduction. If present, it compares the integer limit inclusively with the nested Float64 sum, propagating access errors in source order."
    preconditions := "Float64 evaluation counters and the actual Julia array reduction result."
    status := .todo, prop := ``max_evals_exact
    notes := "Optional access order and scalar nesting are checked. At length 16 and above, Julia's SIMD block may reassociate Float64 additions; model the actual reduction before claiming the general threshold law." },
  { id := "search-global-stop", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!", "_equation_search", "equation_search"]
    statement := "Any loss, quit, timeout, evaluation or external stop exits the shared loop; subsequent visits cannot change any output."
    preconditions := "The loss/clock/IO services return successfully; stopping is checked after collection/relaunch."
    status := .todo, prop := ``global_stopping
    notes := "Needs all five actual calls in order, their side effects and first error, and the resulting shared break." },
  { id := "search-return-format", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_format_output", "equation_search"]
    statement := "dim_out=1 returns one hall, dim_out=2 a hall vector; return_state adds output-major population vectors as the first tuple element."
    preconditions := "Single-hall shape for dim_out=1; metadata embedding already supplied by the expression implementation."
    status := .proven, prop := ``format_shapes, thm := some ``format_shapes_holds },
  { id := "search-population-roundtrip", juliaFile := "src/SearchUtils.jl", juliaFns := ["load_saved_population", "get_population"]
    statement := "Loading a valid nested-vector or column-major matrix coordinate copies the members in order with the same payloads and fresh vector, member and tree identities."
    preconditions := "Requested coordinates exist; the allocation cursor follows the caller's existing identities."
    status := .todo, prop := ``population_roundtrip
    notes := "Both index layouts have independent lookup laws, and successful stock copies have distinct member and tree identities. Route ordered fallible expression copies through copyPopulation and retain the first error." },
  { id := "search-hall-roundtrip", juliaFile := "src/SearchUtils.jl", juliaFns := ["load_saved_hall_of_fame"]
    statement := "Saved hall vectors and scalar halls reload with identical ordered member payloads and occupancy flags and fresh member/occupancy vector and member identities."
    preconditions := "Arbitrary saved halls; the allocation cursor follows the saved objects."
    status := .todo, prop := ``state_hall_roundtrip
    notes := "Both layouts preserve payload and flags and allocate fresh identities. Still needs an address-disjoint mutation frame for loaded hall members and occupancy vectors." },
  { id := "search-saved-shapes", juliaFile := "src/SearchUtils.jl", juliaFns := ["get_population", "load_saved_population", "load_saved_hall_of_fame"]
    statement := "Missing population outputs raise BoundsError; mismatched saved-hall output count raises DimensionMismatch during initialization."
    preconditions := "Default vector/matrix saved-state layouts; metadata services succeed."
    status := .todo, prop := ``saved_shapes
    notes := "Both layouts now reject all invalid coordinates. For hall mismatches, bind loadHalls normalization and copying to initializeHalls before testing that strip and score are skipped." },
  { id := "search-population-resize", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_initialize_search!"]
    statement := "On a saved-population size mismatch, warn if verbose and generate with the worker dataset and options, the first worker size, initial length 3, the computed feature count and head plugin state. After constructing the hall and trace, return that population and Float64 of the later worker size. A failure retains the reached call prefix and skips subsequent calls."
    preconditions := "Saved population already loaded. Stock Options size reads are total and stable per object. For custom AbstractOptions with Int-valued population_size, the accessor law tests independently varying reads and failures, with the warning, feature calculation, population and hall construction successful."
    status := .proven, prop := ``population_size_recreation, thm := some ``population_size_recreation_holds },
  { id := "search-restore-rescore", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_initialize_search!"]
    statement := "A correctly sized saved population is stripped, scored in member order with the current dataset and options, and returned with the stripped, rescored payloads in a distinct copy and with zero initialization evaluations."
    preconditions := "Stock Options; successful stripping, scoring, worker hall and trace construction; fresh allocation cursor follows the saved population vector."
    status := .todo, prop := ``restored_population_rescored
    notes := "Thread complexity cache writes from eval_cost through the ordered rescore before the final fallible copy. Bind the earlier saved-population load to this branch." },
  { id := "search-zero-warmup", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_warmup_search!", "_preserve_loaded_state!"]
    statement := "Zero-iteration warmup copies every initialized population into return storage and leaves evaluation counters zero."
    preconditions := "All initialization tasks return successfully; niterations=0."
    status := .proven, prop := ``zero_warmup_preserves, thm := some ``zero_warmup_preserves_holds },
  { id := "search-return-state-pending", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_create_workers", "_main_search_loop!", "_format_output"]
    statement := "A completed threaded search returns a population_size-member saved population for every population whose workers return population_size members."
    preconditions := "Successful workers; positive cycle budget; arbitrary worker latency."
    status := .refuted, prop := ``returned_population_sizes, thm := some ``returned_population_sizes_refuted
    notes := "src/SymbolicRegression.jl:834 initializes last_pops with one-member dummy populations; only collected populations replace them (:1152). With two populations and two collections both from the first worker, return_state contains member counts [4,1], despite waiting for the second worker at teardown." },
  { id := "search-hall-merge", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!", "update_hall_of_fame!"]
    statement := "Each output hall reduces population members followed by existing best_seen members to the best accepted payload per complexity, with the source's tie/NaN rules."
    preconditions := "In-range hall slot; arbitrary complexity and constraint services; exceptions propagate; reused SymReg.HofMig semantics."
    status := .todo, prop := ``hall_merging
    notes := "Needs the checked hall fold to preserve partial writes and stop on the first complexity or constraint error." },
  { id := "search-dataset-rows", juliaFile := "src/SearchUtils.jl", juliaFns := ["construct_datasets", "equation_search"]
    statement := "Each dataset receives its own target row and weight row, shared input columns, output index, names, units and extra data; absent weights remain absent."
    preconditions := "Each requested weight/name/unit row exists; Dataset construction itself uses the existing loss-data projection."
    status := .todo, prop := ``dataset_rows
    notes := "Needs shared X identity, fresh row slices, and the installed Dataset name and unit defaults and conversions." },
  { id := "search-dataset-names", juliaFile := "src/SearchUtils.jl", juliaFns := ["construct_datasets"]
    statement := "Automatic single-output names avoid variable y by using target; multi-output names use y plus a subscript; explicit scalar/vector names are forwarded."
    preconditions := "Explicit vector names use valid indices."
    status := .proven, prop := ``name_modes, thm := some ``name_modes_holds },
  { id := "search-weights-shape", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["equation_search"]
    statement := "The matrix interface rejects weights whose total length differs from the target matrix before column-major reshaping."
    preconditions := "Nonnegative nonoverflowing dimensions."
    status := .proven, prop := ``weight_length_check, thm := some ``weight_length_check_holds },
  { id := "search-quit-chunks", juliaFile := "src/SearchUtils.jl", juliaFns := ["parse_quit_signal"]
    statement := "Splitting a nonquitting prefix across reads preserves quit parsing. A lone q stays pending; LF or CR then quits and clears it. An ordinary intervening byte clears q, and Ctrl-C quits immediately."
    preconditions := "For the chunking law, the first chunk has not already emitted a quit."
    status := .proven, prop := ``quit_chunks_and_commands, thm := some ``quit_chunks_and_commands_holds },
  { id := "search-stdin", juliaFile := "src/SearchUtils.jl", juliaFns := ["StdinReader", "read_available_nonblocking", "watch_stream", "check_for_user_quit", "close_reader!", "stop_reading_if_unshared"]
    statement := "An unreadable stream never requests quit or consumes a read; stopping a shared Libuv stream with waiters is suppressed."
    preconditions := "IO is supplied as bytes/EOF/error results; stream locking and OS operations are external effects."
    status := .proven, prop := ``stdin_conditions, thm := some ``stdin_conditions_holds },
  { id := "search-process-errors", juliaFile := "src/SearchUtils.jl", juliaFns := ["@filtered_async", "is_process_exit"]
    statement := "The listener suppresses failures whose recursively oldest exception is a process exit, and otherwise rethrows the original exception. A later cleanup error does not prevent suppression."
    preconditions := "Failed tasks have nonempty exception stacks."
    status := .proven, prop := ``process_exit_filter, thm := some ``process_exit_filter_holds },
  { id := "search-external-stop", juliaFile := "src/SearchUtils.jl", juliaFns := ["ExternalStop", "poll_stop_fd", "read_stop_byte", "check_stop_fd", "external_stop", "check_external_stop", "latch_external_stop!", "drain_external_stop!"]
    statement := "An eligible poll drains its successful read prefix and requests stop exactly if already latched or a consumed byte matches. A throttled or disabled check leaves the descriptor unchanged; a final drain consumes the readable prefix without changing the latch or timestamp."
    preconditions := "OS poll/read outcomes supplied to the model; descriptor within platform representation."
    status := .proven, prop := ``external_conditions, thm := some ``external_conditions_holds },
  { id := "search-monitor-capacity", juliaFile := "src/SearchUtils.jl", juliaFns := ["ResourceMonitor", "record_channel_state!"]
    statement := "Recording one readiness sample retains the newest entries up to capacity, in their original order."
    preconditions := "History already fits max_recordings; nonnegative capacity."
    status := .proven, prop := ``monitor_capacity, thm := some ``monitor_capacity_holds },
  { id := "search-monitor-startup", juliaFile := "src/SearchUtils.jl", juliaFns := ["estimate_work_fraction"]
    statement := "Work fraction is zero through the reporting threshold and is one immediately past it when the one-sample trailing window is ready."
    preconditions := "The positive reporting case uses window_size=1."
    status := .proven, prop := ``monitor_startup, thm := some ``monitor_startup_holds },
  { id := "search-monitor-window", juliaFile := "src/SearchUtils.jl", juliaFns := ["estimate_work_fraction", "get_load_string"]
    statement := "After startup the work fraction is the Float64 mean of the history's trailing window, counting only true samples."
    preconditions := "The window fits the history."
    status := .proven, prop := ``monitor_window, thm := some ``monitor_window_holds },
  { id := "search-progress", juliaFile := "src/SearchUtils.jl", juliaFns := ["update_progress_bar!", "print_search_state"]
    statement := "With zero remaining cycles and positive population count, reported completed iterations equal niterations*number_of_outputs."
    preconditions := "Positive population count; nonnegative nonoverflowing counters; terminal rendering external."
    status := .todo, prop := ``progress_complete
    notes := "Needs observable calls to print, absolute bar update and finish in their actual source branches." },
  { id := "search-maxsize", juliaFile := "src/SearchUtils.jl", juliaFns := ["get_cur_maxsize"]
    statement := "Disabled size warmup returns options.maxsize for every elapsed fraction, including nonfinite fractions from a zero cycle budget."
    preconditions := "warmup_maxsize_by=0; JF scalar model."
    status := .proven, prop := ``maxsize_disabled, thm := some ``maxsize_disabled_holds },
  { id := "search-transport", juliaFile := "src/SearchUtils.jl", juliaFns := ["serialize_to_bytes", "deserialize_from_bytes", "run_encoded_result", "spawn_encoded_result", "@sr_spawner"]
    statement := "Every parallelism mode delivers the job applied to the same decoded inputs; only task latency differs."
    preconditions := "Successful serialization/invocation/type assertions; payload-level serialization model, arbitrary nonnegative latency."
    status := .todo, prop := ``transport_payload
    notes := "Needs separate serial, thread and process execution contexts, input fetches, transport and type-check failures." },
  { id := "search-worker-copies", juliaFile := "src/SearchUtils.jl", juliaFns := ["WorkerCopy", "store_worker_copy!", "delete_worker_copy!", "store_on_workers", "delete_on_workers", "fetch"]
    statement := "Worker storage uses the current allocation key, increments its counter, and stores the payload on every requested process; an ordered delete removes precisely that key."
    preconditions := "Worker belongs to the store/delete process list; UInt64 allocation counter has not wrapped; remote calls succeed."
    status := .todo, prop := ``worker_storage
    notes := "Needs the atomic old key, typed remote fetch, ordered wait and cleanup over the actual later process list." },
  { id := "search-final-save", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_info_dump", "save_to_file"]
    statement := "Final output saves every hall even at verbosity zero and zero iterations; each CSV payload is written identically to primary and backup files."
    preconditions := "Saving enabled; rendering/filesystem calls succeed; metadata and expression rendering are external services."
    status := .proven, prop := ``save_conditions, thm := some ``save_conditions_holds },
  { id := "search-guesses", juliaFile := "src/SearchUtils.jl", juliaFns := ["_make_vector_vector", "_parse_guess_expression", "parse_guesses", "_parse_guesses_impl"]
    statement := "Multi-output flat guesses are rejected; oversized parsed guesses remain with a warning; template function fields reject detected dataset variable names."
    preconditions := "Parsing/optimization/stripping are supplied services; retained-guess property disables optimization and uses identity stripping."
    status := .todo, prop := ``guess_conditions
    notes := "Needs template key and regex checks, actual optimization, post-transform complexity and the warning call." },
  { id := "search-runtime", juliaFile := "src/SearchUtils.jl", juliaFns := ["RuntimeOptions", "getproperty", "propertynames", "generate_run_id"]
    statement := "Runtime defaults choose threading, scalar output, no returned state, progress at verbosity one, four processes, timeout 60, and a timestamp-prefixed generated run id."
    preconditions := "No conflicting supplied options; date formatting and random run-id suffix are external inputs."
    status := .todo, prop := ``runtime_conditions
    notes := "Needs environment timeout parsing and the explicit-ID branch bypassing timestamp and RNG services." },
  { id := "search-frontier-cache", juliaFile := "src/SearchUtils.jl", juliaFns := ["FrontierSaveState", "save_frontier_if_changed!", "logging_callback!"]
    statement := "Saving the same frontier twice never writes it again; identity, cost, loss or complexity changes invalidate the cache."
    preconditions := "Successful CSV write; entry comparison models isequal, including NaN; logging remains an arbitrary extension callback."
    status := .todo, prop := ``frontier_cache_correct
    notes := "Needs both CSV writes before replacing the cache, original member identity and signed-zero-sensitive keys." }
]

end SymReg.Search
