import SymReg.MLJ.SelectProps
import SymReg.MLJ.ReportProps
import SymReg.MLJ.PredictProps
import SymReg.MLJ.FitProps
import SymReg.MLJ.UnitsProps
import SymReg.MLJ.Examples
import DynExpr.Registry.Types

/-!
MLJ slice: `src/MLJInterface.jl` (model structs, `fit`/`update`, reports, `choose_best`,
`predict`, units, the native `Machine`), SymbolicRegression.jl `upstream/master` daae84e5.
Hall-of-fame formatting is `SymReg.HofMig.formatHof`; `Options`, the warm-start check,
`equation_search`, expression evaluation and rendering are supplied services.
-/

namespace SymReg.MLJ
open DynExpr.Registry

def entries : List Entry := [
  { id := "mlj-cb-log-rule", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best"]
    statement := "With log loss scaling (or options=nothing), choose_best returns a one-based index whose loss is within 1.5x the minimum loss, whose score is maximal among all such rows, and which is the first row with that score."
    preconditions := "Nonempty losses, all non-NaN and nonnegative; scores of equal length, none NaN or -Inf (as in every report)."
    status := .todo, prop := ``cb_log_rule, notes := "Bind the Float64-rounded cutoff and prove maximality and first tie under Base's signed-zero ordering." },
  { id := "mlj-cb-linear-rule", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best"]
    statement := "With loss_scale = :linear, choose_best returns the first index of the minimum loss."
    preconditions := "Nonempty losses, none NaN."
    status := .todo, prop := ``cb_linear_rule, notes := "Retain negative zero in the loss representation and use Base findmin order." },
  { id := "mlj-cb-linear-nan", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best", "dispatch_selection_for"]
    statement := "A nonempty linear-scale report selects a minimum-loss row with a non-NaN loss under the default selector."
    preconditions := "Successful report and default selection."
    status := .proven, prop := ``cb_linear_nan, thm := some ``cb_linear_nan_holds },
  { id := "mlj-cb-log-nan", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best"]
    statement := "With log scaling, the selected row has the highest score among rows within 1.5x the minimum non-NaN loss."
    preconditions := "Scores of equal length, none NaN or -Inf; some non-NaN loss."
    status := .refuted, prop := ``cb_log_nan, thm := some ``cb_log_nan_refuted
    notes := "losses [2, 1, NaN], scores [0, 1, 0]: minimum(losses) is NaN, so every row compares false with the NaN threshold, all entries become -Inf and argmax returns 1 instead of 2. Not fixed by PR #790, which leaves choose_best unchanged and only keeps NaN losses out of reports." },
  { id := "mlj-cb-single", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best"]
    statement := "With one row, choose_best returns 1 for every loss (including NaN and infinities), score and scaling."
    preconditions := "One score."
    status := .proven, prop := ``cb_single, thm := some ``cb_single_holds },
  { id := "mlj-cb-empty", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best"]
    statement := "With no rows, choose_best throws the empty-reduction ArgumentError under both scalings."
    preconditions := "None."
    status := .proven, prop := ``cb_empty, thm := some ``cb_empty_holds },
  { id := "mlj-cb-nothing", juliaFile := "src/MLJInterface.jl", juliaFns := ["choose_best"]
    statement := "choose_best with options = nothing selects exactly as with loss_scale = :log."
    preconditions := "None."
    status := .todo, prop := ``cb_nothing_is_log, notes := "Specify masked argmax independently, including the first missing eligible score and empty reduction." },
  { id := "mlj-rep-lengths", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "get_equation_strings_for"]
    statement := "Before selection each single-target report vector and any rendered string vector have one entry per frontier member. If selection preserves the vector lengths, the returned vectors have the same lengths."
    preconditions := "full_report returns normally."
    status := .proven, prop := ``rep_lengths, thm := some ``rep_lengths_holds },
  { id := "mlj-rep-best", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "dispatch_selection_for"]
    statement := "An initially empty frontier gives best_idx = 0 and no selector call; otherwise there is one call on the original vectors and fitted options, and best_idx is its returned index."
    preconditions := "full_report returns normally; arbitrary selection_method."
    status := .proven, prop := ``rep_best, thm := some ``rep_best_holds },
  { id := "mlj-rep-order", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report"]
    statement := "The pre-selection complexities are strictly increasing, and the report preserves this order if the selector leaves the complexity vector unchanged."
    preconditions := "Existing hall slots carry cached, strictly increasing complexities (no -1 sentinel), as in a correctly indexed hall."
    status := .proven, prop := ``rep_order, thm := some ``rep_order_holds },
  { id := "mlj-rep-default-rule", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "dispatch_selection_for", "choose_best"]
    statement := "With the default selection and log scaling, a nonempty report's best_idx is the first row of maximal score among rows within 1.5x the minimum loss."
    preconditions := "No existing hall slot has NaN loss; full_report returns normally."
    status := .todo, prop := ``rep_default_rule, notes := "Needs Float64-rounded threshold and Base's signed-zero score ordering on the typed formatted report." },
  { id := "mlj-rep-linear-rule", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "dispatch_selection_for", "choose_best"]
    statement := "With the default selection and linear scaling, a nonempty report's best_idx is the first row of minimum loss."
    preconditions := "No existing hall slot has NaN loss; full_report returns normally."
    status := .proven, prop := ``rep_linear_rule, thm := some ``rep_linear_rule_holds },
  { id := "mlj-rep-strings", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "get_equation_strings_for"]
    statement := "The strings render the original equations with fitted names in order, and match the returned equations if selection preserves their contents and order."
    preconditions := "full_report returns normally."
    status := .proven, prop := ``rep_strings, thm := some ``rep_strings_holds },
  { id := "mlj-rep-default-nan", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "dispatch_selection_for", "choose_best"]
    statement := "With default log selection, a nonempty report has no NaN losses, and best_idx names an eligible row with a score at least as large as every eligible score."
    preconditions := "The report returns normally and is nonempty."
    status := .todo, prop := ``rep_default_nan
    notes := "NaN losses are skipped; needs the rounded threshold and signed score order to prove selected-row eligibility and maximality." },
  { id := "mlj-rep-lengths-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["full_report", "get_equation_strings_for", "dispatch_selection_for"]
    statement := "Before selection there is one set of aligned equation, loss, complexity and score vectors per hall. Strings, when requested, render each original target's equations in order."
    preconditions := "full_report returns normally."
    status := .proven, prop := ``rep_lengthsK, thm := some ``rep_lengthsK_holds },
  { id := "mlj-rep-best-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["dispatch_selection_for"]
    statement := "An initially empty target frontier gives one zero per target and no selector calls. Otherwise the selector runs in target order with each target's original vectors and fitted options, and each best_idx is the index returned by that call."
    preconditions := "full_report returns normally."
    status := .proven, prop := ``rep_bestK, thm := some ``rep_bestK_holds },
  { id := "mlj-pred-select", juliaFile := "src/MLJInterface.jl", juliaFns := ["predict", "_predict"]
    statement := "A data/index tuple overrides the keyword index for both model kinds. Ordinary enclosed data and the tuple index reach the prediction core unchanged; conflicting valid indices produce the tuple index's prediction.",
    preconditions := "None.",
    status := .proven, prop := ``pred_selector_payload, thm := some ``pred_selector_payload_holds },
  { id := "mlj-pred-default", juliaFile := "src/MLJInterface.jl", juliaFns := ["predict", "_predict", "full_report"]
    statement := "After selector dispatch, a single-target prediction without idx evaluates the equation indexed by the best_idx of the report built by that prediction."
    preconditions := "A nonempty report, successful feature preparation, and a valid selected row."
    status := .todo, prop := ``pred_default, notes := "Same-call report is modeled; make evaluation and wrapping fallible and check the actual selected call and first error." },
  { id := "mlj-pred-default-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["predict", "_predict", "full_report"]
    statement := "After selector dispatch, a multitarget prediction without idx evaluates targets using the index vector from the report built by that prediction and combines the pieces into the fitted output form."
    preconditions := "Nonempty frontiers, successful feature preparation, and index and equation vectors with matching lengths."
    status := .todo, prop := ``pred_defaultK, notes := "Derive index alignment from selection and record per-target evaluation; model fallible hcat promotion and table materialization." },
  { id := "mlj-pred-idx", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict", "eval_tree_mlj", "wrap_units", "prediction_fallback"]
    statement := "For a valid integer idx = i, single-target predict evaluates equation i on the new features and wraps the target units; if evaluation does not complete it returns zeros, one per observation, with the target units."
    preconditions := "Feature names and units match the fitted ones; 1 <= i <= number of equations; the input is not a data/idx-keyed table."
    status := .todo, prop := ``pred_idx, notes := "Make evaluation, wrapping and fallback fallible, and distinguish and propagate the first error." },
  { id := "mlj-pred-bounds", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict"]
    statement := "An effective Julia Int below 1 or above the number of single-target equations throws BoundsError after successful selector dispatch and feature preparation."
    preconditions := "Nonempty report; the resolved data has no selector keys and feature extraction, names and units checks succeed."
    status := .proven, prop := ``pred_bounds, thm := some ``pred_bounds_holds },
  { id := "mlj-pred-empty", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict", "prediction_fallback"]
    statement := "With an empty frontier, single-target predict returns zeros with the target units for any idx, without validating names or units."
    preconditions := "Feature matrix extraction succeeds."
    status := .todo, prop := ``pred_empty, notes := "At the post-dispatch stage, model the fallible warning, allocation, zero fill and wrapping before checking results." },
  { id := "mlj-pred-names", juliaFile := "src/MLJInterface.jl", juliaFns := ["validate_variable_names", "_predict"]
    statement := "After selector dispatch, extraction and the nonempty-frontier check, either model kind rejects differing feature names before checking units."
    preconditions := "Feature extraction succeeds and the prediction report has no empty frontier."
    status := .proven, prop := ``pred_names, thm := some ``pred_names_holds },
  { id := "mlj-pred-units", juliaFile := "src/MLJInterface.jl", juliaFns := ["validate_units", "clean_units", "_predict"]
    statement := "After selector dispatch and successful feature extraction, matching names and nonempty single-target report, unequal cleaned unit vectors of equal length raise the units assertion; incompatible broadcast axes raise DimensionMismatch."
    preconditions := "Both cleaned units are vectors; lengths differing with neither length one are incompatible."
    status := .proven, prop := ``pred_units, thm := some ``pred_units_holds },
  { id := "mlj-pred-vec-single", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict"]
    statement := "A single-target Vector{Int} index with any out-of-range entry raises BoundsError. If all entries are in range, including for the empty vector, dispatch on the resulting equation vector raises MethodError."
    preconditions := "Nonempty report; extraction succeeds, names and units match, and the data is not a reserved-key selector."
    status := .proven, prop := ``pred_vec, thm := some ``pred_vec_holds },
  { id := "mlj-pred-feature-table", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict", "predict"]
    statement := "A NamedTuple feature table is predicted as data unless its keys are exactly data and idx."
    preconditions := "Keys are not exactly {data, idx}."
    status := .refuted, prop := ``pred_feature_table, thm := some ``pred_feature_table_refuted
    notes := "A model fitted on X = (data=..., x2=...) throws AssertionError on predict(mach, X): the selector check at src/MLJInterface.jl:570 fires on the column name data." },
  { id := "mlj-pred-int-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict"]
    statement := "After ordinary prediction preparation, an effective integer index for a multitarget model raises MethodError at eachindex before evaluating a tree."
    preconditions := "Data is not a reserved-key selector; no frontier is empty; extraction succeeds and fitted names and units match."
    status := .proven, prop := ``predK_int, thm := some ``predK_int_holds },
  { id := "mlj-pred-length-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict"]
    statement := "After ordinary prediction preparation, a multitarget index vector whose axes differ from the equation vector throws DimensionMismatch before evaluating a tree."
    preconditions := "Data is not a reserved-key selector; no frontier is empty; extraction succeeds and fitted names and units match."
    status := .proven, prop := ``predK_length, thm := some ``predK_length_holds },
  { id := "mlj-pred-empty-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict", "prediction_fallback"]
    statement := "If any target's frontier is empty, multitarget predict returns the all-target zero fallback."
    preconditions := "Feature matrix extraction and the fallback succeed."
    status := .todo, prop := ``predK_empty, notes := "Prove zero-valued columns with observation count and per-target units, and model fallible table materialization." },
  { id := "mlj-pred-vec-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict", "eval_tree_mlj", "wrap_units"]
    statement := "An index vector is per output: column t of a multitarget prediction evaluates equation idx[t] of target t, with target t's units, and there is one column per target."
    preconditions := "Names and units match; idx has one valid entry per target; every selected equation evaluates completely; matrix (not table) target."
    status := .todo, prop := ``predK_vec, notes := "Derive alignment from fitted state and use Base hcat promotion and the table column materializer." },
  { id := "mlj-pred-width-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["_predict", "eval_tree_mlj", "prediction_fallback"]
    statement := "Whenever multitarget predict returns a matrix, it has one column per target."
    preconditions := "None."
    status := .refuted, prop := ``predK_width, thm := some ``predK_width_refuted
    notes := "When target 1's equation fails to evaluate, eval_tree_mlj returns the whole num_targets-column fallback, and hcat with target 2's column gives 3 columns for 2 targets." },
  { id := "mlj-fit-fresh", juliaFile := "src/MLJInterface.jl", juliaFns := ["fit", "update", "_update", "full_report", "SRFitResult"]
    statement := "A fresh single-target fit calls search with no saved state, the supplied weights and budget m.niterations. On success it records that budget, the model, one target and the report."
    preconditions := "fit returns normally."
    status := .todo, prop := ``fit_fresh, notes := "Record actual search invocation and prove its budget, weights and absent saved state rather than recovering an argument witness." },
  { id := "mlj-update-warm", juliaFile := "src/MLJInterface.jl", juliaFns := ["update", "_update"]
    statement := "A successful warm update of either model kind passes the compatibility check and continues search with the old state and the nonnegative machine-Int iteration difference as its budget. It records the requested total."
    preconditions := "update returns normally."
    status := .todo, prop := ``update_warm, notes := "Record the actual compatibility check and search calls, then prove their order and argument identity." },
  { id := "mlj-update-incompatible", juliaFile := "src/MLJInterface.jl", juliaFns := ["update"]
    statement := "If the warm-start check throws, update (single and multitarget) throws that error and never searches."
    preconditions := "get_options succeeds."
    status := .todo, prop := ``update_incompatible, notes := "The exception is propagated; observe the search call count to prove the failed warm check prevents search." },
  { id := "mlj-update-decrease", juliaFile := "src/MLJInterface.jl", juliaFns := ["_update"]
    statement := "For either model kind, a negative machine-Int difference between requested and previous budgets raises AssertionError(\"niterations >= 0\") after preparation."
    preconditions := "Options, warm-start check and data formatting succeed."
    status := .proven, prop := ``update_decrease, thm := some ``update_decrease_holds },
  { id := "mlj-clean-negative", juliaFile := "src/MLJInterface.jl", juliaFns := ["clean!", "fit", "_update"]
    statement := "clean! returns an empty message and leaves the model unchanged. Fresh fitting for either model kind rejects a negative budget with the niterations assertion."
    preconditions := "Options and data formatting succeed."
    status := .todo, prop := ``clean_negative, notes := "Carry every regressor field through clean! and account for all preceding unit and weight preparation errors." },
  { id := "mlj-fit-multi-targets", juliaFile := "src/MLJInterface.jl", juliaFns := ["_update", "format_input_for"]
    statement := "A multitarget fit records the formatted target names in order and the number of target rows passed to search. It repeats the weights once per target and passes the saved state only when warm-starting."
    preconditions := "update returns normally."
    status := .todo, prop := ``fitK_targets, notes := "The target names are exact; observe the actual search call to verify target rows, weights and saved state." },
  { id := "mlj-format-y-single", juliaFile := "src/MLJInterface.jl", juliaFns := ["format_input_for"]
    statement := "Single-target models reject table targets and matrices with more than one column with the documented assertion, and treat an n x 1 matrix as its column vector."
    preconditions := "None."
    status := .proven, prop := ``format_y1, thm := some ``format_y1_holds },
  { id := "mlj-format-y-multi", juliaFile := "src/MLJInterface.jl", juliaFns := ["format_input_for"]
    statement := "Multitarget models reject vectors and matrices with at most one column with the documented assertion."
    preconditions := "None."
    status := .todo, prop := ``format_yK, notes := "Model Tables row-table recognition before the nontable vector and matrix assertions." },
  { id := "mlj-machine-fit", juliaFile := "src/MLJInterface.jl", juliaFns := ["fit!", "Machine"]
    statement := "fit!(mach; force=true) is a fresh fit; fit! on a fitted machine without force is update from the stored fit result; both store the new fit result and report."
    preconditions := "None."
    status := .proven, prop := ``machine_fit, thm := some ``machine_fit_holds },
  { id := "mlj-machine-unfitted", juliaFile := "src/MLJInterface.jl", juliaFns := ["machine", "_check_fitted", "predict", "report"]
    statement := "On a new machine, predict and report throw the ArgumentError naming the call; on a fitted machine, predict(mach) predicts the training features with the default index."
    preconditions := "None."
    status := .proven, prop := ``machine_unfitted, thm := some ``machine_unfitted_holds },
  { id := "mlj-fitted-params", juliaFile := "src/MLJInterface.jl", juliaFns := ["fitted_params", "full_report"]
    statement := "For either model kind, fitted_params projects best_idx, equations and equation_strings from the report built by that call."
    preconditions := "That report returns normally."
    status := .todo, prop := ``fitted_after_fit, notes := "Record exactly one string-enabled report call and its state transition; project its three fields without replaying the selector." },
  { id := "mlj-defaults", juliaFile := "src/MLJInterface.jl", juliaFns := ["modelexpr", "SRRegressor", "MultitargetSRRegressor", "SRTestRegressor", "MultitargetSRTestRegressor"]
    statement := "Each struct stores the given parallelism symbol, defaults to choose_best, and defaults to 1 iteration for the test structs and 100 otherwise."
    preconditions := "None."
    status := .proven, prop := ``defaults, thm := some ``defaults_holds },
  { id := "mlj-defaults-doc", juliaFile := "src/MLJInterface.jl", juliaFns := ["modelexpr", "tag_with_docstring"]
    statement := "The non-test models default to the documented niterations = 10."
    preconditions := "None."
    status := .refuted, prop := ``defaults_doc, thm := some ``defaults_doc_refuted
    notes := "The docstring (src/MLJInterface.jl:808) says `niterations::Int=10`; SRRegressor().niterations is 100 (src/MLJInterface.jl:68,129)." },
  { id := "mlj-parallelism-string", juliaFile := "src/MLJInterface.jl", juliaFns := ["modelexpr", "SRRegressor"]
    statement := "Every documented parallelism spelling, including the string form, constructs a model."
    preconditions := "Mode is serial, multithreading or multiprocessing."
    status := .refuted, prop := ``parallelism_string, thm := some ``parallelism_string_refuted
    notes := "The docstring (src/MLJInterface.jl:818) allows a string, but the field is parallelism::Symbol (src/MLJInterface.jl:74): SRRegressor(; parallelism=\"serial\") throws MethodError." },
  { id := "mlj-units-clean", juliaFile := "src/MLJInterface.jl", juliaFns := ["clean_units"]
    statement := "clean_units returns nothing exactly for dimensionless units (all dimensionless for a vector), and otherwise the units unchanged."
    preconditions := "None."
    status := .proven, prop := ``units_clean, thm := some ``units_clean_holds },
  { id := "mlj-units-unwrap", juliaFile := "src/MLJInterface.jl", juliaFns := ["unwrap_units_single", "dimension_with_fallback", "compat_ustrip"]
    statement := "Successful matrix unit unwrapping strips every value and returns one dimension per feature, shared by every entry of that feature."
    preconditions := "Unwrapping returns normally."
    status := .proven, prop := ``units_unwrap, thm := some ``units_unwrap_holds },
  { id := "mlj-units-unwrap-error", juliaFile := "src/MLJInterface.jl", juliaFns := ["unwrap_units_single"]
    statement := "The first feature with mixed units, numbered from 1, is named in the error \"Inconsistent units in feature i of matrix.\"."
    preconditions := "All features nonempty; earlier features consistent."
    status := .proven, prop := ``units_unwrap_error, thm := some ``units_unwrap_error_holds },
  { id := "mlj-units-vector", juliaFile := "src/MLJInterface.jl", juliaFns := ["unwrap_units_single"]
    statement := "Vector unwrapping returns the stripped values and the shared dimension, throws \"Inconsistent units in vector.\" on mixed units, and a BoundsError when empty."
    preconditions := "None."
    status := .proven, prop := ``units_vector, thm := some ``units_vector_holds },
  { id := "mlj-units-match", juliaFile := "src/MLJInterface.jl", juliaFns := ["validate_units"]
    statement := "Equal-length unit vectors match exactly when equal; nothing matches only nothing, never a nonempty vector."
    preconditions := "None."
    status := .proven, prop := ``units_match, thm := some ``units_match_holds },
  { id := "mlj-matrix-names", juliaFile := "src/MLJInterface.jl", juliaFns := ["get_matrix_and_info", "_matrix", "_istable", "_colnames", "_columns"]
    statement := "get_matrix_and_info returns one name and one dimension per feature: column names (display names equal) for tables, and x1, x2, ... with subscripted display names otherwise."
    preconditions := "Returns normally."
    status := .todo, prop := ``matrix_names, notes := "Bind concrete subscriptify and preserve the exact ordered column names of both row and column tables." },
  { id := "mlj-tables-extension", juliaFile := "src/MLJInterface.jl", juliaFns := ["_has_tables_ext"],
    statement := "An exotic array returns the exact Tables decision or error when loaded, and false otherwise. Built-in row and named-tuple classification does not depend on the extension.", preconditions := "Dispatch reaches the modeled array, row-table or named-tuple overload."
    status := .proven, prop := ``tablesDispatch, thm := some ``tablesDispatch_holds },
  { id := "mlj-option-symbol-priority", juliaFile := "src/MLJInterface.jl", juliaFns := ["getsymb"],
    statement := "Keyword name extraction returns the first depth-first symbol, stops at an unsupported syntax leaf, or returns nothing when no leaves remain.", preconditions := "None."
    status := .proven, prop := ``symbolPriority, thm := some ``symbolPriority_holds },
  { id := "mlj-hof-vector-eltype", juliaFile := "src/MLJInterface.jl", juliaFns := ["hof_eltype"],
    statement := "Nested vectors of halls report the numeric type parameter of the hall, even when empty.", preconditions := "Vector element types end at a concrete hall type.",
    status := .proven, prop := ``hofVectorType, thm := some ``hofVectorType_holds },
  { id := "mlj-prediction-warning", juliaFile := "src/MLJInterface.jl", juliaFns := ["prediction_warn"],
    statement := "Single-target fallback logs the zero-prediction warning before allocation, zero construction, filling and wrapping, and preserves the first exception.", preconditions := "Warning logger records all messages."
    status := .proven, prop := ``predictionWarning, thm := some ``predictionWarning_holds }
]

end SymReg.MLJ
