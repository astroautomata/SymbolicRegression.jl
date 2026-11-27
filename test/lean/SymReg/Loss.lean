import SymReg.Loss.Properties
import SymReg.Loss.Aggregation
import SymReg.Loss.Counterexamples
import SymReg.Loss.EndToEnd
import SymReg.Loss.EqualWeights
import DynExpr.Registry.Types

namespace SymReg.Loss
open DynExpr.Registry

def entries : List Entry := [
  { id := "loss-disabled-floor", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "With baseline use disabled, the cost is independent of the baseline and uses loss divided by the converted floor when complexity is explicit."
    preconditions := "Float16, Float32 or Float64 loss and Float64 parsimony."
    status := .proven, prop := ``disabled_floor, thm := some ``disabled_floor_holds },
  { id := "loss-ineligible-floor", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "For a baseline below or unordered with the converted floor, toggling baseline use leaves cost unchanged and the explicit-complexity formula divides loss by the floor."
    preconditions := "Float16, Float32 or Float64 loss and Float64 parsimony; baseline below or unordered with the floor."
    status := .proven, prop := ``ineligible_floor, thm := some ``ineligible_floor_holds },
  { id := "loss-baseline-finite", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["update_baseline_loss!"]
    statement := "For a basic dataset, successful configured baseline evaluation at numeric zero stores its finite loss unchanged and enables baseline use."
    preconditions := "The Number fallback selects zero(T), the configured builder succeeds, and the Float16, Float32 or Float64 loss is finite."
    status := .proven, prop := ``baseline_finite, thm := some ``baseline_finite_holds },
  { id := "loss-baseline-nonfinite", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["update_baseline_loss!"]
    statement := "For a basic dataset, successful configured baseline evaluation at numeric zero returning NaN or either infinity disables baseline use and stores one."
    preconditions := "The Number fallback selects zero(T), the configured builder succeeds, and the Float16, Float32 or Float64 loss is NaN or either infinity."
    status := .proven, prop := ``baseline_nonfinite, thm := some ``baseline_nonfinite_holds },
  { id := "loss-dispatch-missing", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_tree_dispatch"]
    statement := "A missing prediction always forces completion=false."
    preconditions := "None."
    status := .proven, prop := ``dispatch_missing, thm := some ``dispatch_missing_holds },
  { id := "loss-de-contract", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_tree_dispatch"]
    statement := "The DE evaluation-result adapter and both dispatch methods preserve an existing output array and completion flag."
    preconditions := "DE returned an array rather than nothing."
    status := .proven, prop := ``de_contract, thm := some ``de_contract_holds },
  { id := "loss-unweighted-mean", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_loss"]
    statement := "An unweighted custom loss receives target first and prediction second as documented by Options; its results are averaged."
    preconditions := "Nonempty matching floating vectors and a total homogeneous callback."
    status := .refuted, prop := ``unweighted_mean, thm := some ``unweighted_mean_refuted },
  { id := "loss-supervised-weighted-sum", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_weighted_loss"]
    statement := "On nonempty matching floating vectors, supervised weighted loss divides the Julia sum of weight times point loss by the Julia sum of weights."
    preconditions := "Nonempty matching floating vectors and a total homogeneous callback."
    status := .todo, prop := ``supervised_weighted_sum
    notes := "Proved against an unfaithful model; needs re-proof. Bind the mapped eachindex(x,y,w) and separate sum(w) to the linear or Cartesian reduction selected for each supported array or view, then relate the rounded products to independently indexed samples." },
  { id := "loss-custom-weighted-sum", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_weighted_loss"]
    statement := "A weighted custom loss receives target, prediction and weight in the order documented by Options; its summed outputs are divided by the summed weights."
    preconditions := "Nonempty matching floating vectors and a total homogeneous callback."
    status := .refuted, prop := ``custom_weighted_sum, thm := some ``custom_weighted_sum_refuted },
  { id := "loss-compatible-weighted", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_weighted_loss"]
    statement := "For a pure point loss, a custom ternary function returning the same rounded weight-times-loss value or point-loss error as SupervisedLoss gives the same weighted reduction outcome."
    preconditions := "Equal lengths and a common floating element and rounding type; ordinary one-based vectors and SR-created vector views, excluding OffsetArrays and custom axes (src/SymbolicRegression.jl:481-489; src/Dataset.jl:97-105).",
    status := .proven, prop := ``compatible_weighted, thm := some ``compatible_weighted_holds },
  { id := "loss-element-type-errors", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_loss", "_weighted_loss"]
    statement := "Mismatched array element types raise ErrorException identifying the arrays and their concrete types before indexing or invoking the point loss."
    preconditions := "Function or SupervisedLoss dispatch; the input array element types differ."
    status := .proven, prop := ``element_type_errors, thm := some ``element_type_errors_holds },
  { id := "loss-empty-mean", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_loss", "_weighted_loss"]
    statement := "The empty reduction raises ArgumentError on matching empty vectors.",
    preconditions := "Empty homogeneous ordinary one-based vectors and SR batch views, excluding OffsetArrays and custom axes (src/SymbolicRegression.jl:481-489; src/Dataset.jl:97-105).",
    status := .proven, prop := ``empty_mean, thm := some ``empty_mean_holds },
  { id := "loss-batch-fields", juliaFile := "src/Dataset.jl"
    juliaFns := ["batch", "getproperty", "get_indices", "get_full_dataset", "is_weighted"]
    statement := "An explicit batch counts its signed indices and reads the corresponding columns, targets and weights in order, preserving absent fields and bounds failures."
    preconditions := "None."
    status := .todo, prop := ``batch_fields
    notes := "Proved against an unfaithful model; needs re-proof. Represent parent and index object addresses and one-based view axes; check view bounds before reads while preserving absent targets and weights." },
  { id := "loss-batch-order", juliaFile := "src/Dataset.jl"
    juliaFns := ["batch", "getproperty"]
    statement := "For explicit and sampled batches, at every position of each present field the selected sample corresponds to the index at that position, including repetitions."
    preconditions := "Indices valid for the respective field."
    status := .todo, prop := ``batch_order
    notes := "Proved against an unfaithful model; needs re-proof. Bind rand(rng, 1:dataset.n, batch_size) to the preserved index-vector address, draw cursor and allocation/empty-range failures." },
  { id := "loss-evaluator-explicit", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["evaluator"]
    statement := "When the four-argument objective matches, it receives the full dataset and supplied index vector, regardless of the stored batch indices."
    preconditions := "A matching four-argument method exists for the explicit index."
    status := .proven, prop := ``evaluator_explicit, thm := some ``evaluator_explicit_holds,
    notes := "typedEvaluator_four also follows the supplied index address and looks up the exact argument type tuple." },
  { id := "loss-evaluator-inherited", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["evaluator"]
    statement := "When the four-argument objective matches, default indices pass the stored batch vector or nothing for a basic dataset."
    preconditions := "A matching four-argument method exists for the stored index value or nothing."
    status := .proven, prop := ``evaluator_inherited, thm := some ``evaluator_inherited_holds },
  { id := "loss-evaluator-three", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["evaluator"]
    statement := "When the resolved index has no matching four-argument method, evaluator calls the three-argument objective with the original dataset and returns its outcome independently of the index."
    preconditions := "No four-argument method matches the resolved index."
    status := .proven, prop := ``evaluator_three, thm := some ``evaluator_three_holds,
    notes := "typedEvaluator_three forwards the original options and dataset addresses and preserves MethodError when neither arity matches." },
  { id := "loss-node-objective", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss"]
    statement := "loss_function takes priority, receives the unwrapped node, and bypasses automatic regularization and context reset."
    preconditions := "A node objective is configured; no invalid keywords."
    status := .proven, prop := ``node_objective, thm := some ``node_objective_holds },
  { id := "loss-expression-objective", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss"]
    statement := "Both callback arities of an expression-only objective receive the whole input expression, including its tree and metadata projection."
    preconditions := "Only an expression objective is configured; the input is an expression."
    status := .todo, prop := ``expression_objective
    notes := "Proved against an unfaithful model; needs re-proof. Connect typedEvaluator to the expression-only eval_loss branch and observe the wrapper, metadata and component addresses under both callback arities." },
  { id := "loss-expression-assertion", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss"]
    statement := "An expression-only objective rejects a bare node before invoking it."
    preconditions := "Only an expression objective is configured."
    status := .proven, prop := ``expression_assertion, thm := some ``expression_assertion_holds },
  { id := "loss-context-bypass", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["create_eval_context"]
    statement := "Bumper or a backend without EvalContext support skips allocation and dataset access."
    preconditions := "Bumper is enabled or the operator backend does not take a context."
    status := .proven, prop := ``context_bypass, thm := some ``context_bypass_holds },
  { id := "loss-context-storage", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["create_eval_context"]
    statement := "A successful allocation has the requested slot count, selected sample length per slot, configured turbo flag and index zero; failure to select columns propagates."
    preconditions := "Context-capable non-Bumper backend."
    status := .todo, prop := ``context_storage
    notes := "Proved against an unfaithful model; needs re-proof. Model similar(X, axes(X,2)) followed by similar(array) for each slot, preserving both allocation errors, axes, slot types and the shared index Ref." },
  { id := "loss-context-reset", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_eval_loss"]
    statement := "Resetting a context is idempotent, preserves buffer storage values and turbo, and sets the represented buffer index to zero."
    preconditions := "None."
    status := .proven, prop := ``context_reset, thm := some ``context_reset_holds,
    notes := "resetIndexAliased also observes the zero through the original Ref address, including signed initial indices." },
  { id := "loss-incomplete-infinity", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_eval_loss"]
    statement := "A non-null evaluation result with completion false checks the output type, then returns the outcome of constructing L(Inf). Target, weight, aggregation and regularization paths are skipped, and the evaluation state is retained."
    preconditions := "Default loss dispatch, with the L(Inf) constructor selected for the dataset's loss type."
    status := .proven, prop := ``incomplete_infinity, thm := some ``incomplete_infinity_holds },
  { id := "loss-missing-infinity", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_eval_loss"]
    statement := "A missing prediction returns the outcome of constructing L(Inf), independent of the raw completion value, and retains evaluation state without running aggregation or regularization."
    preconditions := "Default loss dispatch, with the L(Inf) constructor selected for the dataset's loss type."
    status := .proven, prop := ``missing_infinity, thm := some ``missing_infinity_holds,
    notes := "The supplementary missing_template_infinity theorem follows the installed invalid-feature template path." },
  { id := "loss-dimension-no-units", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["dimensional_regularization"]
    statement := "Without units, dimensional_regularization short-circuits via !has_units(dataset) and immediately returns zero of the loss type without reading dataset columns."
    preconditions := "Neither input nor target units."
    status := .proven, prop := ``dimension_no_units, thm := some ``dimension_no_units_holds },
  { id := "loss-eval-context-pool", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["EvalContextPool", "acquire_eval_context", "release_eval_context!"]
    statement := "EvalContextPool returns pooled contexts in LIFO order without reallocation, falls back to create_eval_context when empty or nothing, and ignores release into nothing."
    preconditions := "None."
    status := .proven, prop := ``eval_context_pool, thm := some ``eval_context_pool_holds },
  { id := "loss-dimension-penalty", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["dimensional_regularization"]
    statement := "On nonempty data, a node with no valid dimensional assignment returns the configured penalty, defaulting to 1000, rounded to the loss type."
    preconditions := "Built-in dimensional rules; input units and selected first column are available."
    status := .todo, prop := ``dimension_penalty
    notes := "The regularization finish now separates typed conversion. Bind the dataset's actual L and unit views, relate the independent violation witness to Units.violatesUnits, then prove the configured or default penalty conversion outcome." },
  { id := "loss-dimension-satisfied", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["dimensional_regularization"]
    statement := "On nonempty data, a node with a valid dimensional assignment returns zero regardless of the penalty setting."
    preconditions := "Built-in dimensional rules; input units and selected first column are available."
    status := .todo, prop := ``dimension_satisfied
    notes := "Bind Units.dispatch's maximum degree to the constructor's node type and the units to the dataset; prove that the independent assignment satisfies the runtime's wildcard and builtin-operator rules." },
  { id := "loss-cached-cost", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "Explicit machine-Int complexity gives the typed signed cost and leaves the entire member cache unchanged, even if recomputing complexity would fail."
    preconditions := "Loss and baseline share type Float16, Float32 or Float64; Float64 parsimony."
    status := .proven, prop := ``cached_cost, thm := some ``cached_cost_holds },
  { id := "loss-computed-cost", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "Omitting explicit complexity uses the member's populated cache or computes the configured plain-tree complexity when the cache is unset, propagating computation errors."
    preconditions := "Plain-node tree, integer complexity mapping, floating loss and Float64 parsimony."
    status := .proven, prop := ``computed_cost, thm := some ``computed_cost_holds,
    notes := "recompute_cost_cache also checks cache writes only on successful recomputation." },
  { id := "loss-eligible-normalization", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "With explicit complexity and an enabled baseline at least the converted floor, including positive infinity, the typed cost divides loss by that baseline."
    preconditions := "Float16, Float32 or Float64 loss and Float64 parsimony; baseline at least the converted floor."
    status := .proven, prop := ``eligible_normalization, thm := some ``eligible_normalization_holds },
  { id := "loss-finite-cost", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "Finite floating loss and Float64 parsimony with explicit integer complexity yield finite cost for every baseline and baseline-use setting."
    preconditions := "Loss and parsimony are representable finite floats."
    status := .refuted, prop := ``finite_cost, thm := some ``finite_cost_refuted },
  { id := "loss-finite-cost-normal-range", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["loss_to_cost"]
    statement := "For explicitly supplied complexity and Float64 parsimony, loss and penalty with sufficient magnitude headroom give finite cost for every typed baseline and baseline-use setting."
    preconditions := "Representable baseline and representable finite loss and parsimony; absolute loss at most floatmax/400; absolute size at most 2^53; absolute exact penalty at most floatmax/4."
    status := .proven, prop := ``finite_cost_normal_range, thm := some ``finite_cost_normal_range_holds },
  { id := "loss-baseline-frame", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["update_baseline_loss!"]
    statement := "Relative to the state after callbacks, the updater preserves the BasicDataset's column, target and weight references and recorded mean, and makes no direct writes to their contents or to other datasets."
    preconditions := "BasicDataset; updater succeeds."
    status := .proven, prop := ``baseline_frame, thm := some ``baseline_frame_holds },
  { id := "loss-member-tree", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["get_tree_from_member"]
    statement := "Direct nodes, direct expressions and members return their original node or expression projection, including its metadata."
    preconditions := "The argument is a supported direct node, direct expression or member containing an expression."
    status := .todo, prop := ``member_tree
    notes := "Proved against an unfaithful model; needs re-proof. Stock PopMember stores an AbstractExpression reference, never a bare node. Bind direct and member inputs to addresses and observe metadata and graph sharing through the result." },
  { id := "loss-context-keyword-conflict", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss", "eval_cost"]
    statement := "When the deprecation check succeeds, supplying both evaluation-context keywords raises the conflicting-keywords assertion."
    preconditions := "Both contexts are non-nothing and the deprecation check succeeds."
    status := .proven, prop := ``context_keyword_conflict, thm := some ``context_keyword_conflict_holds,
    notes := "context_keyword_public checks both public warning calls and gives a warning failure priority over the keyword conflict." },
  { id := "loss-score-deprecated", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["score_func"]
    statement := "When deprecation handling succeeds, score_func forwards the original dataset, member, options and optional complexity and returns the eval_cost outcome."
    preconditions := "The deprecation check succeeds."
    status := .proven, prop := ``score_deprecated, thm := some ``score_deprecated_holds,
    notes := "score_deprecated_when_warned also checks the warning failure branch." },
  { id := "loss-initial-baseline", juliaFile := "src/Dataset.jl"
    juliaFns := ["Dataset"]
    statement := "A successfully constructed dataset initially enables baseline use and stores one for the requested or default loss type, after any deprecated argument override."
    preconditions := "Dataset construction succeeds."
    status := .todo, prop := ``initial_baseline
    notes := "Data.construct forwards only an optional type tag to its baseline service. Resolve the explicit or deprecated requested type, or default to T except for Complex{T}, then run one at the effective loss type before unit construction." },
  { id := "loss-equal-weights", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_loss", "_weighted_loss"]
    statement := "Equal finite nonzero weights preserve finiteness when the unweighted supervised mean is finite."
    preconditions := "Nonempty matching floating vectors; representable equal nonzero weights and finite unweighted mean."
    status := .refuted, prop := ``equal_weights, thm := some ``equal_weights_refuted },
  { id := "loss-equal-weights-rounding", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_loss", "_weighted_loss"]
    statement := "For positive normal-range inputs, the equal-weight and unweighted supervised means are finite and differ by at most 16n times machine epsilon times the unweighted mean."
    preconditions := "Nonempty matching floating vectors; normal positive point losses and products; sums in range with headroom and 16n times machine epsilon at most one."
    status := .todo, prop := ``equal_weights_rounding
    notes := "Bind the mapped numerator and separate sum(weights) to their actual, possibly different reduction paths. Lift the half-ULP bounds through positive partial sums and both final quotients, accounting for underflow and overflow." },
  { id := "loss-complete-unweighted", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_eval_loss", "eval_loss"]
    statement := "Completed unweighted evaluation uses the selected label and prediction pairs, adds the enabled penalty after taking the mean, and propagates point-loss and regularization errors."
    preconditions := "Complete prediction; nonempty matching unweighted arrays."
    status := .todo, prop := ``complete_unweighted
    notes := "The default-loss stages now separate aggregate and final types. Bind the Statistics first-point probe, accumulator, divisor and result types to actual dispatch on supported arrays; then connect the independently stated mean, dimensional penalty and final conversion to L." },
  { id := "loss-complete-weighted", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_eval_loss", "eval_loss"]
    statement := "Completed weighted evaluation supplies each selected weight once, adds the enabled penalty after normalization, and propagates point-loss and regularization errors."
    preconditions := "Complete prediction; nonempty matching weighted arrays."
    status := .todo, prop := ``complete_weighted
    notes := "Connect both typed matching-array reductions to the default loss stages: supervised weighting before accumulation, and custom callback on the original weight. Prove the separately typed numerator, denominator, penalty addition and return conversion with first-error order." },
  { id := "loss-cost-pair", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_cost", "loss_to_cost", "get_tree_from_member"]
    statement := "With explicit complexity, eval_cost returns the typed cost formula from the dataset's baseline and the evaluated loss, and retains the resulting context."
    preconditions := "Loss evaluation succeeds; Float64 loss and parsimony; explicit complexity."
    status := .todo, prop := ``cost_pair
    notes := "Proved against an unfaithful model; needs re-proof. Connect one stateful evaluation on the original references to post-callback baseline reads and the signed cost model; with omitted size, observe both reused and newly filled caches." },
  { id := "loss-default-dispatch", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss", "_eval_loss"]
    statement := "Without custom objectives, changing only the explicit idx keyword does not change the loss evaluation result."
    preconditions := "Neither custom objective is configured."
    status := .proven, prop := ``default_dispatch, thm := some ``default_dispatch_holds },
  { id := "loss-keyword-errors", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss", "eval_cost"]
    statement := "Unknown keywords raise a method error before evaluation or complexity computation."
    preconditions := "At least one unknown keyword; no deprecated context conflict."
    status := .proven, prop := ``keyword_errors, thm := some ``keyword_errors_holds },
  { id := "loss-deprecated-context", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss", "eval_cost"]
    statement := "A lone deprecated eval_options context behaves exactly like eval_context."
    preconditions := "Only the deprecated context keyword is supplied."
    status := .proven, prop := ``deprecated_context, thm := some ``deprecated_context_holds },
  { id := "loss-baseline-update", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["update_baseline_loss!"]
    statement := "The BasicDataset updater initializes the input value and then constructs and evaluates the configured expression on the original dataset. It stores and enables a finite result or disables baseline use and stores one of the loss type. A failure before those assignments propagates with callback effects retained and neither assignment made."
    preconditions := "Stock mutable BasicDataset fields; configured builder and loss dispatch, including return conversion, are delegated."
    status := .proven, prop := ``baseline_update, thm := some ``baseline_update_holds },
  { id := "loss-evaluation-error", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["_eval_loss", "eval_tree_dispatch"]
    statement := "Default loss resets the original context before the first X read. The first failing X read, expected output type lookup, or evaluator call propagates its exception and state without running aggregation or regularization."
    preconditions := "Default loss dispatch and a supported context or no context."
    status := .proven, prop := ``evaluation_error, thm := some ``evaluation_error_holds },
  { id := "loss-dimension-empty", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["dimensional_regularization"]
    statement := "On data with zero sample columns, dimensional_regularization returns zero when has_units is false and raises BoundsError (or the TemplateExpression assertion) when has_units is true."
    preconditions := "The node case has zero selected sample columns; the template case has no restriction on columns."
    status := .proven, prop := ``dimension_empty, thm := some ``dimension_empty_holds },
  { id := "loss-baseline-average", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["update_baseline_loss!"]
    statement := "Baseline update stores the documented loss of the constant average predictor."
    preconditions := "Basic numeric dataset; nonempty target array exists."
    status := .refuted, prop := ``baseline_average, thm := some ``baseline_average_refuted
    notes := "src/LossFunctions.jl:260 constructs init_value(T)=0 instead of the target average. With y=[2.0,4.0] and squared loss, update_baseline_loss! stores 10.0; predicting the target average 3.0 has loss 1.0. Reproducer loss-baseline-average.jl evaluates both through SR's expression builder." },
  { id := "loss-dataset-average", juliaFile := "src/Dataset.jl"
    juliaFns := ["Dataset"]
    statement := "Numeric Dataset construction records the weighted or unweighted average of its target values."
    preconditions := "Nonempty target array; sample, target and optional weight lengths agree."
    status := .refuted, prop := ``dataset_average, thm := some ``dataset_average_refuted
    notes := "src/Dataset.jl:183 tests eltype(y) isa Number. Float64 is a type object, so the condition is false and avg_y is nothing. Dataset(X,[2.0,4.0]).avg_y is nothing rather than 3.0; with weights=[1.0,3.0] it is nothing rather than 3.5." },
  { id := "loss-explicit-index", juliaFile := "src/LossFunctions.jl"
    juliaFns := ["eval_loss", "_eval_loss"]
    statement := "An explicit idx keyword selects the same columns, labels and weights as a SubDataset for the default elementwise objective."
    preconditions := "No custom objective; ordinary numeric arrays."
    status := .refuted, prop := ``explicit_index, thm := some ``explicit_index_refuted
    notes := "src/LossFunctions.jl:188 drops idx. With X=[1.0 3.0], y=[0.0,0.0], weights=[1.0,3.0] and tree x1, eval_loss(...;idx=[1]) returns 7.0 while eval_loss(...,batch(dataset,[1]),...) returns 1.0. The accepted keyword only reaches custom callbacks; questions-loss.md records that compatibility interpretation." }
]

end SymReg.Loss
