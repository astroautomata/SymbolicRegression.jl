import SymReg.MutateGen.WeightsProps
import SymReg.MutateGen.SampleProps
import SymReg.MutateGen.ConditionProps
import SymReg.MutateGen.EngineProps
import SymReg.MutateGen.HandlerProps
import DynExpr.Registry.Types

/-!
Slice `MutateGen`: mutation choice and the next-generation engine of `src/Mutate.jl`
(except the simplify handler) and `src/MutationWeights.jl`.
-/

namespace SymReg.MutateGen
open DynExpr.Registry

def entries : List Entry := [
  -- src/MutationWeights.jl
  { id := "mutgen-weights-fields", juliaFile := "src/MutationWeights.jl"
    juliaFns := ["_mutations_from_weights", "MutationWeights", "convert", "copy", "_MUTATION_FROM_SYMBOL"]
    statement := "For every MutationWeights w, _mutations_from_weights(w) pairs each field, in field order, with the mutation type its docstring names (mutate_constant => ConstantMutation, ..., break_connection => BreakConnectionMutation) and that field's weight; its weights are convert(Vector, w); copy(w) has the same fields."
    preconditions := "None."
    status := .todo, prop := ``from_weights, thm := none
    notes := "Need explicit per-position specs independent of fieldNames, stock instance parameters, and mutation through a separately allocated copy." },
  { id := "mutgen-weights-kw", juliaFile := "src/MutationWeights.jl"
    juliaFns := ["MutationWeights", "_mutation_weights"]
    statement := "MutationWeights first propagates a deprecation error, then rejects the first unknown keyword, then converts provided values to Float64 in field order. It uses the stock defaults for omitted fields and stores the resulting values without normalization."
    preconditions := "Keyword names are distinct (Julia keyword syntax); the Julia runtime supplies the deprecation result and Float64 conversion for the keyword value types."
    status := .proven, prop := ``kw_weights, thm := some ``kw_weights_holds },
  -- _sample_mutation and sample_mutation
  { id := "mutgen-sample-errors", juliaFile := "src/Mutate.jl"
    juliaFns := ["_sample_mutation"]
    statement := "_sample_mutation throws ArgumentError(\"Weights must be nonnegative.\") when some weight fails weight >= 0.0 (negative, -Inf or NaN) and ArgumentError(\"At least one weight must be positive.\") when all weights are zero, in both cases without drawing from the RNG."
    preconditions := "Arbitrary weight lists and RNG streams."
    status := .proven, prop := ``sample_errors, thm := some ``sample_errors_holds },
  { id := "mutgen-sample-interval", juliaFile := "src/Mutate.jl"
    juliaFns := ["_sample_mutation"]
    statement := "With Float64 weights and a positive checked total, the sampler picks the first rounded prefix strictly greater than the rounded threshold; if none crosses it picks the last entry."
    preconditions := "Stock one-based Vector of Float64 weights passing validation; task-local Float64 unit draw."
    status := .proven, prop := ``sample_interval, thm := some ``sample_interval_holds,
    notes := "The threshold can equal the total for subnormal weights." },
  { id := "mutgen-sample-reachable", juliaFile := "src/Mutate.jl"
    juliaFns := ["_sample_mutation"]
    statement := "A mutation is reachable exactly when a possible task-local Float64 draw has its index as the first rounded crossing or the last-index fallback."
    preconditions := "Stock one-based Vector of Float64 weights passing validation and a positive checked total."
    status := .proven, prop := ``sample_reachable, thm := some ``sample_reachable_holds },
  { id := "mutgen-sample-infinite", juliaFile := "src/Mutate.jl"
    juliaFns := ["_sample_mutation"]
    statement := "For weights that pass _sample_mutation's own checks (each weight >= 0.0, positive total), including infinite weights, and any draw in [0, 1), the returned index has a positive weight."
    preconditions := "Weights accepted by the weight >= 0.0 and total > 0.0 checks; draw in [0, 1)."
    status := .refuted, prop := ``sample_positive_extended, thm := some ``sample_positive_extended_refuted
    notes := "Bug: with an infinite weight the threshold rand() * total is Inf (NaN when rand() == 0.0), no running sum exceeds it, and the fallback lastindex(mutations) (src/Mutate.jl:261) returns the last entry whatever its weight. _sample_mutation([:operator => Inf, :constant => 0.0]) returns 2 (weight 0.0) instead of 1. Finite weights whose sum overflows do the same: _sample_mutation([:a => 1e308, :b => 1e308, :c => 0.0]) returns 3. Options does not validate weights, so mutations=[OperatorMutation() => Inf] reaches this; the Lean counterexample uses JF's +Inf, since JF has no overflow." },
  { id := "mutgen-sample-exported-zero-draw", juliaFile := "src/MutationWeights.jl"
    juliaFns := ["sample_mutation"]
    statement := "For finite nonnegative weights with at least one positive weight and draws in [0, 1), the exported sample_mutation returns only mutations with a positive weight."
    preconditions := "Finite nonnegative weights, some positive; draws in [0, 1); StatsBase 0.34.13 sample."
    status := .refuted, prop := ``exported_positive, thm := some ``exported_positive_refuted
    notes := "Bug: StatsBase.sample(eachindex, Weights) scans `while cw < t`; when rand() returns exactly 0.0 (a legal value) the scan stops at index 1 even if its weight is 0, so sample_mutation([OperatorMutation() => 0.0, ConstantMutation() => 1.0]) returns OperatorMutation(). The reproducer sets the task-local Xoshiro state so the next rand() is 0.0. Probability 2^-53 per call; _sample_mutation uses a strict `<` after accumulating and does not have this problem. With all weights zero sample_mutation also silently returns the first mutation instead of throwing." },
  -- conditioning
  { id := "mutgen-cond-update", juliaFile := "src/Mutate.jl"
    juliaFns := ["_update_weight!", "_set_weight!", "_scale_weight!"]
    statement := "On the stock Float64 vector, the successful value projection changes only entries matching the mutation type, preserving their tags and vector length. Setting replaces the weight; scaling rounds conversion and multiplication to Float64."
    preconditions := "Stock Float64 weights; the value projection models only successful assignments."
    status := .proven, prop := ``stock_update_weight, thm := some ``stock_update_weight_holds },
  { id := "mutgen-cond-leaf", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "When the generic conditioning method applies to a leaf, it zeroes OperatorMutation, SwapOperandsMutation, DeleteNodeMutation and SimplifyMutation; on a variable leaf also OptimizeMutation and ConstantMutation; on a constant leaf FeatureMutation. Templates instead use their own conditioning method."
    preconditions := "Generic engine conditioning; tree with degree 0 at the root. See mutgen-cond-nonleaf for template dispatch."
    status := .proven, prop := ``leaf_disable, thm := some ``leaf_disable_holds },
  { id := "mutgen-cond-sharing", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "For expression types that do not preserve sharing, condition_mutation_weights! zeroes FormConnectionMutation and BreakConnectionMutation on every tree."
    preconditions := "preserve_sharing(typeof(member.tree)) is false."
    status := .proven, prop := ``sharing_disable, thm := some ``sharing_disable_holds },
  { id := "mutgen-cond-nonleaf", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!", "condition_mutate_constant!"]
    statement := "On generic nonleaves and templates, conditioning zeroes FeatureMutation when nfeatures <= 1, AddNodeMutation and InsertNodeMutation when complexity >= curmaxsize, and SimplifyMutation when should_simplify is false. The generic method also disables SwapOperandsMutation if no node has degree 2 and applies Float64 constant-weight scaling; the template method keeps both SwapOperandsMutation and ConstantMutation weights."
    preconditions := "Inputs are projections of the member and options; installed template method or generic method with the stock constant-scaling hook."
    status := .todo, prop := ``nonleaf_rules, thm := none
    notes := "The branch law is proved for projected facts; bind counts and complexity to the installed member operations, including lazy cache writes and overridden constant hooks." },
  { id := "mutgen-cond-frame", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! keeps every entry's mutation and the order, and leaves the weights of RotateTreeMutation, RandomizeMutation, DoNothingMutation, BacksolveMutation and every user-defined mutation unchanged."
    preconditions := "Arbitrary weights, tree and options."
    status := .todo, prop := ``frame, thm := none
    notes := "Need actual configured mutation payloads and custom object identity in the vector slots rather than Kind tags." },
  { id := "mutgen-cond-swap-arity", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! keeps SwapOperandsMutation's weight whenever some node has at least two children, the condition under which swap_operands swaps two children."
    preconditions := "Finite tree with degrees <= D."
    status := .refuted, prop := ``swap_kept, thm := some ``swap_kept_refuted
    notes := "Bug: the check is any(node -> node.degree == 2, tree) (src/Mutate.jl:193), while swap_operands acts on any node with degree > 1 (src/MutationFunctions.jl:88-101). With operators=OperatorEnum(1 => (cos,), 2 => (+,), 3 => (fma,)) and the tree fma(x1, x2, x3), the conditioned SwapOperandsMutation weight is 0.0 although swap_operands changes the tree (e.g. to fma(x2, x1, x3)); it should keep the options weight." },
  { id := "mutgen-cond-feature-nfeatures", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! zeroes FeatureMutation whenever nfeatures <= 1, where mutate_feature returns the tree unchanged."
    preconditions := "Arbitrary tree; nfeatures <= 1."
    status := .refuted, prop := ``feature_nfeatures, thm := some ``feature_nfeatures_refuted
    notes := "Bug: the leaf branch returns early (src/Mutate.jl:190) before the nfeatures <= 1 check (lines 199-201). For the leaf x1 with nfeatures = 1 the conditioned FeatureMutation weight stays 0.1 (the options weight) instead of 0.0, so a no-op mutation is sampled, passes the constraints and costs an evaluation." },
  { id := "mutgen-cond-add-maxsize", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! zeroes AddNodeMutation and InsertNodeMutation whenever the member's complexity is at least curmaxsize."
    preconditions := "Arbitrary tree and complexity with complexity >= curmaxsize."
    status := .refuted, prop := ``add_maxsize, thm := some ``add_maxsize_refuted
    notes := "Bug: the leaf branch returns early (src/Mutate.jl:190) before the complexity >= curmaxsize check (lines 203-207). With Options(; binary_operators=[+, *], complexity_of_variables=3), the leaf x1 has complexity 3 >= curmaxsize = 3 but AddNodeMutation and InsertNodeMutation keep their weights, so growth mutations that can only fail the constraints are sampled (up to 10 wasted attempts)." },
  { id := "mutgen-cond-feature-variable", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! zeroes FeatureMutation on every tree without a variable leaf, where mutate_feature returns the tree unchanged, as it does for a constant leaf."
    preconditions := "Arbitrary tree without variables; arbitrary options."
    status := .refuted, prop := ``feature_needs_variable, thm := some ``feature_needs_variable_refuted
    notes := "Bug: only the constant-leaf branch zeroes FeatureMutation (src/Mutate.jl:187-189). For the tree 1.0 + 2.0 (built with the Node constructor) and nfeatures = 2, FeatureMutation keeps weight 0.1, and mutate_feature returns the tree unchanged (src/MutationFunctions.jl:201)." },
  { id := "mutgen-cond-optimize-constant", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! zeroes OptimizeMutation on every tree without constants, where optimize_constants does nothing, as it does for a variable leaf."
    preconditions := "Tree with count_constant_nodes = count_scalar_constants = 0; arbitrary options."
    status := .refuted, prop := ``optimize_needs_constant, thm := some ``optimize_needs_constant_refuted
    notes := "Bug: only the variable-leaf branch zeroes OptimizeMutation (src/Mutate.jl:184-186). With mutations=[OptimizeMutation() => 0.1] and the tree x1 + x2, OptimizeMutation keeps weight 0.1; optimize_constants returns the member unchanged with 0 evaluations (src/ConstantOptimization.jl:148-150), and next_generation then reports it accepted (and returns the parent object, see mutgen-ng-no-alias)." },
  { id := "mutgen-cond-rotate-root", juliaFile := "src/Mutate.jl"
    juliaFns := ["condition_mutation_weights!"]
    statement := "condition_mutation_weights! zeroes RotateTreeMutation on every tree without a valid rotation root, where randomly_rotate_tree! returns the tree unchanged."
    preconditions := "Arbitrary tree with no operator node that has an operator child."
    status := .refuted, prop := ``rotate_needs_root, thm := some ``rotate_needs_root_refuted
    notes := "Bug: RotateTreeMutation is never conditioned. On the leaf x1 (and on x1 + x2) it keeps its options weight (4.26 with the Options defaults, the largest weight), while randomly_rotate_tree! returns the tree unchanged (src/MutationFunctions.jl:626-630); the no-op passes the constraints, costs an evaluation and is reported as an accepted mutation." },
  -- next_generation
  { id := "mutgen-ng-evals", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation", "mutate!", "MutationResult"]
    statement := "Starting from Float64 zero, next_generation adds each mutate! call's reported count in order, rounding each addition to Float64. The engine scores the proposed tree directly at most once and adds one dataset fraction after that call. Handler-internal scores count through the handler report."
    preconditions := "Normal return; the handler reports and dataset fraction are Float64."
    status := .proven, prop := ``ng_evals, thm := some ``ng_evals_holds },
  { id := "mutgen-ng-attempts", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation", "mutate!"]
    statement := "next_generation calls mutate! with attempt = 1, 2, ..., n in order, 1 <= n <= max_attempts = 10, and every call after the first follows a check_constraints call that rejected the previous tree."
    preconditions := "As mutgen-ng-evals."
    status := .todo, prop := ``ng_attempts, thm := none
    notes := "Need to log each attempt's actual scratch input and output and prove that the next attempt immediately follows rejection of that output." },
  { id := "mutgen-ng-events", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation", "_fire_on_mutation_end!", "_dispatch_next_generation"]
    statement := "Each next_generation call samples one mutation and fires on_mutation_end! exactly once per plugin, in plugin order, with a single MutationEvent whose accepted flag is the returned mutation_accepted and whose mutation_idx is the sampled index."
    preconditions := "As mutgen-ng-evals."
    status := .todo, prop := ``ng_events, thm := none
    notes := "Need to bind the sampled configured instance and prove all before/after fields from the actual score or immediate result on each exit." },
  { id := "mutgen-ng-sampled", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "condition_mutation_weights!", "_sample_mutation", "_mutation_weights_scratch"]
    statement := "Next generation dispatches the entry at the sampled index of the weights after engine and plugin conditioning."
    preconditions := "Normal return."
    status := .todo, prop := ``ng_sampled, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof with task-cache identity and substituting plugin conditioners. Float64 sampling can dispatch a zero-weight entry." },
  { id := "mutgen-ng-sampled-positive", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_sample_mutation"]
    statement := "A normally returning next_generation dispatches only a mutation with positive conditioned weight when every conditioned weight is finite and nonnegative."
    preconditions := "Stock one-based Vector of representable Float64 weights; task-local draw on Julia Xoshiro's 53-bit grid."
    status := .refuted, prop := ``ng_positive, thm := some ``ng_positive_refuted
    notes := "With weights [nextfloat(0.0), 0.0] and draw 0.75 the threshold rounds to the total, selecting the last entry. The shipped default weights do not hit this case." },
  { id := "mutgen-ng-sampled-positive-normal", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_sample_mutation"]
    statement := "A normally returning next_generation dispatches only a mutation with positive conditioned weight when all conditioned weights are nonnegative and every nonzero weight has a binary64 exponent from -510 through 510."
    preconditions := "Stock one-based Vector with length representable by Int64; representable Float64 weights; task-local draw on Julia Xoshiro's 53-bit grid."
    status := .proven, prop := ``ng_positive_normal, thm := some ``ng_positive_normal_holds },
  { id := "mutgen-ng-accept-sound", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation"]
    statement := "A mutation next_generation reports accepted either came from a mutate! call that returned immediately with success, or is a newly allocated member whose tree passed check_constraints(tree, options, curmaxsize), whose cost and loss are eval_cost of that tree, whose cost is not NaN and whose parent is the input member's ref."
    preconditions := "Store invariant: allocated object ids are below the allocation counter."
    status := .todo, prop := ``ng_accept_sound, thm := none
    notes := "Need to record the actual constraint context and score result, and tie immediate acceptance to the exact handler member." },
  { id := "mutgen-ng-reject-copy", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation"]
    statement := "When next_generation reports a rejection (constraint failure, self-reported failure, NaN cost or acceptance draw), it returns a newly allocated member holding a copy of the parent's tree with the parent's cost and loss and parent = the input member's ref."
    preconditions := "Store invariant as mutgen-ng-accept-sound."
    status := .todo, prop := ``ng_reject_copy, thm := none
    notes := "Need to compose copy_into! and create_child with the expression heap so that copy independence and stock lineage are observable." },
  { id := "mutgen-ng-nan-reject", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation"]
    statement := "A mutated tree whose eval_cost cost is NaN is always rejected."
    preconditions := "As mutgen-ng-evals."
    status := .proven, prop := ``ng_nan_reject, thm := some ``ng_nan_reject_holds },
  { id := "mutgen-ng-accept-rule", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation"]
    statement := "When the engine evaluated a tree with non-NaN cost, the mutation is accepted exactly when the product p of the plugins' mutation_acceptance_multiplier values does not satisfy p < u for one draw u in [0, 1): acceptance probability min(1, p), always for NaN p or p >= 1."
    preconditions := "Draws in [0, 1); arbitrary plugin multipliers (including NaN and infinities)."
    status := .todo, prop := ``ng_accept_rule, thm := none
    notes := "Need an observed draw after the hooks and the typed Julia product for Real multipliers. The old min(1,p) formula is invalid for negative multipliers." },
  { id := "mutgen-ng-no-plugins", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation"]
    statement := "With no plugins (prod(()) == 1.0), every evaluated tree with non-NaN cost is accepted."
    preconditions := "options.plugins is empty; draws in [0, 1)."
    status := .proven, prop := ``ng_no_plugins_accept, thm := some ``ng_no_plugins_accept_holds },
  { id := "mutgen-ng-immediate", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "_next_generation", "MutationResult"]
    statement := "When a mutate! call returns immediately with success, next_generation accepts its member and makes no eval_cost call."
    preconditions := "As mutgen-ng-evals."
    status := .todo, prop := ``ng_immediate, thm := none
    notes := "Need the exact handler member identity, no constraint check of that result, and the assertion for immediate success with no member." },
  { id := "mutgen-ng-no-alias", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "mutate!"]
    statement := "If next_generation returns the input member, it accepted a successful immediate result carrying that same object. The stock allocator for non-immediate results cannot return the parent."
    preconditions := "Existing member addresses below the allocator cursor; normal return."
    status := .todo, prop := ``ng_no_alias, thm := none,
    notes := "The model permits custom immediate parent returns. Need the converse for exact forwarding and binding of the installed simplify handler to the stock allocator." },
  { id := "mutgen-ng-parent-unchanged", juliaFile := "src/Mutate.jl"
    juliaFns := ["next_generation", "mutate!"]
    statement := "The parent's tree field keeps the same reference, and its cost, loss, ref, parent and birth are unchanged. Its complexity field is either unchanged or, if it was -1, becomes the tree's computed complexity."
    preconditions := "Normal return; stock member and allocation with live ids below the allocator cursor; handlers do not return the parent and hooks do not mutate it."
    status := .proven, prop := ``ng_parent_unchanged, thm := some ``ng_parent_unchanged_holds },
  { id := "mutgen-ng-scratch", juliaFile := "src/Mutate.jl"
    juliaFns := ["_mutation_weights_scratch", "next_generation"]
    statement := "next_generation's result does not depend on the previous contents of the per-task scratch vector: _mutation_weights_scratch resizes it and copies options.mutations."
    preconditions := "Arbitrary previous scratch contents, including #undef slots."
    status := .todo, prop := ``ng_scratch, thm := none
    notes := "The current proof covers distinct value storage; model PerTaskCache replacement and vector aliases with options.mutations." },
  -- mutate! methods
  { id := "mutgen-mut-tree", juliaFile := "src/Mutate.jl"
    juliaFns := ["mutate!"]
    statement := "The mutate! methods of ConstantMutation, OperatorMutation, FeatureMutation, SwapOperandsMutation, AddNodeMutation, InsertNodeMutation, DeleteNodeMutation, FormConnectionMutation, BreakConnectionMutation, RotateTreeMutation and RandomizeMutation return the mutated copy as tree with num_evals = 0, return_immediately = false and success = true, only consuming draws of the task-local stream."
    preconditions := "Arbitrary tree-level mutation functions."
    status := .todo, prop := ``tree_handlers, thm := none
    notes := "Need actual helper outputs, helper failures with prior effects, and the successful trace-tag writes." },
  { id := "mutgen-mut-add-node", juliaFile := "src/Mutate.jl"
    juliaFns := ["mutate!"]
    statement := "AddNodeMutation appends a random operator (append_random_op) when its first draw is below 0.5 and prepends one (prepend_random_op) otherwise."
    preconditions := "Arbitrary draws and mutation functions."
    status := .todo, prop := ``add_node_choice, thm := none
    notes := "Need the installed append/prepend heap effects and observations that only the selected helper runs and writes its matching trace tag." },
  { id := "mutgen-mut-do-nothing", juliaFile := "src/Mutate.jl"
    juliaFns := ["mutate!"]
    statement := "DoNothingMutation returns immediately with success and num_evals = 0 a newly allocated member holding the scratch copy of the parent's tree, the parent's cost and loss, and parent = parent_ref."
    preconditions := "Store invariant as mutgen-ng-accept-sound."
    status := .todo, prop := ``do_nothing_child, thm := none
    notes := "Need to model identity tracing, the ordinary reference draw and the separate birth source in create_child." },
  { id := "mutgen-mut-unknown", juliaFile := "src/Mutate.jl"
    juliaFns := ["mutate!"]
    statement := "A mutation that dispatches to the fallback raises ErrorException with `Unknown mutation type: ` followed by the displayed concrete type."
    preconditions := "User mutation type with no more specific method, with Julia's displayed type supplied by the runtime."
    status := .todo, prop := ``unknown_mutation, thm := none,
    notes := "The model now includes the interpolation. Need an independent observation of Julia method resolution and displayed concrete type." },
  { id := "mutgen-bs-success", juliaFile := "src/Mutate.jl"
    juliaFns := ["mutate!"]
    statement := "A BacksolveMutation result that returns immediately carries a newly made child whose tree passed check_constraints with its own complexity, whose cost and loss are eval_cost of that tree and whose cost passed the improvement gate against the parent's cost (re-evaluated on the batch for a SubDataset)."
    preconditions := "Arbitrary node sampler, inversion, fit, splice, constraints and evaluator."
    status := .todo, prop := ``backsolve_success, thm := none
    notes := "Need non-root sampling, masked fit, actual same-batch parent evaluation, and fresh child identity under the installed allocator." },
  { id := "mutgen-bs-restore", juliaFile := "src/Mutate.jl"
    juliaFns := ["mutate!"]
    statement := "When set_child! back to the original node restores the tree, every BacksolveMutation result that does not return immediately reports success = false and hands back the scratch copy unchanged: all rejected candidate splices are reverted."
    preconditions := "set_child!(parent, node, idx) after set_child!(parent, new_node, idx) restores the tree."
    status := .todo, prop := ``backsolve_restores, thm := none
    notes := "Need installed child-slot writes and observations before retry, preserving the saved parent address, slot index, original object and aliases." },
  { id := "mutgen-bs-failure-trace", juliaFile := "src/Mutate.jl", juliaFns := ["backsolve_fail"],
    statement := "An unsupported expression fails before evaluation, preserving the scratch tree and recording the unsupported-expression reason when tracing is enabled.", preconditions := "The expression is not a plain Expression wrapper."
    status := .proven, prop := ``backsolveFailureTrace, thm := some ``backsolveFailureTrace_holds }
]

end SymReg.MutateGen
