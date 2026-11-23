import SymReg.Mutations.Swap
import SymReg.Mutations.Delete
import SymReg.Mutations.FixedSize
import SymReg.Mutations.Refute
import SymReg.Mutations.Backsolve
import SymReg.Mutations.Examples
import SymReg.Mutations.Expression
import DynExpr.Registry.Types

/-!
Registry entries for `src/MutationFunctions.jl` (except `crossover_trees`,
`_random_node_and_parent` and `_find_parent`, covered by `SymReg.Crossover`).
-/

namespace SymReg.Mutations
open DynExpr.Registry

/-- Every registered property of the slice. -/
def entries : List Entry := [
  { id := "mut-mutate-operator"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["mutate_operator"]
    statement := "A leaf is unchanged without a draw. After the sampler selects a branch, an in-range, representable operator draw writes only that branch object's operator and keeps the root and all other objects. Operator lookup, empty range and unrepresentable UInt8 errors propagate. The unshared, well-formed case also preserves unfolded well-formedness."
    preconditions := "Node or GraphNode with readable root and sampled branch. The unfolded well-formedness clause uses an unshared plain Node and compatible operator counts at most 255."
    status := .proven
    prop := ``mutate_operator_spec
    thm := some ``mutate_operator_spec_holds },
  { id := "mut-mutate-operator-changes"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["mutate_operator"]
    statement := "mutate_operator (docstring: \"Randomly convert an operator into another one\") changes the operator of the node it mutates whenever every degree has at least two operators."
    preconditions := "As mut-mutate-operator; every options.nops entry is in 2:255; the root is a branch."
    status := .refuted
    prop := ``mutate_operator_changes
    thm := some ``mutate_operator_changes_refuted
    notes := "Bug (behaviour differs from the docstring): node.op = rand(rng, 1:(options.nops[node.degree])) (src/MutationFunctions.jl:118) draws from all operators of the degree, including the current one, so with k operators the mutation is a no-op with probability 1/k. mutate_feature excludes the current feature (line 204) but mutate_operator does not. Example: tree = Node(1, x1, x1) with binary_operators=[+, *]: mutate_operator(tree, options, rng) leaves op == 1 for about half of all seeds (465 of 1000 Xoshiro seeds)." },
  { id := "mut-mutate-constant"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["mutate_constant", "_mutate_value", "mutate_value", "mutate_factor"]
    statement := "mutate_constant(tree, temperature, options, m, rng) returns the same root object; without a constant leaf (has_constants false) nothing changes and nothing is drawn; otherwise the first draw selects the k-th constant leaf in preorder (uniform over constant leaves), the next three draws (rand(rng, T), rand(rng, Bool), rand(rng)) give the factor of mutate_factor, and the result is the input tree with exactly that constant replaced by val * factor (mutate_value via _mutate_value); every other node is kept."
    preconditions := "Plain Node; finite alias-free tree (unfold succeeds, NoAlias); degrees <= D; arbitrary RNG stream; val * factor and maxChange^r arbitrary functions."
    status := .todo
    prop := ``mutate_constant_spec
    thm := none
    notes := "Proved against an unfaithful model; bind nonnumeric method lookup and prove the sampled address frame with the typed mutation and storage conversion." },
  { id := "mut-mutate-factor-negate"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["mutate_factor", "mutate_value", "ConstantMutation"]
    statement := "For draws in [0, 1) and a positive magnitude, mutate_factor returns a negative factor exactly when the sign draw is strictly greater than the Float64 result of 1 - m.probability_flip_sign."
    preconditions := "perturbation_factor, temperature >= 0; probability_flip_sign a Float64 in [0, 1]; maxChange^r > 0 for maxChange > 0; real draws in [0, 1)."
    status := .proven
    prop := ``mutate_factor_negate
    thm := some ``mutate_factor_negate_holds
    notes := "The documented flip probability is probability_flip_sign in the continuous uniform idealization. Julia uses a discrete draw and a rounded threshold; equality with the threshold leaves the sign unchanged." },
  { id := "mut-mutate-feature"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["mutate_feature"]
    statement := "For Node and GraphNode, signed counts at most one or a search finding no feature leave the root, heap and RNG unchanged. After successful selection, a representable draw writes a different in-range feature only at the selected address. An unrepresentable draw raises InexactError without a heap write. Both outcomes consume the two selections."
    preconditions := "The heap-level branch uses the actual predicate and sampler results. The unfolded-tree clause uses finite unshared plain Nodes with maximum degree D and a representable feature count."
    status := .proven
    prop := ``mutate_feature_spec
    thm := some ``mutate_feature_spec_holds },
  { id := "mut-swap-operands"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["swap_operands"]
    statement := "When no operator has two children, swapping makes no draw or write. Otherwise, for the chosen Node or GraphNode object, swap exactly the two sampled child addresses and preserve its labels, all other cells, and the root. Degree two needs no second slot draw."
    preconditions := "The selected object has valid active child slots. The separate unfolded-tree clause is for unshared plain Nodes."
    status := .proven
    prop := ``swap_operands_spec
    thm := some ``swap_operands_spec_holds },
  { id := "mut-delete-random-op"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["delete_random_op!"]
    statement := "delete_random_op!(tree, rng) leaves a leaf root unchanged with no draw; otherwise the first draw selects the k-th operator node u in preorder (uniform over operator nodes), the second a child index j uniform in 1:degree(u), and the returned root unfolds to the input tree with u's subtree replaced by its j-th child, so the node count drops by size(u) - size(child j); when u is the root its child itself is returned and no object is written, otherwise the same root object is returned."
    preconditions := "Plain Node; finite alias-free tree (unfold succeeds, NoAlias); degrees <= D; every children tuple has at most D slots (NTuple{D}); arbitrary RNG stream."
    status := .proven
    prop := ``delete_random_op_spec
    thm := some ``delete_random_op_spec_holds },
  { id := "mut-append-random-op"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["append_random_op", "_sample_leaf", "make_random_leaf"]
    statement := "For the one-draw leaf fixture and an interior rounded bucket, append grows an unshared tree by the selected arity and returns the same root."
    preconditions := "Finite unshared plain Node, compatible representable operator and feature ranges, and a scaled Float64 draw strictly inside the cumulative total."
    status := .todo
    prop := ``append_random_op_spec
    thm := none
    notes := "Proved against an unfaithful model; needs re-proof of actual sampler effects, exact freshness by address and the ordered failure paths including the zero bucket." },
  { id := "mut-gen-fixed-size-exact"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["gen_random_tree_fixed_size", "_make_node", "_arity_picker", "make_random_leaf", "_sample_leaf"]
    statement := "The one-draw fixture reaches the requested size when a unary operator is available."
    preconditions := "Positive target, compatible feature range and operator table, with traversal and loop bounds at least the target."
    status := .todo
    prop := ``gen_fixed_size_exact
    thm := none
    notes := "Proved against an unfaithful model; needs exact size on normal return for the typed sampler and propagation of the UInt8 degree-conversion error." },
  { id := "mut-gen-fixed-size-realizable"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["gen_random_tree_fixed_size", "_arity_picker"]
    statement := "gen_random_tree_fixed_size(node_count, ...) returns a tree of exactly node_count nodes whenever some tree of that many nodes can be built from the available operator arities (node_count - 1 is a sum of arities with operators)."
    preconditions := "D = length(options.nops); at most 255 operators per degree; 1 <= nfeatures <= 65535; node_count >= 1; such a tree exists; traversal fuel and loop bound at least node_count."
    status := .refuted
    prop := ``gen_fixed_size_realizable
    thm := some ``gen_fixed_size_realizable_refuted
    notes := "Bug (greedy growth dead end): the loop picks arities by _arity_picker without checking that the remaining count stays reachable (src/MutationFunctions.jl:476-491); when it leaves a remainder that no operator arity can fill, _arity_picker returns 0 and the loop silently stops short. Example: Options(; operators=OperatorEnum(1 => (), 2 => (+,), 3 => (fma,))) has nops == (0, 1, 1); gen_random_tree_fixed_size(4, options, 1, Float64, rng) returns a 3-node tree (x + x) for about half of all seeds (94 of 200 Xoshiro seeds), although fma(x, x, x) has exactly 4 nodes. Population initialisation and randomize_tree therefore produce smaller trees than requested for such operator sets." },
  { id := "mut-arity-picker"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["_arity_picker"]
    statement := "With the stock Options operator counts, a zero total returns zero without drawing. For a positive total, one threshold draw selects the arity whose prefix first reaches the threshold, and that arity is available. The heap is unchanged."
    preconditions := "Any remaining::Int and RNG stream; nops is a tuple of actual operator-list lengths as built at src/Options.jl:1180, excluding hand-built signed nops."
    status := .proven
    prop := ``arity_picker_spec
    thm := some ``arity_picker_spec_holds },
  { id := "mut-arity-picker-weights"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["_arity_picker"]
    statement := "_arity_picker weights arities by operator count: among the total = sum(nops[1:limit]) equally likely values of thresh in 1:total, exactly nops[k] give arity k, for every k in 1:limit."
    preconditions := "limit <= D = length(nops); 1 <= k <= limit."
    status := .proven
    prop := ``arity_picker_weights
    thm := some ``arity_picker_weights_holds },
  { id := "mut-pick-degree-interval"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["append_random_op", "insert_random_op", "prepend_random_op"]
    statement := "The @nif degree choice of append_random_op, insert_random_op and prepend_random_op, for scaled_rand strictly between 0 and last(csum), picks the degree i in 1:D with csum[i] < scaled_rand <= csum[i + 1]; that degree has at least one operator."
    preconditions := "D = length(options.nops) >= 1; 0 < scaled_rand < sum(options.nops); exact arithmetic for scaled_rand (Float64 rounding of rand(rng) * total not modelled)."
    status := .proven
    prop := ``pick_degree_interval
    thm := some ``pick_degree_interval_holds },
  { id := "mut-pick-degree-has-operator"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["append_random_op", "insert_random_op", "prepend_random_op"]
    statement := "For every draw rand(rng) in [0, 1), the degree chosen by append_random_op, insert_random_op and prepend_random_op (scaled_rand = rand(rng) * last(csum), then the first i with scaled_rand > csum[i] && scaled_rand <= csum[i + 1], else D) has at least one operator, whenever some operator exists."
    preconditions := "D = length(options.nops) >= 1; sum(options.nops) > 0; rand(rng) in [0, 1)."
    status := .refuted
    prop := ``pick_degree_has_operator
    thm := some ``pick_degree_has_operator_refuted
    notes := "Bug (boundary off-by-one): rand(rng) can return 0.0 (Xoshiro gives (rand(UInt64) >>> 11) * 2^-53, zero once in 2^53 draws); then scaled_rand = 0 fails scaled_rand > csum[1] = 0 and every later test, and Base.Cartesian.@nif evaluates its last branch, degree D, unconditionally (src/MutationFunctions.jl:235-244, 276-291, 323-338). If degree D has no operator, rand(rng, 1:options.nops[D]) = rand(rng, 1:0) throws. Example: Options(binary_operators=[], unary_operators=[cos]) has nops == (1, 0); with an RNG whose rand(rng) is 0.0, append_random_op(Node(Float64; feature=1), options, 1, rng) throws ArgumentError: collection must be non-empty (insert_random_op and prepend_random_op too); expected cos(x1). Fix: test scaled_rand >= csum[i] for i == 1, or draw scaled_rand from (0, total]." },
  { id := "mut-expr-wrappers"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["get_contents_for_mutation", "with_contents_for_mutation", "get_nfeatures_for_mutation"]
    statement := "On a plain Expression, the hooks return the original node object, context nothing and the supplied signed feature count without drawing. Successful delegation returns the delegated node object and state with the original metadata; a delegated error propagates."
    preconditions := "Stock Expression hooks; arbitrary node mutation and RNG stream."
    status := .proven
    prop := ``expr_wrappers_spec
    thm := some ``expr_wrappers_spec_holds },
  { id := "mut-randomize-tree"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["randomize_tree"]
    statement := "The current equality checks independence of the old root argument and forwards a size draw to fixed-size generation in the fixture."
    preconditions := "Positive size bound; one-draw fixture for sample_value."
    status := .todo
    prop := ``randomize_tree_spec
    thm := none
    notes := "Need freedom from aliasing with the entire old heap and exact error forwarding for typed generation and an empty size range." },
  { id := "mut-insert-random-op"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["insert_random_op"]
    statement := "For the one-draw leaf fixture and an interior rounded bucket, insertion carries the sampled subtree by value and grows an unshared tree by the selected arity."
    preconditions := "Finite unshared plain Node with representable labels and compatible ranges, interior scaled Float64 draw, and identity copying of scalar values."
    status := .todo
    prop := ``insert_random_op_spec
    thm := none
    notes := "Proved against an unfaithful model; needs re-proof for address and mutable-payload copy semantics plus the ordered zero, sampler and constructor failures." },
  { id := "mut-prepend-random-op"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["prepend_random_op"]
    statement := "For the one-draw leaf fixture and an interior rounded bucket, prepend returns a new root, preserves old cells and grows an unshared tree by the selected arity."
    preconditions := "Finite unshared plain Node, compatible representable ranges, and an interior scaled Float64 draw."
    status := .todo
    prop := ``prepend_random_op_spec
    thm := none
    notes := "Proved against an unfaithful model; needs the actual carry address and ordered failures, including the zero bucket and typed sampler errors." },
  { id := "mut-make-node"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["_make_node"]
    statement := "The one-draw fixture allocates the selected arity of fresh leaves before a fresh operator root."
    preconditions := "Fixture only, with a compatible nonempty operator range and representable feature range."
    status := .todo
    prop := ``make_node_spec
    thm := none
    notes := "Proved against an unfaithful model; needs typed sampler effects, generated fallback and UInt8 degree conversion after the child draws." },
  { id := "mut-make-random-leaf"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["make_random_leaf"]
    statement := "The constant branch uses the installed sampler after the Boolean draw, keeps its final RNG state, and allocates one fresh constant leaf, or propagates the sampler error. Nonpositive counts cause an empty-range error only on the feature branch."
    preconditions := "Stock DynamicExpressions Node or GraphNode constructor; typed sampler action for the constant type. The one-draw fixture covers uniform feature outcomes when the feature count fits UInt16."
    status := .proven
    prop := ``make_random_leaf_spec
    thm := some ``make_random_leaf_spec_holds },
  { id := "mut-sample-leaf"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["_sample_leaf"]
    statement := "_sample_leaf(rng, tree) on a finite plain Node tree always finds a leaf, leaves the heap unchanged, consumes one draw and returns the object of the k-th leaf in preorder, k the index draw over the preorder indices of the leaves (uniform over leaves)."
    preconditions := "Plain Node; finite tree (unfold succeeds); arbitrary RNG stream."
    status := .proven
    prop := ``sample_leaf_spec
    thm := some ``sample_leaf_spec_holds },
  { id := "mut-random-node"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["random_node"]
    statement := "random_node(tree, rng) on a finite plain Node tree leaves the heap unchanged, consumes one draw and returns the object at preorder index j, j the index draw in 0:(length(tree) - 1) (uniform over all nodes); for any filter, a returned node is reachable from the root and passes the filter."
    preconditions := "Plain Node; finite tree (unfold succeeds); arbitrary filter of the heap and node; arbitrary RNG stream."
    status := .todo
    prop := ``random_node_spec
    thm := none
    notes := "Proved against an unfaithful model; add depwarn and both effectful filter traversals, then prove exact selection, fallback and error ordering." },
  { id := "mut-mutate-value"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["mutate_value", "mutate_factor"]
    statement := "mutate_value(rng, val, temperature, m) returns val * mutate_factor(typeof(val), temperature, m, rng), consuming exactly the three draws of mutate_factor; the factor's magnitude lies in [1/maxChange, maxChange] with maxChange = m.perturbation_factor * temperature + 1.1, and the factor is negative exactly when the sign draw exceeds the Float64 result of 1 - m.probability_flip_sign."
    preconditions := "perturbation_factor >= 0, temperature >= 0; the power T(maxChange^r) lies in [1, maxChange] for r in [0, 1) (exact real powers; Float rounding not modelled); the exponent draw rand(rng, T) in [0, 1); val * factor an arbitrary function."
    status := .todo
    prop := ``mutate_value_spec
    thm := none
    notes := "Proved against an unfaithful model; bind Julia promotion, power, reciprocal and negation in order and separate finite, nonfinite and complex outcomes." },
  { id := "mut-gen-random-tree"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["gen_random_tree"]
    statement := "With interior rounded degree draws and the one-draw sampler fixture, the placeholder root is expanded once per iteration and the result has the corresponding operator count and size."
    preconditions := "Finite unshared plain Node with compatible feature and operator ranges, enough traversal fuel and interior scaled Float64 draws."
    status := .todo
    prop := ``gen_random_tree_spec
    thm := none
    notes := "Proved against an unfaithful model; needs signed-length coverage, the actual per-iteration degree witnesses and first failure propagation." },
  { id := "mut-gen-random-tree-length"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["gen_random_tree"]
    statement := "For valid draws, gen_random_tree succeeds, appends one operator per step, and returns one node plus the sum of selected arities."
    preconditions := "As mut-gen-random-tree, with all real draws in [0, 1)."
    status := .refuted
    prop := ``gen_random_tree_length
    thm := some ``gen_random_tree_length_refuted
    notes := "With unary operators only, a zero draw picks the empty binary arity and throws before the first append." },
  { id := "mut-get-two-nodes"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["get_two_nodes_without_loop"]
    statement := "A nonpositive attempt limit returns the root fallback without drawing. A positive limit on a leaf throws. On a well-formed branch, choose the first sampled reachable pair whose child is non-root and cannot reach the sampled branch, or exhaust the limit if every sampled pair would form a loop. Each attempt consumes two selection draws and the heap is unchanged."
    preconditions := "Finite Node or GraphNode trees. Tree.WF is required for the successful branch guarantee; the no-draw and leaf cases do not require valid operator or feature indices."
    status := .proven
    prop := ``get_two_nodes_spec
    thm := some ``get_two_nodes_spec_holds },
  { id := "mut-form-connection-acyclic"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["form_random_connection!", "get_two_nodes_without_loop"]
    statement := "Connection formation returns the original root and leaves the reachable graph acyclic and finite. Below five counted nodes or on exhaustion the heap is unchanged; otherwise only the sampled parent's sampled child slot is assigned the sampled child."
    preconditions := "Node or GraphNode; finite tree (unfold succeeds); Tree.WF with degrees <= D, operators <= 255, features in 1:65535; every children tuple has at most D slots (NTuple{D}); default max_attempts = 10; arbitrary RNG stream."
    status := .proven
    prop := ``form_random_connection_acyclic
    thm := some ``form_random_connection_acyclic_holds },
  { id := "mut-break-connection"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["break_random_connection!"]
    statement := "Breaking a connection returns the same root and leaves a leaf unchanged. A successful branch call redirects one reachable slot to a fresh root whose unfolded subtree has the old child's size and depth."
    preconditions := "Finite acyclic Node or GraphNode with representable fields and valid child slots. Value-copy dispatch is supplied for the node's scalar type."
    status := .todo
    prop := ``break_random_connection_spec
    thm := none,
    notes := "The identity value-copy case has a fresh-root frame proof for well-formed labels; generalize that proof to zero labels and to the installed stateful copy_value traversal, including internal sharing." },
  { id := "mut-backsolve-rewrite"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["backsolve_rewrite_random_node"]
    statement := "backsolve_rewrite_random_node(tree, dataset, options, rng) on an alias-free Node tree whose root is an operator returns the same root object; its draw selects the node x at preorder index k != 0, uniformly over the non-root nodes. With fewer than min(10, length(targets)) valid inverted rows or a budget curmaxsize - (complexity(tree) - complexity(x)) below 1 the heap is unchanged; otherwise fit_sparse_expression is called with max_complexity = budget, and if it returns nothing only its new objects are added, while if it returns a node unfolding to u (made of new objects and objects of x's subtree) the root unfolds to the input tree with the subtree at k replaced by u."
    preconditions := "Plain Node, T a float type; finite alias-free tree (unfold succeeds, NoAlias); degrees <= D; every children tuple has at most D slots (NTuple{D}); root of nonzero degree (a leaf root is returned unchanged by the code); eval_inverse_tree_array_masked, compute_complexity and fit_sparse_expression arbitrary functions of the heap, compute_complexity total and the fit only allocating; arbitrary RNG stream."
    status := .todo
    prop := ``backsolve_spec
    thm := none
    notes := "Proved against an unfaithful model; bind the real inversion and fit with the old subtree and invalid-row mask, and compute the cap on the final spliced tree." },
  { id := "mut-rotate-graph-acyclic"
    juliaFile := "src/MutationFunctions.jl"
    juliaFns := ["randomly_rotate_tree!", "_valid_rotation_root"]
    statement := "randomly_rotate_tree!(tree, rng) on a finite acyclic GraphNode tree (shared subtrees allowed, as form_random_connection! creates) returns a root from which the node graph is still acyclic."
    preconditions := "GraphNode (preserve_sharing = true); finite acyclic input (unfold succeeds); degrees <= D; arbitrary RNG stream."
    status := .refuted
    prop := ``rotate_graph_acyclic
    thm := some ``rotate_graph_acyclic_refuted
    notes := "Bug (graph mode): when the rotation root holds the pivot object in two slots, set_child!(root, grand_child, pivot_idx) replaces only one of them and set_child!(pivot, root, grand_child_idx) then closes the cycle pivot -> root -> pivot (src/MutationFunctions.jl:643-648). Example: x = GraphNode(Float64; feature=1); p = GraphNode(1, x); tree = GraphNode(1, p, p) (sin(x1) + sin(x1) with one shared sin node): randomly_rotate_tree!(tree, rng) returns p with p.l === tree while tree still holds p in its other slot, for every seed, an infinite expression; expected an acyclic tree. rotate_tree has the largest default mutation weight (4.26) and form_connection (0.5) creates exactly such shared children in graph mode." }
]

end SymReg.Mutations
