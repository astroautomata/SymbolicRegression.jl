import SymReg.Backsolve.Inverse
import SymReg.Backsolve.EvalInverse
import SymReg.Backsolve.Fit
import SymReg.Backsolve.Library
import DynExpr.Registry.Types

/-!
Backsolve at SR upstream/master edbe678e: `src/InverseFunctions.jl`, `src/EvaluateInverse.jl`,
`src/Backsolve.jl`. Scalars are DE's `JF` (exact rationals, `NaN`, `±Inf`) in the inverse
model and exact rationals in the numerical core, without rounding, overflow or signed zero.
Base/SpecialFunctions functions, `sqrt`, the Cholesky solve, `eval_tree_array`,
`compute_complexity` and `hash` are arbitrary functions with facts stated as hypotheses. The
callers `backsolve_rewrite_random_node` and `mutate!(..., ::BacksolveMutation, ...)` are
covered by `mut-backsolve-rewrite` and the MutateGen backsolve entries.
-/

namespace SymReg.Backsolve
open DynExpr DynExpr.Registry

/-- Whether `approx_inverse(f, Val(I), args)` exists depends only on the operator and the
position, never on the fixed argument values (dispatch on the type of `Fix1`/`Fix2`/`FitExcept`,
`src/InverseFunctions.jl:45-150`). -/
def inverseByType : Prop :=
  ∀ (L : Lib) (o : Op) (i : Nat) (a b : List JF),
    (approxInv L (route o i a)).isSome = (approxInv L (route o i b)).isSome

theorem inverseByType_holds : inverseByType := approxInv_route_isSome

def entries : List Entry := [
  { id := "inv-routing", juliaFile := "src/InverseFunctions.jl",
    juliaFns := ["approx_inverse", "FitExcept"],
    statement := "Unary routing passes the operator through. For valid binary slots and for every arity of three or more, the routed function calls the original operator with exactly slot I replaced.",
    preconditions := "args has the operator's arity and 1 <= I <= arity.",
    status := .proven, prop := ``routing, thm := some ``routing_holds },
  { id := "inv-dispatch-type", juliaFile := "src/InverseFunctions.jl",
    juliaFns := ["approx_inverse"],
    statement := "For SR's explicit methods, inverse availability is independent of fixed values at fixed argument types. Delegated lookup retains the returned inverse or NoInverse, or propagates the lookup exception."
    preconditions := "Legal positions and argument tuples; fixed argument types for the explicit method comparison."
    status := .todo, prop := ``inverseByType
    notes := "The explicit overload proof is available. The delegated lookup still needs a value-sensitive effectful result, plus re-proof of row masking when availability varies across rows." },
  { id := "inv-exact-right", juliaFile := "src/InverseFunctions.jl",
    juliaFns := ["approx_inverse"],
    statement := "For neg, inv, Fix1/Fix2 of +, -, * with a finite fixed argument and FitExcept of fma with finite arguments, approx_inverse exists and is a right inverse wherever it returns a finite value.",
    preconditions := "Finite target; exact arithmetic.",
    status := .proven, prop := ``exactRightInverse, thm := some ``exactRightInverse_holds },
  { id := "inv-guarded-right", juliaFile := "src/InverseFunctions.jl",
    juliaFns := ["approx_inverse"],
    statement := "Under exact-real library identities the guarded unary pairs recover the target. With floating arithmetic, rounding exp(y)-1 to -1 or underflowing an exponential to zero gives a finite inverse result that the corresponding forward safe logarithm rejects."
    preconditions := "Exact part uses the stated library identities. The floating part uses the selected IEEE precision and the exponential routine's returned value."
    status := .proven, prop := ``guardedInverseSpec, thm := some ``guardedInverseSpec_holds },
  { id := "inv-doc-local", juliaFile := "src/InverseFunctions.jl",
    juliaFns := ["approx_inverse"],
    statement := "Every operator the docstring describes as locally invertible, including its own example abs, has an approx_inverse that inverts it on [0, eps].",
    preconditions := "None.", status := .refuted,
    prop := ``docLocalInverse, thm := some ``docLocalInverse_refuted,
    notes := "src/InverseFunctions.jl:16-18 says abs has approx_inverse abs, but line 114 returns nothing: approx_inverse(abs) === nothing." },
  { id := "inv-pow-complete", juliaFile := "src/InverseFunctions.jl",
    juliaFns := ["approx_inverse"],
    statement := "approx_inverse(Fix2(safe_pow, a)) returns a finite value on every finite value safe_pow(x, a) attains.",
    preconditions := "Finite a != 0, finite x with safe_pow(x, a) finite; library ^ finite on positive bases.",
    status := .refuted, prop := ``powInverseComplete, thm := some ``powInverseComplete_refuted,
    notes := "src/InverseFunctions.jl:139: safe_pow(-2.0, 3.0) = -8.0 but approx_inverse(Fix2(safe_pow, 3.0))(-8.0) = safe_pow(-8.0, 1/3) = NaN instead of -2.0, so such rows are always masked out." },
  { id := "einv-masked-row-spec", juliaFile := "src/EvaluateInverse.jl",
    juliaFns := ["eval_inverse_tree_array", "eval_inverse_tree_array_masked", "_eval_inverse_tree_array",
      "_eval_inverse_tree_array_masked", "inner_dispatch_degn_masked", "dispatch_degn_masked", "degn_invert!",
      "ResultOk", "ResultMasked", "_masked_eval_context", "_masked_eval_kws", "_reset_eval_buffer!"],
    statement := "On normal return, masked inversion marks row r valid exactly when the target, every inverse step from the root to the node and every sibling value on the path are finite at r (with invertible operators), and returns the inverted value at valid rows. The unmasked wrapper returns the same values with all(valid).",
    preconditions := "Plain Node of degree <= 2, early_exit=false evaluation; y has one entry per sample.",
    status := .proven, prop := ``maskedRowSpec, thm := some ``maskedRowSpec_holds },
  { id := "einv-structural-failure", juliaFile := "src/EvaluateInverse.jl",
    juliaFns := ["eval_inverse_tree_array_masked"],
    statement := "On normal return, an absent node or a missing inverse on its path yields an all-false mask. An earlier sibling evaluation or inversion may throw.",
    preconditions := "As einv-masked-row-spec.",
    status := .proven, prop := ``structuralFailure, thm := some ``structuralFailure_holds },
  { id := "einv-right-inverse-reproduces", juliaFile := "src/EvaluateInverse.jl",
    juliaFns := ["eval_inverse_tree_array_masked"],
    statement := "With operators whose inverses are right inverses wherever finite, replacing the node by a valid row's inverted value reproduces the target at that row.",
    preconditions := "Well-formed tree; RightInvOps hypothesis (witnessed by the empty operator set).",
    status := .proven, prop := ``rightInverseReproduces, thm := some ``rightInverseReproduces_holds },
  { id := "einv-mask-sound", juliaFile := "src/EvaluateInverse.jl",
    juliaFns := ["eval_inverse_tree_array_masked", "dispatch_degn_masked"],
    statement := "With SR's own operators, every row the mask marks valid is reproduced by the rewritten tree.",
    preconditions := "Well-formed tree, one target per sample.", status := .refuted,
    prop := ``maskSound, thm := some ``maskSound_refuted,
    notes := "Fix2(/, 0) inverts y to y*0 = 0, which is finite: for x1/x2 with x1=1, x2=0, y=3 the row is valid with value 0, but 0/0 = NaN, not 3." },
  { id := "einv-no-throw", juliaFile := "src/EvaluateInverse.jl",
    juliaFns := ["eval_inverse_tree_array_masked", "degn_invert!"],
    statement := "On finite data the masked inversion never throws: rows leaving an inverse's domain are marked invalid instead of failing.",
    preconditions := "Finite data and targets; library throws only for sin/cos/tan of an infinity (confirmed in Julia).",
    status := .refuted, prop := ``maskedNoThrow, thm := some ``maskedNoThrow_refuted,
    notes := "degn_invert! applies the next inverse to every row, masked or not: 1/atan(x1) with X=[2 3], y=[0,1] makes row 1 Inf, then tan(Inf) throws DomainError instead of returning a mask." },
  { id := "bs-configured", juliaFile := "src/Backsolve.jl", juliaFns := ["configured_backsolve"],
    statement := "configured_backsolve returns the first BacksolveMutation with positive weight and throws ArgumentError exactly when there is none.",
    preconditions := "None; options.mutations arbitrary.",
    status := .proven, prop := ``configuredSpec, thm := some ``configuredSpec_holds },
  { id := "bs-solve-gram", juliaFile := "src/Backsolve.jl", juliaFns := ["_solve_gram"],
    statement := "For the normalized Hermitian system and three ordered ridges, return the first successful solve, retry after PosDefException only, and return zeros only if all four attempts fail that way. For Hermitian G with nonzero column norms and an exact unridged solve, the rescaled result solves G z = g."
    preconditions := "Compatible matrix/vector dimensions for the normal-equation guarantee."
    status := .todo, prop := ``solveGramSpec
    notes := "Need the upper-triangle Hermitian view and a solver that distinguishes PosDefException from propagating errors, then prove the ordered outcomes and reuse normal_eq." },
  { id := "bs-stlsq", juliaFile := "src/Backsolve.jl", juliaFns := ["stlsq", "_stlsq_gram"],
    statement := "Return zeros and false for a target-length mismatch. Otherwise form conjugate Gram products, apply the reached refits until threshold selection stabilizes or the loop stops, and derive the returned coefficients and success from that actual run."
    preconditions := "Supported real and complex floating-point scalar types."
    status := .todo, prop := ``stlsqFit
    notes := "Need complex conjugate products, real-component epsilon and precision, and the actual refit sequence rather than an existential prior estimate." },
  { id := "bs-greedy-budget", juliaFile := "src/Backsolve.jl", juliaFns := ["greedy_forward_selection_gram"],
    statement := "The accepted sequence uses distinct eligible columns, fits the budget and term limit, and takes the best eligible affordable positive-correlation candidate when its refit passes the improvement test."
    preconditions := "Supported floating scalar types; a missing indexed cost raises BoundsError rather than costing zero."
    status := .todo, prop := ``greedyBudget
    notes := "Need typed epsilon and checked term_costs indexing, then relate the reached accepted sequence to the first improving candidate at each step." },
  { id := "bs-greedy-monotone", juliaFile := "src/Backsolve.jl", juliaFns := ["greedy_forward_selection_gram"],
    statement := "For the best eligible candidate at every reached step, accept exactly when its computed trial meets min_improvement using Julia's denominator rule. At a positive threshold the accepted computed norms strictly decrease."
    preconditions := "The loop reaches the step; the norm and improvement are computed in the real component type."
    status := .todo, prop := ``greedyMonotone
    notes := "Need a recorded trial at every reached step, including rejection, and a strict-decrease proof for the rounded denominator and subtraction." },
  { id := "bs-greedy-scale", juliaFile := "src/Backsolve.jl", juliaFns := ["greedy_forward_selection_gram"],
    statement := "Greedy selection is invariant to the scale of y: scaling y by s > 0 scales the coefficients by s and keeps success.",
    preconditions := "sqrt exact on squares, exact solver, s > 0.", status := .refuted,
    prop := ``greedyScaleInvariant, thm := some ``greedyScaleInvariant_refuted,
    notes := "src/Backsolve.jl:264 uses the absolute test abs(c) > 100 eps: G=[1;;], g=[eps()], yy=eps()^2 returns ([eps()], false) while g=[1] gives ([1], true); fit_sparse_expression fits 2 x1 but returns nothing for 2e-15 x1." },
  { id := "bs-weighted-sum-costs", juliaFile := "src/Backsolve.jl",
    juliaFns := ["weighted_sum_costs", "combine_trees_weighted_sum"],
    statement := "With integer-additive complexity, the combined tree's complexity is the active terms' costs minus overhead for unit coefficients plus one join per extra term. Fractional mappings round probes separately from the final tree; out-of-range active indices raise BoundsError."
    preconditions := "The integer identity uses in-range active indices."
    status := .todo, prop := ``weightedSumCostsExact
    notes := "Checked active gathering and the additive complexity identity are proved. Need to bind the floating ComplexityMapping tree fold and ties-to-even Int conversion separately for each probe and the final tree." },
  { id := "bs-combine-none", juliaFile := "src/Backsolve.jl",
    juliaFns := ["combine_trees_weighted_sum", "_has_weighted_sum_operators"],
    statement := "The weighted sum returns nothing exactly when a required operator is absent or no coefficient exceeds 100 times the real component type's epsilon in magnitude. With both operators, an out-of-range active index raises BoundsError."
    preconditions := "Supported real and complex floating scalar types."
    status := .proven, prop := ``combineNone, thm := some ``combineNone_holds },
  { id := "bs-basis-library", juliaFile := "src/Backsolve.jl",
    juliaFns := ["build_basis_library", "_build_basis_library", "BasisLibrary"],
    statement := "The basis library checks its size guard, evaluates candidates in order, and keeps each finite complete column unless the current hash entry points at an equal column. It propagates evaluation errors."
    preconditions := "Ordinary basis-library candidates and evaluator."
    status := .proven, prop := ``basisLibrary, thm := some ``basisLibrary_holds },
  { id := "bs-fit-guards", juliaFile := "src/Backsolve.jl",
    juliaFns := ["fit_sparse_expression", "_has_weighted_sum_operators"],
    statement := "An omitted backsolve keyword with no enabled mutation raises ArgumentError before either early exit. On body entry the operator and row-count guards return nothing. After selection and combination, a candidate over budget is rejected without evaluation. Otherwise evaluation errors propagate and the candidate is returned exactly when evaluation completes with finite values."
    preconditions := "The final return rule starts from the candidate actually produced by selection and combination."
    status := .proven, prop := ``fitGuardedCall, thm := some ``fitGuardedCall_holds },
  { id := "bs-fit-setup", juliaFile := "src/Backsolve.jl",
    juliaFns := ["fit_sparse_expression", "prepare_backsolve_setup", "BacksolveSetup"],
    statement := "With unchanged inputs and the default top_k, cached and fresh fits return structurally equal results. A retained basis term in a fitted result uses the original setup object, so edits through that reference can make cached columns and costs stale."
    preconditions := "Setup built by prepare_backsolve_setup with the corresponding inputs and max_library_size."
    status := .todo, prop := ``fitSetupTransparent
    notes := "The pure structural equality is proved. Need heap object identities through library retention and combination to establish the edit and subsequent reuse behavior." }
]

end SymReg.Backsolve
