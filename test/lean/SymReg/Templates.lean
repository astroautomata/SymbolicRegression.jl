import SymReg.Templates.Structure
import SymReg.Templates.ConstantsProps
import SymReg.Templates.Composable
import SymReg.Templates.Template
import SymReg.Templates.TemplateOps
import SymReg.Templates.TemplateMut
import SymReg.Templates.TemplateInit
import SymReg.Templates.Builder
import SymReg.Templates.Macro
import DynExpr.Registry.Types

/-!
Templates slice: `src/TemplateExpression.jl`, `src/TemplateExpressionMacro.jl`,
`src/ComposableExpression.jl`, `src/ExpressionBuilder.jl`, `src/ExpressionSpec.jl`,
SymbolicRegression.jl `upstream/master` daae84e5.
-/

namespace SymReg.Templates
open DynExpr.Registry

/-- Shorthand for a proven entry. -/
def pe (id file : String) (fns : List String) (st pre : String) (p t : Lean.Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement := st, preconditions := pre,
    status := .proven, prop := p, thm := some t }

/-- Shorthand for a refuted entry. -/
def re (id file : String) (fns : List String) (st pre notes : String) (p t : Lean.Name) : Entry :=
  { id, juliaFile := file, juliaFns := fns, statement := st, preconditions := pre,
    status := .refuted, prop := p, thm := some t, notes }

def TE := "src/TemplateExpression.jl"
def CE := "src/ComposableExpression.jl"
def EB := "src/ExpressionBuilder.jl"

def entries : List Entry := [
  pe "tmpl-structure-checks" TE ["TemplateStructure"]
    "TemplateStructure construction fails before inference on overlapping names, missing parameter counts, or parameter-count keys differing from Kp."
    "None." ``structureChecks ``structureChecks_holds,
  pe "tmpl-structure-explicit" TE ["TemplateStructure"]
    "Explicit num_features override the deprecated positional argument, the combiner is never run, and counts are stored in key order."
    "Disjoint keys; num_parameters present when Kp nonempty; matching key sets." ``structureExplicit ``structureExplicit_holds,
  pe "tmpl-infer-spec" TE ["infer_variable_constraints", "_record_composable_expression!", "ArgumentRecorder", "check_combiner_applicability"]
    "If combine accepts the dummy arguments, calls only template keys each with one fixed arity and returns, the inferred counts are exactly those arities in key order."
    "Applicable combiner with a consistent call trace covering every key." ``inferSpec ``inferSpec_holds,
  pe "tmpl-infer-inconsistent" TE ["infer_variable_constraints", "_record_composable_expression!"]
    "A key called with two different argument counts makes inference throw." "Applicable combiner." ``inferInconsistent ``inferInconsistent_holds,
  pe "tmpl-infer-uncalled" TE ["infer_variable_constraints"]
    "A key never called by the combiner makes inference throw instead of defaulting its count." "None." ``inferUncalled ``inferUncalled_holds,
  pe "tmpl-infer-not-applicable" TE ["check_combiner_applicability", "infer_variable_constraints"]
    "A combiner not applicable to the dummy arguments is rejected with an ArgumentError before being called." "None." ``inferNotApplicable ``inferNotApplicable_holds,
  pe "tmpl-structure-inferred" TE ["TemplateStructure", "infer_variable_constraints", "has_params", "combine"]
    "Construction without explicit counts stores exactly the inferred arities." "As tmpl-infer-spec plus valid key sets." ``structureInferred ``structureInferred_holds,
  { id := "tmpl-get-set", juliaFile := TE, juliaFns := ["get_scalar_constants", "set_scalar_constants!", "_pack_parameters", "_unpack_parameters!"],
    statement := "Getter packs inner constants and each parameter vector in key order. Reapplying a saved scalar vector after value-only edits restores each recorded node and active parameter array, including aliases.",
    preconditions := "Same writable layout and a fixed-width codec that restores the original values from their encodings.",
    status := .todo, prop := ``templateGetSet, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof using the packed layout and restoration through aliased backing arrays." },
  { id := "tmpl-set-get", juliaFile := TE, juliaFns := ["get_scalar_constants", "set_scalar_constants!"],
    statement := "A vector at least as long as the getter's can be written, and the next getter returns its first packed-width scalars with the same refs.",
    preconditions := "Distinct writable node and parameter addresses; fixed-width reversible packing.",
    status := .todo, prop := ``templateSetGet, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof of address-frame and post-write re-packing." },
  { id := "tmpl-set-short", juliaFile := TE, juliaFns := ["set_scalar_constants!"],
    statement := "A scalar vector shorter than the actual packed width makes the setter throw; earlier writes may persist.",
    preconditions := "Successful getter with fixed-width packing and bounds-checking unpacking as specified by the codec.",
    status := .todo, prop := ``templateSetShort, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof of cursor growth up to the first failed slice or unpack." },
  re "tmpl-set-mismatch-atomic" TE ["set_scalar_constants!"]
    "A length-mismatched constants vector throws and leaves the template unchanged." "Successful getter."
    "Lean witness: inner constant 2.0, p=[5.0,7.0], setting [1.0,2.0] writes 1.0 and p[1]=2.0 before the BoundsError. Julia: inner 2.0, 3.0, p=[5.0,7.0], setting [1.0,2.0,3.0] leaves [1.0,2.0,3.0,7.0]."
    ``templateSetMismatchAtomic ``templateSetMismatchAtomic_refuted,
  pe "tmpl-opt-set-length" TE ["set_optimizable_parameters!", "TemplateOptimizableRefs"]
    "set_optimizable_parameters! checks the length first: a mismatched vector throws DimensionMismatch before any write." "Successful getter." ``optSetLength ``optSetLength_holds,
  { id := "tmpl-opt-roundtrip", juliaFile := TE, juliaFns := ["get_optimizable_parameters", "set_optimizable_parameters!"],
    statement := "The default optimizer restores its own values even through shared storage, and distinct writable addresses read back any matching-length replacement scalar vector.",
    preconditions := "Successful getter and fixed-width reversible packing; distinct node and parameter addresses for arbitrary replacements.",
    status := .todo, prop := ``optRoundtrip, thm := none,
    notes := "Proved against an unfaithful model; needs packing, restoration and readback lemmas for the addressed parameter store." },
  pe "tmpl-composable-roundtrip" CE ["get_scalar_constants", "set_scalar_constants!", "get_optimizable_parameters", "set_optimizable_parameters!"]
    "Composable constants round-trip, and a mismatched length throws DimensionMismatch before any write." "Successful getter; distinct refs for arbitrary vectors." ``composableRoundtrip ``composableRoundtrip_holds,
  pe "tmpl-vv-apply" CE ["apply_operator", "_apply_operator", "_apply_operator_values", "_match_eltype", "_is_valid", "_get_value", "ValidVector", "ValidVectorMixError"]
    "ValidVector operators: all-valid operands give the broadcast result, valid iff all values finite; an invalid operand skips evaluation and returns the first ValidVector's data marked invalid; mixing with a plain vector throws."
    "None." ``applyValidity ``applyValidity_holds,
  pe "tmpl-vv-nan" CE ["(ex::AbstractComposableExpression)(x::AbstractVector...)", "nan"]
    "An incomplete evaluation under a vector call yields only NaNs." "None." ``vectorCallNaN ``vectorCallNaN_holds,
  pe "tmpl-vv-mixed" CE ["(ex::AbstractComposableExpression)(x::Union{ValidVector,Number}...)"]
    "Mixed calls fill numbers to the first ValidVector's length, short-circuit on invalid operands, and otherwise evaluate the stacked rows." "Some ValidVector operand." ``mixedCall ``mixedCall_holds,
  re "tmpl-composable-scalar-call" CE ["(ex::AbstractComposableExpression)(x::Number...)"]
    "The scalar call returns the one-sample vector call's value." "Default EvalContext."
    "f = -(inv(x1)): f(0.0) returns Inf (the incomplete value) while f([0.0]) returns [NaN]."
    ``scalarCallAgrees ``scalarCallAgrees_refuted,
  pe "tmpl-composable-zero-arg" CE ["(ex::AbstractComposableExpression{T})()"]
    "Zero-argument calls fail the typed input check when a feature is read, else return the value or NaN if incomplete." "OperatorEnum operators." ``zeroArgCall ``zeroArgCall_holds,
  pe "tmpl-composable-arity" CE ["(ex::AbstractComposableExpression)(x::Union{ValidVector,Number}...)", "get_eval_context"]
    "A ValidVector call with fewer rows than the largest feature fails DE's input assertion before evaluation." "Valid, equal-length operands." ``arityChecks ``arityChecks_holds,
  { id := "tmpl-compose-denote", juliaFile := CE, juliaFns := ["(ex::AbstractComposableExpression)(x::AbstractComposableExpression...)"],
    statement := "Same-element-type composition preserves outer metadata and substitutes the argument contents. Denotation uses the outer enum throughout, or alternate enums giving the same argument denotations.",
    preconditions := "At least one argument and successful same-element-type composition; denotation assumes a stored outer enum.",
    status := .todo, prop := ``composeDenote, thm := none,
    notes := "The same-element-type proof omits mixed grafts, which may convert constants to the destination field type." },
  { id := "tmpl-compose-bounds", juliaFile := CE, juliaFns := ["(ex::AbstractComposableExpression)(x::AbstractComposableExpression...)"],
    statement := "Same-element-type composition with too few arguments throws BoundsError; successful compositions retain outer metadata.",
    preconditions := "One or more same-element-type composable arguments.",
    status := .todo, prop := ``composeBounds, thm := none,
    notes := "Model fallible mixed-type grafts in traversal order, including conversion errors before the first missing feature." },
  pe "tmpl-ctor-keys" TE ["TemplateExpression"]
    "The constructor stores trees only in the structure's exact key order; any other order, including a permutation, fails the assertion." "Successful parameter construction." ``ctorKeys ``ctorKeys_holds,
  pe "tmpl-ctor-params" TE ["TemplateExpression", "has_params"]
    "Parameters: unknown names rejected, vectors stored in num_parameters order as given or zero-filled, wrong lengths rejected, and parameter-free structures accept only absent/empty parameters." "None." ``ctorParams ``ctorParams_holds,
  pe "tmpl-get-tree" TE ["get_tree"]
    "get_tree succeeds for every nonempty parameter-free template whose combiner succeeds on sum(num_features) variables."
    "No parameters; at least one component expression." ``getTreeTotal ``getTreeTotal_holds,
  pe "tmpl-invalid-vars" TE ["has_invalid_variables", "contains_features_greater_than"]
    "has_invalid_variables holds exactly when an inner expression reads a feature beyond its key's num_features." "Nonnegative num_features." ``invalidVars ``invalidVars_holds,
  pe "tmpl-eval-contract" TE ["eval_tree_array", "(ex::TemplateExpression)(X)", "TemplateReturnError", "_match_input_eltype"]
    "Invalid variables give (nothing, false); otherwise the combiner receives the parameters and valid row copies, its ValidVector is returned and the call yields x iff valid; a non-ValidVector throws TemplateReturnError." "None." ``evalContract ``evalContract_holds,
  pe "tmpl-eval-identity" TE ["eval_tree_array", "combine"]
    "A one-input identity template evaluates exactly like its inner composable expression." "Inner reads at most x1; one data row." ``evalIdentity ``evalIdentity_holds,
  pe "tmpl-complexity-sum" TE ["compute_complexity"]
    "A template's complexity is the sum of its inner complexities, independent of parameters and combiner." "At least one key; inner complexities succeed." ``complexitySum ``complexitySum_holds,
  re "tmpl-complexity-custom" TE ["compute_complexity"]
    "With a user complexity function, a template's complexity is that function's value on the template." "Function-valued complexity_mapping."
    "The function is only called on each inner expression: constant 7 on two keys gives 14; the reproducer's function never sees a TemplateExpression."
    ``complexityCustom ``complexityCustom_refuted,
  pe "tmpl-count-constants" TE ["count_scalar_constants", "has_constants"]
    "count_scalar_constants equals the length of the flat constants vector (inner constants then parameters)." "Plain unshared inner trees." ``countAgrees ``countAgrees_holds,
  pe "tmpl-copy-eq" TE ["copy", "==", "get_contents", "get_metadata"]
    "copy(ex) == ex exactly when no inner constant and no parameter is NaN (Julia == semantics)." "None." ``copyEq ``copyEq_holds,
  pe "tmpl-mutation-context" TE ["get_contents_for_mutation", "with_contents_for_mutation"]
    "Putting back the sampled inner expression restores the template; any replacement changes exactly that key." "Distinct keys; one inner per key." ``mutationContext ``mutationContext_holds,
  { id := "tmpl-mutation-valid", juliaFile := TE,
    juliaFns := ["get_nfeatures_for_mutation", "with_contents_for_mutation", "max_features"],
    statement := "Replacing the sampled inner with an expression whose features fit the key's signed count changes exactly that inner and leaves a valid template valid.",
    preconditions := "Valid template with distinct, aligned keys, inner expressions and feature counts.",
    status := .proven, prop := ``mutationReplacementValid, thm := some ``mutationReplacementValid_holds },
  re "tmpl-crossover-valid" TE ["crossover_trees", "_crossover_template_inners", "_template_crossover_child"]
    "Crossover of two valid templates gives valid children." "Valid parents."
    "Each parent samples its key independently: swapping g = x2 (2 features) into f (1 feature) gives an invalid child."
    ``crossoverValid ``crossoverValid_refuted,
  pe "tmpl-crossover-same-key" TE ["crossover_trees", "_template_crossover_child"]
    "Crossing the same key of two templates with one structure keeps both children valid." "Valid parents with equal structure." ``crossoverSameKey ``crossoverSameKey_holds,
  pe "tmpl-mutconst" TE ["mutate_constant", "has_constants", "condition_mutate_constant!"]
    "mutate_constant takes the inner branch without parameters, the parameter branch with parameters but no inner constants, and the parameter branch keeps structure, inners, lengths and untouched entries." "None." ``mutConst ``mutConst_holds,
  re "tmpl-mutconst-total" TE ["mutate_constant"]
    "mutate_constant succeeds on every template the constructor accepts." "Aligned parameter keys and counts, counts >= 0."
    "num_parameters=(p=0,) is accepted, then rand(rng, 1:0) throws ArgumentError."
    ``mutConstTotal ``mutConstTotal_refuted,
  pe "tmpl-param-init" TE ["_initialize_template_parameters", "extra_init_params"]
    "A parameter_initializer result must be a NamedTuple of vectors with num_parameters' key set; the result follows num_parameters order, takes vectors by key, and has the declared lengths." "None." ``initOrder ``initOrder_holds,
  { id := "tmpl-copy-into", juliaFile := TE, juliaFns := ["allocate_container", "copy_into!", "PreallocatedTemplateExpression"],
    statement := "With adequate distinct allocated tree slots and fresh equal-length parameter arrays in key order, copy_into! stores the source contents in those slots and arrays, returns references into them, and preserves storage outside them.",
    preconditions := "Containers allocated separately from the source, with enough tree slots and matching parameter lengths.",
    status := .todo, prop := ``copyIntoRoundtrip, thm := none,
    notes := "Need to lift DE's node preallocation correctness and frame lemmas over all inner trees, and prove the ordered parameter copy frame." },
  pe "tmpl-string" TE ["string_tree", "_colors", "_color_string", "_format_component", "_prefix_string_with_pipe"]
    "string_tree lists keys then parameter keys in order, each with its rendering; colours repeat with period 6." "One inner per key, one vector per parameter key." ``stringParts ``stringParts_holds,
  pe "tmpl-embed-strip" EB ["embed_metadata", "strip_metadata", "init_params", "extra_init_params", "sort_params", "consistency_checks"]
    "strip(embed(ex)) = strip(ex), embed(strip(ex)) = embed(ex), embed is idempotent, and embedding a created expression equals creating it embedded." "Distinct expression-option keys; prototype of the options' type." ``embedStrip ``embedStrip_holds,
  pe "tmpl-create-dispatch" EB ["create_expression", "get_operators", "consistency_checks"]
    "create_expression wraps values as constant nodes, returns expressions of the options' type unchanged (others fail the typeassert), and with the default spec stores only operators and variable names." "None." ``createDispatch ``createDispatch_holds,
  re "tmpl-create-independent" EB ["create_expression", "extra_init_params"]
    "Expressions created from the same options share no mutable metadata object." "None."
    "extra_init_params returns options.expression_options itself: every ParametricExpression created from one Options shares the parameters matrix."
    ``createIndependent ``createIndependent_refuted,
  pe "tmpl-member-roundtrip" EB ["embed_metadata", "strip_metadata"]
    "Stripping an embedded member gives the stripped expression with the same cost and loss under a fresh ref whose parent is the original; Population/HallOfFame/vector maps keep member counts." "Distinct option keys; tree of the options' type." ``memberRoundtrip ``memberRoundtrip_holds,
  pe "tmpl-create-shape" TE ["create_expression", "_build_inner_template_expressions", "extra_init_params", "sort_params", "make_example_inputs"]
    "A created template holds one copy of the seed tree per key, the options' operators in the template and every inner whether or not embedded, and metadata (structure, operators, variable_names, parameters) with names only when embedded." "TemplateExpressionSpec options." ``tmplCreateShape ``tmplCreateShape_holds,
  re "tmpl-embed-create" TE ["embed_metadata", "create_expression"]
    "Embedding a created template's metadata equals creating it with embedded metadata." "None."
    "embed_metadata only rewrites the template metadata, so inner variable_names stay nothing while create_expression(Val(true)) sets them to the dataset names."
    ``tmplEmbedCreate ``tmplEmbedCreate_refuted,
  pe "tmpl-spec-defaults" "src/ExpressionSpec.jl" ["ExpressionSpec", "get_expression_type", "get_expression_options", "get_node_type", "TemplateExpressionSpec"]
    "ExpressionSpec selects Expression on the chosen node type with empty options. TemplateExpressionSpec selects TemplateExpression on Node and returns exactly the structure, inner expression type, inner expression options, and initializer fields." "None." ``specDefaults ``specDefaults_holds,
  pe "tmpl-composable-buffer" CE ["ComposableExpression", "get_eval_context", "_with_call_time_buffer"]
    "The composable constructor never stores a buffer and rejects unknown keywords; template evaluation lends the call buffer to non-Bumper inners only." "None." ``composableBuffer ``composableBuffer_holds,
  pe "tmpl-macro-expand" "src/TemplateExpressionMacro.jl" ["@template_spec", "template_spec"]
    "@template_spec keys are the expressions in order, parameter keys the parameter names in order with num_parameters the parameters tuple, and num_features/prototype pass through." "Every parameters entry is name = size." ``macroExpand ``macroExpand_holds,
  pe "tmpl-macro-errors" "src/TemplateExpressionMacro.jl" ["template_spec"]
    "Repeated, unknown or positional arguments, missing or non-tuple expressions, bad parameter entries and non-do-block bodies are rejected." "None." ``macroErrors ``macroErrors_holds,
  pe "tmpl-parse-checks" TE ["parse_expression"]
    "Guesses with unknown names, missing expressions, or parameters given both flat and by keyword are rejected; without parameters a parse has none." "None." ``parseChecks ``parseChecks_holds,
  re "tmpl-parse-accepts" TE ["parse_expression"]
    "parse_expression accepts every guess supplying one expression string per key." "None."
    "Inner strings are parsed separately: (f=\"#1 + 1.0\", g=\"sin(#1)\") gives Node{Float64} and Node{Float32}, and the constructor throws MethodError."
    ``parseAccepts ``parseAccepts_refuted,
  pe "tmpl-parameter-key-order" TE ["get_parameter_keys"]
    "Constructed templates expose their declared parameter keys in declaration order." "Construction succeeds." ``parameterKeyOrder ``parameterKeyOrder_holds,
  pe "tmpl-variable-names-priority" TE ["get_variable_names"]
    "Explicit names override metadata names, and missing metadata yields no names." "None." ``templateNamesPriority ``templateNamesPriority_holds,
  pe "composable-variable-names-priority" "src/ComposableExpression.jl" ["get_variable_names"]
    "Explicit names bypass metadata property access, including when accessing that field would fail." "None." ``composableNamesPriority ``composableNamesPriority_holds,
  pe "composable-literal-pow-invalid" "src/ComposableExpression.jl" ["literal_pow"]
    "Literal power preserves invalidity, converts the payload when the inferred element type changes, and propagates conversion errors." "Invalid input vector; Base supplies inference and scalar conversion." ``literalPowInvalid ``literalPowInvalid_holds
]

end SymReg.Templates
