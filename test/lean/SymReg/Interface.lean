import SymReg.Interface.Evaluation
import SymReg.Interface.Rendering
import SymReg.Interface.Hooks
import DynExpr.Registry.Types

/-!
InterfaceDynamicExpressions.jl and InterfaceDataTypes.jl at SR upstream/master.
DE owns tree evaluation and rendering; this slice checks SR argument selection,
return normalization, IO delegation, aliases and extension-hook fallback dispatch.
Custom AbstractOptions operator selection, array conversions, Printf, unit text,
zero/randn and extension callbacks remain arbitrary services. JF/Scalar, EvalContext,
OpEnum, Expression, rendering and numeric mutation reuse existing DE/SR definitions.
There are no Dataset overloads in either target file: callers supply dataset.X and
variable_names=dataset.variable_names; no dataset methods are invented here.
-/
namespace SymReg.Interface
open DynExpr.Registry

def entries : List Entry := [
  { id := "ide-context-policy", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["takes_eval_context", "eval_tree_array"],
    statement := "Enums without context support receive no context. A context-aware enum retains the supplied context, or applies explicit turbo and bumper overrides when constructing a context."
    preconditions := "Resolved enum kind and Loss.Options projections; DE context model reused.",
    status := .proven, prop := ``contextPolicy, thm := some ``contextPolicy_holds },
  { id := "ide-deprecated-context", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["_process_eval_options", "_process_deprecated_eval_options"],
    statement := "The deprecated eval_options supplies a context exactly when eval_context is absent; supplying both raises the documented assertion.",
    preconditions := "Deprecation warnings are outside the value/error model.",
    status := .proven, prop := ``deprecatedPolicy, thm := some ``deprecatedPolicy_holds },
  { id := "ide-eval-forward", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_tree_array"],
    statement := "The evaluator receives the same tree, data, enum and residual keywords. Legacy context routes like modern context when given alone; two context values are rejected before evaluation.",
    preconditions := "Typed evaluator service includes Julia output type assertions; no explicit context supplied in this forwarding specialization.",
    status := .proven, prop := ``evalForwarding, thm := some ``evalForwarding_holds },
  { id := "ide-absent-output", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_tree_array"],
    statement := "The public evaluator returns (nothing, false) for an absent backend output with either Boolean completion flag."
    preconditions := "Typed backend completion flag. Covers no context, modern context alone, and legacy context alone."
    status := .proven, prop := ``absentOutput, thm := some ``absentOutput_holds },
  { id := "ide-derivative-forward", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_diff_tree_array", "differentiable_eval_tree_array"],
    statement := "Both derivative wrappers derive the expected array type before delegating with the actual get_tree result, original data and resolved enum. The directional wrapper preserves the index. Failed expected-type lookup prevents delegation."
    preconditions := "Dispatcher services model get_tree and get_operators for the input representation; backend replies use the expected array type and a Boolean completion flag."
    status := .proven, prop := ``derivativeForwarding, thm := some ``derivativeForwarding_holds },
  { id := "ide-gradient-forward", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_grad_tree_array"],
    statement := "Gradient evaluation forwards the given tree, matrix, operator enum and keywords. It preserves the primal result and completion flag, converts only the gradient, and propagates either evaluation or conversion errors."
    preconditions := "DE evaluation/conversion are arbitrary typed services.",
    status := .proven, prop := ``gradientForwarding, thm := some ``gradientForwarding_holds },
  { id := "ide-gradient-default", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_grad_tree_array", "_grad_evaluator"],
    statement := "The standard gradient backend receives constants mode by default, and the adjoint backend receives features mode by default. An explicit supported mode reaches either backend unchanged."
    preconditions := "Standard DE enum; variable is extracted as a typed optional mode (including both), and residual keywords exclude variable."
    status := .proven, prop := ``defaultModes, thm := some ``defaultModes_holds },
  { id := "ide-array-types", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["expected_array_type"],
    statement := "Matrices and Matrix-backed views select Vector{T}; the generic array path selects typeof(similar(X,axes(X,2))) and gradient paths use typeof(similar(X)).",
    preconditions := "Array type descriptors represent rank and parent type. The fallback similar calls are external services; axes use the ordinary one-based array model."
    status := .proven, prop := ``expectedTypes, thm := some ``expectedTypes_holds },
  { id := "ide-output-type-assertion", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_tree_array", "eval_diff_tree_array", "eval_grad_tree_array", "differentiable_eval_tree_array"],
    statement := "An output with the expected runtime array type passes its type assertion unchanged with its original completion flag.",
    preconditions := "The runtime array tag equals the asserted type by construction; concrete data values arbitrary.",
    status := .todo, prop := ``matchingTypeAssertion, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof with actual wrapper return assertions on array family and element type, including the derivative and converted gradient." },
  { id := "ide-mixed-type-eval", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_tree_array", "expected_array_type"],
    statement := "Evaluation of Float32/Float64 trees and data should preserve DE's promoted output rather than failing SR's return-type assertion.",
    preconditions := "DE evaluation succeeds; standard scalar promotion reuses DE NodeBase.Elt/promoteElt.",
    status := .refuted, prop := ``mixedTypeForwarding, thm := some ``mixedTypeForwarding_refuted,
    notes := "Node(Float64;val=1.0) with ones(Float32,1,2) evaluates directly in DE to Float64[1,1], but SR eval_tree_array(tree,X,options) throws TypeError because lines 91,110,122 assert Vector{Float32}." },
  { id := "ide-callable-keywords", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["(::Union{AbstractExpression,AbstractExpressionNode})", "_grad_evaluator"],
    statement := "Callable trees seed turbo and bumper from options; adjoint helpers seed only turbo. The backend sees the last caller value for a supplied key and otherwise the seeded value, if any."
    preconditions := "Keyword values are opaque tokens."
    status := .proven, prop := ``callableForwarding, thm := some ``callableForwarding_holds },
  { id := "ide-expression-operators", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["eval_tree_array", "string_tree", "print_tree"],
    statement := "An explicitly resolved operator enum overrides Expression metadata through DE's existing get_operators model.",
    preconditions := "Resolved explicit enum; custom AbstractOptions resolution itself is arbitrary.",
    status := .todo, prop := ``expressionOperatorSelection, thm := none,
    notes := "Bind the stock Expression operator lookup at all three SR adapter call sites; the existing lemma checks only DE lookup." },
  { id := "ide-raw-name-default", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_tree"],
    statement := "string_tree defaults to pretty=false, raw variable_names and DE's constant printer, ignoring display names on that branch.",
    preconditions := "None.", status := .proven, prop := ``rawNames, thm := some ``rawNames_holds },
  { id := "ide-pretty-arguments", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_tree", "string_constant", "sprint_precision"],
    statement := "Pretty rendering defaults display names to variable names, forwards remaining keywords and selects options precision plus [?] exactly when units are present and constants may be dimensional.",
    preconditions := "Printf is arbitrary; unit strings supplied by format_dimensions; positive feature indices and available unit entries.",
    status := .proven, prop := ``prettyArguments, thm := some ``prettyArguments_holds },
  { id := "ide-graph-render-routing", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_tree"],
    statement := "Raw graph rendering propagates conversion failure or resolves operators and renders on the converted heap and root as a plain node. Pretty graphs and ordinary heap nodes resolve operators and render from their original root and heap."
    preconditions := "DE heap conversion and rendering; finite traversals."
    status := .proven, prop := ``graphRouting, thm := some ``graphRouting_holds },
  { id := "ide-constant-format", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_constant", "sprint_precision"],
    statement := "Real and Float32 constants use the options precision callback and suffix; complex constants retain DE's parenthesized Julia text and the same suffix.",
    preconditions := "Printf text is an arbitrary callback supplied to PrintOptions.",
    status := .todo, prop := ``constantFormat, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof with Julia string on typed complex components, preserving signed zero." },
  { id := "ide-raw-keyword-forward", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_tree"],
    statement := "Raw string_tree should forward a caller's f_constant keyword to DE just as the pretty branches do.",
    preconditions := "Valid constant node; public DE string keyword.",
    status := .refuted, prop := ``rawKeywordForwarding, thm := some ``rawKeywordForwarding_refuted,
    notes := "string_tree(Node(Float64;val=1.0),options;f_constant=(_ -> \"CUSTOM\")) returns \"1.0\" instead of \"CUSTOM\": the !pretty branch drops kws at lines 238-244." },
  { id := "ide-print-pretty-consistency", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["print_tree", "string_tree"],
    statement := "print_tree and string_tree with the same options and pretty=true should produce the same equation, with one extra newline for printing.",
    preconditions := "Valid variable node and writable IOBuffer.",
    status := .refuted, prop := ``printStringConsistency, thm := some ``printStringConsistency_refuted,
    notes := "For Node(Float64;feature=1), string_tree(...;pretty=true) returns x₁ while print_tree(io,...;pretty=true) writes x1\\n, because print_tree bypasses the SR renderer at lines 335,343." },
  { id := "ide-print-forward", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["print_tree"],
    statement := "For plain nodes, stdout emits the text rendered with the supplied printer keywords and options enum, followed by one newline. Explicit IO appends exactly that text and newline to the selected sink."
    preconditions := "Installed DE printer keyword and append-only sink models, with omitted pretty distinct from false."
    status := .proven, prop := ``printForwarding, thm := some ``printForwarding_holds },
  { id := "ide-print-io", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["print_tree"],
    statement := "A successful print appends the rendered text to the selected sink and preserves contents at every other sink.",
    preconditions := "Append-only writable sink model from DE StringsParse.printTreeIO.",
    status := .proven, prop := ``ioForwarding, thm := some ``ioForwarding_holds },
  { id := "ide-dimension-format", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["format_dimensions", "string_variable"],
    statement := "Missing units and unit-magnitude dimensionless quantities add no suffix; unit-magnitude dimensional quantities print dimensions, others print the whole quantity inside brackets.",
    preconditions := "External DynamicQuantities predicates and text remain arbitrary inputs.",
    status := .proven, prop := ``dimensionFormatting, thm := some ``dimensionFormatting_holds },
  { id := "ide-variable-names", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_variable_raw", "string_variable"],
    statement := "A valid named feature selects its one-based variable name, including names supplied from a Dataset's variable_names field.",
    preconditions := "Positive feature index within the supplied name list.",
    status := .todo, prop := ``namedVariable, thm := none,
    notes := "Raw and pretty helpers select arbitrary in-bounds names; the SearchUtils dataset rendering call must still be bound to the SR renderer." },
  { id := "ide-variable-units", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["string_variable"],
    statement := "Unit-bearing variables append exactly the checked one-based unit suffix to the selected pretty variable name, propagating out-of-range unit errors.",
    preconditions := "Formatted unit text supplied by DynamicQuantities.",
    status := .todo, prop := ``variableUnitForwarding, thm := none,
    notes := "Proved against an unfaithful model; needs re-proof with fallible feature formatting in the actual renderer. DE RenderConfig currently uses a total String callback." },
  { id := "ide-alias-enum", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["define_alias_operators"],
    statement := "For a two-degree enum, the selected constructor receives the inverse aliases in their original degrees and order, with both mutation flags false. Its result or error is returned unchanged."
    preconditions := "Exactly two operator degree tuples, as required by the source assertion.",
    status := .proven, prop := ``aliasConstruction, thm := some ``aliasConstruction_holds },
  { id := "ide-extend-macro", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["@extend_operators"],
    statement := "A non-options result fails after the first evaluation. Otherwise the macro evaluates again, reads that result's operators, and passes the constructed alias to extension; field or constructor failures prevent extension."
    preconditions := "Models the run-time expansion; AST hygiene is outside the value-level model."
    status := .proven, prop := ``macroForwarding, thm := some ``macroForwarding_holds },
  { id := "ide-worker-hooks", juliaFile := "src/InterfaceDynamicExpressions.jl",
    juliaFns := ["require_copy_to_workers", "make_example_inputs"],
    statement := "Default expressions require no explicit worker copying; make_example_inputs fails with its options.expression_type diagnostic and never returns fabricated inputs.",
    preconditions := "Default methods only; custom expression overrides excluded by dispatch.",
    status := .proven, prop := ``workerFallbacks, thm := some ``workerFallbacks_holds },
  { id := "idt-numeric-init", juliaFile := "src/InterfaceDataTypes.jl",
    juliaFns := ["init_value"], statement := "Default Number initialization invokes zero once with the requested type, then returns that call's value or exception unchanged."
    preconditions := "Type objects are represented by their type identifiers; zero is an external typed service."
    status := .proven, prop := ``numericInit, thm := some ``numericInit_holds },
  { id := "idt-numeric-sample", juliaFile := "src/InterfaceDataTypes.jl",
    juliaFns := ["sample_value"], statement := "Number sampling returns precisely randn(rng,T), preserving RNG and requested type, ignores options and propagates unsupported-randn errors.",
    preconditions := "Typed randn service; no claim that every Number implements randn.",
    status := .proven, prop := ``numericSample, thm := some ``numericSample_holds },
  { id := "idt-generic-hooks", juliaFile := "src/InterfaceDataTypes.jl",
    juliaFns := ["init_value", "sample_value", "mutate_value", "parse_scope"],
    statement := "Unimplemented generic initialization, sampling and ConstantMutation fail with type-specific errors; parse_scope returns nothing for every type.",
    preconditions := "Default fallback methods; custom overload behavior remains external.",
    status := .proven, prop := ``genericHooksFail, thm := some ``genericHooksFail_holds },
  { id := "idt-constant-mutation", juliaFile := "src/InterfaceDataTypes.jl",
    juliaFns := ["mutate_value"],
    statement := "Numeric mutation delegates unchanged temperature, perturbation_factor and probability_negate to the existing mutation algorithm; generic ConstantMutation fallback never silently mutates custom values.", preconditions := "Existing Mutations.mutateValue model; range/RNG laws owned by mut-mutate-value.",
    status := .todo, prop := ``constantMutationForwarding, thm := none, notes := "Numerical forwarding restored for arbitrary modeled parameters; missing generic unsupported-type dispatch through the ConstantMutation entry point and typed runtime arithmetic." }
]
end SymReg.Interface
