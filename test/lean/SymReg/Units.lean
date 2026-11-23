import SymReg.Units.Core
import SymReg.Units.Lemmas
import SymReg.Units.Sound
import SymReg.Units.Complete
import SymReg.Units.Refute
import SymReg.Units.Interface
import DynExpr.Registry.Types

/-!
Units slice: `src/DimensionalAnalysis.jl` (the `WildcardQuantity` evaluation behind
`violates_dimensional_constraints`) and `src/InterfaceDynamicQuantities.jl` (`get_units`,
`get_si_units`, `get_sym_units`, `get_dimensions_type`), SymbolicRegression.jl
`upstream/master` edbe678e. The dimensional penalty that calls the check is the Loss
slice's `dimensionalRegularization`.
-/

namespace SymReg.Units
open DynExpr.Registry

def entries : List Entry := [
  { id := "units-sound", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["violates_dimensional_constraints", "violates_dimensional_constraints_dispatch",
      "deg0_eval", "degn_eval", "WildcardQuantity", "same_dimensions", "has_no_dims", "valid",
      "ustrip", "dimension", "+", "-", "*", "/", "^", "sqrt", "cbrt", "abs", "inv", "safe_sqrt"]
    statement := "An accepted GraphNode has a consistent assignment of dimensions to constant objects, matching y_units if provided."
    preconditions := "A well-formed finite GraphNode over the built-in operator rules; no inexact roots of non-wildcard arguments."
    status := .refuted, prop := ``graphUnitsSound, thm := some ``graphUnitsSound_refuted
    notes := "A shared constant divided by itself passes for a length target, although its dimensions cancel under any single assignment to the constant object." },
  { id := "units-wildcard-any", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["WildcardQuantity", "*", "/", "+", "-", "sqrt", "cbrt", "abs", "inv", "deg0_eval"]
    statement := "Every non-violating wildcard GraphNode root can realize any dimension using one dimension per constant object."
    preconditions := "A well-formed finite GraphNode over the built-in operator rules; no inexact roots of non-wildcard arguments."
    status := .refuted, prop := ``graphWildcardAny, thm := some ``graphWildcardAny_refuted
    notes := "A shared constant divided by itself is marked as a wildcard but must be dimensionless." },
  { id := "units-sound-occurrences", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["violates_dimensional_constraints"]
    statement := "On a plain unshared Node or an explicitly unfolded graph, acceptance implies an assignment per constant occurrence matching the target dimension, if present."
    preconditions := "Degrees at most D; no inexact roots of non-wildcard arguments; built-in operator table."
    status := .proven, prop := ``units_sound, thm := some ``units_sound_holds },
  { id := "units-wildcard-occurrences", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["violates_dimensional_constraints_dispatch"]
    statement := "On a plain unshared Node or an explicitly unfolded graph, each non-violating wildcard can realize every dimension under an assignment per constant occurrence."
    preconditions := "Degrees at most D; no inexact roots of non-wildcard arguments; built-in operator table."
    status := .proven, prop := ``units_wildcard_any, thm := some ``units_wildcard_any_holds },
  { id := "units-complete-arith", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["violates_dimensional_constraints", "degn_eval", "+", "-", "*", "/", "^", "sqrt",
      "cbrt", "abs", "inv"]
    statement := "A dimensionally consistent tree using + - * / ^ sqrt cbrt abs inv returns false normally, including with unused nonarithmetic operator slots."
    preconditions := "Readable features in the first column, degrees at most D, finite proper subexpressions on that column, and exact relevant roots."
    status := .todo, prop := ``units_complete_arith
    notes := "The real model proves normal false using only traversed slots. Need to separate documented complex inputs, where safe_sqrt compares the stripped value with zero and can throw." },
  { id := "units-root-rounding", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["sqrt", "cbrt", "safe_sqrt", "violates_dimensional_constraints"]
    statement := "On the arithmetic operators, a dimensionally consistent tree whose subexpressions are finite is never reported as violating."
    preconditions := "Only arithmetic operators; degrees at most D; every subexpression finite."
    status := .refuted, prop := ``units_root_rounding, thm := some ``units_root_rounding_refuted
    notes := "Exponents are FixedRational{Int32,25200}, so sqrt of m^(1/16) is truncated to m^(787/25200): with X_units=[\"m\"], y_units=\"1\", (s5*s5)/s4 for s4=sqrt(sqrt(sqrt(sqrt(x1)))), s5=sqrt(s4) returns violates=true (residual m^(-1/25200)); it should return false." },
  { id := "units-dimensionless-fn", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["degn_eval", "@maybe_return_call"]
    statement := "cos-like functions (Number methods only) and log-like generic functions accept dimensionless arguments with a dimensionless result."
    preconditions := "Arguments non-violating, finite and dimensionless."
    status := .refuted, prop := ``units_dimensionless_fn, thm := some ``units_dimensionless_fn_refuted
    notes := "degn_eval reaches the scalar method only when every argument is a wildcard constant: with X_units=[\"m\",\"1\"], y_units=\"1\", violates_dimensional_constraints on cos(x2), exp(x2) or log(x2) returns true; it should return false." },
  { id := "units-neg-preserve", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["degn_eval", "@maybe_return_call"]
    statement := "neg and relu preserve the dimensions of a non-wildcard argument."
    preconditions := "Argument non-violating, finite, not a wildcard."
    status := .refuted, prop := ``units_neg_preserve, thm := some ``units_neg_preserve_refuted
    notes := "WildcardQuantity has no unary - or zero, so neg(x)=-x and relu(x) throw MethodError and fall to the all-wildcard path: with X_units=[\"m\"], y_units=\"m\", neg(x1), relu(x1) and neg(2.0*x1) all return violates=true; they should return false." },
  { id := "units-compare", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["degn_eval", "@maybe_return_call"]
    statement := "greater, less, greater_equal and less_equal of two equal-dimension arguments are accepted with a dimensionless result."
    preconditions := "Arguments non-violating and finite with equal dimensions."
    status := .refuted, prop := ``units_compare, thm := some ``units_compare_refuted
    notes := "x > y needs isless on WildcardQuantity, which is missing: with X_units=[\"m\",\"1\"], y_units=\"1\", greater(x1,x1), less(x1,x1) and even greater(x2,x2) return violates=true (cond(x2,x1) with y_units=\"m\" too); they should return false." },
  { id := "units-degn-guard", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["degn_eval", "isfinite", "valid"]
    statement := "degn_eval returns the first violating argument unchanged; otherwise any nonfinite argument value on the first data row is reported as a violation."
    preconditions := "For the second part: no argument violates and some argument is nonfinite."
    status := .proven, prop := ``units_degn_guard, thm := some ``units_degn_guard_holds },
  { id := "units-lattice", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["degn_eval", "@maybe_return_call", "safe_call", "compute_lattice", "one"]
    statement := "The dimensional method lattice visits eligible signatures in order, observes the per-task cache, stops at the first valid result, and reports a violation if every eligible attempt fails. Exceptions propagate according to the cached, uncached or all-scalar path."
    preconditions := "Nonempty arguments, none violating, all finite."
    status := .todo, prop := ``units_lattice
    notes := "Need per-task signature status by function type and complete ordered effects; the existing model has no warm Good/Bad states." },
  { id := "units-entry", juliaFile := "src/DimensionalAnalysis.jl"
    juliaFns := ["violates_dimensional_constraints"]
    statement := "The node entry reads X[:, 1] before its no-units, invalid-units, or dimensional-evaluation route. The expression entry resolves get_tree first. Both preserve the result and cache effects of evaluating that column."
    preconditions := "Ordinary arrays and views."
    status := .todo, prop := ``units_entry
    notes := "Reducer now resolves the parent operator after its children. Need stateful cache effects and an effectful get_tree adapter." },
  { id := "units-get-units", juliaFile := "src/InterfaceDynamicQuantities.jl"
    juliaFns := ["get_units", "get_si_units", "get_sym_units"]
    statement := "get_units maps nothing to nothing and the empty string to the unit quantity, parses other strings, converts quantity, dimension and real scalars, and converts vector elements in order, raising MethodError at a reached nothing. SI and symbolic adapters select their own parser and quantity type.",
    preconditions := "DynamicQuantities parsing and conversion arbitrary."
    status := .proven, prop := ``units_get_units, thm := some ``units_get_units_holds },
  { id := "units-dimtype", juliaFile := "src/InterfaceDynamicQuantities.jl"
    juliaFns := ["get_dimensions_type"]
    statement := "For concrete numeric, concrete quantity and generic element types, get_dimensions_type returns the dimension type of the first quantity element (the default when none); non-arrays give the default."
    preconditions := "Nonempty array whose elements match its element type; element type is not a quantity type with unspecified dimensions."
    status := .proven, prop := ``units_dimtype, thm := some ``units_dimtype_holds },
  { id := "units-dimtype-abstract", juliaFile := "src/InterfaceDynamicQuantities.jl"
    juliaFns := ["get_dimensions_type"]
    statement := "For every element type, get_dimensions_type returns the dimension type of the array's first quantity element (docstring: finds the dimension type from an array)."
    preconditions := "Nonempty array whose elements match its element type."
    status := .refuted, prop := ``units_dimtype_abstract, thm := some ``units_dimtype_abstract_refuted
    notes := "get_dimensions_type(Quantity[us\"km\"], Dimensions) returns Dimensions{FRInt32}, since dim_type(Quantity) is the package default, while get_dimensions_type(Any[us\"km\"], Dimensions) returns SymbolicDimensions{FRInt32}; both should be SymbolicDimensions{FRInt32}." }
]

end SymReg.Units
