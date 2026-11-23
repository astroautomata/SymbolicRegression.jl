import DynExpr.StringsParse.Strings
import SymReg.Loss.Core
import DynExpr.NodeBase.Traverse

namespace SymReg.Interface
open DynExpr DynExpr.StringsParse

/-- Options fields consumed by SR's renderer. Printf and unit-library rendering
are arbitrary callbacks, since the wrapper does not implement them.
src/InterfaceDynamicExpressions.jl:247-271,293-317. -/
structure PrintOptions where
  operators : Operators := []
  precision : Nat := 5
  dimensionlessOnly : Bool := false
  sprintPrecision : Scalar → Nat → String := fun v _ => stringConstant v

/-- Julia decimal subscript conversion used by string_variable.
src/InterfaceDynamicExpressions.jl:282-286, Utils.jl:subscriptify. -/
def subscriptDigit (c : Char) : Char :=
  match c with
  | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
  | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉' | c => c

def prettyVariable (feature : Nat) (names : Option (List String)) : String :=
  match names with
  | none => "x" ++ String.ofList ((toString feature).toList.map subscriptDigit)
  | some ns => ns[feature - 1]?.getD
      ("x" ++ String.ofList ((toString feature).toList.map subscriptDigit))

/-- Unit callbacks give already formatted dimensions; bounds errors remain
observable in the separate checked variable helper.
src/InterfaceDynamicExpressions.jl:288-290,300-314. -/
def variableWithUnits (feature : Nat) (names : Option (List String))
    (units : Option (List String)) : Jl String := do
  let base := prettyVariable feature names
  match units with
  | none => return base
  | some us =>
    let u ← SymReg.Loss.at1 us feature
    return base ++ u

/-- format_dimensions distinguishes nothing, unit magnitude one and zero
physical dimension. External dimension/quantity text is supplied unchanged.
src/InterfaceDynamicExpressions.jl:300-314. -/
def formatDimensions (present magnitudeOne dimensionZero : Bool) (dimensionText quantityText : String) : String :=
  if !present then "" else if magnitudeOne then
    if dimensionZero then "" else "[" ++ dimensionText ++ "]"
  else "[" ++ quantityText ++ "]"

/-- Real values use Printf precision; complex values retain parenthesized Julia
text. src/InterfaceDynamicExpressions.jl:293-298. -/
def prettyConstant (o : PrintOptions) (placeholder : String) (v : Scalar) : String :=
  (match v with
   | .real _ | .float32 _ => o.sprintPrecision v o.precision
   | .complex _ _ => stringConstant v) ++ placeholder

/-- Accepted DE keyword overrides. An explicit display_variable_names=nothing
is distinct from omission. src/InterfaceDynamicExpressions.jl:229-234,261,271. -/
structure StringArgs where
  pretty : Bool := false
  names : Option (List String) := none
  displayNames : Option (Option (List String)) := none
  xUnits : Option (List String) := none
  yUnitsPresent : Bool := false
  fVariable : Option (Nat → Option (List String) → String) := none
  fConstant : Option (Scalar → String) := none
  varMap : Option (List String) := none
  raw : Option Bool := none

/-- Raw branch deliberately drops kws, selects raw names and DE's constants.
Pretty branch chooses display names, optional units and options precision,
then forwards caller overrides. Graph-to-Node conversion before this pure
renderer removes graph sharing markers. src/InterfaceDynamicExpressions.jl:226-274. -/
def stringConfig (o : PrintOptions) (a : StringArgs) : RenderConfig :=
  if !a.pretty then
    { operators := some o.operators, names := a.names, pretty := some false,
      fVariable := stringVariable }
  else
    let units := a.xUnits
    let withUnits := units.isSome || a.yUnitsPresent
    let placeholder := if withUnits && !o.dimensionlessOnly then "[?]" else ""
    { operators := some o.operators, names := a.displayNames.getD a.names,
      pretty := some true, raw := a.raw, varMap := a.varMap,
      fVariable := a.fVariable.getD (fun f ns =>
        prettyVariable f ns ++ ((units.bind (fun us => us[f - 1]?)).getD "")),
      fConstant := a.fConstant.getD (prettyConstant o placeholder) }

inductive StringInput where
  | tree (tree : Tree Scalar)
  | heap (isGraph : Bool) (g : NodeBase.SGraph Scalar) (degree root : Nat)

-- Source: src/InterfaceDynamicExpressions.jl:236-244
-- if !pretty
--     tree = tree isa GraphNode ? convert(Node, tree) : tree
--     return DE.string_tree(
--         tree,
--         DE.get_operators(tree, options);
--         f_variable=string_variable_raw,
--         variable_names,
--         pretty,
--     )
-- end
def srStringTree (o : PrintOptions) (a : StringArgs) (input : StringInput)
    (resolve : StringInput → PrintOptions → Jl Operators := fun _ o => .ok o.operators) : Jl String :=
  match input with
  | .tree t => do
    let ops ← resolve input o
    stringTree (stringConfig { o with operators := ops } a) t
  | .heap isGraph g degree root => do
    let (root, g) ← if !a.pretty && isGraph then NodeBase.convertH g degree false true false (g.next + 1) root
      else .ok (root, g)
    let graph := a.pretty && isGraph
    let ops ← resolve (.heap graph g degree root) o
    let cfg := stringConfig { o with operators := ops } a
    if graph then stringGraph cfg g.view (g.next + 1) root
    else match g.view.unfold (g.next + 1) root with
      | none => .error (.argumentError "invalid plain node traversal")
      | some t => stringTree cfg t

def graphRouting : Prop := ∀ (o : PrintOptions) (a : StringArgs)
  (g : NodeBase.SGraph Scalar) (degree root : Nat) (resolve : StringInput → PrintOptions → Jl Operators),
  let renderPlain := fun args (g : NodeBase.SGraph Scalar) n => do
    let ops ← resolve (.heap false g degree n) o
    match g.view.unfold (g.next + 1) n with
    | none => .error (.argumentError "invalid plain node traversal")
    | some t => stringTree (stringConfig { o with operators := ops } args) t
  (∀ e, NodeBase.convertH g degree false true false (g.next + 1) root = .error e →
    srStringTree o { a with pretty := false } (.heap true g degree root) resolve = .error e) ∧
  (∀ n h, NodeBase.convertH g degree false true false (g.next + 1) root = .ok (n, h) →
    srStringTree o { a with pretty := false } (.heap true g degree root) resolve =
      renderPlain { a with pretty := false } h n) ∧
  srStringTree o { a with pretty := true } (.heap true g degree root) resolve = (do
    let ops ← resolve (.heap true g degree root) o
    stringGraph (stringConfig { o with operators := ops } { a with pretty := true })
      g.view (g.next + 1) root) ∧
  srStringTree o a (.heap false g degree root) resolve = renderPlain a g root
theorem graphRouting_holds : graphRouting := by
  intro o a g degree root resolve
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro e he
    simp [srStringTree, he, bind, Except.bind]
  · intro n h hc
    simp [srStringTree, hc, bind, Except.bind]
  · cases ha : a.pretty <;> simp [srStringTree, ha, bind, Except.bind]

/-- The printer receives an omitted `pretty` unchanged so DE can apply `raw`. -/
structure PrintArgs where
  names : Option (List String) := none
  pretty : Option Bool := none
  raw : Option Bool := none
  varMap : Option (List String) := none
  fVariable : Option (Nat → Option (List String) → String) := none
  fConstant : Option (Scalar → String) := none

def printConfig (ops : Operators) (a : PrintArgs) : RenderConfig :=
  { operators := some ops, names := a.names,
    pretty := a.pretty, raw := a.raw, varMap := a.varMap,
    fVariable := a.fVariable.getD stringVariable,
    fConstant := a.fConstant.getD stringConstant }

-- Source: src/InterfaceDynamicExpressions.jl:332-336
-- function DE.print_tree(
--     tree::Union{AbstractExpression,AbstractExpressionNode}, options::AbstractOptions; kws...
-- )
--     return DE.print_tree(tree, DE.get_operators(tree, options); kws...)
-- end
def srPrintTree (o : PrintOptions) (a : PrintArgs) (tree : Tree Scalar) : Jl String :=
  printTree (printConfig o.operators a) tree

-- Source: src/InterfaceDynamicExpressions.jl:337-344
-- function DE.print_tree(
--     io::IO,
--     tree::Union{AbstractExpression,AbstractExpressionNode},
--     options::AbstractOptions;
--     kws...,
-- )
--     return DE.print_tree(io, tree, DE.get_operators(tree, options); kws...)
-- end
def srPrintIO (o : PrintOptions) (a : PrintArgs) (tree : Tree Scalar)
    (io : Heap String) (sink : Addr) : Jl (Unit × Heap String) :=
  printTreeIO (printConfig o.operators a) tree io sink

def rawNames : Prop := ∀ (o : PrintOptions) (names : Option (List String))
  (display : Option (Option (List String))),
  (stringConfig o { names, displayNames := display }).names = names ∧
  (stringConfig o { names, displayNames := display }).pretty = some false
 theorem rawNames_holds : rawNames := by intro o names display; exact ⟨rfl,rfl⟩

def prettyArguments : Prop := ∀ (o : PrintOptions) (a : StringArgs),
  (stringConfig o { a with pretty := true }).names = a.displayNames.getD a.names ∧
  (stringConfig o { a with pretty := true }).varMap = a.varMap ∧
  (stringConfig o { a with pretty := true }).raw = a.raw ∧
  (stringConfig o { a with pretty := true }).fConstant =
    a.fConstant.getD (prettyConstant o
      (if (a.xUnits.isSome || a.yUnitsPresent) && !o.dimensionlessOnly then "[?]" else ""))
 theorem prettyArguments_holds : prettyArguments := by intro o a; exact ⟨rfl,rfl,rfl,rfl⟩

def rawKeywordForwarding : Prop := ∀ (o : PrintOptions) (tree : Tree Scalar)
  (f : Scalar → String),
  srStringTree o { fConstant := some f } (.tree tree) =
    stringTree { operators := some o.operators, fConstant := f, pretty := some false } tree
 theorem rawKeywordForwarding_refuted : ¬ rawKeywordForwarding := by
  intro h
  exact (by decide :
    srStringTree {} { fConstant := some (fun _ => "CUSTOM") } (.tree (.const (.real (.fin 1)))) ≠
      stringTree { operators := some [], fConstant := fun _ => "CUSTOM", pretty := some false }
        (.const (.real (.fin 1)))) (h {} (.const (.real (.fin 1))) (fun _ => "CUSTOM"))

/-- Print and string with identical pretty keywords should agree up to newline.
A variable leaf is sufficient: SR uses x₁; DE's print path uses x1.
Confirmed by repro/ide-print-pretty-consistency.jl on Julia.
src/InterfaceDynamicExpressions.jl:282-286,332-344. -/
def printStringConsistency : Prop := ∀ (o : PrintOptions) (tree : Tree Scalar),
  srPrintTree o { pretty := some true } tree =
    (srStringTree o { pretty := true } (.tree tree)).map (fun s => s ++ "\n")
 theorem printStringConsistency_refuted : ¬ printStringConsistency := by
  intro h
  exact (by decide :
    srPrintTree {} { pretty := some true } (.feature 1) ≠
      (srStringTree {} { pretty := true } (.tree (.feature 1))).map (fun s => s ++ "\n"))
    (h {} (.feature 1))

def printForwarding : Prop := ∀ (o : PrintOptions) (a : PrintArgs) (tree : Tree Scalar)
  (io : Heap String) (sink : Addr),
  let cfg : RenderConfig := {
    operators := some o.operators, names := a.names, raw := a.raw,
    pretty := a.pretty, varMap := a.varMap, fVariable := a.fVariable.getD stringVariable,
    fConstant := a.fConstant.getD stringConstant }
  srPrintTree o a tree = (stringTree cfg tree).map (· ++ "\n") ∧
  srPrintIO o a tree io sink = (do
    let before ← io.read sink
    let text ← stringTree cfg tree
    let after ← io.write sink (before ++ text ++ "\n")
    return ((), after))
theorem printForwarding_holds : printForwarding := by
  intro o a tree io sink
  constructor
  · simp [srPrintTree, printTree, printConfig, Except.map, bind, Except.bind, pure, Except.pure]
  · change printTreeIO (printConfig o.operators a) tree io sink = (do
      let before ← io.read sink
      let text ← stringTree (printConfig o.operators a) tree
      let after ← io.write sink (before ++ text ++ "\n")
      return ((), after))
    cases hs : stringTree (printConfig o.operators a) tree <;>
      simp [printTreeIO, printTree, hs, ← String.append_assoc, bind, Except.bind,
        pure, Except.pure]

private def ioForwardingContract : Prop := ∀ (o : PrintOptions) (a : PrintArgs) (tree : Tree Scalar)
  (io : Heap String) (sink : Addr),
  srPrintIO o a tree io sink = do
    let before ← io.read sink
    let text ← srPrintTree o a tree
    let after ← io.write sink (before ++ text)
    return ((), after)

private theorem ioForwardingContract_holds : ioForwardingContract := by intro o a tree io sink; rfl

private def ioForwardingLaw : Prop := ∀ (o : PrintOptions) (a : PrintArgs) (tree : Tree Scalar)
  (io after : Heap String) (sink : Addr),
  srPrintIO o a tree io sink = .ok ((), after) →
  (∃ before text, io.read sink = .ok before ∧ srPrintTree o a tree = .ok text ∧
    after.read sink = .ok (before ++ text)) ∧
  ∀ other, other ≠ sink → after.read other = io.read other

private theorem ioForwardingLaw_holds : ioForwardingLaw := by
  intro o a tree io after sink h
  change (do
    let before ← io.read sink
    let text ← srPrintTree o a tree
    let next ← io.write sink (before ++ text)
    pure ((), next)) = .ok ((), after) at h
  cases hr : io.read sink <;> cases hp : srPrintTree o a tree <;>
    simp [hr, hp, bind, Except.bind] at h
  rename_i before text
  cases hw : io.write sink (before ++ text) <;>
    simp [hw, bind, Except.bind, pure, Except.pure] at h
  subst after
  exact ⟨⟨before, text, rfl, rfl, Heap.read_write_same _ _ _ _ hw⟩,
    fun other hne => Heap.read_write_other _ _ _ _ _ hw hne⟩

def ioForwarding : Prop := ioForwardingContract ∧ ioForwardingLaw

theorem ioForwarding_holds : ioForwarding := ⟨ioForwardingContract_holds, ioForwardingLaw_holds⟩

def dimensionFormatting : Prop := ∀ (dim qty : String) (one zero : Bool),
  formatDimensions false one zero dim qty = "" ∧
  formatDimensions true true true dim qty = "" ∧
  formatDimensions true true false dim qty = "[" ++ dim ++ "]" ∧
  formatDimensions true false zero dim qty = "[" ++ qty ++ "]"
theorem dimensionFormatting_holds : dimensionFormatting := by
  intro dim qty one zero; exact ⟨rfl,rfl,rfl,rfl⟩

def namedVariable : Prop := ∀ (names : List String) (i : Nat) (name : String),
  names[i]? = some name →
  stringVariable (i + 1) (some names) = name ∧
  prettyVariable (i + 1) (some names) = name
theorem namedVariable_holds : namedVariable := by
  intro names i name h
  simp [stringVariable, prettyVariable, h]

example : ["" , "mass"][1]? = some "mass" := rfl

def variableUnitForwarding : Prop := ∀ (feature : Nat) (names : Option (List String))
  (units : List String),
  variableWithUnits feature names (some units) =
    (SymReg.Loss.at1 units feature).map (fun u => prettyVariable feature names ++ u)
 theorem variableUnitForwarding_holds : variableUnitForwarding := by
  intro feature names units
  simp [variableWithUnits, Except.map, bind, Except.bind, pure, Except.pure]

def constantFormat : Prop := ∀ (o : PrintOptions) (placeholder : String) (v re im : JF),
  prettyConstant o placeholder (.real v) = o.sprintPrecision (.real v) o.precision ++ placeholder ∧
  prettyConstant o placeholder (.float32 v) = o.sprintPrecision (.float32 v) o.precision ++ placeholder ∧
  prettyConstant o placeholder (.complex re im) = stringConstant (.complex re im) ++ placeholder
 theorem constantFormat_holds : constantFormat := by
  intro o placeholder v re im; exact ⟨rfl,rfl,rfl⟩

end SymReg.Interface
