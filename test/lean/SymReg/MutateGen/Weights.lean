import DynExpr.Runtime.Value
import DynExpr.Runtime.Errors

/-!
Mutation kinds and the deprecated `MutationWeights` struct (`src/MutationWeights.jl`,
SymbolicRegression.jl `upstream/master` daae84e5), with the default weighted mutation list
`default_mutations()` of `src/Mutations.jl:156-174` that `_mutation_weights` reads.

Weights are Float64 values, modelled by DE's `JF` (exact rationals plus NaN and the two
infinities). The decimal literals of `default_mutations()` are modelled by their exact
decimal values.
-/

namespace SymReg.MutateGen
open DynExpr

/-- The concrete mutation type of an `AbstractMutation` instance: the fifteen
`BUILTIN_MUTATION_TYPES` (`src/Mutations.jl:132-148`) and user-defined types, numbered.
`m isa M` for a concrete struct type `M` is equality of kinds; field values of
`ConstantMutation` and `BacksolveMutation` play no role in weighting. -/
inductive Kind where
  | constant
  | operator
  | feature
  | swapOperands
  | addNode
  | insertNode
  | deleteNode
  | formConnection
  | breakConnection
  | rotateTree
  | backsolve
  | simplify
  | randomize
  | optimize
  | doNothing
  | custom (n : Nat)
  deriving DecidableEq, Repr

/-- `BUILTIN_MUTATION_TYPES` in tuple order (`src/Mutations.jl:132-148`). -/
def builtinKinds : List Kind :=
  [.constant, .operator, .feature, .swapOperands, .addNode, .insertNode, .deleteNode,
   .formConnection, .breakConnection, .rotateTree, .backsolve, .simplify, .randomize,
   .optimize, .doNothing]

/-- `default_mutations()` (`src/Mutations.jl:156-174`). -/
def defaultMutations : List (Kind × JF) :=
  [(.constant, .fin (353 / 10000)), (.operator, .fin (363 / 100)), (.feature, .fin (1 / 10)),
   (.swapOperands, .fin (608 / 100000)), (.rotateTree, .fin (142 / 100)),
   (.addNode, .fin (771 / 10000)), (.insertNode, .fin (244 / 100)),
   (.deleteNode, .fin (369 / 1000)), (.simplify, .fin (148 / 100000)),
   (.randomize, .fin (695 / 100000)), (.doNothing, .fin (431 / 1000)), (.optimize, .fin 0),
   (.backsolve, .fin 0), (.formConnection, .fin (1 / 2)), (.breakConnection, .fin (1 / 10))]

/-- The fields of `mutable struct MutationWeights` (`src/MutationWeights.jl:64-80`), in
declaration order. -/
inductive WName where
  | mutate_constant
  | mutate_operator
  | mutate_feature
  | swap_operands
  | rotate_tree
  | add_node
  | insert_node
  | delete_node
  | simplify
  | randomize
  | do_nothing
  | optimize
  | backsolve
  | form_connection
  | break_connection
  deriving DecidableEq, Repr

/-- `const mutations = fieldnames(MutationWeights)` (`src/MutationWeights.jl:82`). -/
def fieldNames : List WName :=
  [.mutate_constant, .mutate_operator, .mutate_feature, .swap_operands, .rotate_tree,
   .add_node, .insert_node, .delete_node, .simplify, .randomize, .do_nothing, .optimize,
   .backsolve, .form_connection, .break_connection]

/-- The `Symbol` naming each field. -/
def WName.sym : WName → String
  | .mutate_constant => "mutate_constant"
  | .mutate_operator => "mutate_operator"
  | .mutate_feature => "mutate_feature"
  | .swap_operands => "swap_operands"
  | .rotate_tree => "rotate_tree"
  | .add_node => "add_node"
  | .insert_node => "insert_node"
  | .delete_node => "delete_node"
  | .simplify => "simplify"
  | .randomize => "randomize"
  | .do_nothing => "do_nothing"
  | .optimize => "optimize"
  | .backsolve => "backsolve"
  | .form_connection => "form_connection"
  | .break_connection => "break_connection"

/-- `mutable struct MutationWeights` (`src/MutationWeights.jl:64-80`), fields in
declaration order. -/
structure MutationWeights where
  mutate_constant : JF
  mutate_operator : JF
  mutate_feature : JF
  swap_operands : JF
  rotate_tree : JF
  add_node : JF
  insert_node : JF
  delete_node : JF
  simplify : JF
  randomize : JF
  do_nothing : JF
  optimize : JF
  backsolve : JF
  form_connection : JF
  break_connection : JF
  deriving DecidableEq, Repr

/-- `getfield(w, k)`. -/
def MutationWeights.get (w : MutationWeights) : WName → JF
  | .mutate_constant => w.mutate_constant
  | .mutate_operator => w.mutate_operator
  | .mutate_feature => w.mutate_feature
  | .swap_operands => w.swap_operands
  | .rotate_tree => w.rotate_tree
  | .add_node => w.add_node
  | .insert_node => w.insert_node
  | .delete_node => w.delete_node
  | .simplify => w.simplify
  | .randomize => w.randomize
  | .do_nothing => w.do_nothing
  | .optimize => w.optimize
  | .backsolve => w.backsolve
  | .form_connection => w.form_connection
  | .break_connection => w.break_connection

/-- The positional constructor `MutationWeights(values...)` (`src/MutationWeights.jl:125`):
a `MethodError` unless exactly fifteen values are given. -/
def MutationWeights.ofList : List JF → Jl MutationWeights
  | [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] => pure ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩
  | _ => throw (.methodError "no method matching MutationWeights")

/-- `Base.convert(::Type{Vector}, w::MutationWeights)` (`src/MutationWeights.jl:85-89`):
the fields in `fieldnames` order. -/
def convertVector (w : MutationWeights) : List JF := fieldNames.map w.get

/-- `Base.copy(w::MutationWeights)` (`src/MutationWeights.jl:90-92`): a new struct from
the fields in `fieldnames` order. -/
def copyWeights (w : MutationWeights) : Jl MutationWeights := MutationWeights.ofList (convertVector w)

/-- `_MUTATION_FROM_SYMBOL` (`src/MutationWeights.jl:96-112`) as a lookup by symbol; a
missing key is a `KeyError` (modelled as a bounds error). -/
def mutationFromSymbol (s : String) : Jl Kind :=
  match s with
  | "mutate_constant" => pure .constant
  | "mutate_operator" => pure .operator
  | "mutate_feature" => pure .feature
  | "swap_operands" => pure .swapOperands
  | "rotate_tree" => pure .rotateTree
  | "add_node" => pure .addNode
  | "insert_node" => pure .insertNode
  | "delete_node" => pure .deleteNode
  | "simplify" => pure .simplify
  | "randomize" => pure .randomize
  | "do_nothing" => pure .doNothing
  | "optimize" => pure .optimize
  | "backsolve" => pure .backsolve
  | "form_connection" => pure .formConnection
  | "break_connection" => pure .breakConnection
  | _ => throw .boundsError

/-- `Dict(typeof(mutation) => weight for (mutation, weight) in default_mutations())`
lookup (`src/MutationWeights.jl:119-121`): a later pair for the same type overwrites an
earlier one; a missing key is a `KeyError` (modelled as a bounds error). -/
def dictLookup (ps : List (Kind × JF)) (k : Kind) : Jl JF :=
  match ps.reverse.find? (fun p => p.1 = k) with
  | some p => pure p.2
  | none => throw .boundsError

/-- `get(kws, name, default)` on a keyword list with distinct names. -/
def kwGet (kws : List (String × JF)) (name : String) (default : JF) : JF :=
  match kws.find? (fun p => p.1 = name) with
  | some p => p.2
  | none => default

/-- A Julia `Float64` conversion, dispatched on the keyword value's type.
The value in an existing Float64 field needs no conversion. -/
class WeightConversion (α : Type) where
  toFloat64 : α → Jl JF

instance : WeightConversion JF := ⟨Except.ok⟩

def unknownWeight (key : String) : JlError :=
  .argumentError ("Unknown mutation weight: `" ++ key ++ "`.")

-- Source: src/MutationWeights.jl:114-126
-- function _mutation_weights(; kws...)
--     unknown = setdiff(keys(kws), mutations)
--     isempty(unknown) ||
--         throw(ArgumentError("Unknown mutation weight: `$(first(unknown))`."))
--
--     defaults = Dict(
--         typeof(mutation) => weight for (mutation, weight) in default_mutations()
--     )
--     values = map(mutations) do name
--         Float64(get(kws, name, defaults[typeof(_MUTATION_FROM_SYMBOL[name])]))
--     end
--     return MutationWeights(values...)
-- end
/-- `_mutation_weights(; kws...)` (`src/MutationWeights.jl:114-126`). The first unknown
keyword raises `ArgumentError`; then, for each field name in order, the default
`defaults[typeof(_MUTATION_FROM_SYMBOL[name])]` is evaluated (eagerly, as an argument of
`get`) and the keyword value, if any, replaces it. -/
def mutationWeights {α : Type} [WeightConversion α] (kws : List (String × α)) :
    Jl MutationWeights := do
  match kws.find? (fun p => !(fieldNames.map WName.sym).contains p.1) with
  | some (key, _) => throw (unknownWeight key)
  | none =>
    let values ← fieldNames.mapM fun name => do
      let k ← mutationFromSymbol name.sym
      let d ← dictLookup defaultMutations k
      match kws.find? (fun p => p.1 = name.sym) with
      | some (_, value) => WeightConversion.toFloat64 value
      | none => pure d
    MutationWeights.ofList values

-- Source: src/MutationWeights.jl:128-134
-- function MutationWeights(; kws...)
--     Base.depwarn(
--         "`MutationWeights` is deprecated. Pass weighted mutation instances through `Options(; mutations=...)`.",
--         :MutationWeights,
--     )
--     return _mutation_weights(; kws...)
-- end
/-- Pass the outcome of `Base.depwarn` under the current Julia runtime mode. -/
def mutationWeightsKw {α : Type} [WeightConversion α] (depwarn : Jl Unit)
    (kws : List (String × α)) : Jl MutationWeights := do
  depwarn
  mutationWeights kws

/-- `_mutations_from_weights(w)` (`src/MutationWeights.jl:141-145`). -/
def mutationsFromWeights (w : MutationWeights) : Jl (List (Kind × JF)) :=
  fieldNames.mapM fun k => do
    let m ← mutationFromSymbol k.sym
    pure (m, w.get k)

/-- The mutation each field documents (`src/MutationWeights.jl:36-58`: "How often to mutate
a constant", ... and the type docstrings of `src/Mutations.jl`). -/
def documentedKind : WName → Kind
  | .mutate_constant => .constant
  | .mutate_operator => .operator
  | .mutate_feature => .feature
  | .swap_operands => .swapOperands
  | .rotate_tree => .rotateTree
  | .add_node => .addNode
  | .insert_node => .insertNode
  | .delete_node => .deleteNode
  | .simplify => .simplify
  | .randomize => .randomize
  | .do_nothing => .doNothing
  | .optimize => .optimize
  | .backsolve => .backsolve
  | .form_connection => .formConnection
  | .break_connection => .breakConnection

end SymReg.MutateGen
