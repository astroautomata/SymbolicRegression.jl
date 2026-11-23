import DynExpr.NodeBase.TreeOps
import DynExpr.NodeUtils.Nodes
import SymReg.MutateGen.Sample

/-!
Weight conditioning of `src/Mutate.jl:123-245`: `_update_weight!`, `_set_weight!`,
`_scale_weight!`, the engine method of `condition_mutation_weights!` and the default
`condition_mutate_constant!`.

The member's tree is `get_tree(member.tree)`, a plain `Node` modelled by DE's pure `Tree`
(`Node` has `preserve_sharing = false`; for `GraphNode` expressions `preserveSharing` is
true and the same traversals apply to the unfolded tree). `compute_complexity(member,
options)` and `count_scalar_constants(member.tree)` belong to other files and are inputs.
-/

namespace SymReg.MutateGen
open DynExpr DynExpr.NodeBase

/-- A weighted mutation list `Vector{Pair{AbstractMutation,Float64}}`. -/
abbrev Weights := List (Kind × JF)

/-- `_update_weight!(op, weights, M)` (`src/Mutate.jl:130-140`): every entry whose mutation
`isa M` (the predicate `M`) gets weight `op(w)`, in place. -/
def updateWeight (op : JF → JF) (ws : Weights) (M : Kind → Bool) : Weights :=
  ws.map fun p => if M p.1 then (p.1, op p.2) else p

/-- Effectful vector operations selected by Julia's `AbstractVector` dispatch.
The state tracks the original vector object and any visible assignment effects. -/
structure WeightAccess (S M W V : Type) where
  indices : S → List Nat
  get : S → Nat → Jl (M × W)
  assign : S → Nat → (M × V) → Jl Unit × S

-- Source: src/Mutate.jl:130-140
-- function _update_weight!(
--     op::F, weights::AbstractVector, ::Type{M}
-- ) where {F,M<:AbstractMutation}
--     for i in eachindex(weights)
--         m, w = weights[i]
--         if m isa M
--             weights[i] = m => op(w)
--         end
--     end
--     return nothing
-- end
def updateWeightSlots {S M W V : Type} (a : WeightAccess S M W V)
    (isInstance : M → Bool) (op : S → W → Jl V × S) : List Nat → S → Jl Unit × S
  | [], s => (.ok (), s)
  | i :: ix, s =>
    match a.get s i with
    | .error e => (.error e, s)
    | .ok (m, w) =>
      if isInstance m then
        match op s w with
        | (.error e, s) => (.error e, s)
        | (.ok v, s) =>
          match a.assign s i (m, v) with
          | (.error e, s) => (.error e, s)
          | (.ok (), s) => updateWeightSlots a isInstance op ix s
      else updateWeightSlots a isInstance op ix s

def updateWeightInPlace {S M W V : Type} (a : WeightAccess S M W V)
    (isInstance : M → Bool) (op : S → W → Jl V × S) (s : S) : Jl Unit × S :=
  updateWeightSlots a isInstance op (a.indices s) s

-- Source: src/Mutate.jl:143-147
-- function _set_weight!(
--     weights::AbstractVector, ::Type{M}, value::Real
-- ) where {M<:AbstractMutation}
--     return _update_weight!(Returns(Float64(value)), weights, M)
-- end
def setWeightInPlace {S M W : Type} (a : WeightAccess S M W JF)
    (isInstance : M → Bool) (convert : S → Jl JF × S) (s : S) : Jl Unit × S :=
  match convert s with
  | (.error e, s) => (.error e, s)
  | (.ok v, s) => updateWeightInPlace a isInstance (fun s _ => (.ok v, s)) s

-- Source: src/Mutate.jl:150-154
def scaleWeightInPlace {S M W V : Type} (a : WeightAccess S M W V)
    (isInstance : M → Bool) (convert : S → Jl JF × S)
    (multiply : S → W → JF → Jl V × S) (s : S) : Jl Unit × S :=
  updateWeightInPlace a isInstance (fun s w =>
    match convert s with
    | (.error e, s) => (.error e, s)
    | (.ok f, s) => multiply s w f) s

/-- `_set_weight!(weights, M, value)` (`src/Mutate.jl:143-147`). -/
def setWeight (ws : Weights) (M : Kind → Bool) (value : JF) : Weights :=
  updateWeight (fun _ => value) ws M

-- Source: src/Mutate.jl:149-154
-- """Multiply the weight of every `<: M` entry by `factor` (in place)."""
-- function _scale_weight!(
--     weights::AbstractVector, ::Type{M}, factor::Real
-- ) where {M<:AbstractMutation}
--     return _update_weight!(w -> w * Float64(factor), weights, M)
-- end
def scaleWeight (ws : Weights) (M : Kind → Bool) (factor : JF) : Weights :=
  updateWeight (fun w => SymReg.Loss.LossPrecision.round .float64
    (w * SymReg.Loss.LossPrecision.round .float64 factor)) ws M

/-- `m isa K` for a concrete mutation struct type `K`. -/
def isa (k : Kind) : Kind → Bool := fun m => m == k

/-- `tree.constant` of a leaf `Node`. A childless branch is not a representable `Node`. -/
def isConstLeaf : Tree JF → Bool
  | .const _ => true
  | _ => false

/-- Inputs of `condition_mutation_weights!(weights, member, options, curmaxsize, nfeatures)`
(`src/Mutate.jl:167-214`) besides the weights. `D` is the node type's maximum degree. -/
structure CondIn where
  D : Nat
  tree : Tree JF
  preserveSharing : Bool
  scalarConsts : Nat
  complexity : Int
  curmaxsize : Int
  nfeatures : Int
  shouldSimplify : Bool
  isTemplate : Bool := false

/-- The default `condition_mutate_constant!` (`src/Mutate.jl:233-245`):
`n_constants = max(count_constant_nodes(member.tree), count_scalar_constants(member.tree))`,
then `_scale_weight!(weights, ConstantMutation, min(8, n_constants) / 8.0)`. -/
def conditionMutateConstant (ws : Weights) (constantNodes scalarConsts : Nat) : Weights :=
  let n := max constantNodes scalarConsts
  scaleWeight ws (isa .constant) (.fin ((min 8 n : Nat) / 8))

-- Source: src/Mutate.jl:167-214; src/TemplateExpression.jl:917-946,1034-1044
/-- The two shipped engine conditioning methods. Only the generic method examines the
root for its leaf early return and scans for binary nodes. The template constant hook
does nothing. -/
def conditionMutationWeights (ws : Weights) (c : CondIn) : Weights :=
  let ws := if !c.preserveSharing then
      setWeight (setWeight ws (isa .formConnection) (.fin 0)) (isa .breakConnection) (.fin 0)
    else ws
  if !c.isTemplate && c.tree.degree == 0 then
    let ws := setWeight ws (isa .operator) (.fin 0)
    let ws := setWeight ws (isa .swapOperands) (.fin 0)
    let ws := setWeight ws (isa .deleteNode) (.fin 0)
    let ws := setWeight ws (isa .simplify) (.fin 0)
    if !isConstLeaf c.tree then
      setWeight (setWeight ws (isa .optimize) (.fin 0)) (isa .constant) (.fin 0)
    else setWeight ws (isa .feature) (.fin 0)
  else
    let ws := if c.isTemplate then ws else
      let ws := if !anyT c.D (fun t => t.degree == 2) c.tree then
          setWeight ws (isa .swapOperands) (.fin 0) else ws
      conditionMutateConstant ws (NodeUtils.countConstantNodes c.tree) c.scalarConsts
    let ws := if c.nfeatures ≤ 1 then setWeight ws (isa .feature) (.fin 0) else ws
    let ws := if c.complexity ≥ c.curmaxsize then
        setWeight (setWeight ws (isa .addNode) (.fin 0)) (isa .insertNode) (.fin 0) else ws
    if !c.shouldSimplify then setWeight ws (isa .simplify) (.fin 0) else ws

/-- Weight of every entry of kind `k`: the property statements below speak about all
entries of a kind at once. -/
def weightsOf (ws : Weights) (k : Kind) : List JF := (ws.filter (fun p => p.1 == k)).map Prod.snd

/-- Some node of the tree satisfies `p` (specification-side, over DE's preorder). -/
def someNode (p : Tree JF → Bool) (t : Tree JF) : Bool := (preorder t).any p

/-- `_valid_rotation_root(node)` (`src/MutationFunctions.jl:617-619`): an operator node
with an operator child. `randomly_rotate_tree!` returns the tree unchanged when no node
is a valid rotation root (`src/MutationFunctions.jl:626-630`). -/
def validRotationRoot : Tree JF → Bool
  | .branch _ cs => cs.length > 0 && cs.any (fun c => c.degree > 0)
  | _ => false

end SymReg.MutateGen
