import DynExpr.NodeBase.TraverseCopy
import DynExpr.Expressions.Sampling
import SymReg.Crossover
import SymReg.Loss.Core

/-!
Mirrors of the tree mutations of `src/MutationFunctions.jl` (SymbolicRegression.jl
`upstream/master` daae84e5), on the node heap of the DynamicExpressions formalization
(`DynExpr.NodeBase.SGraph`), except `crossover_trees`, `_random_node_and_parent` and
`_find_parent` (`SymReg.Crossover`).

A mutation runs in `M T`, a state monad over the heap and the RNG stream, on top of the
`Jl` exception monad. Every call into `rand` consumes one position of the abstract stream
`DynExpr.Expressions.Sampling.RNG`: index draws (`rand(rng, 1:n)`, `rand(rng, xs)`,
`rand(rng, Bool)`, `rand(rng, NodeSampler(...))`) read `indexDraws`, real draws (`rand(rng)`,
`rand(rng, T)`, `randn(rng, T)`) read `draws`. Real draws are exact rationals; Float64 rounding
of `rand(rng) * total` and of the constant factor is not modelled.

Nodes are plain `Node{T,D}` objects unless a function takes `isGraph` (`GraphNode`, whose
`NodeSampler` and `length` see each object once). `D` is the maximum degree of the node type
and `nops` the per-degree operator counts `options.nops` (one-based: `nops[i]` is `nops[i-1]?`).
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase

abbrev RNG := Expressions.Sampling.RNG

variable {T : Type}

/-- Heap and RNG stream threaded through a mutation. -/
structure St (T : Type) where
  g : SGraph T
  rng : RNG

/-- Mutation computations: state `St T`, Julia exceptions `Jl`. -/
abbrev M (T α : Type) := StateT (St T) Jl α

/-- The stream after one draw. -/
def adv (r : RNG) : RNG := { r with cursor := r.cursor + 1 }

/-! ## Random draws -/

/-- `rand(rng, xs)` for a nonempty collection (Random stdlib): the element at a uniform
index draw. An empty collection throws `ArgumentError`. -/
def randElem (xs : List Nat) : M T Nat := fun s =>
  if xs = [] then .error (.argumentError "collection must be non-empty")
  else .ok ((xs[(s.rng.indexDraws (xs.length - 1) s.rng.cursor).val]?).getD 0,
    { s with rng := adv s.rng })

/-- `rand(rng, 1:n)`: `1 +` a uniform index draw; an empty range throws `ArgumentError`. -/
def randRange (n : Nat) : M T Nat := fun s =>
  if n = 0 then .error (.argumentError "collection must be non-empty")
  else .ok ((s.rng.indexDraws (n - 1) s.rng.cursor).val + 1, { s with rng := adv s.rng })

/-- `rand(rng, Bool)`: index draw `1` of two. -/
def randBool : M T Bool := fun s =>
  .ok ((s.rng.indexDraws 1 s.rng.cursor).val = 1, { s with rng := adv s.rng })

/-- `rand(rng)` / `rand(rng, T)`: one real draw. -/
def randU : M T Rat := fun s => .ok (s.rng.draws s.rng.cursor, { s with rng := adv s.rng })

/-- Lift a `Jl` computation. -/
def liftJ {α : Type} (x : Jl α) : M T α := fun s => x.map (fun a => (a, s))

/-- Lift a heap transformer. -/
def liftG {α : Type} (f : SGraph T → Jl (α × SGraph T)) : M T α := fun s =>
  (f s.g).map (fun p => (p.1, { s with g := p.2 }))

/-- Run a computation on the current heap. -/
def onG {α : Type} (f : SGraph T → Jl α) : M T α := fun s => (f s.g).map (fun a => (a, s))

/-! ## Node operations -/

/-- Read the fields of a node object. -/
def rd (a : Addr) : M T (SCell T) := onG (fun g => g.read a)

/-- `get_child(n, i)`. -/
def getChildM (D : Nat) (n : Addr) (i : Nat) : M T Addr := onG (fun g => getChild g D n i)

/-- `set_child!(n, child, i)`. -/
def setChildM (D : Nat) (n child : Addr) (i : Nat) : M T Unit :=
  liftG (fun g => (setChild g D n child i).map (fun p => ((), p.2)))

/-- `set_node!(t, s)`. -/
def setNodeM (D : Nat) (t s : Addr) : M T Unit :=
  liftG (fun g => (setNode g D t s).map (fun g' => ((), g')))

/-- The node constructors `constructorof(N)(...)`, with `N` fixing `D`. -/
def ctorM (D : Nat) (kw : Kw T) : M T Addr := liftG (fun g => ctor g D true kw)

/-- `copy(node)`: `copy_node` (`src/base.jl:496-510` of DynamicExpressions.jl). -/
def copyM (D : Nat) (isGraph : Bool) (fuel : Nat) (a : Addr) : M T Addr :=
  liftG (fun g => copyNodeH g D isGraph false fuel a)

/-- `node.op = x` on a `Node`: `convert(UInt8, x)`, then the field write. -/
def setOpM (n : Addr) (o : Nat) : M T Unit :=
  liftG (fun g => do
    if o > 255 then throw (.errorException "InexactError: trunc(UInt8, op)")
    let c ← g.read n
    let g' ← g.write n { c with op := o }
    pure ((), g'))

/-- `node.feature = x` on a `Node`: `convert(UInt16, x)`, then the field write. -/
def setFeatureM (n : Addr) (f : Nat) : M T Unit :=
  liftG (fun g => do
    if f > 65535 then throw .inexactError
    let c ← g.read n
    let g' ← g.write n { c with feature := f }
    pure ((), g'))

/-- `node.val = v`. -/
def setValM (n : Addr) (v : T) : M T Unit :=
  liftG (fun g => do
    let c ← g.read n
    let g' ← g.write n { c with val := some v }
    pure ((), g'))

/-- The current fields of node `a`, as a filter or predicate argument; a missing object
satisfies no cell predicate. -/
def cellP (P : SCell T → Bool) (g : SGraph T) (a : Addr) : Bool :=
  match g.cells a with
  | some c => P c
  | none => false

/-- `rand(rng, NodeSampler(; tree, filter))` (`src/Random.jl:31-71` of DynamicExpressions.jl):
the filter sees the current heap. `isGraph` is `preserve_sharing` of the node type. -/
def sampleMState (fuel : Nat) (isGraph : Bool) (root : Addr) (F : SGraph T → Addr → Bool)
    (s : St T) : Jl Addr × St T :=
  let (r, rng') := Expressions.Sampling.rand
    { graph := s.g.view, root := root, fuel := fuel, filter := F s.g,
      preserveSharing := isGraph } s.rng
  (r, { s with rng := rng' })

def sampleM (fuel : Nat) (isGraph : Bool) (root : Addr) (F : SGraph T → Addr → Bool) :
    M T Addr := fun s =>
  let (r, after) := sampleMState fuel isGraph root F s
  r.map (fun a => (a, after))

/-- `any(f, tree)` (`src/base.jl:177-191` of DynamicExpressions.jl) for a pure predicate. -/
def anyM (D fuel : Nat) (root : Addr) (f : Addr → SCell T → Bool) : M T Bool :=
  onG (fun g => (Crossover.anyH (σ := Unit) g D (fun a c => pure (f a c)) fuel root).run' ())

/-- `options.nops[i]` on the `NTuple{D,Int}` of operator counts. -/
def nopsAt (nops : List Nat) (i : Nat) : Jl Nat :=
  if 1 ≤ i then
    match nops[i - 1]? with
    | some n => .ok n
    | none => .error .boundsError
  else .error .boundsError

/-! ## `random_node` and `swap_operands` -/

/-- `random_node(tree, rng; filter)` (`src/MutationFunctions.jl:72-80`). The deprecation
warning has no effect on the result. -/
def randomNode (fuel : Nat) (tree : Addr) (filter : SGraph T → Addr → Bool) : M T Addr :=
  sampleM fuel false tree filter

/-- The `i2` choice of `swap_operands` (`src/MutationFunctions.jl:95`). -/
def secondIdx (deg i1 : Nat) : M T Nat :=
  if deg = 2 then pure (if i1 = 1 then 2 else 1)
  else randElem ((List.range' 1 deg).filter (· ≠ i1))

/-- `swap_operands(tree, rng)` (`src/MutationFunctions.jl:88-101`). -/
def swapOperands (D fuel : Nat) (tree : Addr) (isGraph : Bool := false) : M T Addr := do
  let has ← anyM D fuel tree (fun _ c => decide (c.degree > 1))
  if !has then pure tree
  else do
    let node ← sampleM fuel isGraph tree (cellP (fun c => decide (c.degree > 1)))
    let c ← rd node
    let deg := c.degree
    let i1 ← randRange deg
    let i2 ← secondIdx deg i1
    let n1 ← getChildM D node i1
    let n2 ← getChildM D node i2
    setChildM D node n2 i1
    setChildM D node n1 i2
    pure tree

/-! ## `mutate_operator`, `mutate_constant`, `mutate_feature` -/

/-- `mutate_operator(tree, options, rng)` (`src/MutationFunctions.jl:111-120`). -/
def mutateOperator (fuel : Nat) (nops : List Nat) (tree : Addr)
    (isGraph : Bool := false) : M T Addr := do
  let rc ← rd tree
  if rc.degree = 0 then pure tree   -- `!(has_operators(tree))`
  else do
    let node ← sampleM fuel isGraph tree (cellP (fun c => c.degree != 0))
    let c ← rd node
    let n ← liftJ (nopsAt nops c.degree)
    let o ← randRange n
    setOpM node o
    pure tree

/-- `mutate_factor(T, temperature, m, rng)` (`src/MutationFunctions.jl:173-185`), with
`m.perturbation_factor = pert`, `m.probability_negate = pneg`, and `pw b r` the value of
`T(b^r)`. -/
def mutateFactor (pw : Rat → Rat → Rat) (pert temperature pneg : Rat) : M T Rat := do
  let bottom : Rat := 1 / 10
  let maxChange := pert * temperature + 1 + bottom
  let r ← randU
  let factor := pw maxChange r
  let makeConstBigger ← randBool
  let factor := if makeConstBigger then factor else 1 / factor
  let u ← randU
  pure (if u > pneg then -factor else factor)

/-- `mutate_value(rng, val::Number, temperature, m)` (`src/MutationFunctions.jl:167-171`);
`mul v f` is `val * f`. -/
def mutateValue (mul : T → Rat → T) (pw : Rat → Rat → Rat) (pert temperature pneg : Rat)
    (v : T) : M T T := do
  let f ← mutateFactor pw pert temperature pneg
  pure (mul v f)

/-- `_mutate_value(rng, val, temperature, m, options)` (`src/MutationFunctions.jl:151-165`):
both methods call `mutate_value`. -/
def mutateValue' (mul : T → Rat → T) (pw : Rat → Rat → Rat) (pert temperature pneg : Rat)
    (v : T) : M T T :=
  mutateValue mul pw pert temperature pneg v

/-- `mutate_constant(tree, temperature, options, m, rng)` (`src/MutationFunctions.jl:136-149`). -/
def mutateConstant (D fuel : Nat) (mul : T → Rat → T) (pw : Rat → Rat → Rat)
    (pert temperature pneg : Rat) (tree : Addr) : M T Addr := do
  let has ← anyM D fuel tree (fun _ c => c.degree == 0 && c.constant)   -- `has_constants`
  if !has then pure tree
  else do
    let node ← sampleM fuel false tree (cellP (fun c => c.degree == 0 && c.constant))
    let c ← rd node
    let v ← liftJ (match c.val with | some v => .ok v | none => .error .undefRefError)
    let v' ← mutateValue' mul pw pert temperature pneg v
    setValM node v'
    pure tree

-- Source: src/MutationFunctions.jl:196-206
/-
function mutate_feature(
    tree::AbstractExpressionNode{T}, nfeatures::Int, rng::AbstractRNG=default_rng()
) where {T<:DATA_TYPE}
    # Quick checks for if there is nothing to do
    nfeatures <= 1 && return tree
    !any(node -> node.degree == 0 && !node.constant, tree) && return tree

    node = rand(rng, NodeSampler(; tree, filter=t -> (t.degree == 0 && !t.constant)))
    node.feature = rand(rng, filter(!=(node.feature), 1:nfeatures))
    return tree
end
-/
def mutateFeature (D fuel : Nat) (nfeatures : Int) (tree : Addr)
    (isGraph : Bool := false) (s : St T) : Jl Addr × St T :=
  if nfeatures.toNat ≤ 1 then (.ok tree, s)
  else
    match anyM D fuel tree (fun _ c => c.degree == 0 && !c.constant) s with
    | .error e => (.error e, s)
    | .ok (false, after) => (.ok tree, after)
    | .ok (true, after) =>
      match sampleMState fuel isGraph tree (cellP (fun c => c.degree == 0 && !c.constant)) after with
      | (.error e, after) => (.error e, after)
      | (.ok node, after) =>
        match rd node after with
        | .error e => (.error e, after)
        | .ok (c, after) =>
          match randElem ((List.range' 1 nfeatures.toNat).filter (· ≠ c.feature)) after with
          | .error e => (.error e, after)
          | .ok (f, drawn) =>
            match setFeatureM node f drawn with
            | .error e => (.error e, drawn)
            | .ok (_, final) => (.ok tree, final)

/-! ## Leaves and new operator nodes -/

-- Source: src/MutationFunctions.jl:344-356; src/InterfaceDataTypes.jl:22-30
-- if rand(rng, Bool)
--     return constructorof(N)(T; val=sample_value(rng, T, options))
-- else
--     return constructorof(N)(T; feature=rand(rng, 1:nfeatures))
-- end
def makeRandomLeaf (D nfeatures : Nat) (sv : M T T) : M T Addr := do
  let b ← randBool
  if b then do
    let v ← sv
    ctorM D { val := some v }
  else do
    let f ← randRange nfeatures
    ctorM D { feature := some f }

/-- One-draw sampler used in deterministic lemmas and RNG fixtures. -/
def sampleReal (sv : Rat → T) : M T T := do
  let u ← randU
  pure (sv u)

/-- `Base.Cartesian.@ntuple(k, j -> make_random_leaf(...))`: `k` leaves, left to right. -/
def mkLeaves (D nfeatures : Nat) (sv : M T T) : Nat → M T (List Addr)
  | 0 => pure []
  | k + 1 => do
    let a ← makeRandomLeaf D nfeatures sv
    let as ← mkLeaves D nfeatures sv k
    pure (a :: as)

/-- `_sample_leaf(rng, tree)` (`src/MutationFunctions.jl:250`). -/
def sampleLeaf (fuel : Nat) (tree : Addr) : M T Addr :=
  sampleM fuel false tree (cellP (fun c => c.degree == 0))

/-- `sum(nops[1:i])`. -/
def psum (nops : List Nat) (i : Nat) : Nat := (nops.take i).sum

/-- The degree chosen by `Base.Cartesian.@nif(D, i -> scaled_rand > csum[i] &&
scaled_rand <= csum[i + 1], ...)` with `csum = (0, cumsum(options.nops)...)`
(`src/MutationFunctions.jl:232-244`): the first `i < D` whose condition holds, else `D`
(`@nif` evaluates its last branch unconditionally). -/
def pickDeg (D : Nat) (nops : List Nat) (x : Rat) : Nat :=
  ((List.range' 1 (D - 1)).find?
    (fun i => decide ((psum nops (i - 1) : Rat) < x ∧ x ≤ (psum nops i : Rat)))).getD D


-- A rounded nonfinite result cannot match any finite bucket; zero likewise selects the fallback.
-- Source: src/MutationFunctions.jl:234,275,321
-- scaled_rand = rand(rng) * last(csum)
def scaledDegreeDraw (u : Rat) (nops : List Nat) : Rat :=
  let round := SymReg.Loss.LossPrecision.round .float64
  match round (.fin u * round (.fin (nops.sum : Rat))) with
  | .fin q => q
  | _ => 0

example : scaledDegreeDraw (3002399751580331 / 9007199254740992) [1, 2] = 1 := by decide +kernel

/-- `constructorof(typeof(tree))(; op=rand(rng, 1:(options.nops[i])), children=@ntuple(i, j ->
make_random_leaf(nfeatures, T, typeof(tree), rng, options)))`, the operator node of degree `i`
built by `append_random_op` (`src/MutationFunctions.jl:238-243`) and `_make_node`
(`src/MutationFunctions.jl:436-441`): the operator draw, then the leaves, then the node. -/
def opNode (D nfeatures : Nat) (nops : List Nat) (sv : M T T) (i : Nat) : M T Addr := do
  let n ← liftJ (nopsAt nops i)
  let o ← randRange n
  let cs ← mkLeaves D nfeatures sv i
  ctorM D { op := some o, children := some cs }

/-- `append_random_op(tree, options, nfeatures, rng)` (`src/MutationFunctions.jl:222-249`). -/
def appendRandomOp (D fuel nfeatures : Nat) (nops : List Nat) (sv : M T T) (tree : Addr) :
    M T Addr := do
  let node ← sampleLeaf fuel tree
  if D ≠ nops.length then liftJ (.error (.assertionError "D == length(options.nops)"))
  else do
    let u ← randU
    let i := pickDeg D nops (scaledDegreeDraw u nops)
    let newnode ← opNode D nfeatures nops sv i
    setNodeM D node newnode
    pure tree

/-- `Base.Cartesian.@ntuple(i, j -> j == carry ? X : make_random_leaf(...))`
(`src/MutationFunctions.jl:281-288,328-335`): slot `j` runs `carryAct` when `j == carry`,
else draws a random leaf, left to right. -/
def kidsWith (D nfeatures : Nat) (sv : M T T) (carryAct : M T Addr) (carry : Nat) :
    Nat → Nat → M T (List Addr)
  | _, 0 => pure []
  | j, k + 1 => do
    let a ← if j = carry then carryAct else makeRandomLeaf D nfeatures sv
    let as ← kidsWith D nfeatures sv carryAct carry (j + 1) k
    pure (a :: as)

/-- The children tuple of `insert_random_op` (`src/MutationFunctions.jl:281-288`): slot `j`
is `copy(node)` when `j == arg_to_carry`, else a random leaf. -/
def insertKids (D fuel nfeatures : Nat) (sv : M T T) (node carry : Nat) : Nat → Nat → M T (List Addr) :=
  kidsWith D nfeatures sv (copyM D false fuel node) carry

/-- `insert_random_op(tree, options, nfeatures, rng)` (`src/MutationFunctions.jl:266-295`). -/
def insertRandomOp (D fuel nfeatures : Nat) (nops : List Nat) (sv : M T T) (tree : Addr) :
    M T Addr := do
  let node ← sampleM fuel false tree (fun _ _ => true)
  let u ← randU
  let i := pickDeg D nops (scaledDegreeDraw u nops)
  let carry ← randRange i
  let cs ← insertKids D fuel nfeatures sv node carry 1 i
  let n ← liftJ (nopsAt nops i)
  let o ← randRange n
  let newnode ← ctorM D { op := some o, children := some cs }
  setNodeM D node newnode
  pure tree

/-- The children tuple of `prepend_random_op` (`src/MutationFunctions.jl:328-335`): slot `j`
is the old root when `j == carry`, else a random leaf. -/
def prependKids (D nfeatures : Nat) (sv : M T T) (tree carry : Nat) : Nat → Nat → M T (List Addr) :=
  kidsWith D nfeatures sv (pure tree) carry

/-- `prepend_random_op(tree, options, nfeatures, rng)` (`src/MutationFunctions.jl:312-342`). -/
def prependRandomOp (D nfeatures : Nat) (nops : List Nat) (sv : M T T) (tree : Addr) :
    M T Addr := do
  if D ≠ nops.length then liftJ (.error (.assertionError "D == length(options.nops)"))
  else do
    let u ← randU
    let i := pickDeg D nops (scaledDegreeDraw u nops)
    let carry ← randRange i
    let cs ← prependKids D nfeatures sv tree carry 1 i
    let n ← liftJ (nopsAt nops i)
    let o ← randRange n
    ctorM D { op := some o, children := some cs }

/-! ## `delete_random_op!` -/

/-- `delete_random_op!(tree, rng)` (`src/MutationFunctions.jl:365-379`). -/
def deleteRandomOp (D fuel : Nat) (tree : Addr) : M T Addr := do
  let rc ← rd tree
  if rc.degree = 0 then pure tree
  else do
    let node ← sampleM fuel false tree (cellP (fun c => decide (c.degree > 0)))
    let c ← rd node
    let carryIdx ← randRange c.degree
    let carry ← getChildM D node carryIdx
    if node = tree then pure carry
    else do
      let (parent, idx) ← onG (fun g => Crossover.findParent g D fuel tree node)
      setChildM D parent carry idx
      pure tree

/-! ## Random trees -/

/-- `gen_random_tree(length, options, nfeatures, T, rng)` (`src/MutationFunctions.jl:407-421`):
a placeholder constant `init_value(T)` (`init`), then `length` calls of `append_random_op`. -/
def genRandomTree (D fuel nfeatures : Nat) (nops : List Nat) (sv : M T T) (init : T)
    (length : Nat) : M T Addr := do
  let tree ← ctorM D { val := some init }
  go tree length
where
  go (tree : Addr) : Nat → M T Addr
    | 0 => pure tree
    | k + 1 => do
      let tree ← appendRandomOp D fuel nfeatures nops sv tree
      go tree k

/-- The degree selected by `@nif(D, i -> arity == i, ...)` in `_make_node`
(`src/MutationFunctions.jl:433-442`): `arity` when `1 ≤ arity < D`, else `D`. -/
def nifArity (D arity : Nat) : Nat := if 1 ≤ arity ∧ arity < D then arity else D

/-- `_make_node(arity, proto, nfeatures, T, options, rng)` (`src/MutationFunctions.jl:423-445`). -/
def makeNode (D nfeatures : Nat) (nops : List Nat) (sv : M T T) (arity : Nat) : M T Addr :=
  opNode D nfeatures nops sv (nifArity D arity)

/-- The early-return loop `for k in 1:(limit - 1); acc += nops[k]; thresh <= acc && return k;
end; return limit` of `_arity_picker` (`src/MutationFunctions.jl:456-461`). -/
def arityScan (nops : List Nat) (thresh limit : Nat) : Nat :=
  ((List.range' 1 (limit - 1)).find? (fun k => decide (thresh ≤ psum nops k))).getD limit

/-- `_arity_picker(rng, remaining, nops)` (`src/MutationFunctions.jl:447-462`), with
`remaining : Int` and `D = length(nops)`. -/
def arityPicker (remaining : Int) (nops : List Nat) : M T Nat := do
  let limit := (min (nops.length : Int) remaining).toNat   -- `1:limit` is empty when `limit ≤ 0`
  let total := psum nops limit
  if total = 0 then pure 0
  else do
    let thresh ← randRange total
    pure (arityScan nops thresh limit)

/-- The `while true` loop of `gen_random_tree_fixed_size` (`src/MutationFunctions.jl:476-491`).
`steps` bounds the number of iterations; running out models nontermination. -/
def fixedSizeLoop (D fuel nfeatures : Nat) (nops : List Nat) (sv : M T T) (nodeCount : Int)
    (tree : Addr) : Nat → Int → M T Addr
  | 0, _ => liftJ (.error (.errorException "nonterminating loop"))
  | steps + 1, curSize => do
    let remaining := nodeCount - curSize
    if remaining = 0 then pure tree
    else do
      let arity ← arityPicker remaining nops
      if arity = 0 then pure tree
      else do
        let leaf ← sampleLeaf fuel tree
        let newnode ← makeNode D nfeatures nops sv arity
        setNodeM D leaf newnode
        fixedSizeLoop D fuel nfeatures nops sv nodeCount tree steps (curSize + arity)

/-- `gen_random_tree_fixed_size(node_count, options, nfeatures, T, rng)`
(`src/MutationFunctions.jl:464-494`). -/
def genRandomTreeFixedSize (D fuel nfeatures : Nat) (nops : List Nat) (sv : M T T)
    (nodeCount : Int) (steps : Nat) : M T Addr := do
  let tree ← makeRandomLeaf D nfeatures sv
  fixedSizeLoop D fuel nfeatures nops sv nodeCount tree steps 1

/-- `randomize_tree(tree, curmaxsize, options, nfeatures, rng)`
(`src/MutationFunctions.jl:395-404`): the input tree is ignored. -/
def randomizeTree (D fuel nfeatures : Nat) (nops : List Nat) (sv : M T T) (curmaxsize : Nat)
    (steps : Nat) (_tree : Addr) : M T Addr := do
  let n ← randRange curmaxsize
  genRandomTreeFixedSize D fuel nfeatures nops sv n steps

/-! ## Rotation -/

/-- `get_child(t, i).degree > 0`, false when the child cannot be read. -/
def childIsBranch (D : Nat) (g : SGraph T) (a : Addr) (i : Nat) : Bool :=
  match getChild g D a i with
  | .ok ch => cellP (fun c => decide (c.degree > 0)) g ch
  | .error _ => false

/-- `_valid_rotation_root(tree)` (`src/MutationFunctions.jl:617-619`). It is used as a
`count` and `NodeSampler` predicate, which the DynamicExpressions model takes as a pure
`Bool`; an unreadable child counts as not a branch (unreachable on well-formed trees). -/
def validRotationRoot (D : Nat) (g : SGraph T) (a : Addr) : Bool :=
  match g.cells a with
  | some c => decide (c.degree > 0) && (List.range' 1 c.degree).any (childIsBranch D g a)
  | none => false

/-- `[i for i in 1:(root.degree) if get_child(root, i).degree > 0]`
(`src/MutationFunctions.jl:643`). -/
def branchKids (D : Nat) (g : SGraph T) (root : Addr) (deg : Nat) : Jl (List Nat) :=
  (List.range' 1 deg).filterM (fun i => do
    let ch ← getChild g D root i
    let c ← g.read ch
    pure (decide (c.degree > 0)))

/-- `randomly_rotate_tree!(tree, rng)` (`src/MutationFunctions.jl:626-656`). `isGraph` is
`preserve_sharing` of the node type: `count(_valid_rotation_root, tree)` and `NodeSampler`
see each `GraphNode` object once. -/
def randomlyRotateTree (D fuel : Nat) (isGraph : Bool) (tree : Addr) : M T Addr := do
  let num ← onG (fun g => countH g D isGraph false (fun a _ => validRotationRoot D g a) 0 fuel tree)
  if num = 0 then pure tree
  else do
    let u ← randU
    let rotateAtRoot := decide (u < 1 / (num : Rat))
    let (parent, rootIdx, root) ← if rotateAtRoot then pure (tree, 0, tree)
      else do
        let r ← sampleM fuel isGraph tree (fun g a => decide (a ≠ tree) && validRotationRoot D g a)
        let (p, i) ← onG (fun g => Crossover.findParent g D fuel tree r)
        pure (p, i, r)
    let rc ← rd root
    let idxs ← onG (fun g => branchKids D g root rc.degree)
    let pivotIdx ← randElem idxs
    let pivot ← getChildM D root pivotIdx
    let pc ← rd pivot
    let gcIdx ← randRange pc.degree
    let grandChild ← getChildM D pivot gcIdx
    setChildM D root grandChild pivotIdx
    setChildM D pivot root gcIdx
    if rotateAtRoot then pure pivot
    else do
      setChildM D parent pivot rootIdx
      pure tree

/-! ## Connections -/

def tryConnectionPairs (D fuel : Nat) (isGraph : Bool) (tree : Addr) :
    Nat → M T (Addr × Addr × Bool)
  | 0 => pure (tree, tree, true)
  | k + 1 => do
    let parent ← sampleM fuel isGraph tree (cellP (fun c => c.degree != 0))
    let newChild ← sampleM fuel isGraph tree (fun _ a => decide (a ≠ tree))
    let wouldFormLoop ← anyM D fuel newChild (fun a _ => decide (a = parent))
    if !wouldFormLoop then pure (parent, newChild, false)
    else tryConnectionPairs D fuel isGraph tree k

-- Source: src/MutationFunctions.jl:543-554
/-
function get_two_nodes_without_loop(tree::AbstractNode, rng::AbstractRNG; max_attempts=10)
    for _ in 1:max_attempts
        parent = rand(rng, NodeSampler(; tree, filter=t -> t.degree != 0))
        new_child = rand(rng, NodeSampler(; tree, filter=t -> t !== tree))

        would_form_loop = any(t -> t === parent, new_child)
        if !would_form_loop
            return (parent, new_child, false)
        end
    end
    return (tree, tree, true)
end
-/
def getTwoNodesWithoutLoop (D fuel : Nat) (isGraph : Bool) (tree : Addr)
    (maxAttempts : Int) : M T (Addr × Addr × Bool) :=
  tryConnectionPairs D fuel isGraph tree maxAttempts.toNat

/-- `form_random_connection!(tree, rng)` (`src/MutationFunctions.jl:560-574`), with the default
`max_attempts = 10`. -/
def formRandomConnection (D fuel : Nat) (isGraph : Bool) (tree : Addr) : M T Addr := do
  let len ← onG (fun g => lengthH g D isGraph fuel tree)
  if len < 5 then pure tree
  else do
    let (parent, newChild, wouldFormLoop) ← getTwoNodesWithoutLoop D fuel isGraph tree 10
    if wouldFormLoop then pure tree
    else do
      let pc ← rd parent
      let i ← randRange pc.degree
      setChildM D parent newChild i
      pure tree

-- Source: src/MutationFunctions.jl:580-586
-- tree.degree == 0 && return tree
-- parent = rand(rng, NodeSampler(; tree, filter=t -> t.degree != 0))
-- i = rand(rng, 1:(parent.degree))
-- set_child!(parent, copy(get_child(parent, i)), i)
-- return tree
def breakRandomConnection (D fuel : Nat) (isGraph : Bool) (tree : Addr)
    (copyValue : Option (T → StateT (SGraph T) Jl T)) : M T Addr := do
  let rc ← rd tree
  if rc.degree = 0 then pure tree
  else do
    let parent ← sampleM fuel isGraph tree (cellP (fun c => c.degree != 0))
    let pc ← rd parent
    let i ← randRange pc.degree
    let ch ← getChildM D parent i
    let cp ← match copyValue with
      | none => copyM D isGraph fuel ch
      | some cv => liftG (fun g => copyNodeVH cv g D isGraph false fuel ch)
    setChildM D parent cp i
    pure tree

/-! ## Backsolve -/

/-- The parts of `backsolve_rewrite_random_node` that live in other modules, as arbitrary
functions of the heap: `eval_inverse_tree_array_masked` (`invert g tree node`, the target
values and validity mask), `compute_complexity` (`cx`), and `fit_sparse_expression` (`fit`,
which receives the node to invert, targets, mask and `max_complexity = budget`, may allocate,
and returns the new node or `nothing`). -/
structure BacksolveOps (T : Type) where
  invert : SGraph T → Addr → Addr → List T × List Bool
  cx : SGraph T → Addr → Jl Int
  fit : SGraph T → Addr → List T → List Bool → Int → Jl (Option Addr × SGraph T)

/-- `backsolve_rewrite_random_node(tree::AbstractExpressionNode, dataset, options, rng; ...)`
(`src/MutationFunctions.jl:703-754`); `isFloat` is `T <: Union{AbstractFloat,Complex}`. -/
def backsolveRewriteRandomNode (D fuel : Nat) (ops : BacksolveOps T) (isFloat : Bool)
    (curmaxsize : Int) (tree : Addr) : M T Addr := do
  if !isFloat then
    liftJ (.error (.argumentError "backsolve_rewrite_random_node only supports floating-point scalar types"))
  else do
    let rc ← rd tree
    if rc.degree = 0 then pure tree
    else do
      let node ← sampleM fuel false tree (fun _ a => decide (a ≠ tree))
      let (targets, mask) ← onG (fun g => pure (ops.invert g tree node))
      if mask.count true < min 10 targets.length then pure tree
      else do
        let ct ← onG (fun g => ops.cx g tree)
        let cn ← onG (fun g => ops.cx g node)
        let budget := curmaxsize - (ct - cn)
        if budget < 1 then pure tree
        else do
          let r ← liftG (fun g => ops.fit g node targets mask budget)
          match r with
          | none => pure tree
          | some newNode => do
            let (parent, idx) ← onG (fun g => Crossover.findParent g D fuel tree node)
            setChildM D parent newNode idx
            pure tree


end SymReg.Mutations
