import DynExpr.NodeBase.TraverseCopy
import DynExpr.Expressions.Sampling
import SymReg.HeapLemmas

/-!
Model of `crossover_trees(tree1::N, tree2::N, rng)` (`src/MutationFunctions.jl:510-541`,
SymbolicRegression.jl `upstream/master` daae84e5) for plain `Node` trees, on the node heap
of the DynamicExpressions formalization, together with `_random_node_and_parent` and
`_find_parent` (`src/MutationFunctions.jl:589-615`).

`copy` on a node is `copy_node` (`src/base.jl:520-522` of DynamicExpressions.jl), modelled
by `DynExpr.NodeBase.copyNodeH`; `rand(rng, NodeSampler(; tree))` is
`DynExpr.Expressions.Sampling.rand`, whose `RNG` is an arbitrary stream of index draws.
-/

namespace SymReg.Crossover
open DynExpr DynExpr.NodeBase

variable {T σ : Type}

/-- `any(f, tree)` with early exit (`src/base.jl:177-191` of DynamicExpressions.jl) on the
heap, for a predicate with state (the `Ref` written by `_find_parent`): the node first,
then, through `get_children`, its children left to right. Fuel bounds the recursion depth;
running out models a stack overflow. -/
def anyH (g : SGraph T) (D : Nat) (f : Addr → SCell T → StateT σ Jl Bool) :
    Nat → Addr → StateT σ Jl Bool
  | 0, _ => throw (.errorException "StackOverflowError")
  | fuel + 1, a => do
    let c ← StateT.lift (g.read a)
    if c.degree = 0 then f a c
    else if ← f a c then pure true
    else do
      let cs ← StateT.lift (getChildren g D a (nifDeg D c.degree))
      cs.anyM (fun x => anyH g D f fuel x)

/-- The `for i in 1:(t.degree)` loop of `_find_parent` (`src/MutationFunctions.jl:604-609`):
the first slot `i` whose child is `node` is stored in the `Ref`. -/
def scanChildren (g : SGraph T) (D : Nat) (node a : Addr) :
    List Nat → StateT (Option (Addr × Nat)) Jl Bool
  | [] => pure false
  | i :: is => do
    let ch ← StateT.lift (getChild g D a i)
    if ch = node then
      set (some (a, i))
      pure true
    else scanChildren g D node a is

/-- The predicate of `_find_parent` (`src/MutationFunctions.jl:602-612`). -/
def parentPred (g : SGraph T) (D : Nat) (node : Addr) (a : Addr) (c : SCell T) :
    StateT (Option (Addr × Nat)) Jl Bool :=
  if c.degree > 0 then scanChildren g D node a (List.range' 1 c.degree) else pure false

/-- `_find_parent(tree, node)` (`src/MutationFunctions.jl:600-615`). Reading the unset
`Ref` is an `UndefRefError`. -/
def findParent (g : SGraph T) (D fuel : Nat) (tree node : Addr) : Jl (Addr × Nat) := do
  let (finished, r) ← (anyH g D (parentPred g D node) fuel tree).run none
  if !finished then throw (.assertionError "finished")
  match r with
  | some p => pure p
  | none => throw .undefRefError

/-- `rand(rng, NodeSampler(; tree))` for a plain `Node` (`src/Random.jl:45-59` of
DynamicExpressions.jl). -/
def sampleNode (g : SGraph T) (fuel : Nat) (tree : Addr) (rng : Expressions.Sampling.RNG) :
    Jl Addr × Expressions.Sampling.RNG :=
  Expressions.Sampling.rand { graph := g.view, root := tree, fuel := fuel } rng

/-- `_random_node_and_parent(tree, rng)` (`src/MutationFunctions.jl:589-599`). -/
def randomNodeAndParent (g : SGraph T) (D fuel : Nat) (tree : Addr)
    (rng : Expressions.Sampling.RNG) : Jl (Addr × Addr × Nat) × Expressions.Sampling.RNG :=
  let (r, rng') := sampleNode g fuel tree rng
  match r with
  | .error e => (.error e, rng')
  | .ok node =>
    if node = tree then (.ok (node, node, 0), rng')
    else ((findParent g D fuel tree node).map (fun pi => (node, pi.1, pi.2)), rng')

/-- `crossover_trees(tree1, tree2, rng)` on plain `Node` trees (`src/MutationFunctions.jl:510-541`).
Returns the two children and the final heap. -/
def crossoverTrees (g : SGraph T) (D fuel : Nat) (tree1 tree2 : Addr)
    (rng : Expressions.Sampling.RNG) : Jl (Addr × Addr × SGraph T) := do
  if tree1 = tree2 then throw (.errorException "Attempted to crossover the same tree!")
  let (t1, h1) ← copyNodeH g D false false fuel tree1
  let (t2, h2) ← copyNodeH h1 D false false fuel tree2
  let (r1, rng1) := randomNodeAndParent h2 D fuel t1 rng
  let (n1, p1, i1) ← r1
  let (r2, _) := randomNodeAndParent h2 D fuel t2 rng1
  let (n2, p2, i2) ← r2
  let (n1', h3) ← copyNodeH h2 D false false fuel n1
  let (t1', h4) ← if i1 = 0 then copyNodeH h3 D false false fuel n2
    else do
      let (c2, h) ← copyNodeH h3 D false false fuel n2
      let (_, h') ← setChild h D p1 c2 i1
      pure (t1, h')
  let (t2', h5) ← if i2 = 0 then pure (n1', h4)
    else do
      let (_, h') ← setChild h4 D p2 n1' i2
      pure (t2, h')
  pure (t1', t2', h5)

/-! ## Specification -/

mutual
  /-- Replace the node at preorder index `k` (`DynExpr.NodeBase.preorder`) by `s`. -/
  def replaceAt : Tree T → Nat → Tree T → Tree T
    | _, 0, s => s
    | .branch o cs, k + 1, s => .branch o (replaceF cs k s)
    | t, _ + 1, _ => t
  /-- `replaceAt` on the concatenated preorders of a list of children. -/
  def replaceF : List (Tree T) → Nat → Tree T → List (Tree T)
    | [], _, _ => []
    | c :: cs, k, s =>
      if k < (preorder c).length then replaceAt c k s :: cs
      else c :: replaceF cs (k - (preorder c).length) s
end

/-! ## Property -/

/-- `crossover_trees` on two distinct well-formed plain `Node` trees swaps exactly the two
sampled subtrees: with `k1` and `k2` the preorder indices drawn by the two `rand` calls,
the first child is the first parent with its `k1`-th node replaced by the second parent's
`k2`-th subtree, and symmetrically. Both parents, and every other existing object, are left
unchanged, and the children consist of newly allocated objects only. -/
def crossover_swap : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree1 tree2 : Nat) (s1 s2 : Tree T)
    (rng : Expressions.Sampling.RNG),
    tree1 ≠ tree2 →
    Graph.unfold g.view fuel tree1 = some s1 → Graph.unfold g.view fuel tree2 = some s2 →
    s1.WF D (fun _ => 255) 65535 → s2.WF D (fun _ => 255) 65535 →
    ∃ (o1 o2 : Addr) (h : SGraph T) (u1 u2 : Tree T) (f : Nat),
      crossoverTrees g D fuel tree1 tree2 rng = .ok (o1, o2, h) ∧
      (preorder s1)[(rng.indexDraws (s1.size - 1) rng.cursor).val]? = some u1 ∧
      (preorder s2)[(rng.indexDraws (s2.size - 1) (rng.cursor + 1)).val]? = some u2 ∧
      (∀ a, a < g.next → h.cells a = g.cells a) ∧
      Graph.unfold h.view f o1 = some (replaceAt s1 (rng.indexDraws (s1.size - 1) rng.cursor).val u2) ∧
      Graph.unfold h.view f o2 = some (replaceAt s2 (rng.indexDraws (s2.size - 1) (rng.cursor + 1)).val u1) ∧
      (∀ b, Graph.Reachable h.view o1 b → g.next ≤ b) ∧
      (∀ b, Graph.Reachable h.view o2 b → g.next ≤ b)

end SymReg.Crossover
