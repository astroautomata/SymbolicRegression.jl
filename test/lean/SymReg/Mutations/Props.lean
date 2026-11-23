import SymReg.Mutations.Core

/-!
Specification helpers and the properties of the mutations of `src/MutationFunctions.jl`.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.Crossover

variable {T : Type}

/-! ## Specification helpers -/

/-- Operator count of degree `d`, `options.nops[d]`; zero out of range. -/
def opsOf (nops : List Nat) (d : Nat) : Nat := (nops[d - 1]?).getD 0

/-- Preorder indices of the nodes of `t` satisfying `P`. -/
def eligT (P : Tree T → Bool) (t : Tree T) : List Nat :=
  eligIdx t.size (fun k => ((preorder t)[k]?).any P)

/-- The element of `xs` selected by the index draw at cursor `c`. -/
def drawAt (rng : RNG) (c : Nat) (xs : List Nat) : Nat :=
  (xs[(rng.indexDraws (xs.length - 1) c).val]?).getD 0

/-- `rand(rng, 1:n)` at cursor `c`. -/
def rangeAt (rng : RNG) (c n : Nat) : Nat := (rng.indexDraws (n - 1) c).val + 1

/-- Node predicates. -/
def isBranchT (s : Tree T) : Bool := s.degree != 0
def isConstT : Tree T → Bool
  | .const _ => true
  | _ => false
def isFeatureT : Tree T → Bool
  | .feature _ => true
  | _ => false

/-- A branch with a new operator. -/
def withOp (o : Nat) : Tree T → Tree T
  | .branch _ cs => .branch o cs
  | t => t

/-! ## `mutate_operator` -/

/-- `mutate_operator(tree, options, rng)` on an alias-free well-formed plain `Node` tree
returns the same root object. A leaf root is returned untouched, with no draw. Otherwise the
first draw selects the `k`-th branch node in preorder (uniformly among branch nodes), the
second an operator `o` uniformly in `1:nops[degree]`, and the result is the input tree with
that node's operator replaced by `o`; children, every other node, and well-formedness are
kept. -/
def mutate_operator_unshared : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (nops : List Nat) (t : Tree T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree →
    nops.length = D → (∀ n ∈ nops, n ≤ 255) → t.WF D (opsOf nops) 65535 →
    ∃ g' rng', mutateOperator fuel nops tree false ⟨g, rng⟩ = .ok (tree, ⟨g', rng'⟩) ∧
      (t.degree = 0 → g' = g ∧ rng' = rng) ∧
      (t.degree ≠ 0 →
        ∃ u, (preorder t)[drawAt rng rng.cursor (eligT isBranchT t)]? = some u ∧
          Graph.unfold g'.view (fuel + fuel) tree =
            some (replaceAt t (drawAt rng rng.cursor (eligT isBranchT t))
              (withOp (rangeAt rng (rng.cursor + 1) (opsOf nops u.degree)) u)) ∧
          (replaceAt t (drawAt rng rng.cursor (eligT isBranchT t))
              (withOp (rangeAt rng (rng.cursor + 1) (opsOf nops u.degree)) u)).WF D
            (opsOf nops) 65535 ∧
          rng'.cursor = rng.cursor + 2)

def mutate_operator_spec : Prop := mutate_operator_unshared ∧
  ∀ (T : Type) (s : St T) (fuel tree : Nat) (nops : List Nat) (isGraph : Bool)
    (root : SCell T), s.g.cells tree = some root →
    (root.degree = 0 → mutateOperator fuel nops tree isGraph s = .ok (tree, s)) ∧
    (∀ x (c : SCell T), root.degree ≠ 0 →
      sampleM fuel isGraph tree (cellP (fun c => c.degree != 0)) s =
        .ok (x, { s with rng := adv s.rng }) →
      s.g.cells x = some c →
      match nopsAt nops c.degree with
      | .error e => mutateOperator fuel nops tree isGraph s = .error e
      | .ok 0 => mutateOperator fuel nops tree isGraph s =
          .error (.argumentError "collection must be non-empty")
      | .ok (n + 1) =>
        let o := rangeAt s.rng (s.rng.cursor + 1) (n + 1)
        1 ≤ o ∧ o ≤ n + 1 ∧
        if o ≤ 255 then
          ∃ g', mutateOperator fuel nops tree isGraph s =
              .ok (tree, ⟨g', adv (adv s.rng)⟩) ∧
            g'.next = s.g.next ∧ g'.cells x = some { c with op := o } ∧
            ∀ y, y ≠ x → g'.cells y = s.g.cells y
        else mutateOperator fuel nops tree isGraph s =
          .error (.errorException "InexactError: trunc(UInt8, op)"))

/-- `mutate_operator` ("Randomly convert an operator into another one",
`src/MutationFunctions.jl:103`) changes the operator of the node it mutates whenever every
degree has at least two operators to choose from. -/
def mutate_operator_changes : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (nops : List Nat) (t : Tree T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree →
    nops.length = D → (∀ n ∈ nops, 2 ≤ n ∧ n ≤ 255) → t.WF D (opsOf nops) 65535 →
    t.degree ≠ 0 →
    ∃ g' rng', mutateOperator fuel nops tree false ⟨g, rng⟩ = .ok (tree, ⟨g', rng'⟩) ∧
      ∀ t', Graph.unfold g'.view (fuel + fuel) tree = some t' →
        ((preorder t')[drawAt rng rng.cursor (eligT isBranchT t)]?).map opOf ≠
          ((preorder t)[drawAt rng rng.cursor (eligT isBranchT t)]?).map opOf

/-! ## `mutate_constant`, `mutate_value`, `mutate_factor` -/

/-- The factor of `mutate_factor` from the three draws at cursors `c`, `c + 1`, `c + 2`. -/
def factorAt (pw : Rat → Rat → Rat) (pert temperature pneg : Rat) (rng : RNG) (c : Nat) : Rat :=
  let fac := pw (pert * temperature + 1 + 1 / 10) (rng.draws c)
  let bigger : Bool := (rng.indexDraws 1 (c + 1)).val = 1
  let fac := if bigger then fac else 1 / fac
  if rng.draws (c + 2) > pneg then -fac else fac

/-- A constant leaf with its value multiplied by `f`. -/
def scaleConst (mul : T → Rat → T) (f : Rat) : Tree T → Tree T
  | .const v => .const (mul v f)
  | t => t

/-- `mutate_constant(tree, temperature, options, m, rng)` on an alias-free plain `Node` tree
returns the same root object. Without constant leaves the heap and the stream are untouched.
Otherwise the first draw selects the `k`-th constant leaf in preorder, the next three draws
give the factor of `mutate_factor`, and the result is the input tree with exactly that
constant multiplied by the factor (`mutate_value`). -/
def mutate_constant_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (rng : RNG) (mul : T → Rat → T)
    (pw : Rat → Rat → Rat) (pert temperature pneg : Rat),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree → DegLe D t →
    ∃ g' rng', mutateConstant D fuel mul pw pert temperature pneg tree ⟨g, rng⟩ =
        .ok (tree, ⟨g', rng'⟩) ∧
      ((preorder t).any isConstT = false → g' = g ∧ rng' = rng) ∧
      ((preorder t).any isConstT = true →
        Graph.unfold g'.view (fuel + fuel) tree =
          some (modifyAt t (drawAt rng rng.cursor (eligT isConstT t))
            (scaleConst mul (factorAt pw pert temperature pneg rng (rng.cursor + 1)))) ∧
        rng'.cursor = rng.cursor + 4)

/-- `mutate_factor` negates the factor with probability `m.probability_negate`
("`probability_negate` is the chance of flipping the constant's sign", `src/Mutations.jl:38`):
for draws in `[0, 1)` and a positive magnitude, the factor is negative exactly when the
negation draw falls below `probability_negate`. -/
def mutate_factor_negate : Prop :=
  ∀ (T : Type) (pw : Rat → Rat → Rat) (pert temperature pneg : Rat) (s : St T),
    (∀ b r, 0 < b → 0 < pw b r) → 0 ≤ pert → 0 ≤ temperature → 0 ≤ pneg → pneg ≤ 1 →
    (∀ i, 0 ≤ s.rng.draws i ∧ s.rng.draws i < 1) →
    ∃ f s', mutateFactor pw pert temperature pneg s = .ok (f, s') ∧
      (f < 0 ↔ s.rng.draws (s.rng.cursor + 2) < pneg)

/-! ## `mutate_feature` -/

/-- `filter(!=(f), 1:nfeatures)`. -/
def featureChoices (nf f : Nat) : List Nat := (List.range' 1 nf).filter (· ≠ f)

/-- `mutate_feature(tree, nfeatures, rng)` on an alias-free plain `Node` tree returns the same
root object. With `nfeatures ≤ 1` or no feature leaf, nothing changes and nothing is drawn.
Otherwise the first draw selects the `k`-th feature leaf in preorder and the second a feature
`f'` uniformly among `1:nfeatures` without the current one; the result is the input tree with
exactly that leaf's feature replaced by `f'`, which differs from the old feature. -/
def mutate_feature_unshared : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf tree : Nat) (t : Tree T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree → DegLe D t →
    nf ≤ 65535 →
    ∃ g' rng', mutateFeature D fuel nf tree false ⟨g, rng⟩ = (.ok tree, ⟨g', rng'⟩) ∧
      ((nf ≤ 1 ∨ (preorder t).any isFeatureT = false) → g' = g ∧ rng' = rng) ∧
      (2 ≤ nf → (preorder t).any isFeatureT = true →
        ∃ f0, (preorder t)[drawAt rng rng.cursor (eligT isFeatureT t)]? = some (.feature f0) ∧
          drawAt rng (rng.cursor + 1) (featureChoices nf f0) ≠ f0 ∧
          1 ≤ drawAt rng (rng.cursor + 1) (featureChoices nf f0) ∧
          drawAt rng (rng.cursor + 1) (featureChoices nf f0) ≤ nf ∧
          Graph.unfold g'.view (fuel + fuel) tree =
            some (replaceAt t (drawAt rng rng.cursor (eligT isFeatureT t))
              (.feature (drawAt rng (rng.cursor + 1) (featureChoices nf f0)))) ∧
          rng'.cursor = rng.cursor + 2)

def mutate_feature_spec : Prop := mutate_feature_unshared ∧
  ∀ (T : Type) (s : St T) (D fuel tree : Nat) (nf : Int) (isGraph : Bool),
    (nf ≤ 1 → mutateFeature D fuel nf tree isGraph s = (.ok tree, s)) ∧
    (1 < nf →
      anyM D fuel tree (fun _ c => c.degree == 0 && !c.constant) s = .ok (false, s) →
      mutateFeature D fuel nf tree isGraph s = (.ok tree, s)) ∧
    (∀ x (c : SCell T), 1 < nf →
      anyM D fuel tree (fun _ c => c.degree == 0 && !c.constant) s = .ok (true, s) →
      sampleM fuel isGraph tree (cellP (fun c => c.degree == 0 && !c.constant)) s =
        .ok (x, { s with rng := adv s.rng }) →
      s.g.cells x = some c →
      let f := drawAt s.rng (s.rng.cursor + 1) (featureChoices nf.toNat c.feature)
      f ≠ c.feature ∧ 1 ≤ f ∧ f ≤ nf.toNat ∧
      (if f ≤ 65535 then
        ∃ g', mutateFeature D fuel nf tree isGraph s =
            (.ok tree, ⟨g', adv (adv s.rng)⟩) ∧
          g'.next = s.g.next ∧ g'.cells x = some { c with feature := f } ∧
          ∀ y, y ≠ x → g'.cells y = s.g.cells y
       else mutateFeature D fuel nf tree isGraph s =
         (.error .inexactError, { s with rng := adv (adv s.rng) })))

/-! ## `swap_operands` -/

/-- Nodes with at least two children. -/
def isMultiT (s : Tree T) : Bool := decide (s.degree > 1)

/-- Swap children `i` and `j` (one-based) of a branch. -/
def swapKids (i j : Nat) : Tree T → Tree T
  | .branch o cs =>
    .branch o ((cs.set (i - 1) ((cs[j - 1]?).getD (.feature 0))).set (j - 1)
      ((cs[i - 1]?).getD (.feature 0)))
  | t => t

/-- The `i2` of `swap_operands` at cursor `c`. -/
def secondAt (rng : RNG) (c deg i1 : Nat) : Nat :=
  if deg = 2 then (if i1 = 1 then 2 else 1)
  else drawAt rng c ((List.range' 1 deg).filter (· ≠ i1))

/-- `swap_operands(tree, rng)` on an alias-free plain `Node` tree returns the same root
object. Without a node of degree at least two nothing changes and nothing is drawn.
Otherwise the first draw selects the `k`-th such node in preorder, the next draws two distinct
argument positions `i1 ≠ i2` of it, and the result is the input tree with exactly those two
children of that node exchanged. -/
def swap_operands_unshared : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree → DegLe D t →
    SlotsLe D 0 g →
    ∃ g' rng', swapOperands D fuel tree false ⟨g, rng⟩ = .ok (tree, ⟨g', rng'⟩) ∧
      ((preorder t).any isMultiT = false → g' = g ∧ rng' = rng) ∧
      ((preorder t).any isMultiT = true →
        ∃ u, (preorder t)[drawAt rng rng.cursor (eligT isMultiT t)]? = some u ∧
          rangeAt rng (rng.cursor + 1) u.degree ≠
            secondAt rng (rng.cursor + 2) u.degree (rangeAt rng (rng.cursor + 1) u.degree) ∧
          1 ≤ secondAt rng (rng.cursor + 2) u.degree (rangeAt rng (rng.cursor + 1) u.degree) ∧
          secondAt rng (rng.cursor + 2) u.degree (rangeAt rng (rng.cursor + 1) u.degree) ≤
            u.degree ∧
          Graph.unfold g'.view (fuel + fuel) tree =
            some (replaceAt t (drawAt rng rng.cursor (eligT isMultiT t))
              (swapKids (rangeAt rng (rng.cursor + 1) u.degree)
                (secondAt rng (rng.cursor + 2) u.degree (rangeAt rng (rng.cursor + 1) u.degree))
                u)))

def swap_operands_spec : Prop := swap_operands_unshared ∧
  ∀ (T : Type) (s : St T) (D fuel tree : Nat) (isGraph : Bool),
    let p := fun (c : SCell T) => decide (c.degree > 1)
    (anyM D fuel tree (fun _ c => p c) s = .ok (false, s) →
      swapOperands D fuel tree isGraph s = .ok (tree, s)) ∧
    (∀ x (c : SCell T), anyM D fuel tree (fun _ c => p c) s = .ok (true, s) →
      sampleM fuel isGraph tree (cellP p) s = .ok (x, { s with rng := adv s.rng }) →
      s.g.cells x = some c → 2 ≤ c.degree → c.degree ≤ D → c.active.length = c.degree →
      (∀ slots, c.slots = some slots → slots.length ≤ D) →
      let i := rangeAt s.rng (s.rng.cursor + 1) c.degree
      let j := secondAt s.rng (s.rng.cursor + 2) c.degree i
      ∃ g' c',
        swapOperands D fuel tree isGraph s =
          .ok (tree, ⟨g', if c.degree = 2 then adv (adv s.rng) else adv (adv (adv s.rng))⟩) ∧
        g'.next = s.g.next ∧ (∀ a, a ≠ x → g'.cells a = s.g.cells a) ∧
        g'.cells x = some c' ∧ c'.degree = c.degree ∧ c'.op = c.op ∧
        c'.val = c.val ∧ c'.feature = c.feature ∧ c'.constant = c.constant ∧
        c'.active = (c.active.set (i - 1) (c.active[j - 1]?.getD 0)).set
          (j - 1) (c.active[i - 1]?.getD 0))

/-! ## `randomly_rotate_tree!` -/

/-- `randomly_rotate_tree!(tree, rng)` on a finite acyclic `GraphNode` tree (shared subtrees
allowed, as produced by `form_random_connection!`) returns a root from which the heap is still
acyclic, so the rotated expression is finite. -/
def rotate_graph_acyclic : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (rng : RNG) (r : Addr) (s' : St T),
    Graph.unfold g.view fuel tree = some t → DegLe D t →
    randomlyRotateTree D fuel true tree ⟨g, rng⟩ = .ok (r, s') →
    Graph.Acyclic s'.g.view r

end SymReg.Mutations
