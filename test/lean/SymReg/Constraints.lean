import SymReg.Complexity

/-!
Model of `check_constraints` (`src/CheckConstraints.jl`, SymbolicRegression.jl
`upstream/master` daae84e5) on plain `Node` trees, which are modelled as pure `Tree`s
(no mutation, no identity caches on `Node`). The complexity of a (sub)tree is the pure
mirror `computeComplexityT` of `src/Complexity.jl`.
-/

namespace SymReg.Constraints
open DynExpr DynExpr.NodeBase SymReg.Complexity SymReg.HeapLemmas

variable {T : Type}

/-- The fields of `Options` read by `check_constraints` (`src/OptionsStruct.jl:199-200`):
`complexity_mapping` (a `ComplexityMapping`, not a user function), `maxdepth`,
`op_constraints` (`opCons[d-1][o-1]` is the `NTuple{d,Int}` of per-argument complexity
limits of operator `o` of degree `d`, `-1` meaning unconstrained; a degree-1 entry is
the `Int` itself, modelled as a one-element tuple), and `nested_constraints` as built by
`build_nested_constraints` (`src/Options.jl:106-180`): a list of
`(degree, op_idx, [(nested_degree, nested_op_idx, max_nestedness)])`. -/
structure Opts where
  cmap : CMap
  maxdepth : Int
  opCons : List (List (List Int))
  nested : Option (List (Nat × Nat × List (Nat × Nat × Int)))

/-- Short-circuiting `any(f, xs)` over a collection with a throwing predicate. -/
def anyListM {α : Type} (f : α → Jl Bool) : List α → Jl Bool
  | [] => pure false
  | x :: xs => do if ← f x then pure true else anyListM f xs

mutual
  /-- `any(f, tree)` with early exit (`src/base.jl:177-191` of DynamicExpressions.jl), for
  a predicate that may throw: the node first, then the children left to right. -/
  def anyM (D : Nat) (f : Tree T → Jl Bool) : Tree T → Jl Bool
    | .const v => f (.const v)
    | .feature i => f (.feature i)
    | .branch o cs =>
      if cs.length = 0 then f (.branch o cs)
      else do if ← f (.branch o cs) then pure true else anyMF D f (nifDeg D cs.length) cs
  /-- The `@nany` over the first `k` children (`src/base.jl:186`). -/
  def anyMF (D : Nat) (f : Tree T → Jl Bool) : Nat → List (Tree T) → Jl Bool
    | 0, _ => pure false
    | _ + 1, [] => pure false
    | k + 1, c :: cs => do if ← anyM D f c then pure true else anyMF D f k cs
end

/-- The children of a node. -/
def kids : Tree T → List (Tree T)
  | .branch _ cs => cs
  | _ => []

/-- `get_child(node, i)` (`src/Node.jl:213-215` of DynamicExpressions.jl). -/
def getChildT (t : Tree T) (i : Nat) : Jl (Tree T) :=
  match (if 1 ≤ i then (kids t)[i - 1]? else none) with
  | some c => pure c
  | none => throw .boundsError

/-- `max(c...)` over the child results; branches always have children. -/
def maxList : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

/-- `past_complexity_limit(tree, options, limit)` (`src/Complexity.jl:7-11`). -/
def pastLimit (D : Nat) (o : Opts) (t : Tree T) (limit : Int) : Jl Bool := do
  let c ← computeComplexityT D o.cmap t
  pure (decide (c > limit))

/-- `_check_operator_constraints(node, degree, cons, options)` (`src/CheckConstraints.jl:24-32`). -/
def checkOpCons (D : Nat) (o : Opts) (node : Tree T) (degree : Nat) (cons : List Int) : Jl Bool := do
  if degree = 0 then throw (.assertionError "degree != 0")
  anyListM (fun i => do
    let ci ← match cons[i - 1]? with
      | some ci => pure ci
      | none => throw .boundsError
    if ci ≠ -1 then
      let child ← getChildT node i
      pastLimit D o child ci
    else pure false) (List.range' 1 degree)

/-- `flag_operator_complexity(tree, degree, op, cons, options)` (`src/CheckConstraints.jl:14-22`). -/
def flagOpComplexity (D : Nat) (o : Opts) (t : Tree T) (degree op : Nat) (cons : List Int) :
    Jl Bool :=
  anyM D (fun s => if s.degree = degree ∧ opOf s = op then checkOpCons D o s degree cons
    else pure false) t

/-- `count_max_nestedness(tree, degree, op)` (`src/CheckConstraints.jl:34-46`):
`tree_mapreduce` with `0` at leaves, `1` at matching branches and `p + max(c...)`, minus
one when the root itself matches. -/
def countMaxNestedness (D : Nat) (t : Tree T) (degree op : Nat) : Int :=
  let nestedness := Id.run (tmrT D (fun _ => pure (0 : Int))
    (fun s => pure (if s.degree = degree ∧ opOf s = op then (1 : Int) else 0))
    (fun p cs => pure (p + maxList cs)) t)
  nestedness - (if t.degree = degree ∧ opOf t = op then 1 else 0)

/-- `flag_illegal_nests(tree, options)` (`src/CheckConstraints.jl:48-63`). -/
def flagIllegalNests (D : Nat) (o : Opts) (t : Tree T) : Bool :=
  match o.nested with
  | none => false
  | some ncs => anyT D (fun s => ncs.any (fun (degree, opIdx, inner) =>
      s.degree = degree && opOf s = opIdx &&
        inner.any (fun (nd, no, mx) => decide (countMaxNestedness D s nd no > mx)))) t

/-- `count_depth(tree)` (`src/NodeUtils.jl:25-29` of DynamicExpressions.jl). -/
def countDepth (D : Nat) (t : Tree T) : Int :=
  Id.run (tmrT D (fun _ => pure (1 : Int)) (fun _ => pure (1 : Int))
    (fun p cs => pure (p + maxList cs)) t)

/-- One-based `enumerate`. -/
def enum1 {α : Type} (xs : List α) : List (Nat × α) := (List.range' 1 xs.length).zip xs

/-- `@something(cached_size, compute_complexity(tree, options))` (`src/CheckConstraints.jl:81`). -/
def cachedSize (D : Nat) (o : Opts) (cached : Option Int) (t : Tree T) : Jl Int :=
  match cached with
  | some s => pure s
  | none => computeComplexityT D o.cmap t

/-- The flag of one degree (`src/CheckConstraints.jl:86-91`): whether any operator
`op_idx` of degree `degree` with some limit `≠ -1` is flagged by `flag_operator_complexity`. -/
def degreeFlag (D : Nat) (o : Opts) (t : Tree T) (x : Nat × List (List Int)) : Jl Bool :=
  anyListM (fun (y : Nat × List Int) =>
    if y.2.any (· ≠ -1) then flagOpComplexity D o t x.1 y.1 y.2 else pure false) (enum1 x.2)

/-- `check_constraints(tree, options, maxsize, cached_size)` (`src/CheckConstraints.jl:75-95`).
The per-degree flags are computed with `map` (every degree), then combined with `any`. -/
def checkConstraints (D : Nat) (o : Opts) (maxsize : Int) (cached : Option Int) (t : Tree T) :
    Jl Bool := do
  let size ← cachedSize D o cached t
  if size > maxsize then return false
  if countDepth D t > o.maxdepth then return false
  let invalidByDegree ← (enum1 o.opCons).mapM (degreeFlag D o t)
  if invalidByDegree.any id then return false
  if flagIllegalNests D o t then return false
  return true

/-! ## Specification -/

/-- The number of nodes of operator `(degree, op)` on the most crowded root-to-leaf path. -/
def pathCount (degree op : Nat) : Tree T → Nat
  | .const _ | .feature _ => 0
  | .branch o cs => (if cs.length = degree ∧ o = op then 1 else 0) +
      (cs.map (pathCount degree op)).foldr max 0

/-- Nesting of `(degree, op)` strictly below the root: the most crowded path through one
child. -/
def nestBelow (degree op : Nat) (t : Tree T) : Nat := ((kids t).map (pathCount degree op)).foldr max 0

/-- The per-argument complexity limits of node `s`'s operator, if any. -/
def consOf (o : Opts) (s : Tree T) : Option (List Int) :=
  if 1 ≤ s.degree ∧ 1 ≤ opOf s then (o.opCons[s.degree - 1]?.getD [])[opOf s - 1]? else none

/-- The constraints `check_constraints` is meant to enforce on a tree of complexity
`size`: complexity at most `maxsize`, depth at most `maxdepth`, every argument of a
constrained operator within its complexity limit, and every nested-operator count within
its limit. Complexity uses the signed machine interpretation of the weighted count. -/
def Accepts (o : Opts) (maxsize : Int) (t : Tree T) : Prop :=
  signedWeight (wsize o.cmap t) ≤ maxsize ∧ (t.depth : Int) ≤ o.maxdepth ∧
  (∀ s ∈ preorder t, ∀ cons, consOf o s = some cons →
    ∀ (i : Nat) c ci, (kids s)[i]? = some c → cons[i]? = some ci → ci ≠ -1 →
      signedWeight (wsize o.cmap c) ≤ ci) ∧
  (∀ ncs, o.nested = some ncs → ∀ s ∈ preorder t, ∀ d oi inner, (d, oi, inner) ∈ ncs →
    s.degree = d → opOf s = oi → ∀ nd no mx, (nd, no, mx) ∈ inner → (nestBelow nd no s : Int) ≤ mx)

/-- Shape of the options as `Options` builds them (`src/Options.jl:76-180`): degree-`d`
tuples of `op_constraints` have `d` entries, and nested-constraint degrees and operator
indices are positive. -/
def OptsShape (o : Opts) : Prop :=
  (∀ d dc, o.opCons[d]? = some dc → ∀ cons ∈ dc, cons.length = d + 1) ∧
  (∀ ncs, o.nested = some ncs → ∀ d oi inner, (d, oi, inner) ∈ ncs →
    1 ≤ d ∧ 1 ≤ oi ∧ ∀ nd no mx, (nd, no, mx) ∈ inner → 1 ≤ nd ∧ 1 ≤ no)

/-! ## Property -/

/-- `check_constraints` accepts a tree exactly when its complexity, depth, per-operator
argument complexities and operator nestings are all within the limits of `Accepts`. -/
def constraints_accept : Prop :=
  ∀ (T : Type) (D : Nat) (o : Opts) (maxsize : Int) (cached : Option Int) (t : Tree T),
    t.WF D (fun _ => 255) 65535 → Covers o.cmap t → OptsShape o →
    (cached = none ∨ cached = some (signedWeight (wsize o.cmap t))) →
    ∃ b, checkConstraints D o maxsize cached t = .ok b ∧ (b = true ↔ Accepts o maxsize t)

end SymReg.Constraints
