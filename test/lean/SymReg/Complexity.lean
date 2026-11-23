import DynExpr.NodeBase.TraverseCount
import SymReg.HeapLemmas

/-!
Model of `compute_complexity` (`src/Complexity.jl`, SymbolicRegression.jl `upstream/master`
edbe678e) with a `ComplexityMapping` (`src/OptionsStruct.jl:24-29`).

Two mirrors, following the DE modelling rules: `computeComplexityH` on the node heap
(needed for `GraphNode`, whose traversal uses the identity cache) and `computeComplexityT`
on pure trees (plain `Node`, used by the constraint checks of `src/CheckConstraints.jl`).
`complexityH_plain` proves that they agree whenever the identity cache is off.

Weights are `Int` (`ComplexityMapping{Int}`), for which `round(Int, x)` at
`src/Complexity.jl:37` is the identity.
-/

namespace SymReg.Complexity
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas

variable {T : Type}

/-- `variable_complexity` (`src/OptionsStruct.jl:27`): one weight for all features, or a
vector indexed by feature. -/
inductive VarC where
  | scalar (w : Int)
  | vector (ws : List Int)

/-- `ComplexityMapping{Int}` (`src/OptionsStruct.jl:24-29`). `opC[d-1][o-1]` is the
weight of operator `o` of degree `d` (`op_complexities::NTuple{D,Vector{Int}}`). -/
structure CMap where
  use : Bool
  opC : List (List Int)
  varC : VarC
  constC : Int

/-- Unchecked one-based indexing `@inbounds(xs[i])`: out of range is undefined behaviour. -/
def idx1 {α : Type} (xs : List α) (i : Nat) : Jl α :=
  match (if 1 ≤ i then xs[i - 1]? else none) with
  | some x => pure x
  | none => throw (.undefinedBehavior "@inbounds index out of range")

/-- Leaf closure `t -> t.constant ? cc : @inbounds(vc[t.feature])` (or `vc` for a scalar)
(`src/Complexity.jl:47-53`). -/
def leafW (m : CMap) (constant : Bool) (feature : Nat) : Jl Int :=
  if constant then pure m.constC
  else match m.varC with
    | .scalar w => pure w
    | .vector ws => idx1 ws feature

/-- Branch closure `t -> @inbounds(op_complexities[t.degree][t.op])` (`src/Complexity.jl:54-56`). -/
def branchW (m : CMap) (degree op : Nat) : Jl Int := do
  let ws ← idx1 m.opC degree
  idx1 ws op

/-- `leafW` on a pure leaf. A childless `branch` is not representable (`Tree.Representable`). -/
def leafT (m : CMap) : Tree T → Jl Int
  | .const _ => leafW m true 0
  | .feature i => leafW m false i
  | .branch _ _ => throw (.undefinedBehavior "childless branch")

/-- `branchW` on a pure branch. -/
def branchT (m : CMap) (t : Tree T) : Jl Int := branchW m t.degree (opOf t)

/-- Signed interpretation of a Julia `Int` sum on a 64-bit runtime. -/
def signedWeight (w : Int) : Int := (Int64.ofInt w).toInt

theorem signedWeight_eq_of_fits {w : Int} (lo : -2^63 ≤ w) (hi : w < 2^63) :
    signedWeight w = w := Int64.toInt_ofInt_of_le lo hi

/-- `compute_complexity(tree::AbstractExpressionNode, options)` for a plain `Node`
(`src/Complexity.jl:29-41`): with `complexity_mapping.use`, `_compute_complexity`
(`src/Complexity.jl:43-63`) is `tree_mapreduce` with the weight closures and `+`; the
`f_on_shared` closure is never called without the identity cache. Otherwise
`count_nodes` (`src/Complexity.jl:39`). -/
private def complexityFoldT (D : Nat) (m : CMap) (t : Tree T) : Jl Int :=
  if m.use then tmrT (m := Jl) D (leafT m) (branchT m) (fun b rs => pure (b + rs.sum)) t
  else pure (countNodesT D t : Int)

-- The only intermediate operations are addition and replacing a cache hit by zero.
-- Both commute with reduction modulo 2^64, so we can reduce once at the result.
def computeComplexityT (D : Nat) (m : CMap) (t : Tree T) : Jl Int :=
  (complexityFoldT D m t).map signedWeight

/-- `f_on_shared=(result, is_shared) -> is_shared ? zero(CT) : result` (`src/Complexity.jl:61`). -/
def onShared (r : Int) (isShared : Bool) : Int := if isShared then 0 else r

/-- `compute_complexity(tree, options; break_sharing)` on the heap (`src/Complexity.jl:29-63`),
for `Node` (`isGraph = false`) and `GraphNode` (`isGraph = true`): the heap
`tree_mapreduce` of `DynExpr.NodeBase.treeMapreduceH`, which uses the identity cache exactly
when `isGraph && !break_sharing` (`src/base.jl:96-109` of DynamicExpressions.jl), or
`count_nodes(tree; break_sharing)`. -/
private def complexityFoldH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (m : CMap)
    (fuel root : Nat) : Jl Int :=
  if m.use then
    (treeMapreduceH (σ := Unit) g D isGraph bs (fun _ c => StateT.lift (leafW m c.constant c.feature))
      (fun _ c => StateT.lift (branchW m c.degree c.op)) (fun b rs => StateT.lift (pure (b + rs.sum)))
      onShared fuel root).run' ()
  else (countNodesH g D isGraph bs fuel root).map (fun n => (n : Int))

-- Source: src/Complexity.jl:29-63
def computeComplexityH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (m : CMap)
    (fuel root : Nat) : Jl Int :=
  (complexityFoldH g D isGraph bs m fuel root).map signedWeight

/-! ## Specification -/

/-- The weight of one node from its fields (degree, op, constant flag, feature). Without
`use`, every node weighs 1 (`count_nodes`). -/
def nodeWeight (m : CMap) (degree op : Nat) (constant : Bool) (feature : Nat) : Int :=
  if !m.use then 1
  else if degree = 0 then
    if constant then m.constC
    else match m.varC with
      | .scalar w => w
      | .vector ws => ws[feature - 1]?.getD 0
  else ((m.opC[degree - 1]?.getD [])[op - 1]?).getD 0

/-- Weight of the root node of a tree. -/
def treeWeight (m : CMap) : Tree T → Int
  | .const _ => nodeWeight m 0 0 true 0
  | .feature i => nodeWeight m 0 0 false i
  | .branch o cs => nodeWeight m cs.length o false 0

/-- Weight of one heap object. -/
def cellWeight (m : CMap) (c : SCell T) : Int :=
  nodeWeight m c.degree c.op c.constant c.feature

/-- Weighted node count: the sum of the node weights over every node of the tree. -/
def wsize (m : CMap) (t : Tree T) : Int := ((preorder t).map (treeWeight m)).sum

/-- A node's weight is defined: its feature indexes the variable weight vector and its
(degree, op) indexes `op_complexities`. -/
def InRange (m : CMap) : Tree T → Prop
  | .const _ => True
  | .feature i => match m.varC with
    | .scalar _ => True
    | .vector ws => 1 ≤ i ∧ i ≤ ws.length
  | .branch o cs => ∃ ws, m.opC[cs.length - 1]? = some ws ∧ 1 ≤ o ∧ o ≤ ws.length

/-- Every node of `t` has a defined weight when the mapping is used. -/
def Covers (m : CMap) (t : Tree T) : Prop := m.use = true → ∀ s ∈ preorder t, InRange m s

/-! ## Properties -/

/-- Signed machine sum of all unfolded nodes, or each reachable object once for a
`GraphNode` with the identity cache. A disabled mapping gives unit weights. -/
def complexity_weighted : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T) (isGraph bs : Bool) (m : CMap),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 → Covers m t →
    ∃ w, computeComplexityH g D isGraph bs m fuel root = .ok w ∧
      ((isGraph && !bs) = false → w = signedWeight (wsize m t)) ∧
      ((isGraph && !bs) = true → ∃ l : List Addr, l.Nodup ∧
        (∀ a, a ∈ l ↔ Graph.Reachable g.view root a) ∧
        w = signedWeight ((l.map (fun a => ((g.cells a).map (cellWeight m)).getD 0)).sum))

/-- Without the identity cache, the result is the signed machine sum over occurrences. -/
def complexity_weighted_tree : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T) (isGraph bs : Bool) (m : CMap),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 → Covers m t →
    (isGraph && !bs) = false → computeComplexityH g D isGraph bs m fuel root = .ok (signedWeight (wsize m t))

/-! ## Proofs -/

private theorem preorder_branch (o : Nat) (cs : List (Tree T)) :
    preorder (.branch o cs) = .branch o cs :: preorder.preorderF cs := rfl

private theorem preorderF_cons (c : Tree T) (cs : List (Tree T)) :
    preorder.preorderF (c :: cs) = preorder c ++ preorder.preorderF cs := rfl

/-- Every child's preorder is part of its parent's. -/
theorem mem_preorder_child {s c : Tree T} {o : Nat} {cs : List (Tree T)} (hc : c ∈ cs)
    (hs : s ∈ preorder c) : s ∈ preorder (.branch o cs) := by
  rw [preorder_branch]
  apply List.mem_cons_of_mem
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    rw [preorderF_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_append_left _ hs
    · exact List.mem_append_right _ (ih hc)

theorem self_mem_preorder (t : Tree T) : t ∈ preorder t := by
  cases t <;> simp [preorder]

theorem wsize_branch (m : CMap) (o : Nat) (cs : List (Tree T)) :
    wsize m (.branch o cs) = treeWeight m (.branch o cs) + (cs.map (wsize m)).sum := by
  unfold wsize
  rw [preorder_branch, List.map_cons, List.sum_cons]
  congr 1
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [preorderF_cons, List.map_append, List.sum_append, ih]; simp

private theorem tmrF_ok (D : Nat) (m : CMap) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, tmrT (m := Jl) D (leafT m) (branchT m) (fun b rs => pure (b + rs.sum)) c =
      .ok (wsize m c)) :
    tmrF (m := Jl) D (leafT m) (branchT m) (fun b rs => pure (b + rs.sum)) cs.length cs =
      .ok (cs.map (wsize m)) := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [List.length_cons, tmrF]
    rw [ih c List.mem_cons_self, ihc (fun x hx => ih x (List.mem_cons_of_mem _ hx))]
    rfl

private theorem idx1_some {α : Type} {xs : List α} {i : Nat} {x : α} (h1 : 1 ≤ i)
    (h : xs[i - 1]? = some x) : idx1 xs i = .ok x := by
  simp [idx1, h1, h]
  rfl

private theorem getElem?_some {α : Type} {xs : List α} {i : Nat} (h1 : 1 ≤ i)
    (h2 : i ≤ xs.length) : ∃ x, xs[i - 1]? = some x :=
  ⟨xs[i - 1]'(by omega), List.getElem?_eq_getElem _⟩

/-- With the mapping in use, the pure mirror is the weighted count on covered trees. -/
theorem computeT_use (D : Nat) (m : CMap) (hu : m.use = true) (t : Tree T)
    (hw : t.WF D (fun _ => 255) 65535) (hcov : ∀ s ∈ preorder t, InRange m s) :
    tmrT (m := Jl) D (leafT m) (branchT m) (fun b rs => pure (b + rs.sum)) t = .ok (wsize m t) := by
  induction t using Tree.induction with
  | hc v =>
    simp [tmrT, leafT, leafW, wsize, preorder, treeWeight, nodeWeight, hu]
    rfl
  | hf i =>
    have hr := hcov (.feature i) (self_mem_preorder _)
    simp only [tmrT, leafT, leafW, Bool.false_eq_true, ↓reduceIte, wsize, preorder, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero, treeWeight, nodeWeight, hu,
      Bool.not_true]
    cases hv : m.varC with
    | scalar w => rfl
    | vector ws =>
      simp only [hv, InRange] at hr
      obtain ⟨x, hx⟩ := getElem?_some hr.1 hr.2
      show idx1 ws i = _
      rw [idx1_some hr.1 hx]
      simp [hx]
  | hb o cs ih =>
    simp only [Tree.WF] at hw
    have hcs0 : cs.length ≠ 0 := by omega
    have hkids : ∀ c ∈ cs, tmrT (m := Jl) D (leafT m) (branchT m)
        (fun b rs => pure (b + rs.sum)) c = .ok (wsize m c) := fun c hc =>
      ih c hc (hw.2.2 c hc) (fun s hs => hcov s (mem_preorder_child hc hs))
    have hnif : nifDeg D cs.length = cs.length := by simp [nifDeg]; omega
    obtain ⟨ws, hws, ho1, ho2⟩ := (hcov (.branch o cs) (self_mem_preorder _) : InRange m _)
    obtain ⟨x, hx⟩ := getElem?_some ho1 ho2
    have hbr : branchT m (Tree.branch o cs) = .ok x := by
      simp only [branchT, branchW, Tree.degree, opOf]
      rw [idx1_some (by omega) hws, ok_bind, idx1_some ho1 hx]
    simp only [tmrT, hcs0, ↓reduceIte, hnif, hbr, ok_bind]
    rw [tmrF_ok D m cs hkids]
    simp only [ok_bind, wsize_branch, treeWeight, nodeWeight, hu, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hcs0, hws, hx, Option.getD_some]
    rfl

private theorem wsize_unit (m : CMap) (hu : m.use = false) (t : Tree T) :
    wsize m t = (t.size : Int) := by
  induction t using Tree.induction with
  | hc v => simp [wsize, preorder, treeWeight, nodeWeight, hu, Tree.size]
  | hf i => simp [wsize, preorder, treeWeight, nodeWeight, hu, Tree.size]
  | hb o cs ih =>
    rw [wsize_branch, Tree.size_branch]
    simp only [treeWeight, nodeWeight, hu, Bool.not_false, ↓reduceIte]
    push_cast
    congr 1
    induction cs with
    | nil => rfl
    | cons c cs ihc =>
      simp only [List.map_cons, List.sum_cons]
      push_cast
      rw [ih c List.mem_cons_self, ihc (fun x hx => ih x (List.mem_cons_of_mem _ hx))]

private theorem complexityFoldT_eq (D : Nat) (m : CMap) (t : Tree T)
    (hw : t.WF D (fun _ => 255) 65535) (hcov : Covers m t) :
    complexityFoldT D m t = .ok (wsize m t) := by
  unfold complexityFoldT
  cases hu : m.use
  · have hd : DegLe D t := degLe_of_WF t hw
    simp only [Bool.false_eq_true, ↓reduceIte, (count_nodes_tree_holds T D t hd).1, wsize_unit m hu]
    rfl
  · simp only [↓reduceIte]
    exact computeT_use D m hu t hw (hcov hu)

theorem computeComplexityT_eq (D : Nat) (m : CMap) (t : Tree T)
    (hw : t.WF D (fun _ => 255) 65535) (hcov : Covers m t) :
    computeComplexityT D m t = .ok (signedWeight (wsize m t)) := by
  unfold computeComplexityT
  rw [complexityFoldT_eq D m t hw hcov]
  rfl

/-- Without the identity cache, the heap mirror agrees with the pure mirror on the unfolded
tree. -/
private theorem complexityFoldH_plain (g : SGraph T) (D fuel root : Nat) (t : Tree T) (isGraph bs : Bool)
    (m : CMap) (hu : Graph.unfold g.view fuel root = some t) (hd : DegLe D t)
    (hsh : (isGraph && !bs) = false) :
    complexityFoldH g D isGraph bs m fuel root = complexityFoldT D m t := by
  unfold complexityFoldH complexityFoldT
  cases huse : m.use
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hc := count_nodes_graph_holds T g D fuel root t hu hd
    have hcount : countNodesH g D isGraph bs fuel root = .ok t.size := by
      cases isGraph
      · cases bs
        · exact hc.2.1
        · exact hc.1 false
      · cases bs
        · simp at hsh
        · exact hc.1 true
    rw [hcount, (count_nodes_tree_holds T D t hd).1]
    rfl
  · simp only [↓reduceIte]
    have hL : ∀ (c : SCell T) l, c.degree = 0 → leafOf c = some l →
        leafW m c.constant c.feature = leafT m l := by
      intro c l _ hlo
      unfold leafOf at hlo
      cases hk : c.constant
      · simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hlo
        subst hlo
        rfl
      · simp only [hk, ↓reduceIte, Option.map_eq_some_iff] at hlo
        obtain ⟨v, _, rfl⟩ := hlo
        rfl
    have hB : ∀ (c : SCell T) (ts : List (Tree T)), c.degree = ts.length → 0 < ts.length →
        branchW m c.degree c.op = branchT m (.branch c.op ts) := by
      intro c ts h _
      simp [branchT, Tree.degree, opOf, h]
    have h := tmrH_plain g D (fun c => leafW m c.constant c.feature)
      (fun c => branchW m c.degree c.op) (fun b rs => pure (b + rs.sum)) onShared
      (leafT m) (branchT m) hL hB fuel root t [] hu hd
    unfold treeMapreduceH
    rw [hsh]
    simp only [StateT.run'_eq, StateT.run_bind]
    erw [h]
    cases tmrT (m := Jl) D (leafT m) (branchT m) (fun b rs => pure (b + rs.sum)) t <;> rfl

theorem complexityH_plain (g : SGraph T) (D fuel root : Nat) (t : Tree T) (isGraph bs : Bool)
    (m : CMap) (hu : Graph.unfold g.view fuel root = some t) (hd : DegLe D t)
    (hsh : (isGraph && !bs) = false) :
    computeComplexityH g D isGraph bs m fuel root = computeComplexityT D m t := by
  unfold computeComplexityH computeComplexityT
  rw [complexityFoldH_plain g D fuel root t isGraph bs m hu hd hsh]

theorem complexity_weighted_tree_holds : complexity_weighted_tree := by
  intro T g D fuel root t isGraph bs m hu hw hcov hsh
  rw [complexityH_plain g D fuel root t isGraph bs m hu (degLe_of_WF t hw) hsh]
  exact computeComplexityT_eq D m t hw hcov

/-! ### `GraphNode` with the identity cache -/

/-- Weight of the heap object at `a` (zero for a missing object). -/
def addrWeight (g : SGraph T) (m : CMap) (a : Addr) : Int := ((g.cells a).map (cellWeight m)).getD 0

/-- Two duplicate-free lists with the same members have the same weighted sum. -/
theorem sum_map_eq_of_nodup {α : Type} (f : α → Int) :
    ∀ (l l' : List α), l.Nodup → l'.Nodup → (∀ a, a ∈ l ↔ a ∈ l') →
      (l.map f).sum = (l'.map f).sum := by
  intro l
  induction l with
  | nil =>
    intro l' _ _ h
    cases l' with
    | nil => rfl
    | cons b l' => exact absurd ((h b).mpr List.mem_cons_self) (by simp)
  | cons x xs ih =>
    intro l' hn hn' h
    obtain ⟨s, u, rfl⟩ := List.append_of_mem ((h x).mp List.mem_cons_self)
    rw [List.nodup_cons] at hn
    rw [List.nodup_append] at hn'
    obtain ⟨hs, hxu, hsep⟩ := hn'
    rw [List.nodup_cons] at hxu
    have hxs : x ∉ s := fun hx => hsep x hx x List.mem_cons_self rfl
    have hsu : (s ++ u).Nodup := by
      rw [List.nodup_append]
      exact ⟨hs, hxu.2, fun a ha b hb => hsep a ha b (List.mem_cons_of_mem _ hb)⟩
    have hmem : ∀ a, a ∈ xs ↔ a ∈ s ++ u := by
      intro a
      constructor
      · intro ha
        have hax : a ≠ x := fun e => hn.1 (by subst e; exact ha)
        rcases List.mem_append.mp ((h a).mp (List.mem_cons_of_mem _ ha)) with h1 | h1
        · exact List.mem_append_left _ h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact absurd h2 hax
          · exact List.mem_append_right _ h2
      · intro ha
        have hax : a ≠ x := by
          rintro rfl
          rcases List.mem_append.mp ha with ha | ha
          · exact hxs ha
          · exact hxu.1 ha
        have hl' : a ∈ s ++ x :: u := by
          rcases List.mem_append.mp ha with ha | ha
          · exact List.mem_append_left _ ha
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
        rcases List.mem_cons.mp ((h a).mpr hl') with e | e
        · exact absurd e hax
        · exact e
    rw [List.map_cons, List.sum_cons, ih (s ++ u) hn.2 hsu hmem]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega

private theorem cw_path_fuel {g : SGraph T} {a b : Addr} {p : List Nat}
    (hp : Graph.Path g.view a p b) :
    ∀ fuel (t : Tree T), Graph.unfold g.view fuel a = some t →
      p.length < fuel ∧ ∃ t', Graph.unfold g.view (fuel - p.length) b = some t' := by
  induction hp with
  | nil a =>
    intro fuel t h
    cases fuel with
    | zero => simp [Graph.unfold] at h
    | succ f => exact ⟨by simp, t, by simpa using h⟩
  | @cons a x z i p c hc hi _ ih =>
    intro fuel t h
    cases fuel with
    | zero => simp [Graph.unfold] at h
    | succ f =>
      obtain ⟨c', hc', hlen, hcase⟩ := unfold_succ h
      have hcc : c = c'.toCell := by
        simp only [SGraph.view, hc', Option.map_some, Option.some.injEq] at hc
        exact hc.symm
      subst hcc
      have hi' : c'.active[i]? = some x := hi
      rcases hcase with ⟨hd, _, _⟩ | ⟨_, ts, hts, _⟩
      · have hnil : c'.active = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [hnil] at hi'
        simp at hi'
      · obtain ⟨tx, _, htx⟩ := mapM_mem _ _ _ hts x (List.mem_iff_getElem?.mpr ⟨i, hi'⟩)
        obtain ⟨hl, t', ht'⟩ := ih f tx htx
        refine ⟨by simp; omega, t', ?_⟩
        simpa using ht'

private theorem cw_path_pow {G : Graph T} {a : Addr} {q : List Nat} (hq : Graph.Path G a q a) :
    ∀ k, ∃ p, Graph.Path G a p a ∧ p.length = k * q.length := by
  intro k
  induction k with
  | zero => exact ⟨[], .nil a, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hl⟩ := ih
    exact ⟨p ++ q, hp.append hq, by simp [hl, Nat.succ_mul]⟩

private theorem cw_no_cycle {g : SGraph T} {fuel : Nat} {a : Addr} {t : Tree T}
    (h : Graph.unfold g.view fuel a = some t) {q : List Nat} (hq : Graph.Path g.view a q a) :
    q = [] := by
  cases q with
  | nil => rfl
  | cons i q' =>
    obtain ⟨p, hp, hl⟩ := cw_path_pow hq fuel
    have h1 := (cw_path_fuel hp fuel t h).1
    have h2 := Nat.mul_le_mul_left fuel (show 1 ≤ (i :: q').length by simp)
    rw [Nat.mul_one] at h2
    omega

private theorem cw_reach_cons {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c)
    (y : Addr) :
    Graph.Reachable g.view a y ↔ y = a ∨ ∃ x ∈ c.active, Graph.Reachable g.view x y := by
  have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
  constructor
  · rintro ⟨p, hp⟩
    cases hp with
    | nil => exact Or.inl rfl
    | cons hc' hi hp' =>
      rw [hv] at hc'
      cases hc'
      exact Or.inr ⟨_, List.mem_iff_getElem?.mpr ⟨_, hi⟩, _, hp'⟩
  · rintro (rfl | ⟨x, hx, p, hp⟩)
    · exact ⟨[], .nil _⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      exact ⟨i :: p, .cons hv hi hp⟩

private theorem cw_reach_trans {G : Graph T} {a b c : Addr} :
    Graph.Reachable G a b → Graph.Reachable G b c → Graph.Reachable G a c
  | ⟨p, hp⟩, ⟨q, hq⟩ => ⟨p ++ q, hp.append hq⟩

/-- A child of a successfully unfolded node does not reach the node. -/
private theorem cw_child_not_reach {g : SGraph T} {fuel : Nat} {a x : Addr} {t : Tree T}
    {c : SCell T} (h : Graph.unfold g.view fuel a = some t) (hc : g.cells a = some c)
    (hx : x ∈ c.active) (hr : Graph.Reachable g.view x a) : False := by
  obtain ⟨q, hq⟩ := hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
  have := cw_no_cycle h (Graph.Path.cons hv hi hq)
  cases this

/-- Every object reachable from a successfully unfolded root exists. -/
private theorem cw_reach_cell {g : SGraph T} {fuel root a : Nat} {t : Tree T}
    (h : Graph.unfold g.view fuel root = some t) (hr : Graph.Reachable g.view root a) :
    ∃ c, g.cells a = some c := by
  obtain ⟨p, hp⟩ := hr
  obtain ⟨hl, t', ht'⟩ := cw_path_fuel hp fuel t h
  cases hf : fuel - p.length with
  | zero => omega
  | succ f =>
    rw [hf] at ht'
    obtain ⟨c, hc, _⟩ := unfold_succ ht'
    exact ⟨c, hc⟩

private theorem cw_find_none {R : Type} {C : Cache R} {a : Addr} (h : a ∉ C.map Prod.fst) :
    findCache C a = none := by
  induction C with
  | nil => rfl
  | cons kv C ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [findCache, Ne.symm h.1, ↓reduceIte]
    exact ih h.2

private theorem cw_find_some {R : Type} {C : Cache R} {a : Addr} (h : a ∈ C.map Prod.fst) :
    ∃ r, findCache C a = some r := by
  induction C with
  | nil => simp at h
  | cons kv C ih =>
    obtain ⟨k, v⟩ := kv
    by_cases hk : k = a
    · exact ⟨v, by simp [findCache, hk]⟩
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm hk
      · obtain ⟨r, hr⟩ := ih h
        exact ⟨r, by simp [findCache, hk, hr]⟩

/-- The cache keys are distinct and closed under reachability. -/
private def cwInv (V : Graph T) (C : Cache Int) : Prop :=
  (C.map Prod.fst).Nodup ∧ ∀ k ∈ C.map Prod.fst, ∀ y, Graph.Reachable V k y → y ∈ C.map Prod.fst

private theorem cw_inv_app {V : Graph T} {C new : Cache Int} (R : Addr → Prop)
    (hR : ∀ y z, R y → Graph.Reachable V y z → R z)
    (hC : cwInv V C) (hn : (new.map Prod.fst).Nodup)
    (hk : ∀ y, y ∈ new.map Prod.fst ↔ R y ∧ y ∉ C.map Prod.fst) : cwInv V (new ++ C) := by
  refine ⟨?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hn, hC.1, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact ((hk x).mp hx).2 hy
  · intro k hk' y hy
    rw [List.map_append, List.mem_append] at hk' ⊢
    rcases hk' with hk' | hk'
    · have hRy := hR k y ((hk k).mp hk').1 hy
      by_cases hyC : y ∈ C.map Prod.fst
      · exact Or.inr hyC
      · exact Or.inl ((hk y).mpr ⟨hRy, hyC⟩)
    · exact Or.inr (hC.2 k hk' y hy)

private theorem cw_fold {α β : Type} (F : β → α → StateT Unit Jl β) (P : List α → β → Prop)
    (xs : List α)
    (hstep : ∀ done x b, P done b → x ∈ xs → ∃ b', (F b x).run () = .ok (b', ()) ∧ P (done ++ [x]) b') :
    ∀ ys done init, (∀ y ∈ ys, y ∈ xs) → P done init →
      ∃ b, (ys.foldlM F init).run () = .ok (b, ()) ∧ P (done ++ ys) b := by
  intro ys
  induction ys with
  | nil => intro done init _ hP; exact ⟨init, rfl, by simpa using hP⟩
  | cons y ys ih =>
    intro done init hsub hP
    obtain ⟨b', hb', hP'⟩ := hstep done y init hP (hsub y List.mem_cons_self)
    obtain ⟨b, hb, hP⟩ := ih (done ++ [y]) b' (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) hP'
    refine ⟨b, ?_, by simpa using hP⟩
    simp only [List.foldlM_cons, StateT.run_bind, hb', ok_bind]
    exact hb

/-- The heap traversal of `computeComplexityH` with the identity cache. -/
private abbrev cwT (g : SGraph T) (D : Nat) (m : CMap) :=
  tmrH (σ := Unit) (R := Int) (B := Int) g D true
    (fun _ c => StateT.lift (leafW m c.constant c.feature))
    (fun _ c => StateT.lift (branchW m c.degree c.op)) (fun b rs => StateT.lift (pure (b + rs.sum)))
    onShared

private def cwStep (g : SGraph T) (D : Nat) (m : CMap) (fuel : Nat) (acc : List Int × Cache Int)
    (x : Addr) : StateT Unit Jl (List Int × Cache Int) := do
  let (r, c2) ← cwT g D m fuel x acc.2
  pure (acc.1 ++ [r], c2)

private theorem cw_hit {g : SGraph T} {D f a : Nat} {m : CMap} {r : Int} {C : Cache Int}
    (hfind : findCache C a = some r) : (cwT g D m (f + 1) a C).run () = .ok ((0, C), ()) := by
  simp only [cwT, tmrH, ↓reduceIte, hfind, onShared, StateT.run_pure, pure_ok]

private theorem cw_leaf {g : SGraph T} {D f a : Nat} {m : CMap} {C : Cache Int} {c : SCell T}
    {w : Int} (hfind : findCache C a = none) (hc : g.cells a = some c) (hd : c.degree = 0)
    (hw : leafW m c.constant c.feature = .ok w) :
    (cwT g D m (f + 1) a C).run () = .ok ((w, (a, w) :: C), ()) := by
  simp only [cwT, tmrH, ↓reduceIte, hfind, StateT.run_bind, StateT.run_lift, Heap.read, hc,
    ok_bind, hd, hw, StateT.run_pure, pure_ok, onShared]
  all_goals rfl

private theorem cw_branch {g : SGraph T} {D f a : Nat} {m : CMap} {C C' : Cache Int}
    {c : SCell T} {cs : List Addr} {rs : List Int} {b : Int}
    (hfind : findCache C a = none) (hc : g.cells a = some c) (hd : c.degree ≠ 0)
    (hb : branchW m c.degree c.op = .ok b)
    (hcs : getChildren g D a (nifDeg D c.degree) = .ok cs)
    (hfold : (cs.foldlM (cwStep g D m f) ([], C)).run () = .ok ((rs, C'), ())) :
    (cwT g D m (f + 1) a C).run () = .ok ((b + rs.sum, (a, b + rs.sum) :: C'), ()) := by
  simp only [cwT, tmrH, ↓reduceIte, hfind, StateT.run_bind, StateT.run_lift, Heap.read, hc,
    ok_bind, hd, hb, StateT.run_pure, pure_ok, hcs]
  erw [hfold]
  all_goals rfl

private theorem cw_step_run {g : SGraph T} {D : Nat} {m : CMap} {f x : Nat} {n : Int}
    {rs : List Int} {C' C'' : Cache Int} (h : (cwT g D m f x C').run () = .ok ((n, C''), ())) :
    (cwStep g D m f (rs, C') x).run () = .ok ((rs ++ [n], C''), ()) := by
  simp only [cwStep, StateT.run_bind, h, ok_bind, StateT.run_pure, pure_ok]

/-- A leaf object weighs its `cellWeight`, when its weight vector entry exists. -/
private theorem cw_leafW {m : CMap} (hu : m.use = true) {c : SCell T} {l : Tree T}
    (hd : c.degree = 0) (hlo : leafOf c = some l) (hr : InRange m l) :
    leafW m c.constant c.feature = .ok (cellWeight m c) := by
  unfold leafOf at hlo
  cases hk : c.constant
  · simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hlo
    subst hlo
    simp only [leafW, cellWeight, nodeWeight, hu, hd, hk, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    cases hv : m.varC with
    | scalar w => rfl
    | vector ws =>
      simp only [hv, InRange] at hr
      obtain ⟨x, hx⟩ := getElem?_some hr.1 hr.2
      show idx1 ws c.feature = _
      rw [idx1_some hr.1 hx]
      simp [hx]
  · simp only [leafW, cellWeight, nodeWeight, hu, hd, hk, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    all_goals rfl

/-- A branch object weighs its `cellWeight`, when its `op_complexities` entry exists. -/
private theorem cw_branchW {m : CMap} (hu : m.use = true) {c : SCell T} {ts : List (Tree T)}
    (hl : ts.length = c.degree) (hd : c.degree ≠ 0) (hr : InRange m (.branch c.op ts)) :
    branchW m c.degree c.op = .ok (cellWeight m c) := by
  obtain ⟨ws, hws, ho1, ho2⟩ := hr
  rw [hl] at hws
  obtain ⟨x, hx⟩ := getElem?_some ho1 ho2
  simp only [branchW]
  rw [idx1_some (by omega) hws, ok_bind, idx1_some ho1 hx]
  simp only [cellWeight, nodeWeight, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hws,
    hx, Option.getD_some]

/-- With the identity cache, a traversal from cache `C` adds exactly the reachable objects
not yet cached, each once, and returns the sum of their weights. -/
private theorem cw_share (g : SGraph T) (D : Nat) (m : CMap) (hu : m.use = true) :
    ∀ fuel a (t : Tree T) (C : Cache Int),
      Graph.unfold g.view fuel a = some t → DegLe D t → (∀ s ∈ preorder t, InRange m s) →
      cwInv g.view C →
      ∃ new : Cache Int, (cwT g D m fuel a C).run () =
          .ok ((((new.map Prod.fst).map (addrWeight g m)).sum, new ++ C), ()) ∧
        (new.map Prod.fst).Nodup ∧
        ∀ y, y ∈ new.map Prod.fst ↔ Graph.Reachable g.view a y ∧ y ∉ C.map Prod.fst := by
  intro fuel
  induction fuel with
  | zero => intro a t C h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t C h hdeg hcov hinv
    by_cases ha : a ∈ C.map Prod.fst
    · obtain ⟨r, hr⟩ := cw_find_some ha
      refine ⟨[], ?_, List.nodup_nil, ?_⟩
      · simpa using cw_hit (g := g) (D := D) (f := f) (m := m) hr
      · intro y
        simp only [List.map_nil, List.not_mem_nil, false_iff, not_and, Classical.not_not]
        exact fun hy => hinv.2 a ha y hy
    · have hfind : findCache C a = none := cw_find_none ha
      obtain ⟨c, hc, hlen, hcase⟩ := unfold_succ h
      have hroot := hcov t (self_mem_preorder t)
      have hwa : addrWeight g m a = cellWeight m c := by simp [addrWeight, hc]
      rcases hcase with ⟨hd, hcst, hfeat⟩ | ⟨hd, ts, hts, rfl⟩
      · have hnil : c.active = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hlo : leafOf c = some t := by
          cases hk : c.constant
          · simp [leafOf, hk, hfeat hk]
          · obtain ⟨v, hv, rfl⟩ := hcst hk
            simp [leafOf, hk, hv]
        refine ⟨[(a, cellWeight m c)], ?_, by simp, ?_⟩
        · rw [cw_leaf hfind hc hd (cw_leafW hu hd hlo hroot)]
          simp [hwa]
        · intro y
          rw [cw_reach_cons hc, hnil]
          simp only [List.map_cons, List.map_nil, List.mem_singleton, List.not_mem_nil,
            false_and, exists_false, or_false]
          constructor
          · rintro rfl; exact ⟨rfl, ha⟩
          · exact fun h => h.1
      · simp only [DegLe] at hdeg
        have htl := mapM_length _ _ _ hts
        have hlen' : c.degree ≤ D := by omega
        have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlen']
        have hcs : getChildren g D a (nifDeg D c.degree) = .ok c.active := by
          rw [hnif]; exact getChildren_active hc hlen hlen'
        have hb := cw_branchW hu (by omega) hd hroot
        let P : List Addr → List Int × Cache Int → Prop := fun done b =>
          ∃ new : Cache Int, b.2 = new ++ C ∧ (new.map Prod.fst).Nodup ∧
            (∀ y, y ∈ new.map Prod.fst ↔
              (∃ x ∈ done, Graph.Reachable g.view x y) ∧ y ∉ C.map Prod.fst) ∧
            b.1.sum = ((new.map Prod.fst).map (addrWeight g m)).sum
        have hstep : ∀ done x b, P done b → x ∈ c.active →
            ∃ b', (cwStep g D m f b x).run () = .ok (b', ()) ∧ P (done ++ [x]) b' := by
          rintro done x ⟨rs, C'⟩ ⟨new, hC', hnd, hkeys, hsum⟩ hx
          simp only at hC' hsum
          subst hC'
          have hinv' : cwInv g.view (new ++ C) :=
            cw_inv_app (fun y => ∃ x ∈ done, Graph.Reachable g.view x y)
              (fun y z ⟨x, hx, hxy⟩ hyz => ⟨x, hx, cw_reach_trans hxy hyz⟩) hinv hnd hkeys
          obtain ⟨tx, htxm, htx⟩ := mapM_mem _ _ _ hts x hx
          obtain ⟨new1, hrun1, hnd1, hk1⟩ := ih x tx (new ++ C) htx (hdeg.2 tx htxm)
            (fun s hs => hcov s (mem_preorder_child htxm hs)) hinv'
          refine ⟨(rs ++ [((new1.map Prod.fst).map (addrWeight g m)).sum], new1 ++ (new ++ C)),
            cw_step_run hrun1, new1 ++ new, by simp, ?_, ?_, ?_⟩
          · rw [List.map_append, List.nodup_append]
            refine ⟨hnd1, hnd, ?_⟩
            intro u hu v hv huv
            subst huv
            have := ((hk1 u).mp hu).2
            rw [List.map_append, List.mem_append] at this
            exact this (Or.inl hv)
          · intro y
            rw [List.map_append, List.mem_append, hk1 y, hkeys y, List.map_append,
              List.mem_append]
            constructor
            · rintro (⟨hr, hn⟩ | ⟨⟨x', hx', hr⟩, hC⟩)
              · exact ⟨⟨x, List.mem_append_right _ (List.mem_singleton_self x), hr⟩,
                  fun h => hn (Or.inr h)⟩
              · exact ⟨⟨x', List.mem_append_left _ hx', hr⟩, hC⟩
            · rintro ⟨⟨x', hx', hr⟩, hC⟩
              rcases List.mem_append.mp hx' with hx' | hx'
              · exact Or.inr ⟨⟨x', hx', hr⟩, hC⟩
              · rw [List.mem_singleton] at hx'
                subst hx'
                by_cases hyn : y ∈ new.map Prod.fst
                · exact Or.inr ((hkeys y).mp hyn)
                · exact Or.inl ⟨hr, fun h => h.elim hyn hC⟩
          · simp only [List.sum_append, List.sum_cons, List.sum_nil, List.map_append, hsum]
            omega
        obtain ⟨⟨rs, C'⟩, hbf, new, hC', hnd, hkeys, hsum⟩ :=
          cw_fold (cwStep g D m f) P c.active hstep c.active [] ([], C) (fun _ h => h)
            ⟨[], rfl, List.nodup_nil, by simp, rfl⟩
        simp only at hC' hsum
        subst hC'
        simp only [List.nil_append] at hkeys
        refine ⟨(a, cellWeight m c + rs.sum) :: new, ?_, ?_, ?_⟩
        · rw [cw_branch hfind hc hd hb hcs hbf]
          simp [hsum, hwa]
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hnd⟩
          obtain ⟨⟨x, hx, hr⟩, _⟩ := (hkeys a).mp hmem
          exact cw_child_not_reach h hc hx hr
        · intro y
          rw [cw_reach_cons hc, List.map_cons, List.mem_cons, hkeys y]
          constructor
          · rintro (rfl | ⟨hr, hC⟩)
            · exact ⟨Or.inl rfl, ha⟩
            · exact ⟨Or.inr hr, hC⟩
          · rintro ⟨rfl | hr, hC⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hr, hC⟩

/-- Without the mapping every existing object weighs 1. -/
private theorem cw_sum_unit {g : SGraph T} {m : CMap} (hu : m.use = false) :
    ∀ l : List Addr, (∀ a ∈ l, ∃ c, g.cells a = some c) → (l.map (addrWeight g m)).sum = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨c, hc⟩ := h a List.mem_cons_self
    have ih := cw_sum_unit hu l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha : addrWeight g m a = 1 := by simp [addrWeight, hc, cellWeight, nodeWeight, hu]
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, ha]
    omega

theorem complexity_weighted_holds : complexity_weighted := by
  intro T g D fuel root t isGraph bs m hu hw hcov
  cases hsh : (isGraph && !bs)
  · exact ⟨signedWeight (wsize m t), complexity_weighted_tree_holds T g D fuel root t isGraph bs m hu hw hcov hsh,
      fun _ => rfl, fun h => absurd h (by decide)⟩
  · obtain ⟨rfl, rfl⟩ : isGraph = true ∧ bs = false := by
      cases isGraph <;> cases bs <;> first | exact ⟨rfl, rfl⟩ | exact absurd hsh (by decide)
    have hd := degLe_of_WF t hw
    suffices hl : ∃ l : List Addr, l.Nodup ∧ (∀ a, a ∈ l ↔ Graph.Reachable g.view root a) ∧
        complexityFoldH g D true false m fuel root = .ok (l.map (addrWeight g m)).sum by
      obtain ⟨l, hnd, hmem, hc⟩ := hl
      refine ⟨_, ?_, fun h => absurd h (by decide), fun _ => ⟨l, hnd, hmem, rfl⟩⟩
      unfold computeComplexityH
      rw [hc]
      rfl
    cases huse : m.use
    · obtain ⟨_, _, l, hnd, hmem, hcnt⟩ := count_nodes_graph_holds T g D fuel root t hu hd
      refine ⟨l, hnd, hmem, ?_⟩
      have e : complexityFoldH g D true false m fuel root =
          (countNodesH g D true false fuel root).map (fun n => (n : Int)) := by
        simp [complexityFoldH, huse]
      rw [e, hcnt, cw_sum_unit huse l (fun a ha => cw_reach_cell hu ((hmem a).mp ha))]
      rfl
    · obtain ⟨new, hrun, hnd, hkeys⟩ := cw_share g D m huse fuel root t [] hu hd (hcov huse)
        ⟨List.nodup_nil, by simp⟩
      refine ⟨new.map Prod.fst, hnd, fun a => by simpa using hkeys a, ?_⟩
      unfold complexityFoldH treeMapreduceH
      simp only [huse, ↓reduceIte, StateT.run'_eq, StateT.run_bind]
      erw [hrun]
      rfl

theorem complexity_weighted_tree_exact (g : SGraph T) (D fuel root : Nat) (t : Tree T)
    (isGraph bs : Bool) (m : CMap) (hu : Graph.unfold g.view fuel root = some t)
    (hw : t.WF D (fun _ => 255) 65535) (hcov : Covers m t)
    (hsh : (isGraph && !bs) = false) (lo : -2^63 ≤ wsize m t) (hi : wsize m t < 2^63) :
    computeComplexityH g D isGraph bs m fuel root = .ok (wsize m t) := by
  rw [complexity_weighted_tree_holds T g D fuel root t isGraph bs m hu hw hcov hsh,
    signedWeight_eq_of_fits lo hi]

/-! ## Witnesses -/

/-- The one-object heap holding the `GraphNode` leaf `x1` at address 0. -/
def leafX1 : SGraph Nat := mkGraph [featC 1]

/-- Every variable weighs 2 (`complexity_of_variables=2`). -/
def varTwo : CMap := { use := true, opC := [], varC := .scalar 2, constC := 1 }

/-- The preconditions of `complexity_weighted` are satisfiable, and on the `GraphNode` leaf
`x1` with variable weight 2 the complexity is 2 (the case of PR #786). -/
example : Graph.unfold leafX1.view 1 0 = some (.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 ∧
    Covers varTwo (Tree.feature 1 : Tree Nat) ∧
    computeComplexityH leafX1 2 true false varTwo 1 0 = .ok 2 := by
  refine ⟨rfl, by simp [Tree.WF], ?_, by decide⟩
  intro _ s hs
  simp only [preorder, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  simp [InRange, varTwo]

end SymReg.Complexity
