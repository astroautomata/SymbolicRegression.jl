import SymReg.Mutations.Graft
import SymReg.Mutations.Pure

/-!
`append_random_op` (`src/MutationFunctions.jl:222-249`) and the shared step of the tree
generators: an operator node over fresh leaves is built and copied onto a node of an alias-free
tree with `set_node!`.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### The graft step -/

theorem setNodeM_ok {s : St T} {D x n : Nat} {g' : SGraph T} (h : setNode s.g D x n = .ok g') :
    setNodeM D x n s = .ok ((), { s with g := g' }) := by
  simp [setNodeM, liftG, h, Except.map]

/-- The objects of a successfully unfolded tree lie below `next`. -/
theorem reach_lt_next {g : SGraph T} {f a : Nat} {t : Tree T} (hu : Graph.unfold g.view f a = some t)
    {z : Addr} (hz : Graph.Reachable g.view a z) : z < g.next :=
  closed_lt (closed_unfold f a t hu) hz

/-- Building the operator node of degree `i` over fresh leaves and copying it onto the object `x`
of an alias-free tree (at path `P`, preorder index `k`) replaces the subtree at `k` by the new
operator over the new leaves; the tree stays alias-free and old objects are kept. -/
theorem graft_step (s : St T) (D f nf : Nat) (nops : List Nat) (sv : Rat → T) (tree x : Addr)
    (t : Tree T) (P : List Nat) (k i n : Nat)
    (hu : Graph.unfold s.g.view f tree = some t) (hna : Graph.NoAlias s.g.view tree)
    (hP : Graph.Path s.g.view tree P x) (hrepl : ∀ v, ReplPath t P v (replaceAt t k v))
    (h1 : 1 ≤ nf) (h2 : nf ≤ 65535) (hn : nopsAt nops i = .ok n) (hn1 : 1 ≤ n) (hn255 : n ≤ 255)
    (hi1 : 1 ≤ i) (hiD : i ≤ D) :
    ∃ (g1 g' : SGraph T),
      opNode D nf nops (sampleReal sv) i s = .ok (s.g.next + i, ⟨g1, advN s.rng (1 + 2 * i)⟩) ∧
      setNodeM D x (s.g.next + i) ⟨g1, advN s.rng (1 + 2 * i)⟩ =
        .ok ((), ⟨g', advN s.rng (1 + 2 * i)⟩) ∧
      Graph.unfold g'.view (f + 2) tree =
        some (replaceAt t k (.branch (rangeAt s.rng s.rng.cursor n)
          (leavesAt s.rng (s.rng.cursor + 1) nf sv i))) ∧
      Graph.NoAlias g'.view tree ∧ (∀ a, a < s.g.next → a ≠ x → g'.cells a = s.g.cells a) ∧
      s.g.next ≤ g'.next ∧ (∀ z, Graph.Reachable g'.view tree z → z < g'.next) := by
  obtain ⟨g1, hop, hn1', hold1, hleaf1, hbr1⟩ := opNode_ok D nf nops sv i n s h1 h2 hn hn1 hn255 hiD
  have hxlt : x < s.g.next := reach_lt_next hu ⟨P, hP⟩
  obtain ⟨tc, htc⟩ : ∃ tc, s.g.cells x = some tc := by
    have := closed_unfold f tree t hu x ⟨P, hP⟩
    cases hc : s.g.cells x with
    | none => simp [SGraph.view, hc] at this
    | some tc => exact ⟨tc, rfl⟩
  have hx1 : g1.cells x = some tc := by rw [hold1 x hxlt, htc]
  obtain ⟨g', hsn, hoth', hnx', c', hc', hdeg', hop', hact'⟩ :=
    setNode_branch_ok g1 D x (s.g.next + i) _ _ tc hx1 hbr1 (by simp; omega) (by simp; exact hiD)
  simp only [List.length_range'] at hdeg'
  refine ⟨g1, g', hop, setNodeM_ok (s := ⟨g1, _⟩) hsn, ?_⟩
  have hold : ∀ a, a < s.g.next → a ≠ x → g'.cells a = s.g.cells a := by
    intro a ha hax; rw [hoth' a hax, hold1 a ha]
  have hnex : ∀ j, s.g.next + j ≠ x := fun j h => by
    have := Nat.le_add_right s.g.next j
    rw [h] at this
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hxlt this)
  have hleaf : ∀ j, j < i →
      g'.cells (s.g.next + j) = some (leafCellAt s.rng (s.rng.cursor + 1 + 2 * j) nf sv) := by
    intro j hj; rw [hoth' (s.g.next + j) (hnex j), hleaf1 j hj]
  have hx : Graph.unfold g'.view 2 x = some (.branch (rangeAt s.rng s.rng.cursor n)
      (leavesAt s.rng (s.rng.cursor + 1) nf sv i)) :=
    fresh_branch_unfold (f := 0) hc' hdeg' hop' hact' (by omega) hleaf
  have hagree : ∀ b, Graph.Reachable s.g.view tree b → b ≠ x → g'.view.cells b = s.g.view.cells b := by
    intro b hb hbx
    simp [SGraph.view, hold b (reach_lt_next hu hb) hbx]
  have hres := rewrite_sub s.g.view g'.view x _ 2 hx f tree t hu hna
    (fun b hb hnr => hagree b hb (fun he => hnr (he ▸ reach_refl _ _))) P _ hP (hrepl _)
  -- the new operator node is an alias-free tree of fresh objects
  have hkid : ∀ b ∈ c'.toCell.children, s.g.next ≤ b ∧ b < s.g.next + i ∧
      ∀ cb, g'.view.cells b = some cb → cb.children = [] := by
    intro b hb
    simp only [SCell.toCell, hact', List.mem_range'_1] at hb
    refine ⟨hb.1, hb.2, fun cb hcb => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb.1
    rw [view_cells (hleaf j (Nat.lt_of_add_lt_add_left hb.2))] at hcb
    cases hcb
    simp [SCell.toCell, (leafCellAt_degree _ _ _ _).2.2]
  have hle : s.g.next + i ≤ g'.next := by rw [hnx', hn1']; exact Nat.le_succ _
  have hle' : s.g.next ≤ g'.next := Nat.le_trans (Nat.le_add_right _ _) hle
  have hnax : Graph.NoAlias g'.view x := by
    apply noAlias_flat (c := c'.toCell) (view_cells hc')
    · simp only [SCell.toCell, hact']; exact List.nodup_range'
    · exact fun b hb => (hkid b hb).2.2
    · intro hm; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hxlt (hkid x hm).1)
  have hfresh : ∀ z, Graph.Reachable g'.view x z → z = x ∨ ¬ Graph.Reachable s.g.view tree z := by
    intro z hz
    rcases reach_inv hz with rfl | ⟨c0, b, hc0, hb, hbz⟩
    · exact Or.inl rfl
    · rw [view_cells hc'] at hc0; cases hc0
      have hzb := reach_leafobj (hkid b hb).2.2 hbz
      subst hzb
      exact Or.inr (fun hr => Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le (reach_lt_next hu hr) (hkid z hb).1))
  obtain ⟨hna', hreach⟩ := graft_noAlias hna hP hagree hnax hfresh
  refine ⟨hres, hna', hold, hle', fun z hz => ?_⟩
  · rcases hreach z hz with h | h
    · exact Nat.lt_of_lt_of_le (reach_lt_next hu h) hle'
    · rcases reach_inv h with rfl | ⟨c0, b, hc0, hb, hbz⟩
      · exact Nat.lt_of_lt_of_le hxlt hle'
      · rw [view_cells hc'] at hc0; cases hc0
        have hzb := reach_leafobj (hkid b hb).2.2 hbz
        subst hzb
        exact Nat.lt_of_lt_of_le (hkid z hb).2.1 hle

/-! ### `append_random_op` -/

theorem leavesAt_advN (r : RNG) (n nf : Nat) (sv : Rat → T) :
    ∀ i c, leavesAt (advN r n) c nf sv i = leavesAt r c nf sv i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih => intro c; simp only [leavesAt]; rw [ih]; rfl

/-- Every tree has a leaf (a node of degree zero) in preorder. -/
theorem preorder_any_leaf (t : Tree T) : (preorder t).any isLeafT = true := by
  induction t using Tree.induction with
  | hc v => simp [preorder, isLeafT, Tree.degree]
  | hf i => simp [preorder, isLeafT, Tree.degree]
  | hb o cs ih =>
    cases cs with
    | nil => simp [preorder_branch, isLeafT, Tree.degree]
    | cons c cs' =>
      rw [preorder_branch, preorderF_cons]
      simp [List.any_append, ih c (by simp)]

theorem leaf_size {u : Tree T} (h : u.degree = 0) : u.size = 1 := by
  cases u with
  | const v => simp [Tree.size]
  | feature i => simp [Tree.size]
  | branch o cs =>
    simp only [Tree.degree, List.length_eq_zero_iff] at h
    subst h; simp [Tree.size]

/-- The degree chosen by `append_random_op` from the real draw at cursor `c + 1`. -/
def appendDeg (rng : RNG) (nops : List Nat) : Nat :=
  pickDeg nops.length nops (scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops)

/-- The tree produced by `append_random_op`: the sampled leaf (first draw) replaced by an
operator (operator draw at cursor `c + 2`) over fresh leaves (draws from cursor `c + 3`). -/
def appendTree (t : Tree T) (rng : RNG) (nops : List Nat) (nf : Nat) (sv : Rat → T) : Tree T :=
  replaceAt t (drawAt rng rng.cursor (eligT isLeafT t))
    (.branch (rangeAt rng (rng.cursor + 2) (opsOf nops (appendDeg rng nops)))
      (leavesAt rng (rng.cursor + 3) nf sv (appendDeg rng nops)))

/-- `append_random_op(tree, options, nfeatures, rng)` ("Add a random unary/binary operation to the
end of a tree") on an alias-free plain `Node` tree, for a degree draw strictly inside `(0, 1)`
(the draw `0` is `mut-pick-degree-has-operator`): it returns the same root object; the first
draw selects the `k`-th leaf in preorder uniformly, the degree `i` is the `csum` bucket of the
second draw and has an operator, and the result is the input tree with that leaf replaced by an
operator of degree `i` over `i` fresh random leaves, so the node count grows by exactly `i`; the
result is alias-free and every pre-existing object other than the leaf is unchanged. -/
def append_random_op_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf tree : Nat) (t : Tree T) (nops : List Nat)
    (sv : Rat → T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree →
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 → 0 < nops.sum →
    0 < scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops →
    scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops < (nops.sum : Rat) →
    ∃ g' rng', appendRandomOp D fuel nf nops (sampleReal sv) tree ⟨g, rng⟩ = .ok (tree, ⟨g', rng'⟩) ∧
      (∃ u, (preorder t)[drawAt rng rng.cursor (eligT isLeafT t)]? = some u ∧ u.degree = 0) ∧
      1 ≤ appendDeg rng nops ∧ appendDeg rng nops ≤ D ∧ 0 < opsOf nops (appendDeg rng nops) ∧
      Graph.unfold g'.view (fuel + 2) tree = some (appendTree t rng nops nf sv) ∧
      (appendTree t rng nops nf sv).size = t.size + appendDeg rng nops ∧
      Graph.NoAlias g'.view tree ∧ g.next ≤ g'.next ∧
      rng' = advN rng (3 + 2 * appendDeg rng nops)

theorem rat_pos_mul {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := Rat.mul_pos ha hb

theorem append_random_op_spec_holds : append_random_op_spec := by
  intro T g D fuel nf tree t nops sv rng hu hna hlen h255 h1 h2 hsum hu0 hu1
  subst hlen
  obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hq, _, _, hrepl, _⟩ :=
    sample_kind ⟨g, rng⟩ fuel tree t _ isLeafT lk_leaf hu (preorder_any_leaf t)
  dsimp only at hsamp hP hpu hrepl
  have hu0' : u.degree = 0 := by simpa [isLeafT] using hq
  -- the degree
  have hD : 1 ≤ nops.length := by
    cases nops with
    | nil => simp at hsum
    | cons _ _ => simp
  obtain ⟨hi1, hiD, _, _, hpos⟩ := pick_degree_interval_holds nops _ hD hu0 hu1
  generalize hi : pickDeg nops.length nops (scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops) = i
    at hi1 hiD hpos
  have hdeg : appendDeg rng nops = i := hi
  have hil : i - 1 < nops.length := by omega
  have hn : nopsAt nops i = .ok (opsOf nops i) := by
    simp [nopsAt, opsOf, show 1 ≤ i from hi1, List.getElem?_eq_getElem hil]
  have hn255 : opsOf nops i ≤ 255 := by
    simp only [opsOf, List.getElem?_eq_getElem hil, Option.getD_some]
    exact h255 _ (List.getElem_mem hil)
  obtain ⟨g1, g', hop, hset, hres, hna', _, hle, _⟩ :=
    graft_step ⟨g, advN rng 2⟩ nops.length fuel nf nops sv tree x t P _ i (opsOf nops i) hu hna hP
      hrepl h1 h2 hn hpos hn255 hi1 hiD
  refine ⟨g', advN (advN rng 2) (1 + 2 * i), ?_, ⟨u, hpu, hu0'⟩, by rw [hdeg]; exact hi1,
    by rw [hdeg]; exact hiD, by rw [hdeg]; exact hpos, ?_, ?_, hna', hle, ?_⟩
  · simp only [appendRandomOp, sampleLeaf]
    rw [bindM hsamp]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [bindM (randU_ok _)]
    refine (bindM (show opNode nops.length nf nops (sampleReal sv)
      (pickDeg nops.length nops (scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops))
      ({ g := g, rng := adv (adv rng) } : St T) = _ by rw [hi]; exact hop)).trans ?_
    refine (bindM hset).trans ?_
    rfl
  · unfold appendTree
    rw [hdeg, leavesAt_advN] at *
    exact hres
  · unfold appendTree
    rw [hdeg]
    have := replaceAt_size t _ u (.branch (rangeAt rng (rng.cursor + 2) (opsOf nops i))
      (leavesAt rng (rng.cursor + 3) nf sv i)) hpu
    rw [leavesAt_size, leaf_size hu0'] at this
    omega
  · rw [advN_advN, hdeg]
    congr 1
    omega

end SymReg.Mutations
