import SymReg.Mutations.Swap

/-! `delete_random_op!` (`src/MutationFunctions.jl:365-379`): statement and proof. -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-- Child `j` (one-based) of a branch. -/
def kidAt : Tree T → Nat → Tree T
  | .branch _ cs, j => (cs[j - 1]?).getD (.feature 0)
  | t, _ => t

/-- `delete_random_op!(tree, rng)` ("Select a random node, and splice it out of the tree") on an
alias-free plain `Node` tree. A leaf root is returned unchanged with no draw. Otherwise the first
draw selects the `k`-th operator node `u` in preorder (uniformly among operator nodes), the
second a child index `j` uniform in `1:degree(u)`, and the returned root unfolds to the input tree
with `u`'s subtree replaced by its `j`-th child: the node count drops by
`size(u) - size(child)`. When `u` is the root its child itself is returned and no object is
written; otherwise the same root object is returned. -/
def delete_random_op_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree → DegLe D t →
    SlotsLe D 0 g →
    ∃ r g' rng', deleteRandomOp D fuel tree ⟨g, rng⟩ = .ok (r, ⟨g', rng'⟩) ∧
      (t.degree = 0 → r = tree ∧ g' = g ∧ rng' = rng) ∧
      (t.degree ≠ 0 →
        ∃ u, (preorder t)[drawAt rng rng.cursor (eligT isBranchT t)]? = some u ∧
          u.degree ≠ 0 ∧
          1 ≤ rangeAt rng (rng.cursor + 1) u.degree ∧
          rangeAt rng (rng.cursor + 1) u.degree ≤ u.degree ∧
          Graph.unfold g'.view (fuel + fuel) r =
            some (replaceAt t (drawAt rng rng.cursor (eligT isBranchT t))
              (kidAt u (rangeAt rng (rng.cursor + 1) u.degree))) ∧
          (replaceAt t (drawAt rng rng.cursor (eligT isBranchT t))
              (kidAt u (rangeAt rng (rng.cursor + 1) u.degree))).size + u.size =
            t.size + (kidAt u (rangeAt rng (rng.cursor + 1) u.degree)).size ∧
          (drawAt rng rng.cursor (eligT isBranchT t) = 0 →
            g' = g ∧ ∃ c, g.cells tree = some c ∧
              c.active[rangeAt rng (rng.cursor + 1) u.degree - 1]? = some r) ∧
          (drawAt rng rng.cursor (eligT isBranchT t) ≠ 0 → r = tree) ∧
          rng'.cursor = rng.cursor + 2)

theorem delete_random_op_spec_holds : delete_random_op_spec := by
  intro T g D fuel tree t rng hu hna hdeg hsl
  obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
  have hrd : rd tree (⟨g, rng⟩ : St T) = .ok (rc, ⟨g, rng⟩) := rd_ok hrc
  by_cases hd0 : rc.degree = 0
  · refine ⟨tree, g, rng, ?_, fun _ => ⟨rfl, rfl, rfl⟩, fun h => absurd (hrdeg ▸ hd0) h⟩
    simp only [deleteRandomOp]
    rw [bindM hrd]
    simp [hd0]
    rfl
  have htd : t.degree ≠ 0 := by rw [← hrdeg]; exact hd0
  have hany : (preorder t).any isBranchT = true := by
    rw [List.any_eq_true]
    exact ⟨t, preorder_mem (preorder_zero t), by simp [isBranchT, htd]⟩
  obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hq, hf', hun, hrepl, hPk, _⟩ :=
    sample_kind ⟨g, rng⟩ fuel tree t _ isBranchT lk_pos hu hany
  dsimp only at hsamp hP hpu hun hrepl hPk
  generalize hk : drawAt rng rng.cursor (eligT isBranchT t) = k at hpu hrepl hPk ⊢
  obtain ⟨c, hcx, hlx, hdx, hcase⟩ := cell_of_unfold hun
  obtain ⟨c0, hc0, _, hdD⟩ := good_reach g D fuel tree t hu hdeg x ⟨P, hP⟩
  rw [hcx] at hc0; cases hc0
  have hdc : c.degree ≠ 0 := by rw [hdx]; simpa [isBranchT] using hq
  rcases hcase with ⟨hd, _⟩ | ⟨_, ts, hts, rfl⟩
  · exact absurd hd hdc
  have hlts : ts.length = c.degree := by rw [mapM_length _ _ _ hts, hlx]
  have hdegu : (Tree.branch c.op ts).degree = c.degree := by simp [Tree.degree, hlts]
  simp only [Nat.add_sub_cancel] at hts
  -- the carried child
  let s1 : St T := { g := g, rng := adv rng }
  let j := (s1.rng.indexDraws (c.degree - 1) s1.rng.cursor).val
  have hj : j < c.degree := by
    have := (s1.rng.indexDraws (c.degree - 1) s1.rng.cursor).isLt
    simp only [j]; omega
  let s2 : St T := { s1 with rng := adv s1.rng }
  have hgc := getChildM_ok (s := s2) (D := D) hcx hlx hdD hj
  let carry := (c.active[j]?).getD 0
  have hjact : j < c.active.length := by omega
  have hcm : c.active[j]? = some carry := by
    simp only [carry, List.getElem?_eq_getElem hjact, Option.getD_some]
  obtain ⟨v, hv, hcv⟩ := mapM_get _ _ _ hts j carry hcm
  have hrange : rangeAt rng (rng.cursor + 1) (Tree.branch c.op ts).degree = j + 1 := by
    rw [hdegu]; rfl
  have hkid : kidAt (Tree.branch c.op ts) (j + 1) = v := by simp [kidAt, hv]
  have hsize := replaceAt_size t k _ v hpu
  have hunv : ∀ F, f' ≤ F → Graph.unfold g.view F carry = some v :=
    fun F hF => unfold_mono _ _ _ hcv _ hF
  by_cases hxt : x = tree
  · -- the root is deleted: its child is returned
    subst hxt
    have hP0 : P = [] := hna.acyclic x (reach_refl _ _) P hP
    have hk0 : k = 0 := hPk.mp hP0
    have hrun : deleteRandomOp D fuel x ⟨g, rng⟩ = .ok (carry, s2) := by
      simp only [deleteRandomOp]
      rw [bindM hrd]
      simp only [hd0, ↓reduceIte]
      rw [bindM hsamp, bindM (rd_ok (s := s1) hcx), bindM (randRange_ok _ (by omega) s1),
        bindM hgc]
      simp
      rfl
    refine ⟨carry, g, adv s1.rng, hrun, fun h => absurd h htd, fun _ =>
      ⟨.branch c.op ts, hpu, by rw [hdegu]; exact hdc, ?_, ?_, ?_, ?_, ?_,
        fun h => absurd hk0 h, rfl⟩⟩
    · rw [hrange]; omega
    · rw [hrange, hdegu]; omega
    · rw [hrange, hkid, hk0, replaceAt_zero]; exact hunv _ (by omega)
    · rw [hrange, hkid]; exact hsize
    · intro _
      refine ⟨rfl, c, hcx, ?_⟩
      rw [hrange, Nat.add_sub_cancel]
      exact hcm
  · -- an inner node is deleted: its parent's slot now holds the child
    have hPne : P ≠ [] := fun he => by
      subst he; exact hxt (path_nil_inv hP).symm
    have hk0 : k ≠ 0 := fun h => hPne (hPk.mpr h)
    obtain ⟨Q, i, rfl⟩ := exists_snoc P hPne
    obtain ⟨q, cq', hQ, hcq', hi⟩ := path_snoc_inv Q hP
    obtain ⟨cq, hcq, rfl⟩ : ∃ cq, g.cells q = some cq ∧ cq' = cq.toCell := by
      cases hc : g.cells q with
      | none => simp [SGraph.view, hc] at hcq'
      | some cq => simp [SGraph.view, hc] at hcq'; exact ⟨cq, rfl, hcq'.symm⟩
    have hi' : cq.active[i]? = some x := by simpa [SCell.toCell] using hi
    have hfp := findParent_spec g D fuel tree x q t Q i cq hu hdeg hna hQ hcq hi'
    obtain ⟨cq0, hcq0, hlq, hDq⟩ := good_reach g D fuel tree t hu hdeg q ⟨Q, hQ⟩
    rw [hcq] at hcq0; cases hcq0
    have hiq : i < cq.degree := by
      have := (List.getElem?_eq_some_iff.mp hi').1; omega
    obtain ⟨g', c', hset, hoth, _, hq', hact', hdeg', hop', hcst', hval', hfeat', _⟩ :=
      setChildM_ok (s := s2) (x := carry) hcq hlq hDq hiq
        (fun sl h => hsl q cq sl (Nat.zero_le _) hcq h)
    have hrun : deleteRandomOp D fuel tree ⟨g, rng⟩ = .ok (tree, { s2 with g := g' }) := by
      simp only [deleteRandomOp]
      rw [bindM hrd]
      simp only [hd0, ↓reduceIte]
      rw [bindM hsamp, bindM (rd_ok (s := s1) hcx), bindM (randRange_ok _ (by omega) s1),
        bindM hgc]
      simp only [hxt, ↓reduceIte]
      have hfp' : onG (T := T) (fun g => Crossover.findParent g D fuel tree x) s2 =
          .ok ((q, i + 1), s2) := by
        simp [onG, hfp, Except.map, s2, s1]
      rw [bindM hfp']
      simp only
      rw [bindM hset]
      rfl
    -- the new heap differs from the old one only at the parent
    have hvq' : g'.view.cells q =
        some { cq.toCell with children := cq.toCell.children.set i carry } := by
      rw [view_cells hq']
      simp [SCell.toCell, hact', hdeg', hop', hcst', hval', hfeat']
    have hcnr : ¬ Graph.Reachable g.view carry q := by
      intro ⟨R, hR⟩
      have hcarry : Graph.Path g.view x [j] carry :=
        .cons (view_cells hcx) (by simpa [SCell.toCell] using hcm) (.nil _)
      have hqq : Graph.Path g.view q (i :: [j] ++ R) q := by
        refine .cons (view_cells hcq) (by simpa [SCell.toCell] using hi') ?_
        exact hcarry.append hR
      have := hna.acyclic q ⟨Q, hQ⟩ _ hqq
      simp at this
    have hcv' : Graph.unfold g'.view f' carry = some v := by
      rw [unfold_agree f' carry (fun z hz => view_oth hoth z (fun hzq => hcnr (hzq ▸ hz)))]
      exact hcv
    have hres := repl_heap g.view g'.view q carry i cq.toCell v f' (view_cells hcq)
      (by simp [SCell.toCell]; omega) hvq' (view_oth hoth) hcv' fuel tree t hu hna Q
      (replaceAt t k v) hQ (hrepl v)
    have hf'f : f' ≤ fuel := by omega
    refine ⟨tree, g', adv s1.rng, hrun, fun h => absurd h htd, fun _ =>
      ⟨.branch c.op ts, hpu, by rw [hdegu]; exact hdc, ?_, ?_, ?_, ?_, fun h => absurd h hk0,
        fun _ => rfl, rfl⟩⟩
    · rw [hrange]; omega
    · rw [hrange, hdegu]; omega
    · rw [hrange, hkid]; exact unfold_mono _ _ _ hres _ (by omega)
    · rw [hrange, hkid]; exact hsize

end SymReg.Mutations
