import SymReg.Mutations.Prepend

/-! `insert_random_op` (`src/MutationFunctions.jl:266-295`): statement and proof. -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-- The preorder index of the node sampled by `insert_random_op` (index draw at the cursor). -/
def insertIdx (rng : RNG) (t : Tree T) : Nat := (rng.indexDraws (t.size - 1) rng.cursor).val

/-- The degree chosen by `insert_random_op` from the real draw at cursor `c + 1`. -/
def insertDeg (rng : RNG) (nops : List Nat) : Nat :=
  pickDeg nops.length nops (scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops)

/-- `arg_to_carry = rand(rng, 1:i)` of `insert_random_op` (draw at cursor `c + 2`). -/
def insertCarry (rng : RNG) (nops : List Nat) : Nat := rangeAt rng (rng.cursor + 2) (insertDeg rng nops)

/-- The tree produced by `insert_random_op`: the sampled subtree `u` replaced by an operator of
degree `i` (operator draw at cursor `c + 1 + 2i`) whose `arg_to_carry`-th child is `u` and whose
other children are fresh leaves (draws from `c + 3`). -/
def insertTree (t u : Tree T) (rng : RNG) (nops : List Nat) (nf : Nat) (sv : Rat → T) : Tree T :=
  replaceAt t (insertIdx rng t)
    (.branch (rangeAt rng (rng.cursor + 1 + 2 * insertDeg rng nops) (opsOf nops (insertDeg rng nops)))
      (kidsT rng nf sv (insertCarry rng nops) u (rng.cursor + 3) 1 (insertDeg rng nops)))

/-- `insert_random_op(tree, options, nfeatures, rng)` ("Insert random node") on an alias-free
well-formed plain `Node` tree, for a degree draw strictly inside `(0, 1)` (the draw `0` is
`mut-pick-degree-has-operator`): it returns the same root object; the first draw selects the node
at preorder index `k` uniformly over all nodes, the degree `i` is the `csum` bucket of the second
draw and has an operator, `arg_to_carry` is uniform in `1:i`, and the result is the input tree
with the subtree `u` at `k` replaced by an operator of degree `i` whose `arg_to_carry`-th child is
(a copy of) `u` and whose other children are fresh random leaves, so the node count grows by
exactly `i`; the result is alias-free and `2 + 2i` draws are consumed. -/
def insert_random_op_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf tree : Nat) (t : Tree T) (nops : List Nat)
    (sv : Rat → T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree →
    t.WF D (fun _ => 255) 65535 →
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 → 0 < nops.sum →
    0 < scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops →
    scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops < (nops.sum : Rat) →
    ∃ u g' rng', insertRandomOp D fuel nf nops (sampleReal sv) tree ⟨g, rng⟩ = .ok (tree, ⟨g', rng'⟩) ∧
      (preorder t)[insertIdx rng t]? = some u ∧
      1 ≤ insertDeg rng nops ∧ insertDeg rng nops ≤ D ∧ 0 < opsOf nops (insertDeg rng nops) ∧
      1 ≤ insertCarry rng nops ∧ insertCarry rng nops ≤ insertDeg rng nops ∧
      Graph.unfold g'.view (fuel + (fuel + 1)) tree = some (insertTree t u rng nops nf sv) ∧
      (kidsT rng nf sv (insertCarry rng nops) u (rng.cursor + 3) 1 (insertDeg rng nops))[
        insertCarry rng nops - 1]? = some u ∧
      (insertTree t u rng nops nf sv).size = t.size + insertDeg rng nops ∧
      Graph.NoAlias g'.view tree ∧ g.next ≤ g'.next ∧
      rng'.cursor = rng.cursor + 2 + 2 * insertDeg rng nops

theorem insert_random_op_spec_holds : insert_random_op_spec := by
  intro T g D fuel nf tree t nops sv rng hu hna hwf hlen h255 h1 h2 hsum hu0 hu1
  subst hlen
  -- the sampled node
  have hne : eligIdx t.size (fun _ => true) ≠ [] := by
    have := Tree.size_pos t
    exact eligIdx_ne_nil (k := 0) (by omega) rfl
  obtain ⟨k, x, P, u, hk, hsamp, hP, hpu, hun, hrepl, _, _⟩ :=
    sample_spec ⟨g, rng⟩ fuel tree t (fun _ _ => true) (fun _ => true) hu
      (fun _ _ _ _ _ _ _ _ => rfl) hne
  have hkk : k = insertIdx rng t := by
    have hL : eligIdx t.size (fun _ => true) = List.range t.size := by simp [eligIdx]
    rw [hL] at hk
    have hj : (rng.indexDraws ((List.range t.size).length - 1) rng.cursor).val =
        (rng.indexDraws (t.size - 1) rng.cursor).val := by rw [List.length_range]
    have hlt := (rng.indexDraws (t.size - 1) rng.cursor).isLt
    have hsz := Tree.size_pos t
    rw [hj, List.getElem?_range (by omega)] at hk
    cases hk
    rfl
  subst hkk
  have hwfu : u.WF nops.length (fun _ => 255) 65535 := preorder_wf t hwf u (preorder_mem hpu)
  have hux : Graph.unfold g.view fuel x = some u :=
    unfold_mono _ _ _ hun fuel (Nat.sub_le _ _)
  have hcl := closed_unfold fuel tree t hu
  have hxlt : @LT.lt Nat _ x g.next := closed_lt hcl ⟨P, hP⟩
  obtain ⟨tc, htc⟩ : ∃ tc, g.cells x = some tc := by
    have := hcl x ⟨P, hP⟩
    cases hc : g.cells x with
    | none => simp [SGraph.view, hc] at this
    | some tc => exact ⟨tc, rfl⟩
  have hF : 1 ≤ fuel := by
    cases fuel with
    | zero => simp [Graph.unfold] at hu
    | succ _ => omega
  -- the degree
  obtain ⟨hi1, hiD, hpos⟩ := pick_ok hsum hu0 hu1
  generalize hi : pickDeg nops.length nops (scaledDegreeDraw (rng.draws (rng.cursor + 1)) nops) = i
    at hi1 hiD hpos
  have hdeg : insertDeg rng nops = i := hi
  generalize hcy : rangeAt rng (rng.cursor + 2) i = carry
  have hcar : insertCarry rng nops = carry := by unfold insertCarry; rw [hdeg, hcy]
  have hc1 : 1 ≤ carry := by rw [← hcy]; simp [rangeAt]
  have hci : carry ≤ i := by
    rw [← hcy]; have := (rng.indexDraws (i - 1) (rng.cursor + 2)).isLt; simp only [rangeAt]; omega
  -- the copy of the sampled subtree
  have hcopy : CarryOK g 0 fuel (copyM nops.length false fuel x) u := by
    intro s hs
    have hux' : Graph.unfold s.g.view fuel x = some u := by
      rw [(ext_tree hs (closed_unfold fuel x u hux)).1 fuel]; exact hux
    obtain ⟨r, h, hc, hpres, ⟨hu', hna', hrange⟩, hle⟩ :=
      copy_spec s.g nops.length fuel x u hux' hwfu
    exact ⟨r, h, by simp [copyM, liftG, hc, Except.map], ⟨hle, hpres⟩, hu', hna',
      closed_unfold fuel r u hu', fun z hz => ⟨Or.inr (hrange z hz).1, (hrange z hz).2⟩⟩
  let s3 : St T := ⟨g, advN rng 3⟩
  obtain ⟨as, g1, hrun, hext1, hmap, htr, hpd, hreach⟩ :=
    kidsWith_ok nops.length nf sv (copyM nops.length false fuel x) carry u g 0 fuel h1 h2 hF
      (Nat.zero_le _) hcopy i 1 s3 (ext_refl _)
  have hnew : ∀ b ∈ as, ∀ z : Nat, Graph.Reachable g1.view b z → g.next ≤ z ∧ z < g1.next := by
    intro b hb z hz
    obtain ⟨h3, h4⟩ := hreach b hb z hz
    rcases h3 with h3 | ⟨h3, _⟩
    · exact ⟨h3, h4⟩
    · omega
  have hnl : nLeaves carry 1 i = i - 1 := by unfold nLeaves; split <;> omega
  have hkl : ∀ k c j, (kidsT s3.rng nf sv carry u c j k).length = k := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih => intro c j; simp only [kidsT]; split <;> simp [ih]
  have hlen : as.length = i := by
    have := mapM_length _ _ _ hmap
    have := hkl i s3.rng.cursor 1
    omega
  have ho : rangeAt rng (rng.cursor + 1 + 2 * i) (opsOf nops i) ≤ 255 := by
    have := (rng.indexDraws (opsOf nops i - 1) (rng.cursor + 1 + 2 * i)).isLt
    have := opsOf_le h255 hi1 hiD
    simp only [rangeAt]; omega
  have hasne : as ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
  -- the new operator node
  obtain ⟨g2, hk, hext2, hu2, _, hc2⟩ := ctor_kids_ok (rng := advN rng (2 + 2 * i)) g1 nops.length
    (rangeAt rng (rng.cursor + 1 + 2 * i) (opsOf nops i)) fuel as _ (by omega) hasne ho hmap htr hpd
  -- `set_node!(node, newnode)`
  have hx2 : g2.cells x = some tc := by
    rw [hext2.2 x (Nat.lt_of_lt_of_le hxlt hext1.1), hext1.2 x hxlt, htc]
  obtain ⟨g3, hsn, hoth3, hnx3, c', hc', hdeg', hop', hact'⟩ :=
    setNode_branch_ok g2 nops.length x g1.next _ as tc hx2 hc2 (by omega) (by omega)
  -- the children are unchanged by the write to `x`
  have hag : ∀ b ∈ as, ∀ y, Graph.Reachable g1.view b y → g3.view.cells y = g1.view.cells y := by
    intro b hb y hy
    have hy1 := hnew b hb y hy
    have hyx : y ≠ x := fun h => by rw [h] at hy1; omega
    rw [DynExpr.NoAlias.view_cells, DynExpr.NoAlias.view_cells, hoth3 y hyx, hext2.2 y hy1.2]
  have hsame : ∀ b ∈ as, SameKidsOn g1.view g3.view b := fun b hb => sameKids_of_agree (hag b hb)
  have hmap3 : as.mapM (Graph.unfold g3.view fuel) = as.mapM (Graph.unfold g1.view fuel) :=
    mapM_congr' _ _ as (fun b hb => unfold_agree fuel b (hag b hb))
  have hx3 : Graph.unfold g3.view (fuel + 1) x =
      some (.branch (rangeAt rng (rng.cursor + 1 + 2 * i) (opsOf nops i))
        (kidsT s3.rng nf sv carry u s3.rng.cursor 1 i)) := by
    refine unfold_of_cell (view_cells hc') (by simp only [SCell.toCell]; rw [hact', hdeg'])
      (Or.inr ⟨by show c'.degree ≠ 0; omega, _, ?_, by rw [← hop']; rfl⟩)
    simp only [SCell.toCell]
    rw [hact', hmap3, hmap]
  -- the rest of the tree is unchanged
  have hagree : ∀ b, Graph.Reachable g.view tree b → b ≠ x → g3.view.cells b = g.view.cells b := by
    intro b hb hbx
    have hb' : @LT.lt Nat _ b g.next := closed_lt hcl hb
    rw [DynExpr.NoAlias.view_cells, DynExpr.NoAlias.view_cells, hoth3 b hbx,
      hext2.2 b (Nat.lt_of_lt_of_le hb' hext1.1), hext1.2 b hb']
  have hres := rewrite_sub g.view g3.view x _ (fuel + 1) hx3 fuel tree t hu hna
    (fun b hb hnr => hagree b hb (fun he => hnr (he ▸ reach_refl _ _))) P _ hP (hrepl _)
  -- alias-freedom
  have hnax : Graph.NoAlias g3.view x := by
    have hcx : g3.view.cells x = some c'.toCell := view_cells hc'
    have hch : c'.toCell.children = as := by simp only [SCell.toCell]; exact hact'
    refine noAlias_node hcx (by rw [hch]; exact hpd.1) ?_ ?_ ?_
    · intro b hb; rw [hch] at hb
      exact noAlias_transfer (hsame b hb) (htr b hb).1
    · intro b hb hr; rw [hch] at hb
      have := (hnew b hb x ((reach_transfer (hsame b hb)).mp hr)).1
      omega
    · intro b hb b' hb' hne; rw [hch] at hb hb'
      exact disjoint_transfer (hsame b hb) (hsame b' hb') (hpd.2 b hb b' hb' hne)
  have hfresh : ∀ z, Graph.Reachable g3.view x z → z = x ∨ ¬ Graph.Reachable g.view tree z := by
    intro z hz
    rcases reach_inv hz with rfl | ⟨c0, b, hc0, hb, hbz⟩
    · exact Or.inl rfl
    · rw [view_cells hc'] at hc0; cases hc0
      have hb' : b ∈ as := by simpa only [SCell.toCell, hact'] using hb
      have := (hnew b hb' z ((reach_transfer (hsame b hb')).mp hbz)).1
      exact Or.inr (fun hr => by have : @LT.lt Nat _ z g.next := closed_lt hcl hr; omega)
  obtain ⟨hna', _⟩ := graft_noAlias hna hP hagree hnax hfresh
  have hrk : kidsT s3.rng nf sv carry u s3.rng.cursor 1 i = kidsT rng nf sv carry u (rng.cursor + 3) 1 i := by
    rw [kidsT_advN]; rfl
  refine ⟨u, g3, advN rng (2 + 2 * i), ?_, hpu, by rw [hdeg]; exact hi1, by rw [hdeg]; exact hiD,
    by rw [hdeg]; exact hpos, by rw [hcar]; exact hc1, by rw [hcar, hdeg]; exact hci, ?_, ?_, ?_,
    hna', ?_, by simp only [advN, hdeg]; omega⟩
  · simp only [insertRandomOp]
    rw [bindM hsamp, bindM (randU_ok _)]
    have hdr : (St.mk (St.mk g rng).g (adv (St.mk g rng).rng) : St T).rng.draws
        (St.mk (St.mk g rng).g (adv (St.mk g rng).rng) : St T).rng.cursor =
        rng.draws (rng.cursor + 1) := rfl
    rw [hdr, hi, bindM (randRange_ok i hi1 _)]
    show (kidsWith nops.length nf (sampleReal sv) (copyM nops.length false fuel x) (rangeAt rng (rng.cursor + 2) i)
      1 i >>= fun cs => _) s3 = _
    rw [hcy, bindM hrun, hnl, bindM (liftJ_ok (nopsAt_ok hi1 hiD) _), bindM (randRange_ok _ hpos _)]
    have ho' : ((advN s3.rng (2 * (i - 1))).indexDraws (opsOf nops i - 1)
        (advN s3.rng (2 * (i - 1))).cursor).val + 1 =
        rangeAt rng (rng.cursor + 1 + 2 * i) (opsOf nops i) := by
      simp only [rangeAt, advN, s3]
      congr 3
      omega
    rw [ho']
    have hst : adv (advN s3.rng (2 * (i - 1))) = advN rng (2 + 2 * i) := by
      simp only [adv, advN, s3]
      congr 1
      omega
    show (ctorM nops.length _ >>= fun newnode => _) ⟨g1, adv (advN s3.rng (2 * (i - 1)))⟩ = _
    rw [hst, bindM hk, bindM (setNodeM_ok (s := ⟨g2, advN rng (2 + 2 * i)⟩) hsn)]
    rfl
  · unfold insertTree
    rw [hdeg, hcar, ← hrk]
    exact hres
  · rw [hcar, hdeg]
    exact kidsT_get _ _ _ _ _ i _ 1 hc1 (by omega)
  · unfold insertTree
    rw [hdeg, hcar]
    have := replaceAt_size t _ u (.branch (rangeAt rng (rng.cursor + 1 + 2 * i) (opsOf nops i))
      (kidsT rng nf sv carry u (rng.cursor + 3) 1 i)) hpu
    rw [Tree.size_branch, kidsT_size] at this
    have hc' : 1 ≤ carry ∧ carry < 1 + i := by omega
    simp only [hc', and_self, ↓reduceIte, nLeaves] at this
    omega
  · rw [hnx3]
    exact Nat.le_trans hext1.1 (Nat.le_trans hext2.1 (Nat.le_refl _))

end SymReg.Mutations
