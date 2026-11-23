import SymReg.Mutations.Write

/-! Proof of `swap_operands_spec` (`src/MutationFunctions.jl:88-101`). -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

theorem getChildM_ok' {s : St T} {D x i : Nat} {c : SCell T} (hc : s.g.cells x = some c)
    (hl : c.active.length = c.degree) (hD : c.degree ≤ D) (h1 : 1 ≤ i) (hi : i ≤ c.degree) :
    getChildM D x i s = .ok ((c.active[i - 1]?).getD 0, s) := by
  have := getChildM_ok hc hl hD (i := i - 1) (by omega)
  rwa [Nat.sub_add_cancel h1] at this

theorem setChildM_ok' {s : St T} {D p x j : Nat} {c : SCell T} (hc : s.g.cells p = some c)
    (hl : c.active.length = c.degree) (hD : c.degree ≤ D) (h1 : 1 ≤ j) (hj : j ≤ c.degree)
    (hsl : ∀ sl, c.slots = some sl → sl.length ≤ D) :
    ∃ (g' : SGraph T) (c' : SCell T), setChildM D p x j s = .ok ((), { s with g := g' }) ∧
      (∀ b, b ≠ p → g'.cells b = s.g.cells b) ∧ g'.next = s.g.next ∧ g'.cells p = some c' ∧
      c'.active = c.active.set (j - 1) x ∧ c'.degree = c.degree ∧ c'.op = c.op ∧
      c'.constant = c.constant ∧ c'.val = c.val ∧ c'.feature = c.feature ∧
      (∀ sl, c'.slots = some sl → sl.length ≤ D) := by
  have := setChildM_ok (s := s) (x := x) hc hl hD (j := j - 1) (by omega) hsl
  rwa [Nat.sub_add_cancel h1] at this

theorem secondIdx_ok (s : St T) (deg i1 : Nat) (h2 : 2 ≤ deg) (hi1 : 1 ≤ i1) (hi1' : i1 ≤ deg) :
    ∃ s' : St T, secondIdx deg i1 s = .ok (secondAt s.rng s.rng.cursor deg i1, s') ∧
      s'.g = s.g ∧ secondAt s.rng s.rng.cursor deg i1 ≠ i1 ∧
      1 ≤ secondAt s.rng s.rng.cursor deg i1 ∧ secondAt s.rng s.rng.cursor deg i1 ≤ deg := by
  by_cases hd : deg = 2
  · subst hd
    refine ⟨s, by simp only [secondIdx, secondAt, ↓reduceIte]; rfl, rfl, ?_⟩
    simp only [secondAt, ↓reduceIte]
    split <;> omega
  · have hne : (List.range' 1 deg).filter (· ≠ i1) ≠ [] := by
      intro he
      have : (if i1 = 1 then 2 else 1) ∈ (List.range' 1 deg).filter (· ≠ i1) := by
        simp only [List.mem_filter, List.mem_range'_1]
        split <;> simp_all <;> omega
      rw [he] at this; simp at this
    have hmem := drawAt_mem (rng := s.rng) (c := s.rng.cursor) hne
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hmem
    refine ⟨{ s with rng := adv s.rng }, ?_, rfl, ?_⟩
    · simp only [secondIdx, hd, ↓reduceIte, secondAt]
      exact randElem_ok _ hne s
    · simp only [secondAt, hd, ↓reduceIte]
      omega

theorem mem_set_of_mem {α : Type} {l : List α} {i : Nat} {a y : α} (hy : y ∈ l.set i a) :
    y ∈ l ∨ y = a := by
  rw [List.mem_iff_getElem?] at hy
  obtain ⟨m, hm⟩ := hy
  rw [List.getElem?_set] at hm
  split at hm
  · split at hm
    · simp at hm; exact Or.inr hm.symm
    · simp at hm
  · exact Or.inl (List.mem_of_getElem? hm)

theorem swap_operands_unshared_holds : swap_operands_unshared := by
  intro T g D fuel tree t rng hu hna hdeg hsl
  have hany := anyM_kind (⟨g, rng⟩ : St T) D fuel tree t
    (fun _ c => decide (c.degree > 1)) isMultiT (fun _ _ => rfl) lk_multi hu hdeg
  cases hq : (preorder t).any isMultiT
  · refine ⟨g, rng, ?_, fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide)⟩
    simp only [swapOperands]
    rw [bindM hany, hq]
    rfl
  obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hQu, hf', hun, hrepl, _⟩ :=
    sample_kind ⟨g, rng⟩ fuel tree t _ isMultiT lk_multi hu hq
  obtain ⟨c, hcx, hlx, hdx, hcase⟩ := cell_of_unfold hun
  obtain ⟨c0, hc0, _, hdD⟩ := good_reach g D fuel tree t hu hdeg x ⟨P, hP⟩
  rw [hcx] at hc0; cases hc0
  rcases hcase with ⟨hd, _⟩ | ⟨_, ts, hts, rfl⟩
  · rw [hd] at hdx; simp [isMultiT, ← hdx] at hQu
  have hlts : ts.length = c.degree := by rw [mapM_length _ _ _ hts, hlx]
  have hdegu : (Tree.branch c.op ts).degree = c.degree := by simp [Tree.degree, hlts]
  have hd2 : 2 ≤ c.degree := by
    simp only [isMultiT, decide_eq_true_eq] at hQu; rw [hdegu] at hQu; omega
  simp only [Nat.add_sub_cancel] at hts
  -- the two argument positions
  let s1 : St T := { g := g, rng := adv rng }
  let i1 := (s1.rng.indexDraws (c.degree - 1) s1.rng.cursor).val + 1
  have hi1 : i1 ≤ c.degree := by
    have := (s1.rng.indexDraws (c.degree - 1) s1.rng.cursor).isLt
    simp only [i1]; omega
  let s2 : St T := { s1 with rng := adv s1.rng }
  obtain ⟨s3, hsec, hs3g, hne12, hi2a, hi2b⟩ :=
    secondIdx_ok s2 c.degree i1 hd2 (by simp [i1]) hi1
  generalize hi2 : secondAt s2.rng s2.rng.cursor c.degree i1 = i2 at hsec hne12 hi2a hi2b
  -- the children reads and writes
  have hcx3 : s3.g.cells x = some c := by rw [hs3g]; exact hcx
  let n1 := (c.active[i1 - 1]?).getD 0
  let n2 := (c.active[i2 - 1]?).getD 0
  have hg1 := getChildM_ok' (s := s3) (D := D) hcx3 hlx hdD (by simp [i1]) hi1
  have hg2 := getChildM_ok' (s := s3) (D := D) hcx3 hlx hdD hi2a hi2b
  obtain ⟨g4, c4, hset4, hoth4, _, hx4, hact4, hdeg4, hop4, _, _, _, hsl4⟩ :=
    setChildM_ok' (s := s3) (x := n2) hcx3 hlx hdD (by simp [i1]) hi1
      (fun sl h => hsl x c sl (Nat.zero_le _) hcx h)
  obtain ⟨g5, c5, hset5, hoth5, _, hx5, hact5, hdeg5, hop5, _, _, _, _⟩ :=
    setChildM_ok' (s := ({ s3 with g := g4 } : St T)) (x := n1) hx4
      (by rw [hact4, hdeg4, List.length_set, hlx]) (by omega) hi2a (by omega) hsl4
  have hrun : swapOperands D fuel tree false ⟨g, rng⟩ = .ok (tree, { s3 with g := g5 }) := by
    simp only [swapOperands]
    rw [bindM hany, hq]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bindM hsamp, bindM (rd_ok (s := s1) hcx), bindM (randRange_ok _ (by omega) s1),
      bindM hsec, bindM hg1, bindM hg2, bindM hset4, bindM hset5]
    rfl
  -- the swapped node unfolds to the swapped branch
  have hnax : Graph.NoAlias g.view x := noAlias_reach hna ⟨P, hP⟩
  have hv : g.view.cells x = some c.toCell := view_cells hcx
  have hoth : ∀ b, b ≠ x → g5.cells b = g.cells b := by
    intro b hb; rw [hoth5 b hb, hoth4 b hb, hs3g]
  have hmem : ∀ i, 1 ≤ i → i ≤ c.degree → (c.active[i - 1]?).getD 0 ∈ c.active := by
    intro i h1 h2
    have : i - 1 < c.active.length := by omega
    rw [List.getElem?_eq_getElem this]; exact List.getElem_mem this
  have hnr : ∀ y ∈ c5.active, ¬ Graph.Reachable g.view y x := by
    intro y hy
    have hy' : y ∈ c.active := by
      rw [hact5, hact4] at hy
      rcases mem_set_of_mem hy with hy | hy
      · rcases mem_set_of_mem hy with hy | hy
        · exact hy
        · rw [hy]; exact hmem i2 hi2a hi2b
      · rw [hy]; exact hmem i1 (by simp [i1]) hi1
    exact noAlias_child_not_reach hnax hv (by simpa [SCell.toCell] using hy')
  obtain ⟨v1, hv1⟩ : ∃ v, ts[i1 - 1]? = some v :=
    ⟨ts[i1 - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨v2, hv2⟩ : ∃ v, ts[i2 - 1]? = some v :=
    ⟨ts[i2 - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hu1 : Graph.unfold g.view f' n1 = some v1 := by
    obtain ⟨w, hw, hfw⟩ := mapM_get _ _ _ hts (i1 - 1) n1
      (by simp only [n1]; rw [List.getElem?_eq_getElem (by omega)]; simp)
    rw [hv1] at hw; cases hw; exact hfw
  have hu2 : Graph.unfold g.view f' n2 = some v2 := by
    obtain ⟨w, hw, hfw⟩ := mapM_get _ _ _ hts (i2 - 1) n2
      (by simp only [n2]; rw [List.getElem?_eq_getElem (by omega)]; simp)
    rw [hv2] at hw; cases hw; exact hfw
  have hts' : c5.active.mapM (Graph.unfold g.view f') =
      some ((ts.set (i1 - 1) v2).set (i2 - 1) v1) := by
    rw [hact5, hact4]
    apply mapM_set _ _ _ _ _ _ (mapM_set _ _ _ _ _ _ hts (by omega) hu2) (by simp; omega) hu1
  have hx' : Graph.unfold g5.view (f' + 1) x =
      some (.branch c.op ((ts.set (i1 - 1) v2).set (i2 - 1) v1)) := by
    have hv5 : g5.view.cells x = some c5.toCell := view_cells hx5
    refine unfold_of_cell hv5 (by simp [SCell.toCell, hact5, hact4, hdeg5, hdeg4, hlx]) ?_
    refine Or.inr ⟨by simp [SCell.toCell, hdeg5, hdeg4]; omega,
      (ts.set (i1 - 1) v2).set (i2 - 1) v1, ?_, by simp [SCell.toCell, hop5, hop4]⟩
    simp only [SCell.toCell]
    rw [mapM_agree c5.active hoth hnr, hts']
  have hres := write_node_spec hu hna hP hrepl hoth (f' + 1) (by omega) hx'
  refine ⟨g5, s3.rng, hrun, fun h => absurd h (by decide), fun _ => ⟨.branch c.op ts, hpu, ?_⟩⟩
  rw [hdegu]
  have hi2' : secondAt rng (rng.cursor + 2) c.degree i1 = i2 := hi2
  show i1 ≠ secondAt rng (rng.cursor + 2) c.degree i1 ∧
    1 ≤ secondAt rng (rng.cursor + 2) c.degree i1 ∧
    secondAt rng (rng.cursor + 2) c.degree i1 ≤ c.degree ∧
    Graph.unfold g5.view (fuel + fuel) tree =
      some (replaceAt t _ (swapKids i1 (secondAt rng (rng.cursor + 2) c.degree i1)
        (.branch c.op ts)))
  rw [hi2']
  refine ⟨hne12.symm, hi2a, hi2b, ?_⟩
  simp only [swapKids, hv1, hv2, Option.getD_some]
  exact hres

theorem swap_operands_spec_holds : swap_operands_spec := by
  refine ⟨swap_operands_unshared_holds, ?_⟩
  intro T s D fuel tree isGraph
  dsimp only
  constructor
  · intro h
    rw [swapOperands, bindM h]
    rfl
  · intro x c hany hsamp hc hd hD hl hslots
    let i := rangeAt s.rng (s.rng.cursor + 1) c.degree
    let j := secondAt s.rng (s.rng.cursor + 2) c.degree i
    let s1 : St T := { s with rng := adv s.rng }
    let s2 : St T := { s with rng := adv (adv s.rng) }
    let s3 : St T := { s with rng := if c.degree = 2 then s2.rng else adv s2.rng }
    have hi := (s.rng.indexDraws (c.degree - 1) (s.rng.cursor + 1)).isLt
    have hi1 : 1 ≤ i := by dsimp [i, rangeAt]; omega
    have hi2 : i ≤ c.degree := by dsimp [i, rangeAt]; omega
    obtain ⟨s4, hsec, h4, _, hj1, hj2⟩ := secondIdx_ok s2 c.degree i hd hi1 hi2
    change 1 ≤ j at hj1
    change j ≤ c.degree at hj2
    have h2nd : secondIdx c.degree i s2 = .ok (j, s3) := by
      by_cases he : c.degree = 2
      · simp [secondIdx, secondAt, s3, s2, adv, he, j, pureM]
      · have hne : (List.range' 1 c.degree).filter (· ≠ i) ≠ [] :=
          featureChoices_ne_nil (nf := c.degree) (f := i) hd
        simp only [secondIdx, he, ↓reduceIte]
        rw [randElem_ok _ hne s2]
        simp only [s3, he, ↓reduceIte, j, secondAt, drawAt]
        rfl
    let n1 := (c.active[i - 1]?).getD 0
    let n2 := (c.active[j - 1]?).getD 0
    have hr1 := getChildM_ok' (s := s3) (D := D) hc hl hD hi1 hi2
    have hr2 := getChildM_ok' (s := s3) (D := D) hc hl hD hj1 hj2
    obtain ⟨g4, c4, hw4, hf4, hn4, hc4, ha4, hd4, ho4, hk4, hv4, hfeat4, hslots4⟩ :=
      setChildM_ok' (s := s3) (x := n2) hc hl hD hi1 hi2 hslots
    obtain ⟨g5, c5, hw5, hf5, hn5, hc5, ha5, hd5, ho5, hk5, hv5, hfeat5, _⟩ :=
      setChildM_ok' (s := { s3 with g := g4 }) (x := n1) hc4
        (by rw [ha4, hd4, List.length_set, hl]) (by omega) hj1 (by omega) hslots4
    refine ⟨g5, c5, ?_, hn5.trans hn4, fun a ha => (hf5 a ha).trans (hf4 a ha),
      hc5, hd5.trans hd4, ho5.trans ho4, hv5.trans hv4, hfeat5.trans hfeat4,
      hk5.trans hk4, by rw [ha5, ha4]⟩
    simp only [swapOperands]
    rw [bindM hany]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bindM hsamp, bindM (rd_ok (s := s1) hc), bindM (randRange_ok _ (by omega) s1)]
    change (secondIdx c.degree i >>= _) s2 = _
    rw [bindM h2nd]
    change (getChildM D x i >>= fun n1 => getChildM D x j >>= fun n2 =>
      setChildM D x n2 i >>= fun _ => setChildM D x n1 j >>= fun _ => pure tree) s3 = _
    rw [bindM hr1, bindM hr2, bindM hw4, bindM hw5]
    rfl
