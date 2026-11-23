import SymReg.Mutations.Leaf

/-!
The children tuples `@ntuple(i, j -> j == carry ? X : make_random_leaf(...))` of
`insert_random_op` and `prepend_random_op` (`src/MutationFunctions.jl:281-288,328-335`), and
`prepend_random_op` (`src/MutationFunctions.jl:312-342`): statement and proof.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ## Children tuples with one carried slot -/

/-- The trees of the children tuple of `kidsWith`: slot `j` is `u` when `j = carry`, otherwise
the `make_random_leaf` leaf drawn from cursor `c` (two draws per leaf). -/
def kidsT (rng : RNG) (nf : Nat) (sv : Rat → T) (carry : Nat) (u : Tree T) :
    Nat → Nat → Nat → List (Tree T)
  | _, _, 0 => []
  | c, j, k + 1 =>
    if j = carry then u :: kidsT rng nf sv carry u c (j + 1) k
    else leafAt rng c nf sv :: kidsT rng nf sv carry u (c + 2) (j + 1) k

/-- The number of leaf slots among `j, ..., j + k - 1`. -/
def nLeaves (carry j k : Nat) : Nat := if j ≤ carry ∧ carry < j + k then k - 1 else k

/-- The carried slot's action: from any heap extending `g0` it returns, without a draw and only
allocating, an alias-free tree unfolding to `u` whose objects lie below `lo` or are new. -/
def CarryOK (g0 : SGraph T) (lo F : Nat) (act : M T Addr) (u : Tree T) : Prop :=
  ∀ s : St T, Ext g0 s.g → ∃ a g', act s = .ok (a, ⟨g', s.rng⟩) ∧ Ext s.g g' ∧
    Graph.unfold g'.view F a = some u ∧ Graph.NoAlias g'.view a ∧ Closed g'.view a ∧
    ∀ z : Nat, Graph.Reachable g'.view a z → (z < lo ∨ s.g.next ≤ z) ∧ z < g'.next

theorem kidsT_advN (r : RNG) (n nf : Nat) (sv : Rat → T) (carry : Nat) (u : Tree T) :
    ∀ k c j, kidsT (advN r n) nf sv carry u c j k = kidsT r nf sv carry u c j k := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro c j
    simp only [kidsT]
    rw [ih, ih]
    rfl

theorem kidsT_size (rng : RNG) (nf : Nat) (sv : Rat → T) (carry : Nat) (u : Tree T) :
    ∀ k c j, ((kidsT rng nf sv carry u c j k).map Tree.size).sum =
      nLeaves carry j k + (if j ≤ carry ∧ carry < j + k then u.size else 0) := by
  intro k
  induction k with
  | zero => intro _ _; simp [kidsT, nLeaves]; intro _ _; omega
  | succ k ih =>
    intro c j
    simp only [kidsT]
    by_cases hj : j = carry
    · subst hj
      simp only [↓reduceIte, List.map_cons, List.sum_cons, ih, nLeaves]
      have h1 : ¬ (j + 1 ≤ j ∧ j < j + 1 + k) := by omega
      have h2 : j ≤ j ∧ j < j + (k + 1) := by omega
      simp only [h1, h2, and_self, ↓reduceIte, Nat.add_sub_cancel]
      omega
    · simp only [hj, ↓reduceIte, List.map_cons, List.sum_cons, ih, nLeaves]
      have hl : (leafAt rng c nf sv).size = 1 := by unfold leafAt; split <;> simp [Tree.size]
      rw [hl]
      by_cases hc : j + 1 ≤ carry ∧ carry < j + 1 + k
      · have hc' : j ≤ carry ∧ carry < j + (k + 1) := by omega
        simp only [hc, hc', and_self, ↓reduceIte]
        omega
      · have hc' : ¬ (j ≤ carry ∧ carry < j + (k + 1)) := by omega
        simp only [hc, hc', ↓reduceIte]
        omega

theorem kidsT_get (rng : RNG) (nf : Nat) (sv : Rat → T) (carry : Nat) (u : Tree T) :
    ∀ k c j, j ≤ carry → carry < j + k → (kidsT rng nf sv carry u c j k)[carry - j]? = some u := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
    intro c j h1 h2
    simp only [kidsT]
    by_cases hj : j = carry
    · subst hj; simp
    · simp only [hj, ↓reduceIte]
      rw [show carry - j = (carry - (j + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact ih _ _ (by omega) (by omega)

/-- Unfolding and the shape of a tree transfer to a heap that only adds objects. -/
theorem ext_tree {g h : SGraph T} (he : Ext g h) {a : Addr} (hc : Closed g.view a) :
    (∀ f, Graph.unfold h.view f a = Graph.unfold g.view f a) ∧
      (Graph.NoAlias g.view a → Graph.NoAlias h.view a) ∧ Closed h.view a ∧
      ∀ z, Graph.Reachable h.view a z ↔ Graph.Reachable g.view a z := by
  have hs := sameKidsOn_ext he hc
  refine ⟨fun f => unfold_agree f a (fun x hx => ?_), noAlias_transfer hs, closed_transfer hs hc,
    fun z => reach_transfer hs⟩
  rw [DynExpr.NoAlias.view_cells, DynExpr.NoAlias.view_cells, he.2 x (closed_lt hc hx)]

theorem mapM_ext {g h : SGraph T} (he : Ext g h) (f : Nat) (as : List Addr)
    (hcl : ∀ b ∈ as, Closed g.view b) :
    as.mapM (Graph.unfold h.view f) = as.mapM (Graph.unfold g.view f) :=
  mapM_congr' _ _ as (fun b hb => (ext_tree he (hcl b hb)).1 f)

theorem pairDisj_cons {g : Graph T} {a : Addr} {as : List Addr} (hp : PairDisj g as)
    (hd : ∀ b ∈ as, Disjoint g a b) : PairDisj g (a :: as) := by
  refine ⟨List.nodup_cons.mpr ⟨fun ha => hd a ha a (reach_refl _ _) (reach_refl _ _), hp.1⟩, ?_⟩
  intro b hb b' hb' hne
  rcases List.mem_cons.mp hb with h | hb <;> rcases List.mem_cons.mp hb' with h' | hb'
  · exact absurd (h.trans h'.symm) hne
  · rw [h]; exact hd b' hb'
  · rw [h']; exact disjoint_symm (hd b hb)
  · exact hp.2 b hb b' hb' hne

theorem leaf_alloc_ext (g : SGraph T) (c : SCell T) : Ext g (g.alloc c).2 :=
  ⟨by simp [Heap.alloc], fun x hx => by simp [Heap.alloc, Nat.ne_of_lt hx]⟩

/-- `kidsWith` builds `k` alias-free, closed, pairwise disjoint children: fresh leaves in the
non-carried slots and the carried tree in slot `carry`; only the carried tree may hold objects
below `lo`. -/
theorem kidsWith_ok (D nf : Nat) (sv : Rat → T) (act : M T Addr) (carry : Nat) (u : Tree T)
    (g0 : SGraph T) (lo F : Nat) (h1 : 1 ≤ nf) (h2 : nf ≤ 65535) (hF : 1 ≤ F)
    (hlo : lo ≤ g0.next) (hact : CarryOK g0 lo F act u) :
    ∀ (k j : Nat) (s : St T), Ext g0 s.g →
      ∃ (as : List Addr) (g' : SGraph T),
        kidsWith D nf (sampleReal sv) act carry j k s = .ok (as, ⟨g', advN s.rng (2 * nLeaves carry j k)⟩) ∧
        Ext s.g g' ∧
        as.mapM (Graph.unfold g'.view F) = some (kidsT s.rng nf sv carry u s.rng.cursor j k) ∧
        Trees g'.view as ∧ PairDisj g'.view as ∧
        ∀ b ∈ as, ∀ z : Nat, Graph.Reachable g'.view b z →
          (s.g.next ≤ z ∨ (z < lo ∧ j ≤ carry ∧ carry < j + k)) ∧ z < g'.next := by
  intro k
  induction k with
  | zero =>
    intro j s _
    have h0 : nLeaves carry j 0 = 0 := by unfold nLeaves; split <;> rfl
    refine ⟨[], s.g, ?_, ext_refl _, rfl, trees_nil _, pairDisj_nil _,
      fun b hb => absurd hb List.not_mem_nil⟩
    rw [h0]
    rfl
  | succ k ih =>
    intro j s hs
    by_cases hj : j = carry
    · subst hj
      obtain ⟨a, g1, hrun1, hext1, hu1, hna1, hcl1, hr1⟩ := hact s hs
      obtain ⟨as, g', hrun2, hext2, hmap, htr, hpd, hreach⟩ :=
        ih (j + 1) ⟨g1, s.rng⟩ (ext_trans hs hext1)
      have hn1 : nLeaves j j (k + 1) = nLeaves j (j + 1) k := by unfold nLeaves; split <;> split <;> omega
      have ⟨hu', hna', hcl', hre'⟩ := ext_tree hext2 hcl1
      have hfresh : ∀ b ∈ as, ∀ z, Graph.Reachable g'.view b z → g1.next ≤ z := by
        intro b hb z hz
        rcases (hreach b hb z hz).1 with h | ⟨_, h, _⟩
        · exact h
        · omega
      refine ⟨a :: as, g', ?_, ext_trans hext1 hext2, ?_, ?_, ?_, ?_⟩
      · simp only [kidsWith, ↓reduceIte]
        rw [bindM hrun1]
        show (kidsWith D nf (sampleReal sv) act j (j + 1) k >>= fun as => pure (a :: as)) ⟨g1, s.rng⟩ = _
        rw [bindM hrun2, hn1]
        rfl
      · rw [List.mapM_cons, hu', hu1, hmap]
        simp [kidsT]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨hna' hna1, hcl'⟩
        · exact htr b hb
      · refine pairDisj_cons hpd (fun b hb z hz hz' => ?_)
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hr1 z ((hre' z).mp hz)).2 (hfresh b hb z hz'))
      · intro b hb z hz
        rcases List.mem_cons.mp hb with rfl | hb
        · obtain ⟨h3, h4⟩ := hr1 z ((hre' z).mp hz)
          refine ⟨?_, Nat.lt_of_lt_of_le h4 hext2.1⟩
          rcases h3 with h3 | h3
          · exact Or.inr ⟨h3, by omega, by omega⟩
          · exact Or.inl h3
        · exact ⟨Or.inl (Nat.le_trans hext1.1 (hfresh b hb z hz)), (hreach b hb z hz).2⟩
    · let s1 : St T := ⟨(s.g.alloc (leafCellAt s.rng s.rng.cursor nf sv)).2, advN s.rng 2⟩
      have hext1 : Ext s.g s1.g := leaf_alloc_ext _ _
      have hc1 : s1.g.cells s.g.next = some (leafCellAt s.rng s.rng.cursor nf sv) := by
        simp [s1, Heap.alloc]
      have hn1 : s1.g.next = s.g.next + 1 := rfl
      obtain ⟨as, g', hrun2, hext2, hmap, htr, hpd, hreach⟩ := ih (j + 1) s1 (ext_trans hs hext1)
      have hc' : g'.cells s.g.next = some (leafCellAt s.rng s.rng.cursor nf sv) := by
        rw [hext2.2 _ (by omega), hc1]
      have hleaf : ∀ cb, g'.view.cells s.g.next = some cb → cb.children = [] := by
        intro cb hcb
        rw [view_cells hc'] at hcb; cases hcb
        simp [SCell.toCell, (leafCellAt_degree _ _ _ _).2.2]
      have hnl : 2 + 2 * nLeaves carry (j + 1) k = 2 * nLeaves carry j (k + 1) := by
        unfold nLeaves; split <;> split <;> omega
      refine ⟨s.g.next :: as, g', ?_, ext_trans hext1 hext2, ?_, ?_, ?_, ?_⟩
      · simp only [kidsWith, hj, ↓reduceIte]
        rw [bindM (makeRandomLeaf_ok D nf sv s h1 h2)]
        show (kidsWith D nf (sampleReal sv) act carry (j + 1) k >>= fun as => pure (s.g.next :: as)) s1 = _
        rw [bindM hrun2]
        show (Except.ok (_, (⟨g', advN (advN s.rng 2) (2 * nLeaves carry (j + 1) k)⟩ : St T)) :
          Except JlError _) = _
        rw [advN_advN, hnl]
      · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
        rw [List.mapM_cons, leafCellAt_unfold hc' F', hmap]
        simp only [kidsT, hj, ↓reduceIte]
        rw [kidsT_advN]
        rfl
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · refine ⟨noAlias_leaf hleaf, fun z hz => ?_⟩
          rw [reach_leafobj hleaf hz, view_cells hc']; rfl
        · exact htr b hb
      · refine pairDisj_cons hpd (fun b hb z hz hz' => ?_)
        have hz0 := reach_leafobj hleaf hz
        rw [hz0] at hz'
        rcases (hreach b hb _ hz').1 with h | ⟨h, _, _⟩
        · rw [hn1] at h; exact Nat.not_succ_le_self _ h
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (Nat.le_trans hlo hs.1))
      · intro b hb z hz
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [reach_leafobj hleaf hz]
          exact ⟨Or.inl (Nat.le_refl _), Nat.lt_of_lt_of_le (by omega) hext2.1⟩
        · obtain ⟨h3, h4⟩ := hreach b hb z hz
          refine ⟨?_, h4⟩
          rcases h3 with h3 | ⟨h3, h5, h6⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨h3, by omega, by omega⟩

/-- The operator node over built children: the constructor allocates one object whose subtrees
are exactly the children. -/
theorem ctor_kids_ok {rng : RNG} (g : SGraph T) (D o F : Nat) (as : List Addr) (ts : List (Tree T))
    (hl : as.length ≤ D) (hne : as ≠ []) (ho : o ≤ 255)
    (hmap : as.mapM (Graph.unfold g.view F) = some ts) (htr : Trees g.view as)
    (hpd : PairDisj g.view as) :
    ∃ g' : SGraph T, ctorM D { op := some o, children := some as } ⟨g, rng⟩ =
        .ok (g.next, ⟨g', rng⟩) ∧ Ext g g' ∧
      Graph.unfold g'.view (F + 1) g.next = some (.branch o ts) ∧ Graph.NoAlias g'.view g.next ∧
      g'.cells g.next = some (branchCell D o as) := by
  obtain ⟨g', hk, hnx, hoth, hc⟩ := ctor_branch_ok g D o as hl ho
  have hb := (ctor_built (kw := { op := some o, children := some as }) htr hpd hk).2
  have hact : (branchCell (T := T) D o as).active = as := branchCell_active D o as hl
  refine ⟨g', by simp [ctorM, liftG, hk, Except.map], hb.ext, ?_, hb.noAlias, hc⟩
  refine unfold_of_cell (view_cells hc) (by simp only [SCell.toCell]; rw [hact]; rfl)
    (Or.inr ⟨?_, ts, ?_, rfl⟩)
  · show as.length ≠ 0
    exact fun h => hne (List.eq_nil_of_length_eq_zero h)
  simp only [SCell.toCell, hact]
  rw [mapM_ext hb.ext F as (fun b hb' => (htr b hb').2), hmap]

theorem liftJ_ok {α : Type} {x : Jl α} {a : α} (h : x = .ok a) (s : St T) :
    liftJ x s = .ok (a, s) := by
  simp [liftJ, h, Except.map]

/-! ## `prepend_random_op` -/

/-- The degree chosen by `prepend_random_op` from the real draw at the cursor. -/
def prependDeg (rng : RNG) (nops : List Nat) : Nat :=
  pickDeg nops.length nops (scaledDegreeDraw (rng.draws rng.cursor) nops)

/-- The tree returned by `prepend_random_op`: an operator of degree `i` (operator draw at cursor
`c + 2i`) whose `carry`-th child (`carry` the draw at `c + 1`) is the old tree and whose other
children are fresh leaves (draws from `c + 2`). -/
def prependTree (t : Tree T) (rng : RNG) (nops : List Nat) (nf : Nat) (sv : Rat → T) : Tree T :=
  .branch (rangeAt rng (rng.cursor + 2 * prependDeg rng nops) (opsOf nops (prependDeg rng nops)))
    (kidsT rng nf sv (rangeAt rng (rng.cursor + 1) (prependDeg rng nops)) t (rng.cursor + 2) 1
      (prependDeg rng nops))

/-- `prepend_random_op(tree, options, nfeatures, rng)` ("Add random node to the top of a tree") on
an alias-free plain `Node` tree, for a degree draw strictly inside `(0, 1)` (the draw `0` is
`mut-pick-degree-has-operator`): it returns a new root object and changes no existing object. The
degree `i` is the `csum` bucket of the first draw and has an operator; the second draw `carry` is
uniform in `1:i`; the result unfolds to an operator of degree `i` whose `carry`-th child is the old
tree and whose other `i - 1` children are fresh random leaves, so the node count grows by exactly
`i`; the result is alias-free and `1 + 2i` draws are consumed. -/
def prepend_random_op_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf tree : Nat) (t : Tree T) (nops : List Nat)
    (sv : Rat → T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree →
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 → 0 < nops.sum →
    0 < scaledDegreeDraw (rng.draws rng.cursor) nops →
    scaledDegreeDraw (rng.draws rng.cursor) nops < (nops.sum : Rat) →
    ∃ r g' rng', prependRandomOp D nf nops (sampleReal sv) tree ⟨g, rng⟩ = .ok (r, ⟨g', rng'⟩) ∧
      g.next ≤ r ∧ (∀ a, a < g.next → g'.cells a = g.cells a) ∧
      1 ≤ prependDeg rng nops ∧ prependDeg rng nops ≤ D ∧ 0 < opsOf nops (prependDeg rng nops) ∧
      1 ≤ rangeAt rng (rng.cursor + 1) (prependDeg rng nops) ∧
      rangeAt rng (rng.cursor + 1) (prependDeg rng nops) ≤ prependDeg rng nops ∧
      Graph.unfold g'.view (fuel + 1) r = some (prependTree t rng nops nf sv) ∧
      kidAt (prependTree t rng nops nf sv) (rangeAt rng (rng.cursor + 1) (prependDeg rng nops)) = t ∧
      (prependTree t rng nops nf sv).size = t.size + prependDeg rng nops ∧
      Graph.NoAlias g'.view r ∧ rng'.cursor = rng.cursor + 1 + 2 * prependDeg rng nops

/-- An interior scaled draw selects a degree with an operator. -/
theorem pick_ok {nops : List Nat} {u : Rat} (hsum : 0 < nops.sum)
    (hu0 : 0 < u) (hu1 : u < (nops.sum : Rat)) :
    1 ≤ pickDeg nops.length nops u ∧ pickDeg nops.length nops u ≤ nops.length ∧
      0 < opsOf nops (pickDeg nops.length nops u) := by
  have hD : 1 ≤ nops.length := by
    cases nops with
    | nil => simp at hsum
    | cons _ _ => simp
  obtain ⟨hi1, hiD, _, _, hpos⟩ := pick_degree_interval_holds nops _ hD hu0 hu1
  exact ⟨hi1, hiD, hpos⟩

theorem prepend_random_op_spec_holds : prepend_random_op_spec := by
  intro T g D fuel nf tree t nops sv rng hu hna hlen h255 h1 h2 hsum hu0 hu1
  subst hlen
  obtain ⟨hi1, hiD, hpos⟩ := pick_ok hsum hu0 hu1
  generalize hi : pickDeg nops.length nops (scaledDegreeDraw (rng.draws rng.cursor) nops) = i
    at hi1 hiD hpos
  have hdeg : prependDeg rng nops = i := hi
  have hF : 1 ≤ fuel := by
    cases fuel with
    | zero => simp [Graph.unfold] at hu
    | succ _ => omega
  have hcl := closed_unfold fuel tree t hu
  -- the carried slot is the old tree itself
  have hcarry : CarryOK g g.next fuel (pure tree) t := by
    intro s hs
    obtain ⟨hu', hna', hcl', hre'⟩ := ext_tree hs hcl
    refine ⟨tree, s.g, rfl, ext_refl _, by rw [hu']; exact hu, hna' hna, hcl', fun z hz => ?_⟩
    have := closed_lt hcl ((hre' z).mp hz)
    exact ⟨Or.inl this, Nat.lt_of_lt_of_le this hs.1⟩
  generalize hcy : rangeAt rng (rng.cursor + 1) i = carry
  have hc1 : 1 ≤ carry := by rw [← hcy]; simp [rangeAt]
  have hci : carry ≤ i := by
    rw [← hcy]; have := (rng.indexDraws (i - 1) (rng.cursor + 1)).isLt; simp only [rangeAt]; omega
  let s2 : St T := ⟨g, advN rng 2⟩
  obtain ⟨as, g1, hrun, hext1, hmap, htr, hpd, _⟩ :=
    kidsWith_ok nops.length nf sv (pure tree) carry t g g.next fuel h1 h2 hF (Nat.le_refl _) hcarry
      i 1 s2 (ext_refl _)
  have hnl : nLeaves carry 1 i = i - 1 := by unfold nLeaves; split <;> omega
  have hkl : ∀ k c j, (kidsT s2.rng nf sv carry t c j k).length = k := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih => intro c j; simp only [kidsT]; split <;> simp [ih]
  have hlen : as.length = i := by
    have := mapM_length _ _ _ hmap
    have := hkl i s2.rng.cursor 1
    omega
  have ho : rangeAt rng (rng.cursor + 2 * i) (opsOf nops i) ≤ 255 := by
    have := (rng.indexDraws (opsOf nops i - 1) (rng.cursor + 2 * i)).isLt
    have := opsOf_le h255 hi1 hiD
    simp only [rangeAt]; omega
  obtain ⟨g2, hk, hext2, hu2, hna2, _⟩ := ctor_kids_ok (rng := advN rng (1 + 2 * i)) g1 nops.length
    (rangeAt rng (rng.cursor + 2 * i) (opsOf nops i)) fuel as _ (by omega)
    (fun h => by rw [h] at hlen; simp at hlen; omega) ho hmap htr hpd
  refine ⟨g1.next, g2, advN rng (1 + 2 * i), ?_, hext1.1, fun a ha => ?_, by rw [hdeg]; exact hi1,
    by rw [hdeg]; exact hiD, by rw [hdeg]; exact hpos, by rw [hdeg, hcy]; exact hc1,
    by rw [hdeg, hcy]; exact hci, ?_, ?_, ?_, hna2, by simp only [advN, hdeg]; omega⟩
  · simp only [prependRandomOp, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [bindM (randU_ok _)]
    simp only [hi]
    rw [bindM (randRange_ok i hi1 _)]
    have hc' : ((adv rng).indexDraws (i - 1) (adv rng).cursor).val + 1 = carry := by
      rw [← hcy]; rfl
    rw [hc']
    show (kidsWith nops.length nf (sampleReal sv) (pure tree) carry 1 i >>= fun cs => _) s2 = _
    rw [bindM hrun, hnl]
    rw [bindM (liftJ_ok (nopsAt_ok hi1 hiD) _)]
    rw [bindM (randRange_ok _ hpos _)]
    have ho' : ((advN s2.rng (2 * (i - 1))).indexDraws (opsOf nops i - 1)
        (advN s2.rng (2 * (i - 1))).cursor).val + 1 = rangeAt rng (rng.cursor + 2 * i) (opsOf nops i) := by
      simp only [rangeAt, advN, s2]
      congr 3
      omega
    rw [ho']
    have hst : adv (advN s2.rng (2 * (i - 1))) = advN rng (1 + 2 * i) := by
      simp only [adv, advN, s2]
      congr 1
      omega
    show ctorM nops.length _ ⟨g1, adv (advN s2.rng (2 * (i - 1)))⟩ = _
    rw [hst]
    exact hk
  · rw [hext2.2 a (Nat.lt_of_lt_of_le ha hext1.1), hext1.2 a ha]
  · unfold prependTree
    rw [hdeg, hcy]
    rw [hu2]
    congr 2
    rw [kidsT_advN]
    rfl
  · unfold prependTree kidAt
    rw [hdeg, hcy]
    simp only
    rw [show carry - 1 = carry - 1 from rfl, kidsT_get _ _ _ _ _ i _ 1 hc1 (by omega)]
    rfl
  · unfold prependTree
    rw [hdeg, hcy, Tree.size_branch, kidsT_size]
    have hc' : 1 ≤ carry ∧ carry < 1 + i := by omega
    simp only [hc', and_self, ↓reduceIte, nLeaves]
    omega

end SymReg.Mutations
