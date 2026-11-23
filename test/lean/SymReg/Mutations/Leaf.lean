import SymReg.Mutations.FixedSize

/-!
`make_random_leaf` and `_sample_leaf` (`src/MutationFunctions.jl:344-356,250`), `_make_node`
(`src/MutationFunctions.jl:423-445`), `random_node` (`src/MutationFunctions.jl:72-80`) and the
outer method of `mutate_value` (`src/MutationFunctions.jl:167-171`).
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ## Statements -/

/-- The leaf of `make_random_leaf` for the `rand(rng, Bool)` draw `b`, the feature draw `f`
(`rand(rng, 1:nfeatures)`) and the sampled value `v`. -/
def randLeaf (b : Bool) (f : Nat) (v : T) : Tree T := if b then .const v else .feature f

/-- Feature leaves with index `i`. -/
def isFeatAt (i : Nat) : Tree T → Bool
  | .feature j => j == i
  | _ => false

/-- The leaves for all `2 * nfeatures` equally likely pairs of draws `(b, f)`. -/
def leafOutcomes (nf : Nat) (v : T) : List (Tree T) :=
  [true, false].flatMap fun b => (List.range' 1 nf).map fun f => randLeaf b f v

/-- `make_random_leaf(nfeatures, T, N, rng, options)` allocates exactly one new object, a leaf
that is alias-free; old objects are unchanged; it consumes two draws. The leaf is a constant
holding `sample_value` when `rand(rng, Bool)` is `true`, else the feature `rand(rng, 1:nfeatures)`,
which lies in `1:nfeatures`; over the equally likely draws, half the outcomes are constants and
each feature `i` in `1:nfeatures` has exactly one outcome (probability `1/(2 nfeatures)`). -/
def make_random_leaf_fixture : Prop :=
  ∀ (T : Type) (D nf : Nat) (sv : Rat → T) (s : St T), 1 ≤ nf → nf ≤ 65535 →
    ∃ g', makeRandomLeaf D nf (sampleReal sv) s = .ok (s.g.next, ⟨g', advN s.rng 2⟩) ∧
      g'.next = s.g.next + 1 ∧ (∀ a, a < s.g.next → g'.cells a = s.g.cells a) ∧
      Graph.unfold g'.view 1 s.g.next =
        some (randLeaf (decide ((s.rng.indexDraws 1 s.rng.cursor).val = 1))
          (rangeAt s.rng (s.rng.cursor + 1) nf) (sv (s.rng.draws (s.rng.cursor + 1)))) ∧
      Graph.NoAlias g'.view s.g.next ∧
      1 ≤ rangeAt s.rng (s.rng.cursor + 1) nf ∧ rangeAt s.rng (s.rng.cursor + 1) nf ≤ nf ∧
      ∀ v : T, (leafOutcomes nf v).length = 2 * nf ∧ (leafOutcomes nf v).countP isConstT = nf ∧
        ∀ i, 1 ≤ i → i ≤ nf → (leafOutcomes nf v).countP (isFeatAt i) = 1

def make_random_leaf_spec : Prop := make_random_leaf_fixture ∧
  ∀ (T : Type) (D : Nat) (nf : Int) (sv : M T T) (s : St T),
    let next := { s with rng := adv s.rng }
    (∀ v after, (s.rng.indexDraws 1 s.rng.cursor).val = 1 → sv next = .ok (v, after) →
      ∃ g, makeRandomLeaf D nf.toNat sv s = .ok (after.g.next, ⟨g, after.rng⟩) ∧
        g.next = after.g.next + 1 ∧ Graph.unfold g.view 1 after.g.next = some (.const v) ∧
        ∀ a < after.g.next, g.cells a = after.g.cells a) ∧
    (∀ e, (s.rng.indexDraws 1 s.rng.cursor).val = 1 → sv next = .error e →
      makeRandomLeaf D nf.toNat sv s = .error e) ∧
    ((s.rng.indexDraws 1 s.rng.cursor).val ≠ 1 → nf ≤ 0 →
      makeRandomLeaf D nf.toNat sv s = .error (.argumentError "collection must be non-empty"))

/-- `_sample_leaf(rng, tree)` on a finite plain `Node` tree: the tree has a leaf, the heap is
unchanged, one draw is consumed, and the result is the object at the `k`-th leaf in preorder, `k`
the index draw over the preorder indices of the leaves (uniform over leaves). -/
def sample_leaf_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (fuel tree : Nat) (t : Tree T) (rng : RNG),
    Graph.unfold g.view fuel tree = some t →
    eligT isLeafT t ≠ [] ∧
    ∃ x P u, sampleLeaf fuel tree ⟨g, rng⟩ = .ok (x, ⟨g, adv rng⟩) ∧
      drawAt rng rng.cursor (eligT isLeafT t) ∈ eligT isLeafT t ∧
      Graph.Path g.view tree P x ∧
      (preorder t)[drawAt rng rng.cursor (eligT isLeafT t)]? = some u ∧ u.degree = 0 ∧
      Graph.unfold g.view (fuel - P.length) x = some u ∧
      (∃ xs, Expressions.Sampling.occurrences g.view fuel tree = .ok xs ∧
        xs[drawAt rng rng.cursor (eligT isLeafT t)]? = some x)

/-- `random_node(tree, rng; filter)` on a finite plain `Node` tree. With the default filter
`Returns(true)` it consumes one draw, leaves the heap unchanged and returns the object at preorder
index `j`, `j` the index draw in `0:(length(tree) - 1)` (uniform over all nodes). For any filter,
a returned node is reachable from the root, passes the filter, and exactly one draw was
consumed. -/
def random_node_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (fuel tree : Nat) (t : Tree T) (rng : RNG)
    (filter : SGraph T → Addr → Bool),
    Graph.unfold g.view fuel tree = some t →
    (∃ x P u, randomNode fuel tree (fun _ _ => true) ⟨g, rng⟩ = .ok (x, ⟨g, adv rng⟩) ∧
      Graph.Path g.view tree P x ∧
      (preorder t)[(rng.indexDraws (t.size - 1) rng.cursor).val]? = some u ∧
      Graph.unfold g.view (fuel - P.length) x = some u) ∧
    ∀ x s', randomNode fuel tree filter ⟨g, rng⟩ = .ok (x, s') →
      Graph.Reachable g.view tree x ∧ filter g x = true ∧ s' = ⟨g, adv rng⟩

/-- `_make_node(arity, proto, nfeatures, T, options, rng)` for an arity `1 ≤ arity ≤ D` with an
operator: it allocates `arity` fresh `make_random_leaf` leaves and then one operator node with an
operator `o` uniform in `1:options.nops[arity]`, consuming `1 + 2 * arity` draws; the new node is an
alias-free tree of `arity + 1` nodes and no old object changes. -/
def make_node_spec : Prop :=
  ∀ (T : Type) (D nf arity : Nat) (nops : List Nat) (sv : Rat → T) (s : St T),
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 → 1 ≤ arity → arity ≤ D →
    0 < opsOf nops arity →
    ∃ g', makeNode D nf nops (sampleReal sv) arity s =
        .ok (s.g.next + arity, ⟨g', advN s.rng (1 + 2 * arity)⟩) ∧
      Graph.unfold g'.view 2 (s.g.next + arity) =
        some (.branch (rangeAt s.rng s.rng.cursor (opsOf nops arity))
          (leavesAt s.rng (s.rng.cursor + 1) nf sv arity)) ∧
      (Tree.branch (rangeAt s.rng s.rng.cursor (opsOf nops arity))
          (leavesAt s.rng (s.rng.cursor + 1) nf sv arity)).size = arity + 1 ∧
      Graph.NoAlias g'.view (s.g.next + arity) ∧
      1 ≤ rangeAt s.rng s.rng.cursor (opsOf nops arity) ∧
      rangeAt s.rng s.rng.cursor (opsOf nops arity) ≤ opsOf nops arity ∧
      g'.next = s.g.next + arity + 1 ∧ (∀ a, a < s.g.next → g'.cells a = s.g.cells a)

/-- `maxChange = m.perturbation_factor * temperature + 1 + 1//10` of `mutate_factor`. -/
def maxChange (pert temperature : Rat) : Rat := pert * temperature + 1 + 1 / 10

/-- `mutate_value(rng, val, temperature, m)` returns `val * mutate_factor(typeof(val),
temperature, m, rng)`, consuming exactly the three draws of `mutate_factor`; for a power
`T(maxChange^r)` in `[1, maxChange]` (`r = rand(rng, T)` in `[0, 1)`), the factor's magnitude lies
in `[1/maxChange, maxChange]`, and the factor is negative exactly when the negation draw exceeds
`probability_negate`. -/
def mutate_value_spec : Prop :=
  ∀ (T : Type) (mul : T → Rat → T) (pw : Rat → Rat → Rat) (pert temperature pneg : Rat) (v : T)
    (s : St T),
    0 ≤ pert → 0 ≤ temperature → (∀ b r, 1 ≤ b → 0 ≤ r → r < 1 → 1 ≤ pw b r ∧ pw b r ≤ b) →
    0 ≤ s.rng.draws s.rng.cursor → s.rng.draws s.rng.cursor < 1 →
    mutateValue mul pw pert temperature pneg v s =
      .ok (mul v (factorAt pw pert temperature pneg s.rng s.rng.cursor),
        { s with rng := advN s.rng 3 }) ∧
    ((0 < factorAt pw pert temperature pneg s.rng s.rng.cursor ∧
        factorAt pw pert temperature pneg s.rng s.rng.cursor ≤ maxChange pert temperature ∧
        1 ≤ maxChange pert temperature * factorAt pw pert temperature pneg s.rng s.rng.cursor) ∨
      (factorAt pw pert temperature pneg s.rng s.rng.cursor < 0 ∧
        -factorAt pw pert temperature pneg s.rng s.rng.cursor ≤ maxChange pert temperature ∧
        1 ≤ maxChange pert temperature * -factorAt pw pert temperature pneg s.rng s.rng.cursor)) ∧
    (factorAt pw pert temperature pneg s.rng s.rng.cursor < 0 ↔
      pneg < s.rng.draws (s.rng.cursor + 2))

/-! ## Sampling -/

/-- A successful `rand(rng, NodeSampler(...))` returns an occurrence that passes the filter,
after one draw. -/
theorem sampleM_mem {fuel : Nat} {b : Bool} {a : Addr} {F : SGraph T → Addr → Bool} {s : St T}
    {x : Addr} {s' : St T} (h : sampleM fuel b a F s = .ok (x, s')) :
    ∃ xs, Expressions.Sampling.occurrences s.g.view fuel a = .ok xs ∧ x ∈ xs ∧ F s.g x = true ∧
      s' = { s with rng := adv s.rng } := by
  cases ho : Expressions.Sampling.occurrences s.g.view fuel a with
  | error e =>
    have hm : Expressions.Sampling.matching
        ({ graph := s.g.view, root := a, fuel := fuel, filter := F s.g,
           preserveSharing := b } : Expressions.Sampling.NodeSampler T) = .error e := by
      simp [Expressions.Sampling.matching, Expressions.Sampling.traversal, ho]; rfl
    simp [sampleM, sampleMState, Expressions.Sampling.rand, hm, Except.map] at h
  | ok xs =>
    refine ⟨xs, rfl, ?_⟩
    have hm : Expressions.Sampling.matching
        ({ graph := s.g.view, root := a, fuel := fuel, filter := F s.g,
           preserveSharing := b } : Expressions.Sampling.NodeSampler T) =
        .ok ((if b then xs.eraseDups else xs).filter (F s.g)) := by
      cases b <;> (simp [Expressions.Sampling.matching, Expressions.Sampling.traversal, ho]; rfl)
    have hsub : ∀ y, y ∈ (if b then xs.eraseDups else xs).filter (F s.g) → y ∈ xs ∧ F s.g y = true := by
      intro y hy
      rw [List.mem_filter] at hy
      refine ⟨?_, hy.2⟩
      cases b
      · exact hy.1
      · exact List.mem_eraseDups.mp hy.1
    generalize hL : (if b then xs.eraseDups else xs).filter (F s.g) = L at hm hsub
    cases L with
    | nil => simp [sampleM, sampleMState, Expressions.Sampling.rand, hm, Except.map] at h
    | cons y ys =>
      simp only [sampleM, sampleMState, Expressions.Sampling.rand, hm, Except.map] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, hs⟩ := h
      have hlt := (s.rng.indexDraws ys.length s.rng.cursor).isLt
      have hmem : x ∈ y :: ys := by
        rw [← hx]
        unfold Expressions.Sampling.getNode
        rw [if_neg (by omega), Nat.add_sub_cancel,
          List.getElem?_eq_getElem (by simp only [List.length_cons]; omega), Option.getD_some]
        exact List.getElem_mem _
      obtain ⟨h1, h2⟩ := hsub x hmem
      exact ⟨h1, h2, by rw [← hs]; rfl⟩

/-- Every occurrence of a successfully unfolded tree is reachable. -/
theorem occ_reach {g : SGraph T} {fuel a : Nat} {t : Tree T} {xs : List Addr} {x : Addr}
    (hu : Graph.unfold g.view fuel a = some t)
    (ho : Expressions.Sampling.occurrences g.view fuel a = .ok xs) (hx : x ∈ xs) :
    ∃ (k : Nat) (P : List Nat) (u : Tree T), (preorder t)[k]? = some u ∧ Graph.Path g.view a P x ∧
      Graph.unfold g.view (fuel - P.length) x = some u := by
  obtain ⟨xs', ho', _, hspec⟩ := occ_spec g.view fuel a t hu
  rw [ho] at ho'; cases ho'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨P, u, hP, hpu, hun, _, _⟩ := hspec k x hk
  exact ⟨k, P, u, hpu, hP, hun⟩

/-! ## Proofs -/

theorem leafAt_eq_randLeaf (rng : RNG) (c nf : Nat) (sv : Rat → T) :
    leafAt rng c nf sv =
      randLeaf (decide ((rng.indexDraws 1 c).val = 1)) (rangeAt rng (c + 1) nf) (sv (rng.draws (c + 1))) := by
  unfold leafAt randLeaf
  by_cases h : (rng.indexDraws 1 c).val = 1 <;> simp [h]

theorem leafOutcomes_eq (nf : Nat) (v : T) :
    leafOutcomes nf v =
      (List.range' 1 nf).map (fun _ => (Tree.const v : Tree T)) ++
        (List.range' 1 nf).map (fun f => (Tree.feature f : Tree T)) := by
  simp [leafOutcomes, randLeaf]

theorem make_random_leaf_fixture_holds : make_random_leaf_fixture := by
  intro T D nf sv s h1 h2
  refine ⟨_, makeRandomLeaf_ok D nf sv s h1 h2, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_, fun v => ?_⟩
  · simp [Heap.alloc, Nat.ne_of_lt ha]
  · have hc : (s.g.alloc (leafCellAt s.rng s.rng.cursor nf sv)).2.cells s.g.next =
        some (leafCellAt s.rng s.rng.cursor nf sv) := by simp [Heap.alloc]
    rw [leafCellAt_unfold hc 0, leafAt_eq_randLeaf]
  · apply noAlias_leaf
    intro c hc
    have hc0 : (s.g.alloc (leafCellAt s.rng s.rng.cursor nf sv)).2.cells s.g.next =
        some (leafCellAt s.rng s.rng.cursor nf sv) := by simp [Heap.alloc]
    rw [view_cells hc0] at hc; cases hc
    simp [SCell.toCell, (leafCellAt_degree _ _ _ _).2.2]
  · simp [rangeAt]
  · have := (s.rng.indexDraws (nf - 1) (s.rng.cursor + 1)).isLt
    simp only [rangeAt]; omega
  · rw [leafOutcomes_eq]
    refine ⟨by simp; omega, ?_, fun i hi1 hi2 => ?_⟩
    · simp [List.countP_append, List.countP_map, Function.comp_def, isConstT]
    · simp only [List.countP_append, List.countP_map, Function.comp_def, isFeatAt]
      rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
      have := count_interval (i - 1) i nf (by omega) hi2
      have he : (List.range' 1 nf).filter (fun x => x == i) =
          (List.range' 1 nf).filter (fun th => decide (i - 1 < th ∧ th ≤ i)) := by
        apply List.filter_congr
        intro th _
        by_cases h : th = i
        · subst h
          have : th - 1 < th ∧ th ≤ th := by omega
          simp [this]
        · have : ¬ (i - 1 < th ∧ th ≤ i) := by omega
          simp [h, this]
      have h0 : ((List.range' 1 nf).filter (fun _ => false)).length = 0 := by simp
      rw [he, this, h0]
      omega

theorem make_random_leaf_spec_holds : make_random_leaf_spec := by
  refine ⟨make_random_leaf_fixture_holds, ?_⟩
  intro T D nf sv s
  dsimp only
  constructor
  · intro v after hb hs
    let c : SCell T := { (blankCell : SCell T) with constant := true, val := some v }
    let g := (after.g.alloc c).2
    have hc : g.cells after.g.next = some c := by simp [g, Heap.alloc]
    refine ⟨g, ?_, rfl, ?_, ?_⟩
    · unfold makeRandomLeaf
      rw [bindM (randBool_ok s)]
      simp only [hb, decide_true, ↓reduceIte]
      exact (bindM hs).trans rfl
    · rw [unfold_leaf_cell hc rfl rfl]
      rfl
    · intro a ha
      simp [g, Heap.alloc, Nat.ne_of_lt ha]
  constructor
  · intro e hb hs
    unfold makeRandomLeaf
    rw [bindM (randBool_ok s)]
    simp only [hb, decide_true, ↓reduceIte]
    exact bindM_err hs
  · intro hb hn
    have h : nf.toNat = 0 := by omega
    unfold makeRandomLeaf
    rw [bindM (randBool_ok s)]
    simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, h]
    rfl

theorem sample_leaf_spec_holds : sample_leaf_spec := by
  intro T g fuel tree t rng hu
  obtain ⟨x, P, u, f', hmem, hsamp, hP, hpu, hq, hf', hux, _, _, haddr⟩ :=
    sample_kind ⟨g, rng⟩ fuel tree t _ isLeafT lk_leaf hu (preorder_any_leaf t)
  refine ⟨eligT_ne_nil (preorder_any_leaf t), x, P, u, hsamp, hmem, hP, hpu,
    by simpa [isLeafT] using hq, by rw [hf']; exact hux, haddr⟩

theorem random_node_spec_holds : random_node_spec := by
  intro T g fuel tree t rng filter hu
  refine ⟨?_, fun x s' h => ?_⟩
  · have hne : eligIdx t.size (fun _ => true) ≠ [] := by
      have := Tree.size_pos t
      exact eligIdx_ne_nil (k := 0) (by omega) rfl
    obtain ⟨k, x, P, u, hk, hsamp, hP, hpu, hun, _, _, _⟩ :=
      sample_spec ⟨g, rng⟩ fuel tree t (fun _ _ => true) (fun _ => true) hu
        (fun _ _ _ _ _ _ _ _ => rfl) hne
    have hL : eligIdx t.size (fun _ => true) = List.range t.size := by simp [eligIdx]
    rw [hL] at hk
    have hj : (rng.indexDraws ((List.range t.size).length - 1) rng.cursor).val =
        (rng.indexDraws (t.size - 1) rng.cursor).val := by rw [List.length_range]
    have hlt := (rng.indexDraws (t.size - 1) rng.cursor).isLt
    have hsz := Tree.size_pos t
    rw [hj, List.getElem?_range (by omega)] at hk
    cases hk
    exact ⟨x, P, u, hsamp, hP, hpu, hun⟩
  · obtain ⟨xs, ho, hx, hf, hs⟩ := sampleM_mem h
    obtain ⟨_, P, _, _, hP, _⟩ := occ_reach hu ho hx
    exact ⟨⟨P, hP⟩, hf, hs⟩

theorem make_node_spec_holds : make_node_spec := by
  intro T D nf arity nops sv s hlen h255 h1 h2 ha1 haD hpos
  subst hlen
  obtain ⟨g', hop, hnx, hold, hleaf, hbr⟩ := opNode_ok nops.length nf nops sv arity
    (opsOf nops arity) s h1 h2 (nopsAt_ok ha1 haD) hpos (opsOf_le h255 ha1 haD) haD
  have hbr' := hbr
  have hact : (branchCell (T := T) nops.length (rangeAt s.rng s.rng.cursor (opsOf nops arity))
      (List.range' s.g.next arity)).active = List.range' s.g.next arity :=
    branchCell_active _ _ _ (by simp; exact haD)
  refine ⟨g', ?_, ?_, ?_, ?_, by simp [rangeAt], ?_, hnx, hold⟩
  · unfold makeNode; rw [nifArity_eq ha1 haD]; exact hop
  · exact fresh_branch_unfold (f := 0) hbr (by simp [branchCell]) rfl hact (by omega) hleaf
  · rw [leavesAt_size]; omega
  · apply noAlias_flat (c := (branchCell (T := T) nops.length
        (rangeAt s.rng s.rng.cursor (opsOf nops arity)) (List.range' s.g.next arity)).toCell)
        (view_cells hbr')
    · simp only [SCell.toCell, hact]; exact List.nodup_range'
    · intro b hb cb hcb
      simp only [SCell.toCell, hact, List.mem_range'_1] at hb
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb.1
      rw [view_cells (hleaf j (by omega))] at hcb
      cases hcb
      simp [SCell.toCell, (leafCellAt_degree _ _ _ _).2.2]
    · simp only [SCell.toCell, hact, List.mem_range'_1]; omega
  · have := (s.rng.indexDraws (opsOf nops arity - 1) s.rng.cursor).isLt
    simp only [rangeAt]; omega

theorem maxChange_ge_one {pert temperature : Rat} (hp : 0 ≤ pert) (ht : 0 ≤ temperature) :
    1 ≤ maxChange pert temperature := by
  have h0 : 0 ≤ pert * temperature := by
    have := Rat.mul_le_mul_of_nonneg_left ht hp
    rwa [Rat.mul_zero] at this
  unfold maxChange
  grind

theorem mutate_value_spec_holds : mutate_value_spec := by
  intro T mul pw pert temperature pneg v s hp ht hpw hr0 hr1
  have hm := maxChange_ge_one hp ht
  obtain ⟨hf1, hfm⟩ := hpw (maxChange pert temperature) (s.rng.draws s.rng.cursor) hm hr0 hr1
  have hrun : mutateValue mul pw pert temperature pneg v s =
      .ok (mul v (factorAt pw pert temperature pneg s.rng s.rng.cursor),
        { s with rng := advN s.rng 3 }) := by
    unfold mutateValue
    rw [bindM (mutateFactor_ok pw pert temperature pneg s)]
    rfl
  refine ⟨hrun, ?_⟩
  generalize hfac : pw (maxChange pert temperature) (s.rng.draws s.rng.cursor) = fac at hf1 hfm
  have hfac' : pw (pert * temperature + 1 + 1 / 10) (s.rng.draws s.rng.cursor) = fac := hfac
  have hpos : 0 < fac := by grind
  -- the magnitude before the sign
  have hmag : ∀ b : Bool, 0 < (if b then fac else 1 / fac) ∧
      (if b then fac else 1 / fac) ≤ maxChange pert temperature ∧
      1 ≤ maxChange pert temperature * (if b then fac else 1 / fac) := by
    intro b
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hi : 0 < 1 / fac := by rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr hpos
      have hle1 : 1 / fac ≤ 1 := by
        apply Rat.not_lt.mp
        intro h
        have := (Rat.lt_div_iff hpos).mp h
        grind
      refine ⟨hi, Rat.le_trans hle1 hm, ?_⟩
      apply Rat.not_lt.mp
      intro h
      rw [show maxChange pert temperature * (1 / fac) = maxChange pert temperature / fac by
        rw [Rat.div_def, Rat.div_def, Rat.one_mul]] at h
      have := (Rat.div_lt_iff hpos).mp h
      grind
    · simp only [↓reduceIte]
      refine ⟨hpos, hfm, ?_⟩
      have := Rat.mul_le_mul_of_nonneg_left hf1 (Rat.le_trans (by decide) hm)
      rw [Rat.mul_one] at this
      exact Rat.le_trans hm this
  unfold factorAt
  simp only [hfac']
  generalize ((s.rng.indexDraws 1 (s.rng.cursor + 1)).val = 1 : Bool) = b
  obtain ⟨h1, h2, h3⟩ := hmag b
  by_cases hneg : s.rng.draws (s.rng.cursor + 2) > pneg
  · rw [if_pos hneg]
    refine ⟨Or.inr ⟨by grind, by rw [Rat.neg_neg]; exact h2, by rw [Rat.neg_neg]; exact h3⟩,
      ⟨fun _ => hneg, fun _ => by grind⟩⟩
  · rw [if_neg hneg]
    exact ⟨Or.inl ⟨h1, h2, h3⟩, ⟨fun h => by grind, fun h => absurd h hneg⟩⟩

end SymReg.Mutations
