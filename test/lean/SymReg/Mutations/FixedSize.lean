import SymReg.Mutations.Append

/-! `gen_random_tree_fixed_size` (`src/MutationFunctions.jl:464-494`): statement and proof. -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### Depth -/

theorem le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [List.foldr_cons]; exact Nat.le_max_left _ _
    · simp only [List.foldr_cons]; exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem foldr_max_le_sum {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → (l.map f).foldr max 0 ≤ (l.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.foldr_cons, List.sum_cons]
    have h1 := h x (by simp)
    have h2 := foldr_max_le_sum f g xs (fun y hy => h y (by simp [hy]))
    omega

theorem depth_le_size (t : Tree T) : t.depth ≤ t.size := by
  induction t using Tree.induction with
  | hc v => simp [Tree.depth, Tree.size]
  | hf i => simp [Tree.depth, Tree.size]
  | hb o cs ih =>
    simp only [Tree.depth, Tree.size_branch]
    have := foldr_max_le_sum Tree.depth Tree.size cs ih
    omega

/-- A successful unfolding also succeeds with any fuel covering the depth. -/
theorem unfold_depth {G : Graph T} :
    ∀ f a (t : Tree T), Graph.unfold G f a = some t → ∀ f', t.depth ≤ f' → Graph.unfold G f' a = some t := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h f' hf'
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG h
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by have := Tree.depth_pos t; omega⟩
    refine unfold_of_cell hc hl ?_
    rcases hcase with hleaf | ⟨hd, ts, hm, rfl⟩
    · exact Or.inl hleaf
    · refine Or.inr ⟨hd, ts, ?_, rfl⟩
      apply mapM_of_get _ _ _ (mapM_length _ _ _ hm).symm
      intro i x y hx hy
      obtain ⟨y', hy', hfx⟩ := mapM_get _ _ _ hm i x hx
      rw [hy] at hy'
      cases hy'
      apply ih x y hfx f''
      have := le_foldr_max (List.mem_map_of_mem (f := Tree.depth) (List.mem_of_getElem? hy))
      simp only [Tree.depth] at hf'
      omega

/-! ### The growth loop -/

theorem nifArity_eq {D k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ D) : nifArity D k = k := by
  unfold nifArity; split <;> omega

theorem nopsAt_ok {nops : List Nat} {i : Nat} (h1 : 1 ≤ i) (h2 : i ≤ nops.length) :
    nopsAt nops i = .ok (opsOf nops i) := by
  have hil : i - 1 < nops.length := by omega
  simp [nopsAt, opsOf, h1, List.getElem?_eq_getElem hil]

theorem opsOf_le {nops : List Nat} {i : Nat} (h255 : ∀ m ∈ nops, m ≤ 255) (h1 : 1 ≤ i)
    (h2 : i ≤ nops.length) : opsOf nops i ≤ 255 := by
  have hil : i - 1 < nops.length := by omega
  simp only [opsOf, List.getElem?_eq_getElem hil, Option.getD_some]
  exact h255 _ (List.getElem_mem hil)

theorem psum_one_pos {nops : List Nat} (h : 0 < opsOf nops 1) {l : Nat} (hl : 1 ≤ l)
    (hl' : l ≤ nops.length) : psum nops l ≠ 0 := by
  have h1 := psum_succ nops (k := 0) (by omega)
  have h2 := psum_mono nops hl
  simp [psum_zero] at h1
  omega

/-- One growth iteration of `gen_random_tree_fixed_size` after a nonzero arity draw `k`: a
random leaf becomes an operator of degree `k` over fresh leaves. -/
theorem loop_step (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (N : Nat) (tree : Addr)
    (h255 : ∀ m ∈ nops, m ≤ 255) (h1 : 1 ≤ nf) (h2 : nf ≤ 65535)
    (steps : Nat) (s s1 : St T) (cur k : Nat) (t : Tree T)
    (hu : Graph.unfold s.g.view fuel tree = some t) (hna : Graph.NoAlias s.g.view tree)
    (hsize : t.size = cur) (hrem : ((N : Int) - (cur : Int)) ≠ 0)
    (hk : arityPicker ((N : Int) - (cur : Int)) nops s = .ok (k, s1)) (hs1g : s1.g = s.g)
    (hk1 : 1 ≤ k) (hkD : k ≤ D) (hkl : k ≤ nops.length) (hkops : 0 < opsOf nops k) :
    ∃ (s2 : St T) (t' : Tree T),
      fixedSizeLoop D fuel nf nops (sampleReal sv) (N : Int) tree (steps + 1) (cur : Int) s =
        fixedSizeLoop D fuel nf nops (sampleReal sv) (N : Int) tree steps ((cur + k : Nat) : Int) s2 ∧
      Graph.unfold s2.g.view (fuel + 2) tree = some t' ∧ t'.size = cur + k ∧
      Graph.NoAlias s2.g.view tree ∧ s.g.next ≤ s2.g.next := by
  have hk0' : k ≠ 0 := by omega
  have hu1 : Graph.unfold s1.g.view fuel tree = some t := by rw [hs1g]; exact hu
  have hna1 : Graph.NoAlias s1.g.view tree := by rw [hs1g]; exact hna
  obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hq, _, _, hrepl, _⟩ :=
    sample_kind s1 fuel tree t _ isLeafT lk_leaf hu1 (preorder_any_leaf t)
  have hu0 : u.degree = 0 := by simpa [isLeafT] using hq
  obtain ⟨g1, g', hop, hset, hres, hna', _, hle, _⟩ :=
    graft_step { s1 with rng := adv s1.rng } D fuel nf nops sv tree x t P _ k (opsOf nops k)
      hu1 hna1 hP hrepl h1 h2 (nopsAt_ok hk1 hkl) hkops (opsOf_le h255 hk1 hkl) hk1 hkD
  refine ⟨⟨g', advN (adv s1.rng) (1 + 2 * k)⟩, _, ?_, hres, ?_, hna', ?_⟩
  · simp only [fixedSizeLoop]
    rw [if_neg hrem, bindM hk]
    simp only [hk0', ↓reduceIte]
    show (sampleM fuel false tree (cellP fun c => c.degree == 0) >>= _) s1 = _
    rw [bindM hsamp]
    have hop' : makeNode D nf nops (sampleReal sv) k { s1 with rng := adv s1.rng } =
        .ok ({ s1 with rng := adv s1.rng }.g.next + k, ⟨g1, advN (adv s1.rng) (1 + 2 * k)⟩) := by
      unfold makeNode; rw [nifArity_eq hk1 hkD]; exact hop
    rw [bindM hop', bindM hset]
    rw [show ((cur : Int) + (k : Int)) = ((cur + k : Nat) : Int) by omega]
  · have := replaceAt_size t _ u (.branch (rangeAt (adv s1.rng) (adv s1.rng).cursor (opsOf nops k))
      (leavesAt (adv s1.rng) ((adv s1.rng).cursor + 1) nf sv k)) hpu
    rw [leavesAt_size, leaf_size hu0] at this
    dsimp only at this ⊢
    omega
  · rw [← hs1g]; exact hle

theorem fixedSizeLoop_spec (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (N : Nat) (tree : Addr)
    (hlen : nops.length = D) (h255 : ∀ m ∈ nops, m ≤ 255) (hun : 0 < opsOf nops 1)
    (h1 : 1 ≤ nf) (h2 : nf ≤ 65535) (hNf : N ≤ fuel) :
    ∀ (steps : Nat) (s : St T) (cur : Nat) (t : Tree T),
      Graph.unfold s.g.view fuel tree = some t → Graph.NoAlias s.g.view tree → t.size = cur →
      cur ≤ N → N - cur < steps →
      ∃ s' : St T, fixedSizeLoop D fuel nf nops (sampleReal sv) (N : Int) tree steps (cur : Int) s = .ok (tree, s') ∧
        ∃ t', Graph.unfold s'.g.view fuel tree = some t' ∧ t'.size = N ∧
          Graph.NoAlias s'.g.view tree ∧ s.g.next ≤ s'.g.next := by
  intro steps
  induction steps with
  | zero => intro s cur t _ _ _ _ h; omega
  | succ steps ih =>
    intro s cur t hu hna hsize hcur hsteps
    by_cases hN : cur = N
    · subst hN
      refine ⟨s, ?_, t, hu, hsize, hna, Nat.le_refl _⟩
      simp [fixedSizeLoop]
      rfl
    have hrem : ((N : Int) - (cur : Int)) ≠ 0 := by omega
    -- the arity draw
    obtain ⟨k, s1, hk, hk0, hkpos⟩ := arity_picker_spec_holds T ((N : Int) - (cur : Int)) nops s
    have hlim1 : 1 ≤ arityLimit ((N : Int) - (cur : Int)) nops := by
      unfold arityLimit
      have : 1 ≤ nops.length := by
        cases nops with
        | nil => simp [opsOf] at hun
        | cons _ _ => simp
      omega
    have hlimL : arityLimit ((N : Int) - (cur : Int)) nops ≤ nops.length := by
      unfold arityLimit; omega
    obtain ⟨hk1, hkrem, hklen, hkops, _, _, hs1g, hs1r⟩ := hkpos (psum_one_pos hun hlim1 hlimL)
    have hk0' : k ≠ 0 := by omega
    -- the leaf to expand
    have hu1 : Graph.unfold s1.g.view fuel tree = some t := by rw [hs1g]; exact hu
    have hna1 : Graph.NoAlias s1.g.view tree := by rw [hs1g]; exact hna
    obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hq, _, _, hrepl, _⟩ :=
      sample_kind s1 fuel tree t _ isLeafT lk_leaf hu1 (preorder_any_leaf t)
    have hu0 : u.degree = 0 := by simpa [isLeafT] using hq
    -- the new operator node
    have hkD : k ≤ D := by omega
    obtain ⟨g1, g', hop, hset, hres, hna', _, hle, _⟩ :=
      graft_step { s1 with rng := adv s1.rng } D fuel nf nops sv tree x t P _ k (opsOf nops k)
        hu1 hna1 hP hrepl h1 h2 (nopsAt_ok hk1 (by omega)) hkops (opsOf_le h255 hk1 (by omega)) hk1 hkD
    generalize hnew : replaceAt t (drawAt s1.rng s1.rng.cursor (eligT isLeafT t))
      (.branch (rangeAt (adv s1.rng) (adv s1.rng).cursor (opsOf nops k))
        (leavesAt (adv s1.rng) ((adv s1.rng).cursor + 1) nf sv k)) = t' at hres
    have hsize' : t'.size = cur + k := by
      have := replaceAt_size t _ u (.branch (rangeAt (adv s1.rng) (adv s1.rng).cursor (opsOf nops k))
        (leavesAt (adv s1.rng) ((adv s1.rng).cursor + 1) nf sv k)) hpu
      rw [leavesAt_size, leaf_size hu0, hnew] at this
      omega
    have hu' : Graph.unfold g'.view fuel tree = some t' :=
      unfold_depth _ _ _ hres _ (by have := depth_le_size t'; omega)
    obtain ⟨s'', hrun, t'', hu'', hsz'', hna'', hle''⟩ :=
      ih ⟨g', advN (adv s1.rng) (1 + 2 * k)⟩ (cur + k) t' hu' hna' hsize' (by omega) (by omega)
    refine ⟨s'', ?_, t'', hu'', hsz'', hna'', ?_⟩
    · simp only [fixedSizeLoop]
      rw [if_neg hrem]
      rw [bindM hk]
      simp only [hk0', ↓reduceIte]
      show (sampleM fuel false tree (cellP fun c => c.degree == 0) >>= _) s1 = _
      rw [bindM hsamp]
      have hop' : makeNode D nf nops (sampleReal sv) k { s1 with rng := adv s1.rng } =
          .ok ({ s1 with rng := adv s1.rng }.g.next + k, ⟨g1, advN (adv s1.rng) (1 + 2 * k)⟩) := by
        unfold makeNode; rw [nifArity_eq hk1 hkD]; exact hop
      rw [bindM hop', bindM hset]
      rw [show ((cur : Int) + (k : Int)) = ((cur + k : Nat) : Int) by omega]
      exact hrun
    · rw [← hs1g]; exact Nat.le_trans hle hle''

/-- `gen_random_tree_fixed_size(node_count, options, nfeatures, T, rng)` returns an alias-free
tree of exactly `node_count` nodes whenever a unary operator exists (`options.nops[1] > 0`). -/
def gen_fixed_size_exact : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (n steps : Nat)
    (rng : RNG),
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 0 < opsOf nops 1 → 1 ≤ nf → nf ≤ 65535 →
    1 ≤ n → n ≤ fuel → n ≤ steps →
    ∃ r s', genRandomTreeFixedSize D fuel nf nops (sampleReal sv) (n : Int) steps ⟨g, rng⟩ = .ok (r, s') ∧
      ∃ t, Graph.unfold s'.g.view fuel r = some t ∧ t.size = n ∧ Graph.NoAlias s'.g.view r

theorem gen_fixed_size_exact_holds : gen_fixed_size_exact := by
  intro T g D fuel nf nops sv n steps rng hlen h255 hun h1 h2 hn1 hnf hns
  let s0 : St T := ⟨(g.alloc (leafCellAt rng rng.cursor nf sv)).2, advN rng 2⟩
  have hc0 : s0.g.cells g.next = some (leafCellAt rng rng.cursor nf sv) := by
    simp [s0, Heap.alloc]
  have hu0 : Graph.unfold s0.g.view fuel g.next = some (leafAt rng rng.cursor nf sv) := by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact leafCellAt_unfold hc0 f
  have hna0 : Graph.NoAlias s0.g.view g.next := by
    apply noAlias_leaf
    intro c hc
    rw [view_cells hc0] at hc; cases hc
    simp [SCell.toCell, (leafCellAt_degree _ _ _ _).2.2]
  have hsz0 : (leafAt rng rng.cursor nf sv).size = 1 := by
    unfold leafAt; split <;> simp [Tree.size]
  obtain ⟨s', hrun, t', hu', hsz', hna', _⟩ :=
    fixedSizeLoop_spec D fuel nf nops sv n g.next hlen h255 hun h1 h2 hnf steps s0 1 _ hu0 hna0 hsz0
      hn1 (by omega)
  refine ⟨g.next, s', ?_, t', hu', hsz', hna'⟩
  simp only [genRandomTreeFixedSize]
  rw [bindM (makeRandomLeaf_ok D nf sv ⟨g, rng⟩ h1 h2)]
  exact hrun

/-- A node count reachable with the available arities: one leaf plus the arities of some
operators that exist. -/
def Realizable (nops : List Nat) (n : Nat) : Prop :=
  ∃ l : List Nat, (∀ a ∈ l, 1 ≤ a ∧ 0 < opsOf nops a) ∧ l.sum + 1 = n

/-- `gen_random_tree_fixed_size(node_count, ...)` returns a tree of exactly `node_count` nodes
whenever some tree of that many nodes can be built from the available operators. -/
def gen_fixed_size_realizable : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (n steps : Nat)
    (rng : RNG),
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 →
    1 ≤ n → n ≤ fuel → n ≤ steps → Realizable nops n →
    ∃ r s', genRandomTreeFixedSize D fuel nf nops (sampleReal sv) (n : Int) steps ⟨g, rng⟩ = .ok (r, s') ∧
      ∃ t, Graph.unfold s'.g.view fuel r = some t ∧ t.size = n

end SymReg.Mutations
