import SymReg.Mutations.Insert
import SymReg.Mutations.Refute

/-! `gen_random_tree` (`src/MutationFunctions.jl:406-421`): statements and proofs. -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-- The number of operator nodes (nodes of nonzero degree) of a tree. -/
def nOps (t : Tree T) : Nat := (preorder t).countP isBranchT

/-- `gen_random_tree(length, options, nfeatures, T, rng)` ("Create a random equation by appending
random operators") with every real draw strictly inside `(0, 1)`: it returns the placeholder
object `constructorof(options.node_type)(T; val=init_value(T))`, which unfolds to an alias-free
tree with exactly `length` operator nodes and `1 + d_1 + ... + d_length` nodes, where each `d_j`
is the degree picked by the `j`-th `append_random_op` (`1 ≤ d_j ≤ D`, with an operator); for
`length = 0` the placeholder constant itself is returned. -/
def gen_random_tree_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (init : T)
    (len : Nat) (rng : RNG),
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 → 0 < nops.sum →
    1 + len * D ≤ fuel →
    (∀ n, 0 < scaledDegreeDraw (rng.draws n) nops ∧
      scaledDegreeDraw (rng.draws n) nops < (nops.sum : Rat)) →
    ∃ (s' : St T) (t : Tree T) (ds : List Nat),
      genRandomTree D fuel nf nops (sampleReal sv) init len ⟨g, rng⟩ = .ok (g.next, s') ∧
      Graph.unfold s'.g.view fuel g.next = some t ∧ Graph.NoAlias s'.g.view g.next ∧
      ds.length = len ∧ (∀ d ∈ ds, 1 ≤ d ∧ d ≤ D ∧ 0 < opsOf nops d) ∧
      t.size = 1 + ds.sum ∧ nOps t = len ∧ (len = 0 → t = .const init)

/-- The resulting size counts one initial leaf and the arity contributed by each appended operator. -/
def gen_random_tree_length : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (init : T)
    (len : Nat) (rng : RNG),
    nops.length = D → (∀ m ∈ nops, m ≤ 255) → 1 ≤ nf → nf ≤ 65535 → 0 < nops.sum →
    1 + len * D ≤ fuel → (∀ n, 0 ≤ rng.draws n ∧ rng.draws n < 1) →
    ∃ (s' : St T) (t : Tree T) (ds : List Nat),
      genRandomTree D fuel nf nops (sampleReal sv) init len ⟨g, rng⟩ = .ok (g.next, s') ∧
      Graph.unfold s'.g.view fuel g.next = some t ∧ nOps t = len ∧ ds.length = len ∧
      (∀ d ∈ ds, 1 ≤ d ∧ d ≤ D ∧ 0 < opsOf nops d) ∧ t.size = 1 + ds.sum

/-! ### Operator counts -/

theorem replaceF_length (u : Tree T) :
    ∀ (ds : List (Tree T)) (k : Nat), (replaceF ds k u).length = ds.length := by
  intro ds
  induction ds with
  | nil => intro k; simp [replaceF]
  | cons d ds ih => intro k; rw [replaceF_cons]; split <;> simp [ih]

theorem nOps_leaf {u : Tree T} (hpos : ∀ o, u ≠ .branch o []) (h : u.degree = 0) : nOps u = 0 := by
  cases u with
  | const v => simp [nOps, preorder, isBranchT, Tree.degree]
  | feature i => simp [nOps, preorder, isBranchT, Tree.degree]
  | branch o cs =>
    simp only [Tree.degree, List.length_eq_zero_iff] at h
    exact absurd (h ▸ rfl) (hpos o)

/-- `replaceAt` changes the operator count by the difference of the two subtrees. -/
theorem nOps_replaceAt :
    ∀ (t : Tree T) (k : Nat) (s u : Tree T), (preorder t)[k]? = some s →
      nOps (replaceAt t k u) + nOps s = nOps t + nOps u := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro k s u h
    cases k with
    | zero => simp [preorder] at h; subst h; rw [replaceAt_zero]; omega
    | succ k => simp [preorder] at h
  | hf i =>
    intro k s u h
    cases k with
    | zero => simp [preorder] at h; subst h; rw [replaceAt_zero]; omega
    | succ k => simp [preorder] at h
  | hb o cs ih =>
    intro k s u h
    cases k with
    | zero => simp [preorder_branch] at h; subst h; rw [replaceAt_zero]; omega
    | succ k =>
      rw [preorder_branch, List.getElem?_cons_succ] at h
      rw [replaceAt_succ]
      unfold nOps
      rw [preorder_branch, preorder_branch, List.countP_cons, List.countP_cons]
      have hroot : isBranchT (Tree.branch o (replaceF cs k u)) = isBranchT (Tree.branch o cs) := by
        simp [isBranchT, Tree.degree, replaceF_length]
      rw [hroot]
      suffices hF : ∀ (ds : List (Tree T)), (∀ d ∈ ds, d ∈ cs) → ∀ k,
          (preorder.preorderF ds)[k]? = some s →
          (preorder.preorderF (replaceF ds k u)).countP isBranchT + nOps s =
            (preorder.preorderF ds).countP isBranchT + nOps u by
        have := hF cs (fun d hd => hd) k h
        simp only [nOps] at this ⊢
        omega
      intro ds
      induction ds with
      | nil => intro _ k h; simp [preorder.preorderF] at h
      | cons d ds ihd =>
        intro hsub k h
        rw [preorderF_cons] at h
        rw [replaceF_cons]
        by_cases hk : k < (preorder d).length
        · rw [if_pos hk]
          rw [List.getElem?_append_left hk] at h
          have := ih d (hsub d List.mem_cons_self) k s u h
          rw [preorderF_cons, preorderF_cons, List.countP_append, List.countP_append]
          simp only [nOps] at this ⊢
          omega
        · rw [if_neg hk]
          rw [List.getElem?_append_right (by omega)] at h
          have := ihd (fun e he => hsub e (List.mem_cons_of_mem _ he)) _ h
          rw [preorderF_cons, preorderF_cons, List.countP_append, List.countP_append]
          simp only [nOps] at this ⊢
          omega

/-- Unfolded trees have no childless branch. -/
theorem unfold_noEmpty {G : Graph T} :
    ∀ f a (t : Tree T), Graph.unfold G f a = some t → ∀ s ∈ preorder t, ∀ o, s ≠ .branch o [] := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h s hs o
    obtain ⟨c, _, hl, hcase⟩ := unfold_succG h
    rcases hcase with ⟨_, ⟨_, v, _, rfl⟩ | ⟨_, rfl⟩⟩ | ⟨hd, ts, hm, rfl⟩
    · simp [preorder] at hs; subst hs; simp
    · simp [preorder] at hs; subst hs; simp
    · rw [preorder_branch] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · intro he
        cases he
        have := mapM_length _ _ _ hm
        simp at this
        omega
      · suffices H : ∀ (as : List Addr) (us : List (Tree T)), as.mapM (Graph.unfold G f) = some us →
            s ∈ preorder.preorderF us → s ≠ .branch o [] from H _ ts hm hs
        intro as
        induction as with
        | nil => intro us hus hs'; simp at hus; subst hus; simp [preorder.preorderF] at hs'
        | cons b bs ihb =>
          intro us hus hs'
          obtain ⟨tb, tbs, htb, htbs, rfl⟩ := (mapM_cons _ b bs us).mp hus
          rw [preorderF_cons, List.mem_append] at hs'
          rcases hs' with hs' | hs'
          · exact ih b tb htb s hs' o
          · exact ihb tbs htbs hs'

theorem sum_le_mul {ds : List Nat} {D : Nat} (h : ∀ d ∈ ds, d ≤ D) : ds.sum ≤ ds.length * D := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h d List.mem_cons_self
    have := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    omega

/-! ### The append loop -/

theorem go_spec (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (hlen : nops.length = D)
    (h255 : ∀ m ∈ nops, m ≤ 255) (h1 : 1 ≤ nf) (h2 : nf ≤ 65535) (hsum : 0 < nops.sum) :
    ∀ (k : Nat) (tree : Addr) (s : St T) (t : Tree T) (ds : List Nat),
      Graph.unfold s.g.view fuel tree = some t → Graph.NoAlias s.g.view tree →
      t.size = 1 + ds.sum → (∀ d ∈ ds, 1 ≤ d ∧ d ≤ D ∧ 0 < opsOf nops d) →
      1 + (ds.length + k) * D ≤ fuel →
      (∀ n, 0 < scaledDegreeDraw (s.rng.draws n) nops ∧
        scaledDegreeDraw (s.rng.draws n) nops < (nops.sum : Rat)) →
      ∃ (s' : St T) (t' : Tree T) (ds' : List Nat),
        genRandomTree.go D fuel nf nops (sampleReal sv) tree k s = .ok (tree, s') ∧
        Graph.unfold s'.g.view fuel tree = some t' ∧ Graph.NoAlias s'.g.view tree ∧
        ds'.length = ds.length + k ∧ (∀ d ∈ ds', 1 ≤ d ∧ d ≤ D ∧ 0 < opsOf nops d) ∧
        t'.size = 1 + ds'.sum ∧ nOps t' = nOps t + k ∧ (k = 0 → t' = t) := by
  intro k
  induction k with
  | zero =>
    intro tree s t ds hu hna hsz hds _ _
    exact ⟨s, t, ds, rfl, hu, hna, rfl, hds, hsz, rfl, fun _ => rfl⟩
  | succ k ih =>
    intro tree s t ds hu hna hsz hds hfuel hdr
    obtain ⟨g', rng', hrun, ⟨u, hpu, hu0⟩, hi1, hiD, hpos, hres, hsz', hna', _, hrng⟩ :=
      append_random_op_spec_holds T s.g D fuel nf tree t nops sv s.rng hu hna hlen h255 h1 h2
        hsum (hdr _).1 (hdr _).2
    generalize hd : appendDeg s.rng nops = d at hi1 hiD hpos hsz' hrng
    have hdsD : ds.sum ≤ ds.length * D := sum_le_mul (fun e he => (hds e he).2.1)
    have hbound : 1 + (ds.length + 1) * D ≤ fuel := by
      have : (ds.length + 1) * D ≤ (ds.length + (k + 1)) * D := Nat.mul_le_mul_right _ (by omega)
      omega
    have hsz2 : (appendTree t s.rng nops nf sv).size ≤ fuel := by
      rw [Nat.succ_mul] at hbound
      omega
    have hu' : Graph.unfold g'.view fuel tree = some (appendTree t s.rng nops nf sv) :=
      unfold_depth _ _ _ hres _ (Nat.le_trans (depth_le_size _) hsz2)
    have hds' : ∀ e ∈ ds ++ [d], 1 ≤ e ∧ e ≤ D ∧ 0 < opsOf nops e := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hds e he
      · simp at he; subst he; exact ⟨hi1, hiD, hpos⟩
    obtain ⟨s', t', ds', hrun', hu'', hna'', hlen', hds'', hsz'', hops, _⟩ :=
      ih tree ⟨g', rng'⟩ _ (ds ++ [d]) hu' hna' (by rw [hsz', List.sum_append]; simp; omega) hds'
        (by simp only [List.length_append, List.length_singleton]
            rw [show ds.length + 1 + k = ds.length + (k + 1) by omega]; exact hfuel)
        (by rw [hrng]; exact hdr)
    refine ⟨s', t', ds', ?_, hu'', hna'', by simp at hlen'; omega, hds'', hsz'', ?_, fun h => absurd h (by omega)⟩
    · show (appendRandomOp D fuel nf nops (sampleReal sv) tree >>= fun tree => genRandomTree.go D fuel nf nops (sampleReal sv) tree k) s = _
      rw [bindM hrun]
      exact hrun'
    · rw [hops]
      have hne := unfold_noEmpty fuel tree t hu u (preorder_mem hpu)
      unfold appendTree
      have := nOps_replaceAt t _ u (Tree.branch
        (rangeAt s.rng (s.rng.cursor + 2) (opsOf nops (appendDeg s.rng nops)))
        (leavesAt s.rng (s.rng.cursor + 3) nf sv (appendDeg s.rng nops))) hpu
      rw [nOps_leaf hne hu0] at this
      have hv : nOps (Tree.branch (rangeAt s.rng (s.rng.cursor + 2) (opsOf nops (appendDeg s.rng nops)))
          (leavesAt s.rng (s.rng.cursor + 3) nf sv (appendDeg s.rng nops))) = 1 := by
        rw [hd]
        unfold nOps
        rw [preorder_branch, List.countP_cons]
        have hl : ∀ c j, (preorder.preorderF (leavesAt s.rng c nf sv j)).countP isBranchT = 0 := by
          intro c j
          induction j generalizing c with
          | zero => rfl
          | succ j ihj =>
            simp only [leavesAt]
            rw [preorderF_cons, List.countP_append, ihj]
            unfold leafAt; split <;> simp [preorder, isBranchT, Tree.degree]
        rw [hl]
        simp [isBranchT, Tree.degree, leavesAt_length]
        omega
      omega

theorem gen_random_tree_spec_holds : gen_random_tree_spec := by
  intro T g D fuel nf nops sv init len rng hlen h255 h1 h2 hsum hfuel hdr
  let c0 : SCell T := { (blankCell : SCell T) with constant := true, val := some init }
  let s0 : St T := ⟨(g.alloc c0).2, rng⟩
  have hc0 : s0.g.cells g.next = some c0 := by simp [s0, Heap.alloc]
  have hF : 1 ≤ fuel := by omega
  have hu0 : Graph.unfold s0.g.view fuel g.next = some (.const init) := by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [unfold_leaf_cell hc0 rfl rfl]
    rfl
  have hna0 : Graph.NoAlias s0.g.view g.next := by
    apply noAlias_leaf
    intro c hc
    rw [view_cells hc0] at hc; cases hc
    rfl
  obtain ⟨s', t', ds', hrun, hu', hna', hlen', hds', hsz', hops, hk0⟩ :=
    go_spec D fuel nf nops sv hlen h255 h1 h2 hsum len g.next s0 (.const init) [] hu0 hna0
      (by simp [Tree.size])
      (fun _ h => absurd h List.not_mem_nil) (by simpa using hfuel) hdr
  refine ⟨s', t', ds', ?_, hu', hna', by simpa using hlen', hds', hsz', ?_, hk0⟩
  · show (ctorM D { val := some init } >>= fun tree => genRandomTree.go D fuel nf nops (sampleReal sv) tree len)
      ⟨g, rng⟩ = _
    rw [bindM (show ctorM D { val := some init } (⟨g, rng⟩ : St T) = .ok (g.next, s0) from rfl)]
    exact hrun
  · rw [hops]; simp [nOps, preorder, isBranchT, Tree.degree]

attribute [local semireducible] Rat.add Rat.mul Rat.inv

theorem gen_random_tree_length_refuted : ¬ gen_random_tree_length := by
  intro h
  obtain ⟨s', t, ds, hr, _⟩ :=
    h Nat (mkGraph []) 2 3 1 [1, 0] (fun _ => 0) 0 1 zeroRng rfl
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ => by simp only [zeroRng]; decide)
  have hm : (genRandomTree 2 3 1 [1, 0] (sampleReal (fun _ => (0 : Nat))) 0 1
      ⟨mkGraph [], zeroRng⟩).toOption.isNone = true := by decide +kernel
  rw [hr] at hm
  cases hm

end SymReg.Mutations
