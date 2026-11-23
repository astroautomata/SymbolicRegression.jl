import SymReg.Mutations.Delete
import DynExpr.NoAlias.Ctor

/-!
Fresh objects built by the mutations: the leaves of `make_random_leaf`, the operator nodes of
`_make_node`, `set_node!` onto a leaf, and grafting a fresh subtree into an alias-free tree.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### Streams -/

/-- The stream after `n` draws. -/
def advN (r : RNG) (n : Nat) : RNG := { r with cursor := r.cursor + n }

theorem advN_advN (r : RNG) (a b : Nat) : advN (advN r a) b = advN r (a + b) := by
  simp [advN, Nat.add_assoc]

theorem adv_eq (r : RNG) : adv r = advN r 1 := rfl

/-! ### Leaves -/

/-- The cell of the leaf built by `make_random_leaf` from the draws at cursors `c`
(`rand(rng, Bool)`) and `c + 1` (`sample_value` or `rand(rng, 1:nfeatures)`). -/
def leafCellAt (rng : RNG) (c nf : Nat) (sv : Rat → T) : SCell T :=
  if (rng.indexDraws 1 c).val = 1 then
    { (blankCell : SCell T) with constant := true, val := some (sv (rng.draws (c + 1))) }
  else { (blankCell : SCell T) with feature := rangeAt rng (c + 1) nf }

/-- The leaf built by `make_random_leaf` from the draws at cursors `c` and `c + 1`. -/
def leafAt (rng : RNG) (c nf : Nat) (sv : Rat → T) : Tree T :=
  if (rng.indexDraws 1 c).val = 1 then .const (sv (rng.draws (c + 1)))
  else .feature (rangeAt rng (c + 1) nf)

/-- The leaves of `@ntuple(k, j -> make_random_leaf(...))` from cursor `c`. -/
def leavesAt (rng : RNG) (c nf : Nat) (sv : Rat → T) : Nat → List (Tree T)
  | 0 => []
  | k + 1 => leafAt rng c nf sv :: leavesAt rng (c + 2) nf sv k

theorem leafCellAt_advN (r : RNG) (n c nf : Nat) (sv : Rat → T) :
    leafCellAt (advN r n) c nf sv = leafCellAt r c nf sv := rfl

theorem leafCellAt_degree (rng : RNG) (c nf : Nat) (sv : Rat → T) :
    (leafCellAt rng c nf sv).degree = 0 ∧ (leafCellAt rng c nf sv).slots = none ∧
      (leafCellAt rng c nf sv).active = [] := by
  unfold leafCellAt; split <;> simp [blankCell, SCell.active]

theorem leafCellAt_unfold {g : SGraph T} {a : Addr} {rng : RNG} {c nf : Nat} {sv : Rat → T}
    (h : g.cells a = some (leafCellAt rng c nf sv)) (f : Nat) :
    Graph.unfold g.view (f + 1) a = some (leafAt rng c nf sv) := by
  obtain ⟨hd, _, ha⟩ := leafCellAt_degree rng c nf sv
  rw [unfold_leaf_cell h hd ha]
  unfold leafOf leafCellAt leafAt
  split <;> simp [blankCell]

theorem leafAt_feature (rng : RNG) (c nf : Nat) (sv : Rat → T) (i : Nat) (h1 : 1 ≤ nf)
    (h : leafAt rng c nf sv = .feature i) : 1 ≤ i ∧ i ≤ nf := by
  unfold leafAt at h
  split at h
  · cases h
  · cases h
    have := (rng.indexDraws (nf - 1) (c + 1)).isLt
    simp only [rangeAt]; omega

/-- `make_random_leaf(nfeatures, T, N, rng, options)`: one fresh leaf at the next address,
two draws. -/
theorem makeRandomLeaf_ok (D nf : Nat) (sv : Rat → T) (s : St T) (h1 : 1 ≤ nf)
    (h2 : nf ≤ 65535) :
    makeRandomLeaf D nf (sampleReal sv) s =
      .ok (s.g.next, ⟨(s.g.alloc (leafCellAt s.rng s.rng.cursor nf sv)).2, advN s.rng 2⟩) := by
  unfold makeRandomLeaf sampleReal
  rw [bindM (randBool_ok s)]
  by_cases hb : (s.rng.indexDraws 1 s.rng.cursor).val = 1
  · simp only [hb, decide_true, ↓reduceIte]
    simp only [leafCellAt, hb, ↓reduceIte]
    rfl
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [bindM (randRange_ok nf h1 _)]
    have hle : ((adv s.rng).indexDraws (nf - 1) (adv s.rng).cursor).val + 1 ≤ 65535 := by
      have := ((adv s.rng).indexDraws (nf - 1) (adv s.rng).cursor).isLt; omega
    simp [leafCellAt, hb, ctorM, liftG, ctor, hle, Except.map, rangeAt]
    rfl

/-- `k` fresh leaves at consecutive addresses, `2k` draws. -/
theorem mkLeaves_ok (D nf : Nat) (sv : Rat → T) (h1 : 1 ≤ nf) (h2 : nf ≤ 65535) :
    ∀ (k : Nat) (s : St T), ∃ g' : SGraph T,
      mkLeaves D nf (sampleReal sv) k s = .ok (List.range' s.g.next k, ⟨g', advN s.rng (2 * k)⟩) ∧
      g'.next = s.g.next + k ∧ (∀ a, a < s.g.next → g'.cells a = s.g.cells a) ∧
      ∀ j, j < k → g'.cells (s.g.next + j) = some (leafCellAt s.rng (s.rng.cursor + 2 * j) nf sv)
  | 0, s => ⟨s.g, by simp [mkLeaves, advN]; rfl, rfl, fun _ _ => rfl, fun j hj => absurd hj (by omega)⟩
  | k + 1, s => by
    let s1 : St T := ⟨(s.g.alloc (leafCellAt s.rng s.rng.cursor nf sv)).2, advN s.rng 2⟩
    obtain ⟨g', hrun, hnext, hold, hcells⟩ := mkLeaves_ok D nf sv h1 h2 k s1
    have hn1 : s1.g.next = s.g.next + 1 := rfl
    have hc0 : s1.g.cells s.g.next = some (leafCellAt s.rng s.rng.cursor nf sv) := by
      simp [s1, Heap.alloc]
    have hold1 : ∀ a, a < s.g.next → s1.g.cells a = s.g.cells a := by
      intro a ha; simp [s1, Heap.alloc, Nat.ne_of_lt ha]
    refine ⟨g', ?_, by omega, fun a ha => by rw [hold a (by omega), hold1 a ha], ?_⟩
    · simp only [mkLeaves]
      rw [bindM (makeRandomLeaf_ok D nf sv s h1 h2)]
      show (mkLeaves D nf (sampleReal sv) k >>= fun as => pure (s.g.next :: as)) s1 = _
      rw [bindM hrun]
      show (Except.ok (_, (⟨g', advN (advN s.rng 2) (2 * k)⟩ : St T)) : Except JlError _) = _
      rw [List.range'_succ, advN_advN, show 2 + 2 * k = 2 * (k + 1) by omega]
      rfl
    · intro j hj
      cases j with
      | zero => simpa using (hold s.g.next (by omega)).trans hc0
      | succ j =>
        have := hcells j (by omega)
        rw [hn1, show s.g.next + 1 + j = s.g.next + (j + 1) by omega] at this
        rw [this, leafCellAt_advN]
        congr 2
        simp only [s1, advN]
        omega

/-- The object built by the branch constructor on `cs`. -/
def branchCell (D o : Nat) (cs : List Addr) : SCell T :=
  { (blankCell : SCell T) with degree := cs.length, op := o, slots := some (slotsOf D (cs.map some)) }

/-- The branch constructor `constructorof(N)(; op, children)` on `cs` with at most `D`
children. -/
theorem ctor_branch_ok (g : SGraph T) (D o : Nat) (cs : List Addr) (hl : cs.length ≤ D)
    (ho : o ≤ 255) :
    ∃ g' : SGraph T, ctor g D true { op := some o, children := some cs } = .ok (g.next, g') ∧
      g'.next = g.next + 1 ∧ (∀ x, x ≠ g.next → g'.cells x = g.cells x) ∧
      g'.cells g.next = some (branchCell D o cs) := by
  let c0 : SCell T := { (blankCell : SCell T) with degree := cs.length, op := o }
  have hc0 : (g.alloc c0).2.cells g.next = some c0 := by simp [Heap.alloc]
  obtain ⟨g', hw, hc', hoth, hnext⟩ := write_ok hc0 (branchCell D o cs)
  refine ⟨g', ?_, by rw [hnext]; rfl, fun x hx => by rw [hoth x hx]; simp [Heap.alloc, hx], hc'⟩
  have h1 : ¬ cs.length > D := by omega
  have h2 : ¬ o > 255 := by omega
  have hr : (g.alloc c0).2.read g.next = .ok c0 := by simp [Heap.read, hc0]
  have hsc : setChildren (g.alloc c0).2 D g.next cs = .ok g' := by
    simp only [setChildren, setChildrenRaw, List.length_map, h1, ↓reduceIte]
    rw [show ((g.alloc c0).2.read g.next >>= fun c =>
        (g.alloc c0).2.write g.next { c with slots := some (slotsOf D (cs.map some)) }) =
        (g.alloc c0).2.write g.next (branchCell D o cs) from by rw [hr]; rfl]
    exact hw
  show (if cs.length > D then (throw (.assertionError "D2 <= max_degree(N)") : Jl (Addr × SGraph T))
    else if o > 255 then throw (.errorException "InexactError: trunc(UInt8, op)")
    else (do let g2 ← setChildren (g.alloc c0).2 D (g.alloc c0).1 cs; pure ((g.alloc c0).1, g2))) = _
  rw [if_neg h1, if_neg h2]
  show (setChildren (g.alloc c0).2 D g.next cs >>= fun g2 => pure (g.next, g2)) = _
  rw [hsc]
  rfl

end SymReg.Mutations
