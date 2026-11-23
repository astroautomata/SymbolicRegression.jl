import SymReg.Mutations.Fresh
import SymReg.Mutations.Concrete

/-!
Grafting a fresh subtree into an alias-free tree: `_make_node` builds an operator node over
fresh leaves, `set_node!` copies it onto a leaf, and the root then unfolds to the old tree with
that leaf replaced, still alias-free.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### Grafting on a graph -/

/-- A path from an object of the old tree in the new graph either is an old path or passes
through the rewritten object `x`. -/
theorem path_split {G G' : Graph T} {a x : Addr}
    (hagree : ∀ b, Graph.Reachable G a b → b ≠ x → G'.cells b = G.cells b) :
    ∀ {b p z}, Graph.Path G' b p z → Graph.Reachable G a b →
      Graph.Path G b p z ∨ ∃ p1 p2, p = p1 ++ p2 ∧ Graph.Path G b p1 x ∧ Graph.Path G' x p2 z := by
  intro b p z hp
  induction hp with
  | nil b => intro _; exact Or.inl (.nil b)
  | @cons b b' z i p c hc hi hp' ih =>
    intro hb
    by_cases hbx : b = x
    · subst hbx
      exact Or.inr ⟨[], i :: p, rfl, .nil _, .cons hc hi hp'⟩
    · have hcG : G.cells b = some c := by rw [← hagree b hb hbx, hc]
      have hb' : Graph.Reachable G a b' := reach_trans hb (reach_child hcG hi)
      rcases ih hb' with h | ⟨p1, p2, rfl, h1, h2⟩
      · exact Or.inl (.cons hcG hi h)
      · exact Or.inr ⟨i :: p1, p2, rfl, .cons hcG hi h1, h2⟩

/-- Replacing the object `x` of an alias-free tree by an alias-free subtree that shares no
object with the rest of the tree keeps the tree alias-free; its objects are old ones or objects
of the new subtree. -/
theorem graft_noAlias {G G' : Graph T} {a x : Addr} {P : List Nat}
    (hna : Graph.NoAlias G a) (hP : Graph.Path G a P x)
    (hagree : ∀ b, Graph.Reachable G a b → b ≠ x → G'.cells b = G.cells b)
    (hnax : Graph.NoAlias G' x)
    (hfresh : ∀ z, Graph.Reachable G' x z → z = x ∨ ¬ Graph.Reachable G a z) :
    Graph.NoAlias G' a ∧
      ∀ z, Graph.Reachable G' a z → Graph.Reachable G a z ∨ Graph.Reachable G' x z := by
  have hsplit := fun {p z} (h : Graph.Path G' a p z) => path_split hagree h (reach_refl _ _)
  refine ⟨?_, fun z ⟨p, hp⟩ => ?_⟩
  · intro p q z hp hq
    -- a new path to an old object that passes through `x` ends at `x`
    have back : ∀ {p1 p2 r}, Graph.Path G a r z → Graph.Path G a p1 x → Graph.Path G' x p2 z →
        p2 = [] ∧ z = x := by
      intro p1 p2 r hr h1 h2
      rcases hfresh z ⟨p2, h2⟩ with rfl | hn
      · exact ⟨hnax.acyclic z (reach_refl _ _) p2 h2, rfl⟩
      · exact absurd ⟨r, hr⟩ hn
    rcases hsplit hp with hp | ⟨p1, p2, rfl, h1, h2⟩ <;>
      rcases hsplit hq with hq | ⟨q1, q2, rfl, k1, k2⟩
    · exact hna p q z hp hq
    · obtain ⟨rfl, rfl⟩ := back hp k1 k2
      simpa using hna p q1 _ hp k1
    · obtain ⟨rfl, rfl⟩ := back hq h1 h2
      simpa using hna p1 q _ h1 hq
    · rw [hna p1 q1 x h1 k1, hnax p2 q2 z h2 k2]
  · rcases hsplit hp with h | ⟨p1, p2, rfl, _, h2⟩
    · exact Or.inl ⟨p, h⟩
    · exact Or.inr ⟨p2, h2⟩

/-! ### Operator nodes over fresh leaves -/

theorem slotsOf_slotsOf (D : Nat) (l : List (Option Addr)) :
    slotsOf D (slotsOf D l) = slotsOf D l := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < D <;> simp [slotsOf, hi]

theorem branchCell_active (D o : Nat) (cs : List Addr) (h : cs.length ≤ D) :
    (branchCell (T := T) D o cs).active = cs := by
  simp only [SCell.active, branchCell, Option.getD_some]
  exact active_slotsOf D cs h

/-- An operator node over fresh leaves at `base`, `base + 1`, ... unfolds to the operator over
those leaves. -/
theorem fresh_branch_unfold {g : SGraph T} {b base : Addr} {o i c nf : Nat} {rng : RNG}
    {sv : Rat → T} {cb : SCell T} (hb : g.cells b = some cb) (hdeg : cb.degree = i)
    (hop : cb.op = o) (hact : cb.active = List.range' base i) (hi : i ≠ 0)
    (hl : ∀ j, j < i → g.cells (base + j) = some (leafCellAt rng (c + 2 * j) nf sv)) (f : Nat) :
    Graph.unfold g.view (f + 2) b = some (.branch o (leavesAt rng c nf sv i)) := by
  refine unfold_of_cell (view_cells hb) (by simp [SCell.toCell, hact, hdeg])
    (Or.inr ⟨?_, leavesAt rng c nf sv i, ?_, ?_⟩)
  · simp [SCell.toCell, hdeg, hi]
  · simp only [SCell.toCell, hact]
    suffices H : ∀ i base c, (∀ j, j < i → g.cells (base + j) = some (leafCellAt rng (c + 2 * j) nf sv)) →
        (List.range' base i).mapM (Graph.unfold g.view (f + 1)) = some (leavesAt rng c nf sv i) from
      H i base c hl
    intro i
    induction i with
    | zero => intro _ _ _; rfl
    | succ i ih =>
      intro base c hl
      rw [List.range'_succ, List.mapM_cons]
      have h0 := hl 0 (by omega)
      simp only [Nat.add_zero, Nat.mul_zero] at h0
      rw [leafCellAt_unfold h0 f]
      have hrest := ih (base + 1) (c + 2) (fun j hj => by
        have := hl (j + 1) (by omega)
        rw [show base + (j + 1) = base + 1 + j by omega,
          show c + 2 * (j + 1) = c + 2 + 2 * j by omega] at this
        exact this)
      rw [hrest]
      rfl
  · simp [SCell.toCell, hop]

theorem leavesAt_length (rng : RNG) (c nf : Nat) (sv : Rat → T) :
    ∀ i, (leavesAt rng c nf sv i).length = i := by
  intro i
  induction i generalizing c with
  | zero => rfl
  | succ i ih => simp [leavesAt, ih]

theorem leavesAt_size (rng : RNG) (c nf : Nat) (sv : Rat → T) (o : Nat) (i : Nat) :
    (Tree.branch o (leavesAt rng c nf sv i)).size = 1 + i := by
  rw [Tree.size_branch]
  suffices H : ∀ c, ((leavesAt rng c nf sv i).map Tree.size).sum = i by rw [H]
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro c
    simp only [leavesAt, List.map_cons, List.sum_cons, ih]
    unfold leafAt; split <;> simp [Tree.size] <;> omega

/-- The operator node of degree `i` (`opNode`): one operator draw, `i` fresh leaves, then the
node. -/
theorem opNode_ok (D nf : Nat) (nops : List Nat) (sv : Rat → T) (i n : Nat) (s : St T)
    (h1 : 1 ≤ nf) (h2 : nf ≤ 65535) (hn : nopsAt nops i = .ok n)
    (hn1 : 1 ≤ n) (hn255 : n ≤ 255) (hiD : i ≤ D) :
    ∃ g' : SGraph T,
      opNode D nf nops (sampleReal sv) i s = .ok (s.g.next + i, ⟨g', advN s.rng (1 + 2 * i)⟩) ∧
      g'.next = s.g.next + i + 1 ∧
      (∀ a, a < s.g.next → g'.cells a = s.g.cells a) ∧
      (∀ j, j < i →
        g'.cells (s.g.next + j) = some (leafCellAt s.rng (s.rng.cursor + 1 + 2 * j) nf sv)) ∧
      g'.cells (s.g.next + i) =
        some (branchCell D (rangeAt s.rng s.rng.cursor n) (List.range' s.g.next i)) := by
  let s1 : St T := { s with rng := adv s.rng }
  obtain ⟨g1, hl, hn1', hold1, hc1⟩ := mkLeaves_ok D nf sv h1 h2 i s1
  have hs1 : s1.g = s.g := rfl
  rw [hs1] at hl hn1' hold1 hc1
  have ho : rangeAt s.rng s.rng.cursor n ≤ 255 := by
    have := (s.rng.indexDraws (n - 1) s.rng.cursor).isLt; simp only [rangeAt]; omega
  obtain ⟨g2, hk, hn2, hold2, hc2⟩ := ctor_branch_ok g1 D (rangeAt s.rng s.rng.cursor n)
    (List.range' s.g.next i) (by simp; exact hiD) ho
  rw [hn1'] at hk hn2 hold2 hc2
  refine ⟨g2, ?_, by simp [hn2], fun a ha => ?_, fun j hj => ?_, hc2⟩
  · simp only [opNode]
    rw [hn]
    show (randRange n >>= fun o => (mkLeaves D nf (sampleReal sv) i >>= fun cs =>
      ctorM D { op := some o, children := some cs })) s = _
    rw [bindM (randRange_ok n hn1 s), bindM hl]
    show (ctor g1 D true
      { op := some (rangeAt s.rng s.rng.cursor n), children := some (List.range' s.g.next i) }).map _ = _
    rw [hk]
    simp only [Except.map, s1, advN_advN, adv_eq]
  · rw [hold2 a (by omega), hold1 a ha]
  · rw [hold2 _ (by omega), hc1 j hj]
    rfl

/-- `set_node!(leaf, newnode)` with `newnode` an operator node built by the constructor. -/
theorem setNode_branch_ok (g : SGraph T) (D x n o : Nat) (cs : List Addr) (tc : SCell T)
    (hx : g.cells x = some tc) (hn : g.cells n = some (branchCell D o cs)) (hne : cs.length ≠ 0)
    (hD : cs.length ≤ D) :
    ∃ g' : SGraph T, setNode g D x n = .ok g' ∧ (∀ b, b ≠ x → g'.cells b = g.cells b) ∧
      g'.next = g.next ∧ ∃ c', g'.cells x = some c' ∧ c'.degree = cs.length ∧ c'.op = o ∧
        c'.active = cs := by
  let c1 : SCell T := { tc with degree := cs.length, op := o }
  obtain ⟨g1, hw1, hx1, hoth1, hnx1⟩ := write_ok hx c1
  let c2 : SCell T := { c1 with slots := some (slotsOf D (slotsOf D (cs.map some))) }
  obtain ⟨g2, hw2, hx2, hoth2, hnx2⟩ := write_ok hx1 c2
  refine ⟨g2, ?_, fun b hb => by rw [hoth2 b hb, hoth1 b hb], by rw [hnx2, hnx1], c2, hx2, rfl,
    rfl, ?_⟩
  · have hrn : g.read n = .ok (branchCell D o cs) := by simp [Heap.read, hn]
    have hrx : g.read x = .ok tc := by simp [Heap.read, hx]
    have hr1 : g1.read x = .ok c1 := by simp [Heap.read, hx1]
    have hlen : ¬ (slotsOf D (cs.map some)).length > D := by simp [slotsOf]
    unfold setNode
    rw [hrn]
    show (g.read x >>= fun tc => _) = _
    rw [hrx]
    simp only [branchCell, hne, ↓reduceIte]
    show (g.write x c1 >>= fun g1 => setChildrenRaw g1 D x (slotsOf D (cs.map some))) = _
    rw [hw1]
    show setChildrenRaw g1 D x (slotsOf D (cs.map some)) = _
    simp only [setChildrenRaw, hlen, ↓reduceIte]
    show (g1.read x >>= fun c => g1.write x { c with slots := some (slotsOf D (slotsOf D (cs.map some))) }) = _
    rw [hr1]
    exact hw2
  · simp only [c2, c1, SCell.active, Option.getD_some, slotsOf_slotsOf]
    exact active_slotsOf D cs hD

end SymReg.Mutations
