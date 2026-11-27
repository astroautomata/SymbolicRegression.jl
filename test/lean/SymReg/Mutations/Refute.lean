import SymReg.Mutations.FixedSize
import SymReg.Mutations.Write
import SymReg.Mutations.Concrete

/-! Counterexamples for the refuted mutation properties. -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase

/-- `mutate_operator` on `x1 op1 x2` with two binary operators: the operator draw `1` keeps
operator `1`. -/
theorem mutate_operator_changes_refuted : ¬ mutate_operator_changes := by
  intro h
  obtain ⟨g', rng', hrun, hne⟩ := h Nat exG 2 2 2 [2, 2] exT zeroRng exG_unfold exG_noAlias rfl
    (by decide) (by simp [exT, Tree.WF, opsOf]) (by decide)
  have hcomp : (match mutateOperator 2 [2, 2] 2 false (⟨exG, zeroRng⟩ : St Nat) with
      | .ok (_, s) => Graph.unfold s.g.view 4 2
      | .error _ => none) = some exT := rfl
  rw [hrun] at hcomp
  exact hne _ hcomp rfl

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-- Unary operators only (`nops = (1, 0)`, `D = 2`) and `rand(rng) = 0.0`: `scaled_rand = 0`
fails every `scaled_rand > csum[i]` test, so the last branch, degree `2`, is taken although it
has no operator. -/
theorem pick_degree_has_operator_refuted : ¬ pick_degree_has_operator := by
  intro h
  have h1 := h [1, 0] 0 (by decide) (by decide) (by decide) (by decide)
  have h2 : opsOf [1, 0] (pickDeg ([1, 0] : List Nat).length [1, 0]
      (scaledDegreeDraw 0 [1, 0])) = 0 := by decide +kernel
  omega

/-- `sin(x1)` shared twice under `+`: `x1` at 0, `p = sin(x1)` at 1, `p + p` at 2. -/
def rotG : SGraph Nat := mkGraph [featC 1, br2 1 [0], br2 1 [1, 1]]

/-- Rotating `p + p` at the root with pivot slot 1 makes `p` the new root with child `x1 + p`,
whose second slot still holds `p`: `p → (x1 + p) → p` is a cycle. -/
theorem rotate_graph_acyclic_refuted : ¬ rotate_graph_acyclic := by
  intro h
  have key : (match randomlyRotateTree 2 3 true 2 (⟨rotG, zeroRng⟩ : St Nat) with
      | .ok (r, s) => decide (r = 1 ∧ (s.g.view.cells 1).map Cell.children = some [2] ∧
          (s.g.view.cells 2).map Cell.children = some [0, 1])
      | .error _ => false) = true := by decide
  cases hr : randomlyRotateTree 2 3 true 2 (⟨rotG, zeroRng⟩ : St Nat) with
  | error e => rw [hr] at key; cases key
  | ok p =>
    obtain ⟨r, s⟩ := p
    rw [hr] at key
    simp only [decide_eq_true_eq] at key
    obtain ⟨rfl, h1, h2⟩ := key
    obtain ⟨c1, hc1, hch1⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨c2, hc2, hch2⟩ := Option.map_eq_some_iff.mp h2
    have hac := h Nat rotG 2 3 2 _ zeroRng 1 s rfl (by simp [DegLe]) hr
    have hp : Graph.Path s.g.view 1 [0, 1] 1 :=
      .cons hc1 (by rw [hch1]; rfl) (.cons hc2 (by rw [hch2]; rfl) (.nil 1))
    exact absurd (hac 1 ⟨[], .nil 1⟩ [0, 1] hp) (by simp)

/-- Binary and ternary operators only (`nops = (0, 1, 1)`) and `node_count = 4`: a ternary root
over three leaves has 4 nodes, but the threshold draw `1` picks arity 2, leaving one node to go,
and no unary operator exists, so the loop stops at 3 nodes. -/
theorem gen_fixed_size_realizable_refuted : ¬ gen_fixed_size_realizable := by
  intro h
  let sv : Rat → Nat := fun _ => 0
  let nops : List Nat := [0, 1, 1]
  obtain ⟨r, s', hrun, t, hu, hsz⟩ := h Nat (mkGraph []) 3 4 1 nops sv 4 4 zeroRng
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨[3], by simp [nops, opsOf], rfl⟩
  -- the first leaf
  let s0 : St Nat := ⟨((mkGraph [] : SGraph Nat).alloc (leafCellAt zeroRng 0 1 sv)).2, advN zeroRng 2⟩
  have hc0 : s0.g.cells 0 = some (leafCellAt zeroRng 0 1 sv) := rfl
  have hu0 : Graph.unfold s0.g.view 4 0 = some (leafAt zeroRng 0 1 sv) := leafCellAt_unfold hc0 3
  have hna0 : Graph.NoAlias s0.g.view 0 := by
    apply DynExpr.NoAlias.noAlias_leaf
    intro c hc
    rw [view_cells hc0] at hc; cases hc
    simp [SCell.toCell, (leafCellAt_degree _ _ _ _).2.2]
  have hsz0 : (leafAt zeroRng 0 1 sv).size = 1 := by
    unfold leafAt; split <;> simp [Tree.size]
  have e1 : genRandomTreeFixedSize 3 4 1 nops (sampleReal sv) ((4 : Nat) : Int) 4 ⟨mkGraph [], zeroRng⟩ =
      fixedSizeLoop 3 4 1 nops (sampleReal sv) ((4 : Nat) : Int) 0 (3 + 1) ((1 : Nat) : Int) s0 := by
    simp only [genRandomTreeFixedSize]
    rw [bindM (makeRandomLeaf_ok 3 1 sv ⟨mkGraph [], zeroRng⟩ (by decide) (by decide))]
    rfl
  -- the first arity draw is 2
  obtain ⟨k, s1, hk, _, hkpos⟩ :=
    arity_picker_spec_holds Nat (((4 : Nat) : Int) - ((1 : Nat) : Int)) nops s0
  obtain ⟨hk1, _, hklen, _, hlo, hhi, hs1g, _⟩ := hkpos (by decide)
  have hk2 : k = 2 := by
    have hk3 : k ≤ 3 := hklen
    have h : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h with rfl | rfl | rfl
    · exact False.elim ((by decide : ¬ _) hhi)
    · rfl
    · exact False.elim ((by decide : ¬ _) hlo)
  subst hk2
  obtain ⟨s2, t', e2, hu2, hsz2, _, _⟩ := loop_step 3 4 1 nops sv 4 0 (by decide) (by decide)
    (by decide) 3 s0 s1 1 2 _ hu0 hna0 hsz0 (by decide) hk hs1g (by decide) (by decide) (by decide)
    (by decide)
  -- one node remains and no unary operator exists: the loop stops
  have e3 : fixedSizeLoop 3 4 1 nops (sampleReal sv) ((4 : Nat) : Int) 0 3 ((1 + 2 : Nat) : Int) s2 =
      .ok (0, s2) := by
    obtain ⟨k', s3, hk', hk'0, _⟩ :=
      arity_picker_spec_holds Nat (((4 : Nat) : Int) - ((1 + 2 : Nat) : Int)) nops s2
    obtain ⟨rfl, rfl⟩ := hk'0 (by decide)
    simp only [fixedSizeLoop]
    rw [if_neg (by decide), bindM hk']
    rfl
  rw [e1, e2, e3] at hrun
  cases hrun
  have := unfold_mono _ _ _ hu 6 (by decide)
  rw [hu2] at this
  cases this
  omega
end SymReg.Mutations
