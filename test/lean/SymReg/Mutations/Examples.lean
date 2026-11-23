import SymReg.Mutations.Backsolve
import SymReg.Mutations.Concrete

/-!
Satisfiability of the hypotheses of the proven mutation properties: each `example` exhibits
inputs meeting all hypotheses of one property.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase

theorem exG_slotsLe : SlotsLe 2 0 exG := by
  intro a c s _ hc hs
  rcases a with _ | _ | _ | a
  · cases hc; cases hs
  · cases hc; cases hs
  · cases hc; cases hs; decide
  · cases hc

theorem exT_degLe : DegLe 2 exT := by simp [exT, DegLe]

/-- `mutate_operator_spec`: `x1 op1 x2` with two binary operators. -/
example : Graph.unfold exG.view 2 2 = some exT ∧ Graph.NoAlias exG.view 2 ∧
    ([2, 2] : List Nat).length = 2 ∧ (∀ n ∈ ([2, 2] : List Nat), n ≤ 255) ∧
    exT.WF 2 (opsOf [2, 2]) 65535 :=
  ⟨exG_unfold, exG_noAlias, rfl, by decide, by simp [exT, Tree.WF, opsOf]⟩

/-- `mutate_constant_spec`, `mutate_feature_spec`, `swap_operands_spec` and
`delete_random_op_spec`. -/
example : Graph.unfold exG.view 2 2 = some exT ∧ Graph.NoAlias exG.view 2 ∧ DegLe 2 exT ∧
    SlotsLe 2 0 exG ∧ (2 : Nat) ≤ 65535 :=
  ⟨exG_unfold, exG_noAlias, exT_degLe, exG_slotsLe, by decide⟩

/-- `mutate_factor_negate`: a constant power and a stream of zero draws. -/
example : (∀ b r : Rat, 0 < b → 0 < (fun _ _ : Rat => (1 : Rat)) b r) ∧
    (0 : Rat) ≤ 0 ∧ (0 : Rat) ≤ 0 ∧ (0 : Rat) ≤ 1 / 2 ∧ (1 / 2 : Rat) ≤ 1 ∧
    SymReg.Loss.LossPrecision.round .float64 (.fin (1 / 2)) = .fin (1 / 2) ∧
    (∀ i, 0 ≤ zeroRng.draws i ∧ zeroRng.draws i < 1) :=
  ⟨fun _ _ _ => by change (0 : Rat) < 1; decide, by decide, by decide,
    by decide +kernel, by decide +kernel, by decide +kernel,
    fun _ => by simp only [zeroRng]; decide⟩

-- 1 - 5/2^54 rounds up to 1 - 2/2^53. Equality with that threshold keeps the sign.
example : factorAt (fun _ _ => 1) 0 0 (.fin (5 / 18014398509481984))
    { draws := fun _ => 1 - 2 / 9007199254740992 } 0 = 1 := by decide +kernel

example : factorAt (fun _ _ => 1) 0 0 (.fin (5 / 18014398509481984))
    { draws := fun _ => 1 - 1 / 9007199254740992 } 0 = -1 := by decide +kernel

/-- `arity_picker_weights`. -/
example : (2 : Nat) ≤ ([1, 2] : List Nat).length ∧ 1 ≤ 2 ∧ 2 ≤ 2 := by decide

/-- `pick_degree_interval`. -/
example : 1 ≤ ([1, 1] : List Nat).length ∧ (0 : Rat) < 1 ∧
    (1 : Rat) < ((([1, 1] : List Nat).sum : Nat) : Rat) := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [List.sum_cons, List.sum_nil]
  decide

/-- `randomize_tree_spec`. -/
example : 1 ≤ (5 : Nat) := by decide

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-- The stream whose real draws are all `1/2`. -/
def halfDraws : RNG := { draws := fun _ => 1 / 2 }

/-- `append_random_op_spec`: `x1 op1 x2`, one unary and one binary operator, real draws `1/2`. -/
example : Graph.unfold exG.view 2 2 = some exT ∧ Graph.NoAlias exG.view 2 ∧
    ([1, 1] : List Nat).length = 2 ∧ (∀ m ∈ ([1, 1] : List Nat), m ≤ 255) ∧ 1 ≤ (2 : Nat) ∧
    (2 : Nat) ≤ 65535 ∧ 0 < ([1, 1] : List Nat).sum ∧
    0 < halfDraws.draws (halfDraws.cursor + 1) ∧ halfDraws.draws (halfDraws.cursor + 1) < 1 :=
  ⟨exG_unfold, exG_noAlias, rfl, by decide, by decide, by decide, by decide,
    by simp only [halfDraws]; decide, by simp only [halfDraws]; decide⟩

/-- `gen_fixed_size_exact`: one unary and one binary operator, three nodes. -/
example : ([1, 1] : List Nat).length = 2 ∧ (∀ m ∈ ([1, 1] : List Nat), m ≤ 255) ∧
    0 < opsOf [1, 1] 1 ∧ 1 ≤ (1 : Nat) ∧ (1 : Nat) ≤ 65535 ∧ 1 ≤ (3 : Nat) ∧ (3 : Nat) ≤ 3 ∧
    (3 : Nat) ≤ 3 := by decide

/-- `make_random_leaf_spec` and `make_node_spec`: two features, one unary and one binary operator,
arity 1. -/
example : 1 ≤ (2 : Nat) ∧ (2 : Nat) ≤ 65535 ∧ ([1, 1] : List Nat).length = 2 ∧
    (∀ m ∈ ([1, 1] : List Nat), m ≤ 255) ∧ 1 ≤ (1 : Nat) ∧ (1 : Nat) ≤ 2 ∧ 0 < opsOf [1, 1] 1 := by
  decide

/-- `sample_leaf_spec` and `random_node_spec`: `x1 op1 x2`. -/
example : Graph.unfold exG.view 2 2 = some exT := exG_unfold

/-- `mutate_value_spec`: the power `T(maxChange^r) = 1` and zero draws. -/
example : (0 : Rat) ≤ 0 ∧
    (∀ b r : Rat, 1 ≤ b → 0 ≤ r → r < 1 → 1 ≤ (fun _ _ => (1 : Rat)) b r ∧ (fun _ _ => (1 : Rat)) b r ≤ b) ∧
    0 ≤ zeroRng.draws zeroRng.cursor ∧ zeroRng.draws zeroRng.cursor < 1 :=
  ⟨Rat.le_refl, fun _ _ h _ _ => ⟨Rat.le_refl, h⟩, by simp only [zeroRng]; decide,
    by simp only [zeroRng]; decide⟩

/-- `prepend_random_op_spec` and `insert_random_op_spec`: `x1 op1 x2`, one unary and one binary
operator, real draws `1/2`. -/
example : Graph.unfold exG.view 2 2 = some exT ∧ Graph.NoAlias exG.view 2 ∧
    exT.WF 2 (fun _ => 255) 65535 ∧ ([1, 1] : List Nat).length = 2 ∧ 0 < ([1, 1] : List Nat).sum ∧
    0 < halfDraws.draws halfDraws.cursor ∧ halfDraws.draws halfDraws.cursor < 1 ∧
    0 < halfDraws.draws (halfDraws.cursor + 1) ∧ halfDraws.draws (halfDraws.cursor + 1) < 1 :=
  ⟨exG_unfold, exG_noAlias, by simp [exT, Tree.WF], rfl, by decide,
    by simp only [halfDraws]; decide, by simp only [halfDraws]; decide,
    by simp only [halfDraws]; decide, by simp only [halfDraws]; decide⟩

/-- `gen_random_tree_spec`: one unary and one binary operator, two appends, fuel 5. -/
example : ([1, 1] : List Nat).length = 2 ∧ 1 + 2 * 2 ≤ (5 : Nat) ∧
    ∀ n, 0 < halfDraws.draws n ∧ halfDraws.draws n < 1 :=
  ⟨rfl, by decide, fun _ => ⟨by simp only [halfDraws]; decide, by simp only [halfDraws]; decide⟩⟩

/-- `get_two_nodes_spec`, `form_random_connection_acyclic` and `break_random_connection_spec`:
`x1 op1 x2`. -/
example : Graph.unfold exG.view 2 2 = some exT ∧ exT.WF 2 (fun _ => 255) 65535 ∧ SlotsLe 2 0 exG ∧
    exT.degree ≠ 0 :=
  ⟨exG_unfold, by simp [exT, Tree.WF], exG_slotsLe, by simp [exT, Tree.degree]⟩

/-- `backsolve_spec`: complexity `0`, a fit that always returns `nothing`. -/
example : let ops : BacksolveOps Nat := ⟨fun _ _ _ => ([], []), fun _ _ => .ok 0,
      fun g _ _ _ _ => .ok (none, g)⟩
    (∀ g1 a, ∃ c, ops.cx g1 a = .ok c) ∧
      (∀ g1 a ts ms b, ∃ o g2, ops.fit g1 a ts ms b = .ok (o, g2) ∧ DynExpr.NoAlias.Ext g1 g2) :=
  ⟨fun _ _ => ⟨0, rfl⟩, fun g1 _ _ _ _ => ⟨none, g1, rfl, DynExpr.NoAlias.ext_refl _⟩⟩

end SymReg.Mutations
