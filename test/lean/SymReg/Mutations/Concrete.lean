import SymReg.Mutations.Props

/-!
Concrete heaps for counterexamples and for satisfiability examples of the preconditions.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase DynExpr.NoAlias

variable {T : Type}

/-- A childless object reaches only itself. -/
theorem reach_leafobj {g : Graph T} {b z : Addr}
    (hleaf : ∀ cb, g.cells b = some cb → cb.children = []) (h : Graph.Reachable g b z) : z = b := by
  rcases reach_inv h with h | ⟨c, y, hc, hy, _⟩
  · exact h
  · rw [hleaf c hc] at hy; simp at hy

/-- A root whose children are distinct childless objects is alias-free. -/
theorem noAlias_flat {g : Graph T} {r : Addr} {c : Cell T} (hc : g.cells r = some c)
    (hnd : c.children.Nodup) (hleaf : ∀ b ∈ c.children, ∀ cb, g.cells b = some cb → cb.children = [])
    (hnr : r ∉ c.children) : Graph.NoAlias g r := by
  apply noAlias_node hc hnd (fun b hb => noAlias_leaf (hleaf b hb))
  · intro b hb hr
    have := reach_leafobj (hleaf b hb) hr
    subst this
    exact hnr hb
  · intro b hb b' hb' hne z hz hz'
    have h1 := reach_leafobj (hleaf b hb) hz
    have h2 := reach_leafobj (hleaf b' hb') hz'
    exact hne (h1.symm.trans h2)

/-- `x1 op x2` with operator `1`: `x1` at 0, `x2` at 1, the branch at 2 (`D = 2`). -/
def exG : SGraph Nat := mkGraph [featC 1, featC 2, br2 1 [0, 1]]

def exT : Tree Nat := .branch 1 [.feature 1, .feature 2]

theorem exG_unfold : Graph.unfold exG.view 2 2 = some exT := rfl

theorem exG_noAlias : Graph.NoAlias exG.view 2 := by
  have hch : (br2 1 [0, 1] : SCell Nat).toCell.children = [0, 1] := rfl
  apply noAlias_flat (c := (br2 1 [0, 1] : SCell Nat).toCell) rfl (by rw [hch]; decide)
  · intro b hb cb hcb
    rw [hch] at hb
    simp at hb
    rcases hb with rfl | rfl <;> (cases hcb; rfl)
  · rw [hch]; decide

/-- The stream whose every draw is zero. -/
def zeroRng : RNG := { draws := fun _ => 0 }

end SymReg.Mutations
