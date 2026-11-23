import SymReg.SimpCons.Members

namespace SymReg.SimpCons
open DynExpr DynExpr.Simplify SymReg.HeapLemmas

/-- The custom complexity observed after SR's simplification sequence,
`src/Mutate.jl:906-908`, `src/Complexity.jl:20-27`. Structural custom functions are
interpreted on the unfolded expression contents; metadata-dependent functions are
covered separately by the general callback in `mutateSimplify`. -/
def simplifiedComplexity (o : CEnum JF) (fuel root : Nat) (g : Graph JF)
    (complexity : Tree JF → Int) : Jl Int := do
  let (e, g) ← simplifyMemberTree (⟨.expression, root, o, ()⟩ : Ex JF Unit) none fuel g
  let t ← match g.unfold fuel e.tree with
    | some t => pure t
    | none => throw (.errorException "tree does not unfold")
  pure (complexity t)

/-- Simplification should preserve an already-satisfied maxsize with a user
complexity function. SR's immediate-return mutation does not check this bound. -/
def customSimplificationBound : Prop :=
  ∀ (o : CEnum JF) fuel (g : Graph JF) root (t : Tree JF)
    (complexity : Tree JF → Int) maxsize,
    g.unfold fuel root = some t → t.WF 2 o.nops 1 → Graph.NoAlias g root →
    complexity t ≤ maxsize →
    ∃ n, simplifiedComplexity o fuel root g complexity = .ok n ∧ n ≤ maxsize

theorem customSimplificationBound_refuted : ¬ customSimplificationBound := by
  intro h
  let g := (Graph.ofTree (Heap.empty : Graph JF) foldingTree).2
  let root := (Graph.ofTree (Heap.empty : Graph JF) foldingTree).1
  let complexity := fun t : Tree JF => (20 : Int) - DynExpr.NodeBase.countNodesT 2 t
  have hu : g.unfold 10 root = some foldingTree :=
    Graph.unfold_ofTree _ _ (by simp [foldingTree, Tree.Representable]) _
      (by simp [foldingTree, Tree.depth])
  have hw : foldingTree.WF 2 opsPMTD.nops 1 := by
    simp [foldingTree, Tree.WF, CEnum.nops, opsPMTD]
  have hb : complexity foldingTree ≤ 18 := by decide +kernel
  obtain ⟨n, hn, hsize⟩ := h opsPMTD 10 g root foldingTree complexity 18 hu hw
    (Graph.noAlias_ofTree _ _) hb
  have he : simplifiedComplexity opsPMTD 10 root g complexity = .ok 19 := by
    decide +kernel
  rw [he] at hn
  cases hn
  omega

example : ∃ (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 opsPMTD.nops 1 ∧ Graph.NoAlias g root ∧
      (20 : Int) - t.size ≤ 18 :=
  ⟨(Graph.ofTree (Heap.empty : Graph JF) foldingTree).2,
    (Graph.ofTree (Heap.empty : Graph JF) foldingTree).1, foldingTree,
    Graph.unfold_ofTree _ _ (by simp [foldingTree, Tree.Representable]) _
      (by simp [foldingTree, Tree.depth]),
    by simp [foldingTree, Tree.WF, CEnum.nops, opsPMTD], Graph.noAlias_ofTree _ _,
    by simp [foldingTree, Tree.size]⟩

end SymReg.SimpCons
