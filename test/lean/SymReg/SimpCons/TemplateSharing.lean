import SymReg.SimpCons.Simplification

namespace SymReg.SimpCons
open DynExpr DynExpr.Simplify SymReg.HeapLemmas

/-- Per-inner denotations seen by an arbitrary template combiner,
`src/TemplateExpression.jl:1047-1055`. A combiner can use either inner independently. -/
def templateValues (fuel : Nat) (g : Graph JF) (ex : Template JF Unit)
    (x : Nat → Option JF) : Option (List JF) :=
  ex.inners.mapM (fun (_, e) => observe e.operators fuel e.tree x g)

/-- Combining a template should preserve all inner functions when every individual
inner tree is well formed and alias-free; cross-inner sharing is permitted. -/
def templateDenotation : Prop :=
  ∀ (ex : Template JF Unit) fuel (g : Graph JF) nf (x : Nat → Option JF),
    (∀ p ∈ ex.inners, ∃ t, g.unfold fuel p.2.tree = some t ∧
      t.WF 2 p.2.operators.nops nf ∧ Graph.NoAlias g p.2.tree) →
    (match templateCombine ex none fuel g with
      | .ok (e, h) => templateValues fuel h e x
      | .error _ => none) = templateValues fuel g ex x

theorem templateDenotation_refuted : ¬ templateDenotation := by
  intro h
  let g := (Graph.ofTree (Heap.empty : Graph JF) tPlus12).2
  let root := (Graph.ofTree (Heap.empty : Graph JF) tPlus12).1
  let e : Ex JF Unit := ⟨.expression, root, opsPMTD, ()⟩
  let ex : Template JF Unit := ⟨[(1, e), (2, e)], ()⟩
  have hu : g.unfold 10 root = some tPlus12 :=
    Graph.unfold_ofTree _ _ (by simp [tPlus12, Tree.Representable]) _
      (by simp [tPlus12, Tree.depth])
  have hw : tPlus12.WF 2 opsPMTD.nops 1 := by simp [tPlus12, Tree.WF, CEnum.nops, opsPMTD]
  have hvalid : ∀ p ∈ ex.inners, ∃ t, g.unfold 10 p.2.tree = some t ∧
      t.WF 2 p.2.operators.nops 1 ∧ Graph.NoAlias g p.2.tree := by
    intro p hp
    simp only [ex, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨tPlus12, hu, hw, Graph.noAlias_ofTree _ _⟩
    · exact ⟨tPlus12, hu, hw, Graph.noAlias_ofTree _ _⟩
  have hh := h ex 10 g 1 bindX3 hvalid
  have hb : templateValues 10 g ex bindX3 = some [.fin 6, .fin 6] := by decide +kernel
  have ha : (match templateCombine ex none 10 g with
      | .ok (e, h) => templateValues 10 h e bindX3
      | .error _ => none) = some [.fin 8, .fin 8] := by decide +kernel
  rw [ha, hb] at hh
  cases hh

end SymReg.SimpCons
