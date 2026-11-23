import SymReg.SimpCons.Simplification
import DynExpr.Simplify.JFLaws

namespace SymReg.SimpCons
open DynExpr DynExpr.Simplify SymReg.HeapLemmas

private theorem enumNops {T : Type} [Add T] [Mul T] [Sub T] [Inhabited T]
    (o : CEnum T) : o.toOpEnum.nops = o.nops := by
  funext d
  cases d with
  | zero => rfl
  | succ d =>
    cases d with
    | zero => simp [CEnum.toOpEnum, CEnum.nops, OpEnum.nops]
    | succ d =>
      cases d with
      | zero => simp [CEnum.toOpEnum, CEnum.nops, OpEnum.nops]
      | succ d => simp [CEnum.toOpEnum, CEnum.nops, OpEnum.nops]

private theorem foldSize {T : Type} [JlValue T] (o : OpEnum T) (t : Tree T) :
    (simplifyPure o t).size ≤ t.size := by
  induction t using Tree.induction with
  | hc v => simp [simplifyPure]
  | hf i => simp [simplifyPure]
  | hb op cs ih =>
    have hs : ((simplifyForestPure o cs).map Tree.size).sum ≤ (cs.map Tree.size).sum := by
      induction cs with
      | nil => simp [simplifyForestPure]
      | cons c cs ihcs =>
        simp only [simplifyForestPure, List.map_cons, List.sum_cons]
        exact Nat.add_le_add (ih c List.mem_cons_self)
          (ihcs (fun x hx => ih x (List.mem_cons_of_mem _ hx)))
    simp only [simplifyPure]
    cases hf : foldValue o op (simplifyForestPure o cs) with
    | none => simpa [hf, Tree.size] using Nat.add_le_add_left hs 1
    | some v => simp [Tree.size]

/-- SR's full constant-folding then operator-combination sequence,
`src/SingleIteration.jl:95-99`, preserves the denotation under DE's rewrite laws,
keeps the same enum/feature bounds, and never increases ordinary node count. -/
def simplificationPipeline : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [Neg T] [JlValue T] [Inhabited T], RingLaws T →
    ∀ (ex : Ex T M) (operators : CEnum T) nf fuel (g : Graph T) (t : Tree T),
    g.unfold fuel ex.tree = some t → t.WF 2 operators.nops nf → Graph.NoAlias g ex.tree →
    ∃ e g' t', simplifyMemberTree ex (some operators) fuel g = .ok (e, g') ∧
      g'.unfold fuel e.tree = some t' ∧ t'.WF 2 operators.nops nf ∧
      t'.size ≤ t.size ∧
      ∀ x, t'.denote operators.toOpEnum x = t.denote operators.toOpEnum x

theorem simplificationPipeline_holds : simplificationPipeline := by
  intro T M _ _ _ _ _ _ laws ex operators nf fuel g t hu hw hna
  have hw0 : t.WF 2 operators.toOpEnum.nops nf := by simpa only [enumNops] using hw
  obtain ⟨g1, hs, hu1⟩ := simplify_matches_spec_proof T operators.toOpEnum 2 nf fuel g ex.tree t hu hw0
  obtain ⟨g2, t1, hs2, ht1, hw1, _⟩ :=
    simplify_wf_proof T operators.toOpEnum 2 nf fuel g ex.tree t hu hw0
  rw [hs] at hs2
  cases hs2
  rw [hu1] at ht1
  cases ht1
  obtain ⟨g3, hs3, hna1⟩ :=
    simplify_preserves_noalias_proof T operators.toOpEnum 2 nf fuel g ex.tree t hu hw0 hna
  rw [hs] at hs3
  cases hs3
  obtain ⟨g4, t4, hs4, hu4, hd1⟩ :=
    simplify_preserves_denote_proof T operators.toOpEnum 2 nf fuel g ex.tree t hu hw0
  rw [hs] at hs4
  cases hs4
  rw [hu1] at hu4
  cases hu4
  have hw1' : (simplifyPure operators.toOpEnum t).WF 2 operators.nops nf := by
    simpa only [enumNops] using hw1
  obtain ⟨r, g', t', hc, ht', hwt', hsize⟩ := combine_wf_proof T operators nf fuel g1 ex.tree
    (simplifyPure operators.toOpEnum t) hu1 hw1' hna1
  obtain ⟨r2, g2, t2, hc2, ht2, hd2⟩ := combine_preserves_denote_ring_proof T laws operators nf fuel
    g1 ex.tree (simplifyPure operators.toOpEnum t) hu1 hw1' hna1
  rw [hc] at hc2
  cases hc2
  rw [ht'] at ht2
  cases ht2
  refine ⟨{ ex with tree := r }, g', t', ?_, ht', hwt', Nat.le_trans hsize (foldSize _ _), ?_⟩
  · simp [simplifyMemberTree, composableSimplify, patchSimplify, hs, composableCombine,
      patchCombineDeprecated, patchCombine, hc, pure_ok, ok_bind]
  · intro x
    exact (hd2 x).trans (hd1 x)

example : RingLaws JF := jf_ringLaws
example : ∃ (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 opsPMTD.nops 1 ∧ Graph.NoAlias g root :=
  ⟨(Graph.ofTree (Heap.empty : Graph JF) tPlus12).2,
    (Graph.ofTree (Heap.empty : Graph JF) tPlus12).1, tPlus12,
    Graph.unfold_ofTree _ _ (by simp [tPlus12, Tree.Representable]) _
      (by simp [tPlus12, Tree.depth]),
    by simp [tPlus12, Tree.WF, CEnum.nops, opsPMTD], Graph.noAlias_ofTree _ _⟩

end SymReg.SimpCons
