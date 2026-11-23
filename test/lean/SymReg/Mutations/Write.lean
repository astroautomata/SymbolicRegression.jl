import SymReg.Mutations.Sampled

/-!
Field writes on one sampled node: `mutate_operator`, `mutate_constant`, `mutate_feature`.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### Heap writes -/

theorem write_ok {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) (v : SCell T) :
    ∃ g' : SGraph T, g.write a v = .ok g' ∧ g'.cells a = some v ∧
      (∀ b, b ≠ a → g'.cells b = g.cells b) ∧ g'.next = g.next := by
  unfold Heap.write
  rw [dite_eq_right (by simp [h])]
  exact ⟨_, rfl, by simp, by intro b hb; simp [hb], rfl⟩

theorem setOpM_ok {s : St T} {x o : Nat} {c : SCell T} (hc : s.g.cells x = some c) (ho : o ≤ 255) :
    ∃ g' : SGraph T, setOpM x o s = .ok ((), { s with g := g' }) ∧
      g'.cells x = some { c with op := o } ∧ (∀ b, b ≠ x → g'.cells b = s.g.cells b) ∧
      g'.next = s.g.next := by
  obtain ⟨g', hw, h1, h2, h3⟩ := write_ok hc { c with op := o }
  refine ⟨g', ?_, h1, h2, h3⟩
  have hr : s.g.read x = .ok c := by simp [Heap.read, hc]
  unfold setOpM liftG
  simp only [gt_iff_lt, Nat.not_lt.mpr ho, ↓reduceIte, hr, ok_bind, pure_bind]
  rw [hw]; rfl

theorem setFeatureM_ok {s : St T} {x f : Nat} {c : SCell T} (hc : s.g.cells x = some c)
    (hf : f ≤ 65535) :
    ∃ g' : SGraph T, setFeatureM x f s = .ok ((), { s with g := g' }) ∧
      g'.cells x = some { c with feature := f } ∧ (∀ b, b ≠ x → g'.cells b = s.g.cells b) ∧
      g'.next = s.g.next := by
  obtain ⟨g', hw, h1, h2, h3⟩ := write_ok hc { c with feature := f }
  refine ⟨g', ?_, h1, h2, h3⟩
  have hr : s.g.read x = .ok c := by simp [Heap.read, hc]
  unfold setFeatureM liftG
  simp only [gt_iff_lt, Nat.not_lt.mpr hf, ↓reduceIte, hr, ok_bind, pure_bind]
  rw [hw]; rfl

theorem setValM_ok {s : St T} {x : Nat} {c : SCell T} (hc : s.g.cells x = some c) (v : T) :
    ∃ g' : SGraph T, setValM x v s = .ok ((), { s with g := g' }) ∧
      g'.cells x = some { c with val := some v } ∧ (∀ b, b ≠ x → g'.cells b = s.g.cells b) ∧
      g'.next = s.g.next := by
  obtain ⟨g', hw, h1, h2, h3⟩ := write_ok hc { c with val := some v }
  refine ⟨g', ?_, h1, h2, h3⟩
  have hr : s.g.read x = .ok c := by simp [Heap.read, hc]
  unfold setValM liftG
  simp only [hr, ok_bind]
  rw [hw]; rfl

theorem view_cells {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) :
    g.view.cells a = some c.toCell := by
  simp [SGraph.view, h]

theorem view_oth {g g' : SGraph T} {x : Addr} (h : ∀ b, b ≠ x → g'.cells b = g.cells b) :
    ∀ b, b ≠ x → g'.view.cells b = g.view.cells b := by
  intro b hb; simp [SGraph.view, h b hb]

/-- Writing new fields into an object whose active children are unchanged relabels its
branch: the children still unfold to the same subtrees. -/
theorem unfold_relabel_branch {g g' : SGraph T} {x f : Nat} {c c' : SCell T} {ts : List (Tree T)}
    (hc : g.cells x = some c) (hc' : g'.cells x = some c') (hact : c'.active = c.active)
    (hdeg : c'.degree = c.degree) (hoth : ∀ b, b ≠ x → g'.cells b = g.cells b)
    (hna : Graph.NoAlias g.view x) (hd : c.degree ≠ 0)
    (hts : c.active.mapM (Graph.unfold g.view f) = some ts) (hl : c.active.length = c.degree) :
    Graph.unfold g'.view (f + 1) x = some (.branch c'.op ts) := by
  have hv' : g'.view.cells x = some c'.toCell := view_cells hc'
  have hv : g.view.cells x = some c.toCell := view_cells hc
  refine unfold_of_cell hv' (by simp [SCell.toCell, hact, hdeg, hl]) (Or.inr ⟨by simp [SCell.toCell, hdeg, hd], ts, ?_, rfl⟩)
  simp only [SCell.toCell, hact]
  rw [← hts]
  apply mapM_congr'
  intro y hy
  apply unfold_agree
  intro z hz
  apply view_oth hoth
  intro hzx
  subst hzx
  exact noAlias_child_not_reach hna hv (by simpa [SCell.toCell] using hy) hz

/-- A degree-zero object without active children unfolds to its leaf fields. -/
theorem unfold_leaf_cell {g : SGraph T} {x f : Nat} {c : SCell T} (hc : g.cells x = some c)
    (hd : c.degree = 0) (ha : c.active = []) :
    Graph.unfold g.view (f + 1) x = leafOf c := by
  have hv : g.view.cells x = some c.toCell := view_cells hc
  cases hk : c.constant <;> cases hval : c.val <;>
    simp [Graph.unfold, hv, SCell.toCell, ha, hd, hk, hval, leafOf]

/-- Writing one object of an alias-free tree, which then unfolds to `u'`, replaces the
subtree at its path. -/
theorem write_node_spec {g g' : SGraph T} {fuel tree x k : Nat} {t u' : Tree T} {P : List Nat}
    (hu : Graph.unfold g.view fuel tree = some t) (hna : Graph.NoAlias g.view tree)
    (hP : Graph.Path g.view tree P x) (hrepl : ∀ v, ReplPath t P v (replaceAt t k v))
    (hoth : ∀ b, b ≠ x → g'.cells b = g.cells b) (F : Nat) (hF : F ≤ fuel)
    (hx : Graph.unfold g'.view F x = some u') :
    Graph.unfold g'.view (fuel + fuel) tree = some (replaceAt t k u') := by
  have h := rewrite_sub g.view g'.view x u' F hx fuel tree t hu hna
    (fun b _ hnr => view_oth hoth b (fun hb => hnr (hb ▸ reach_refl _ _))) P _ hP (hrepl u')
  exact unfold_mono _ _ _ h _ (by omega)

/-! ### `mutate_operator` -/

theorem mutate_operator_unshared_holds : mutate_operator_unshared := by
  intro T g D fuel tree nops t rng hu hna hlen h255 hwf
  obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
  have hrd : rd tree (⟨g, rng⟩ : St T) = .ok (rc, ⟨g, rng⟩) := rd_ok hrc
  by_cases hd0 : rc.degree = 0
  · refine ⟨g, rng, ?_, fun _ => ⟨rfl, rfl⟩, fun h => absurd (hrdeg ▸ hd0) h⟩
    simp only [mutateOperator]
    rw [bindM hrd]
    simp [hd0]
    rfl
  have htd : t.degree ≠ 0 := by rw [← hrdeg]; exact hd0
  -- the sample
  let E : Nat → Bool := fun k => ((preorder t)[k]?).any isBranchT
  have hne : eligIdx t.size E ≠ [] :=
    eligIdx_ne_nil (Tree.size_pos t) (by simp [E, preorder_zero, isBranchT, htd])
  have hFE : ∀ k x P u, Graph.Path g.view tree P x → (preorder t)[k]? = some u →
      Graph.unfold g.view (fuel - P.length) x = some u → (P = [] ↔ k = 0) →
      cellP (fun c => c.degree != 0) g x = E k := by
    intro k x P u _ hpu hun _
    rw [cellP_of_unfold (Q := isBranchT) (fun c s hd _ => by simp [isBranchT, hd]) hun]
    simp [E, hpu]
  obtain ⟨k, x, P, u, hk, hsamp, hP, hpu, hun, hrepl, _, _⟩ :=
    sample_spec ⟨g, rng⟩ fuel tree t (cellP (fun c => c.degree != 0)) E hu hFE hne
  have hkE : k ∈ eligT isBranchT t := List.mem_of_getElem? hk
  have hku : drawAt rng rng.cursor (eligT isBranchT t) = k := by
    simp only [drawAt, eligT]; exact (by rw [hk]; rfl)
  obtain ⟨u0, hu0, hbu⟩ := elig_pick hkE
  rw [hpu] at hu0; cases hu0
  obtain ⟨fx, hfx⟩ := fuel_sub_pos hun
  rw [hfx] at hun
  obtain ⟨c, hcx, hlx, hdx, hcase⟩ := cell_of_unfold hun
  have hdc : c.degree ≠ 0 := by rw [hdx]; simpa [isBranchT] using hbu
  rcases hcase with ⟨hd, _⟩ | ⟨_, ts, hts, rfl⟩
  · exact absurd hd hdc
  -- well-formedness of the sampled node
  have hwu : (Tree.branch c.op ts).WF D (opsOf nops) 65535 := preorder_wf t hwf _ (preorder_mem hpu)
  have hlts : ts.length = c.degree := by rw [mapM_length _ _ _ hts, hlx]
  simp only [Tree.WF] at hwu
  obtain ⟨⟨h1, hD, _⟩, ⟨ho1, hon, _⟩, hkids⟩ := hwu
  rw [hlts] at h1 hD hon
  have hnth : nopsAt nops c.degree = .ok (opsOf nops c.degree) := by
    have : c.degree - 1 < nops.length := by omega
    simp [nopsAt, show 1 ≤ c.degree by omega, opsOf, List.getElem?_eq_getElem this]
  have hn1 : 1 ≤ opsOf nops c.degree := by omega
  have hn255 : opsOf nops c.degree ≤ 255 := by
    have : c.degree - 1 < nops.length := by omega
    simp only [opsOf, List.getElem?_eq_getElem this, Option.getD_some]
    exact h255 _ (List.getElem_mem this)
  -- the operator draw and the write
  let s1 : St T := { g := g, rng := adv rng }
  let o := (s1.rng.indexDraws (opsOf nops c.degree - 1) s1.rng.cursor).val + 1
  have ho : o ≤ opsOf nops c.degree := by
    have := (s1.rng.indexDraws (opsOf nops c.degree - 1) s1.rng.cursor).isLt
    simp only [o]; omega
  obtain ⟨g2, hset, hx2, hoth, _⟩ :=
    setOpM_ok (s := ({ s1 with rng := adv s1.rng } : St T)) (x := x) (o := o) hcx (by omega)
  have hrun : mutateOperator fuel nops tree false ⟨g, rng⟩ = .ok (tree, ⟨g2, adv s1.rng⟩) := by
    simp only [mutateOperator]
    rw [bindM hrd]
    simp only [hd0, ↓reduceIte]
    rw [bindM hsamp, bindM (rd_ok (s := s1) hcx)]
    show (liftJ (nopsAt nops c.degree) >>= _) s1 = _
    rw [hnth]
    rw [bindM (rfl : liftJ (T := T) (.ok (opsOf nops c.degree)) s1 = .ok (opsOf nops c.degree, s1)),
      bindM (randRange_ok _ hn1 s1), bindM hset]
    rfl
  -- the new node unfolds to the relabelled branch
  have hnax : Graph.NoAlias g.view x := noAlias_reach hna ⟨P, hP⟩
  have hx' : Graph.unfold g2.view (fx + 1) x = some (.branch o ts) :=
    unfold_relabel_branch hcx hx2 rfl rfl hoth hnax hdc (by simpa using hts) hlx
  have hF : fx + 1 ≤ fuel := by omega
  have hres := write_node_spec hu hna hP hrepl hoth (fx + 1) hF hx'
  have hdegu : (Tree.branch c.op ts).degree = c.degree := by simp [Tree.degree, hlts]
  have hw' : withOp (rangeAt rng (rng.cursor + 1) (opsOf nops (Tree.branch c.op ts).degree))
      (Tree.branch c.op ts) = .branch o ts := by
    rw [hdegu]; rfl
  refine ⟨g2, adv s1.rng, hrun, fun h => absurd h htd, fun _ => ⟨.branch c.op ts, ?_, ?_, ?_, rfl⟩⟩
  · rw [hku]; exact hpu
  · rw [hku, hw']; exact hres
  · rw [hku, hw']
    apply replaceAt_wf t k _ hwf
    simp only [Tree.WF]
    refine ⟨⟨by omega, by omega, by omega⟩, ⟨by simp [o], by rw [hlts]; exact ho, by omega⟩, hkids⟩

theorem mutate_operator_spec_holds : mutate_operator_spec := by
  refine ⟨mutate_operator_unshared_holds, ?_⟩
  intro T s fuel tree nops isGraph root hroot
  refine ⟨?_, ?_⟩
  · intro hd
    simp only [mutateOperator, bindM (rd_ok hroot), if_pos hd]
    rfl
  · intro x c hd hsamp hc
    let s1 : St T := { s with rng := adv s.rng }
    have hrun : mutateOperator fuel nops tree isGraph s =
        (do
          let n ← liftJ (nopsAt nops c.degree)
          let o ← randRange n
          setOpM x o
          pure tree) s1 := by
      simp only [mutateOperator, bindM (rd_ok hroot), if_neg hd]
      rw [bindM hsamp, bindM (rd_ok (s := s1) hc)]
    rw [hrun]
    cases hn : nopsAt nops c.degree with
    | error e => rfl
    | ok n =>
      cases n with
      | zero => rfl
      | succ n =>
        let o := rangeAt s.rng (s.rng.cursor + 1) (n + 1)
        let s2 : St T := { s with rng := adv (adv s.rng) }
        have hbound := (s.rng.indexDraws n (s.rng.cursor + 1)).isLt
        change 1 ≤ o ∧ o ≤ n + 1 ∧ _
        refine ⟨by dsimp [o, rangeAt]; omega, by dsimp [o, rangeAt]; omega, ?_⟩
        have hop : (randRange (n + 1) >>= fun j => setOpM x j >>= fun _ => pure tree)
            s1 = (setOpM x o >>= fun _ => pure tree) s2 :=
          bindM (randRange_ok (n + 1) (by omega) s1)
        by_cases ho : o ≤ 255
        · rw [if_pos ho]
          obtain ⟨g', hw, hcell, hframe, hnext⟩ := setOpM_ok (s := s2) hc ho
          refine ⟨g', ?_, hnext, hcell, hframe⟩
          exact hop.trans ((bindM hw).trans rfl)
        · rw [if_neg ho]
          have hw : setOpM x o s2 = .error (.errorException "InexactError: trunc(UInt8, op)") := by
            simp only [setOpM, liftG, gt_iff_lt, if_pos (Nat.lt_of_not_ge ho)]
            rfl
          exact hop.trans (bindM_err hw)

/-! ### `mutate_constant` -/

theorem mutateFactor_ok (pw : Rat → Rat → Rat) (pert temperature pneg : Rat) (s : St T) :
    mutateFactor (T := T) pw pert temperature pneg s =
      .ok (factorAt pw pert temperature pneg s.rng s.rng.cursor,
        { s with rng := adv (adv (adv s.rng)) }) := rfl

theorem mutate_constant_spec_holds : mutate_constant_spec := by
  intro T g D fuel tree t rng mul pw pert temperature pneg hu hna hdeg
  have hany := anyM_kind (⟨g, rng⟩ : St T) D fuel tree t
    (fun _ c => c.degree == 0 && c.constant) isConstT (fun _ _ => rfl) lk_const hu hdeg
  cases hq : (preorder t).any isConstT
  · refine ⟨g, rng, ?_, fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩
    simp only [mutateConstant]
    rw [bindM hany, hq]
    rfl
  obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hQu, hf', hun, hrepl, _⟩ :=
    sample_kind ⟨g, rng⟩ fuel tree t _ isConstT lk_const hu hq
  obtain ⟨c, hcx, _, _, hcase⟩ := cell_of_unfold hun
  rcases hcase with ⟨hd, ⟨hk, v, hv, rfl⟩ | ⟨hk, rfl⟩⟩ | ⟨hd, ts, _, rfl⟩
  · let s1 : St T := { g := g, rng := adv rng }
    let fct := factorAt pw pert temperature pneg rng (rng.cursor + 1)
    obtain ⟨g2, hset, hx2, hoth, _⟩ :=
      setValM_ok (s := ({ s1 with rng := adv (adv (adv s1.rng)) } : St T)) (x := x) hcx (mul v fct)
    have hrun : mutateConstant D fuel mul pw pert temperature pneg tree ⟨g, rng⟩ =
        .ok (tree, ⟨g2, adv (adv (adv s1.rng))⟩) := by
      simp only [mutateConstant]
      rw [bindM hany, hq]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [bindM hsamp, bindM (rd_ok (s := s1) hcx)]
      show (liftJ (match c.val with | some v => .ok v | none => .error .undefRefError) >>= _) s1 = _
      rw [hv]
      rw [bindM (rfl : liftJ (T := T) (.ok v) s1 = .ok (v, s1)),
        bindM (show mutateValue' (T := T) mul pw pert temperature pneg v s1 =
          .ok (mul v fct, { s1 with rng := adv (adv (adv s1.rng)) }) from rfl),
        bindM hset]
      rfl
    have hact : ({ c with val := some (mul v fct) } : SCell T).active = [] := by
      simp [SCell.active, hd]
    have hx' := unfold_leaf_cell (f := f') hx2 (by simp [hd]) hact
    simp only [leafOf, hk, ↓reduceIte, Option.map_some] at hx'
    have hres := write_node_spec hu hna hP hrepl hoth (f' + 1) (by omega) hx'
    refine ⟨g2, adv (adv (adv s1.rng)), hrun, fun h => absurd h (by decide), fun _ => ⟨?_, rfl⟩⟩
    rw [modifyAt_eq _ hpu]
    exact hres
  · simp [isConstT] at hQu
  · simp [isConstT] at hQu

/-! ### `mutate_feature` -/

theorem drawAt_mem {rng : RNG} {c : Nat} {xs : List Nat} (h : xs ≠ []) : drawAt rng c xs ∈ xs := by
  have hpos : 0 < xs.length := List.length_pos_iff.mpr h
  have hlt := (rng.indexDraws (xs.length - 1) c).isLt
  have hi : (rng.indexDraws (xs.length - 1) c).val < xs.length := by omega
  simp only [drawAt, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem featureChoices_ne_nil {nf f : Nat} (h : 2 ≤ nf) : featureChoices nf f ≠ [] := by
  intro he
  have h1 : (if f = 1 then 2 else 1) ∈ featureChoices nf f := by
    simp only [featureChoices, List.mem_filter, List.mem_range'_1]
    split <;> simp_all <;> omega
  rw [he] at h1
  simp at h1

private theorem sampleMState_ok {T : Type} {fuel isGraph root F} {s : St T} {a after}
    (h : sampleM fuel isGraph root F s = .ok (a, after)) :
    sampleMState fuel isGraph root F s = (.ok a, after) := by
  unfold sampleM at h
  generalize sampleMState fuel isGraph root F s = result at h ⊢
  rcases result with ⟨r, final⟩
  cases r <;> cases h <;> rfl

theorem mutate_feature_unshared_holds : mutate_feature_unshared := by
  intro T g D fuel nf tree t rng hu hna hdeg hnf
  by_cases h1 : nf ≤ 1
  · refine ⟨g, rng, ?_, fun _ => ⟨rfl, rfl⟩, fun h => by omega⟩
    simp [mutateFeature, h1]
  have hany := anyM_kind (⟨g, rng⟩ : St T) D fuel tree t
    (fun _ c => c.degree == 0 && !c.constant) isFeatureT (fun _ _ => rfl) lk_feature hu hdeg
  cases hq : (preorder t).any isFeatureT
  · refine ⟨g, rng, ?_, fun _ => ⟨rfl, rfl⟩, fun _ h => by cases h⟩
    simp only [mutateFeature, show ((nf : Int).toNat) = nf from rfl, h1, ↓reduceIte]
    rw [hany, hq]
  obtain ⟨x, P, u, f', _, hsamp, hP, hpu, hQu, hf', hun, hrepl, _⟩ :=
    sample_kind ⟨g, rng⟩ fuel tree t _ isFeatureT lk_feature hu hq
  obtain ⟨c, hcx, _, _, hcase⟩ := cell_of_unfold hun
  rcases hcase with ⟨hd, ⟨hk, v, hv, rfl⟩ | ⟨hk, rfl⟩⟩ | ⟨hd, ts, _, rfl⟩
  · simp [isFeatureT] at hQu
  · let s1 : St T := { g := g, rng := adv rng }
    have hne := featureChoices_ne_nil (f := c.feature) (show 2 ≤ nf by omega)
    let fn := drawAt rng (rng.cursor + 1) (featureChoices nf c.feature)
    have hmem : fn ∈ featureChoices nf c.feature := drawAt_mem hne
    simp only [featureChoices, List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hmem
    obtain ⟨⟨hfn1, hfn2⟩, hfne⟩ := hmem
    obtain ⟨g2, hset, hx2, hoth, _⟩ :=
      setFeatureM_ok (s := ({ s1 with rng := adv s1.rng } : St T)) (x := x) (f := fn) hcx
        (by omega)
    have hrun : mutateFeature D fuel nf tree false ⟨g, rng⟩ = (.ok tree, ⟨g2, adv s1.rng⟩) := by
      simp only [mutateFeature, show ((nf : Int).toNat) = nf from rfl, h1, ↓reduceIte]
      rw [hany, hq]
      dsimp only
      rw [sampleMState_ok hsamp]
      dsimp only
      rw [rd_ok (s := s1) hcx]
      dsimp only
      rw [randElem_ok ((List.range' 1 nf).filter (· ≠ c.feature)) hne s1]
      change (match setFeatureM x fn { s1 with rng := adv s1.rng } with
        | .error e => (Except.error e, { s1 with rng := adv s1.rng })
        | .ok (_, out) => (Except.ok tree, out)) = _
      rw [hset]
    have hact : ({ c with feature := fn } : SCell T).active = [] := by simp [SCell.active, hd]
    have hx' := unfold_leaf_cell (f := f') hx2 (by simp [hd]) hact
    simp only [leafOf, hk, Bool.false_eq_true, ↓reduceIte] at hx'
    have hres := write_node_spec hu hna hP hrepl hoth (f' + 1) (by omega) hx'
    refine ⟨g2, adv s1.rng, hrun, fun h => ?_, fun _ _ => ⟨c.feature, hpu, hfne, hfn1,
      (show fn ≤ nf by omega), hres, rfl⟩⟩
    rcases h with h | h
    · omega
    · exact absurd h (by decide)
  · simp [isFeatureT] at hQu

theorem mutate_feature_spec_holds : mutate_feature_spec := by
  refine ⟨mutate_feature_unshared_holds, ?_⟩
  intro T s D fuel tree nf isGraph
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    have h : nf.toNat ≤ 1 := by omega
    simp only [mutateFeature, if_pos h]
  · intro hn hany
    have h : ¬ nf.toNat ≤ 1 := by omega
    simp only [mutateFeature, if_neg h]
    rw [hany]
  · intro x c hn hany hsamp hc
    dsimp only
    have h : ¬ nf.toNat ≤ 1 := by omega
    have hne := featureChoices_ne_nil (f := c.feature) (show 2 ≤ nf.toNat by omega)
    let f := drawAt s.rng (s.rng.cursor + 1) (featureChoices nf.toNat c.feature)
    have hm : f ∈ featureChoices nf.toNat c.feature := drawAt_mem hne
    simp only [featureChoices, List.mem_filter, List.mem_range'_1, decide_eq_true_eq] at hm
    refine ⟨hm.2, hm.1.1, by omega, ?_⟩
    have hr := rd_ok (s := { s with rng := adv s.rng }) hc
    have hd := randElem_ok ((List.range' 1 nf.toNat).filter (· ≠ c.feature)) hne
      ({ s with rng := adv s.rng } : St T)
    by_cases hf : f ≤ 65535
    · rw [if_pos hf]
      obtain ⟨g', hw, hcell, hframe, hnext⟩ :=
        setFeatureM_ok (s := { s with rng := adv (adv s.rng) }) hc hf
      refine ⟨g', ?_, hnext, hcell, hframe⟩
      simp only [mutateFeature, if_neg h]
      rw [hany]
      dsimp only
      rw [sampleMState_ok hsamp]
      dsimp only
      rw [hr]
      dsimp only
      rw [hd]
      change (match setFeatureM x f { s with rng := adv (adv s.rng) } with
        | .error e => (Except.error e, { s with rng := adv (adv s.rng) })
        | .ok (_, out) => (Except.ok tree, out)) = _
      rw [hw]
    · rw [if_neg hf]
      have hw : setFeatureM x f ({ s with rng := adv (adv s.rng) } : St T) =
          .error .inexactError := by
        simp only [setFeatureM, liftG, gt_iff_lt, if_pos (Nat.lt_of_not_ge hf)]
        rfl
      simp only [mutateFeature, if_neg h]
      rw [hany]
      dsimp only
      rw [sampleMState_ok hsamp]
      dsimp only
      rw [hr]
      dsimp only
      rw [hd]
      change (match setFeatureM x f { s with rng := adv (adv s.rng) } with
        | .error e => (Except.error e, { s with rng := adv (adv s.rng) })
        | .ok (_, out) => (Except.ok tree, out)) = _
      rw [hw]

end SymReg.Mutations
