import SymReg.Mutations.Graph

/-! `backsolve_rewrite_random_node` (`src/MutationFunctions.jl:703-754`): statement and proof. -/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-- `backsolve_rewrite_random_node(tree, dataset, options, rng)` on an alias-free plain `Node`
tree of floating-point values whose root is an operator, with `compute_complexity` total and a
fit that only allocates: it returns the same root object, after one draw selecting the node `x`
at preorder index `k ≠ 0`, uniformly over the non-root nodes. With fewer than
`min(10, length(targets))` valid inverted rows, or a complexity budget
`budget = curmaxsize - (complexity(tree) - complexity(x))` below `1`, the heap is unchanged.
Otherwise `fit_sparse_expression` is called once with `max_complexity = budget`; if it returns
`nothing` the heap only gains the fit's objects, and if it returns a node `n` unfolding to `u`
whose objects are new or belong to `x`'s subtree, the root unfolds to the input tree with the
subtree at `k` replaced by `u`. -/
def backsolve_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (ops : BacksolveOps T) (cm : Int)
    (rng : RNG),
    Graph.unfold g.view fuel tree = some t → Graph.NoAlias g.view tree → DegLe D t →
    SlotsLe D 0 g → t.degree ≠ 0 →
    (∀ g1 a, ∃ c, ops.cx g1 a = .ok c) →
    (∀ g1 a ts ms b, ∃ o g2, ops.fit g1 a ts ms b = .ok (o, g2) ∧ Ext g1 g2) →
    ∃ (x : Addr) (P : List Nat) (s' : St T),
      backsolveRewriteRandomNode D fuel ops true cm tree ⟨g, rng⟩ = .ok (tree, s') ∧
      Graph.Path g.view tree P x ∧ P ≠ [] ∧
      drawAt rng rng.cursor (eligIdx t.size (fun k => k != 0)) ≠ 0 ∧
      (∃ u0, (preorder t)[drawAt rng rng.cursor (eligIdx t.size (fun k => k != 0))]? = some u0 ∧
        Graph.unfold g.view (fuel - P.length) x = some u0) ∧
      ((ops.invert g tree x).2.count true < min 10 (ops.invert g tree x).1.length → s'.g = g) ∧
      ∀ ct cn, ops.cx g tree = .ok ct → ops.cx g x = .ok cn →
        min 10 (ops.invert g tree x).1.length ≤ (ops.invert g tree x).2.count true →
        (cm - (ct - cn) < 1 → s'.g = g) ∧
        (1 ≤ cm - (ct - cn) → ∀ o g2,
          ops.fit g x (ops.invert g tree x).1 (ops.invert g tree x).2 (cm - (ct - cn)) = .ok (o, g2) →
          (o = none → s'.g = g2) ∧
          ∀ n (u : Tree T) F, o = some n → Graph.unfold g2.view F n = some u →
            (∀ z : Nat, Graph.Reachable g2.view n z → g.next ≤ z ∨ Graph.Reachable g.view x z) →
            Graph.unfold s'.g.view (fuel + F) tree =
              some (replaceAt t (drawAt rng rng.cursor (eligIdx t.size (fun k => k != 0))) u))

theorem backsolve_spec_holds : backsolve_spec := by
  intro T g D fuel tree t ops cm rng hu hna hdeg hsl htd hcx hfit
  obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
  have hd0 : rc.degree ≠ 0 := by rw [hrdeg]; exact htd
  have hcl := closed_unfold fuel tree t hu
  -- the node to invert
  have hFE : ∀ k x P u, Graph.Path g.view tree P x → (preorder t)[k]? = some u →
      Graph.unfold g.view (fuel - P.length) x = some u → (P = [] ↔ k = 0) →
      decide (x ≠ tree) = (k != 0) := by
    intro k x P u hP _ _ hPk
    by_cases hk : k = 0
    · have hP0 := hPk.mpr hk
      subst hP0
      have hx := path_nil_inv hP
      subst hx
      simp [hk]
    · have hPne : P ≠ [] := fun h => hk (hPk.mp h)
      have hxt : x ≠ tree := fun he => by
        subst he; exact hPne (hna.acyclic x (reach_refl _ _) P hP)
      simp [hk, hxt]
  have hsz : 2 ≤ t.size := by
    cases t with
    | const v => simp [Tree.degree] at htd
    | feature i => simp [Tree.degree] at htd
    | branch o cs =>
      cases cs with
      | nil => simp [Tree.degree] at htd
      | cons c cs => have := Tree.size_pos c; simp [Tree.size_branch]; omega
  have hne : eligIdx t.size (fun k => k != 0) ≠ [] := eligIdx_ne_nil (k := 1) (by omega) rfl
  obtain ⟨k, x, P, u0, hk, hsamp, hP, hpu, hun, hrepl, hPk, _⟩ :=
    sample_spec ⟨g, rng⟩ fuel tree t (fun _ a => decide (a ≠ tree)) (fun k => k != 0) hu hFE hne
  have hkd : drawAt rng rng.cursor (eligIdx t.size fun k => k != 0) = k := by
    simp only [drawAt]; rw [hk]; rfl
  have hk0 : k ≠ 0 := by
    have := (mem_eligIdx.mp (List.mem_of_getElem? hk)).2
    simpa using this
  have hPne : P ≠ [] := fun h => hk0 (hPk.mp h)
  rw [hkd]
  -- the inversion and the complexities
  obtain ⟨ct, hct⟩ := hcx g tree
  obtain ⟨cn, hcn⟩ := hcx g x
  obtain ⟨tg, mk, hiv⟩ : ∃ tg mk, ops.invert g tree x = (tg, mk) := ⟨_, _, rfl⟩
  have hinv : onG (fun g => pure (ops.invert g tree x)) (⟨g, adv rng⟩ : St T) =
      .ok ((tg, mk), ⟨g, adv rng⟩) := by simp [onG, hiv]; rfl
  have hcxt : onG (fun g => ops.cx g tree) (⟨g, adv rng⟩ : St T) = .ok (ct, ⟨g, adv rng⟩) := by
    simp [onG, hct, Except.map]
  have hcxn : onG (fun g => ops.cx g x) (⟨g, adv rng⟩ : St T) = .ok (cn, ⟨g, adv rng⟩) := by
    simp [onG, hcn, Except.map]
  by_cases hen : mk.count true < min 10 tg.length
  · refine ⟨x, P, ⟨g, adv rng⟩, ?_, hP, hPne, hk0, ⟨u0, hpu, hun⟩, fun _ => rfl,
      fun _ _ _ _ h => by rw [hiv] at h; simp only at h; exfalso; omega⟩
    simp only [backsolveRewriteRandomNode, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bindM (rd_ok (s := ⟨g, rng⟩) hrc)]
    simp only [hd0, ↓reduceIte]
    rw [bindM hsamp, bindM hinv]
    simp only [hen, ↓reduceIte]
    rfl
  have hen' : min 10 tg.length ≤ mk.count true := by omega
  by_cases hb : cm - (ct - cn) < 1
  · refine ⟨x, P, ⟨g, adv rng⟩, ?_, hP, hPne, hk0, ⟨u0, hpu, hun⟩, fun h => absurd (by rw [hiv] at h; exact h) hen,
      fun ct' cn' hct' hcn' _ => ?_⟩
    · simp only [backsolveRewriteRandomNode, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [bindM (rd_ok (s := ⟨g, rng⟩) hrc)]
      simp only [hd0, ↓reduceIte]
      rw [bindM hsamp, bindM hinv]
      simp only [hen, ↓reduceIte]
      rw [bindM hcxt, bindM hcxn]
      simp only [hb, ↓reduceIte]
      rfl
    · rw [hct] at hct'; cases hct'
      rw [hcn] at hcn'; cases hcn'
      exact ⟨fun _ => rfl, fun h => absurd h (by omega)⟩
  -- the fit
  obtain ⟨o, g2, hft, hext2⟩ := hfit g x tg mk (cm - (ct - cn))
  have hfitM : liftG (fun g => ops.fit g x tg mk (cm - (ct - cn))) (⟨g, adv rng⟩ : St T) =
      .ok (o, ⟨g2, adv rng⟩) := by simp [liftG, hft, Except.map]
  have hcx' : ∀ ct' cn', ops.cx g tree = .ok ct' → ops.cx g x = .ok cn' → ct' = ct ∧ cn' = cn := by
    intro ct' cn' h1 h2
    rw [hct] at h1; rw [hcn] at h2
    cases h1; cases h2
    exact ⟨rfl, rfl⟩
  cases o with
  | none =>
    refine ⟨x, P, ⟨g2, adv rng⟩, ?_, hP, hPne, hk0, ⟨u0, hpu, hun⟩, fun h => absurd (by rw [hiv] at h; exact h) hen,
      fun ct' cn' hct' hcn' _ => ?_⟩
    · simp only [backsolveRewriteRandomNode, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [bindM (rd_ok (s := ⟨g, rng⟩) hrc)]
      simp only [hd0, ↓reduceIte]
      rw [bindM hsamp, bindM hinv]
      simp only [hen, ↓reduceIte]
      rw [bindM hcxt, bindM hcxn]
      simp only [hb, ↓reduceIte]
      rw [bindM hfitM]
      rfl
    · obtain ⟨rfl, rfl⟩ := hcx' ct' cn' hct' hcn'
      refine ⟨fun h => absurd h hb, fun _ o' g2' hft' => ?_⟩
      rw [hiv] at hft'
      rw [hft] at hft'; cases hft'
      exact ⟨fun _ => rfl, fun _ _ _ h => by cases h⟩
  | some n =>
    -- the parent of `x` and the rewritten slot
    obtain ⟨Q, i, rfl⟩ := exists_snoc P hPne
    obtain ⟨q, cq', hQ, hcq', hi⟩ := path_snoc_inv Q hP
    obtain ⟨cq, hcq, rfl⟩ : ∃ cq, g.cells q = some cq ∧ cq' = cq.toCell := by
      cases hc : g.cells q with
      | none => simp [SGraph.view, hc] at hcq'
      | some cq => simp [SGraph.view, hc] at hcq'; exact ⟨cq, rfl, hcq'.symm⟩
    have hi' : cq.active[i]? = some x := by simpa [SCell.toCell] using hi
    have hqlt : @LT.lt Nat _ q g.next := closed_lt hcl ⟨Q, hQ⟩
    have hcq2 : g2.cells q = some cq := by rw [hext2.2 q hqlt, hcq]
    obtain ⟨hu2e, hna2, _, _⟩ := ext_tree hext2 hcl
    have hu2 : Graph.unfold g2.view fuel tree = some t := by rw [hu2e]; exact hu
    have hna2' := hna2 hna
    have hQ2 : Graph.Path g2.view tree Q q := path_transfer (sameKidsOn_ext hext2 hcl) hQ
    have hfp := findParent_spec g2 D fuel tree x q t Q i cq hu2 hdeg hna2' hQ2 hcq2 hi'
    obtain ⟨cq0, hcq0, hlq, hDq⟩ := good_reach g2 D fuel tree t hu2 hdeg q ⟨Q, hQ2⟩
    rw [hcq2] at hcq0; cases hcq0
    have hiq : i < cq.degree := by
      have := (List.getElem?_eq_some_iff.mp hi').1; omega
    obtain ⟨g', c', hset, hoth, _, hq', hact', hdeg', hop', hcst', hval', hfeat', _⟩ :=
      setChildM_ok (s := ⟨g2, adv rng⟩) (x := n) hcq2 hlq hDq hiq
        (fun sl h => hsl q cq sl (Nat.zero_le _) hcq h)
    have hfpM : onG (T := T) (fun g => Crossover.findParent g D fuel tree x) ⟨g2, adv rng⟩ =
        .ok ((q, i + 1), ⟨g2, adv rng⟩) := by simp [onG, hfp, Except.map]
    refine ⟨x, Q ++ [i], ⟨g', adv rng⟩, ?_, hP, hPne, hk0, ⟨u0, hpu, hun⟩, fun h => absurd (by rw [hiv] at h; exact h) hen,
      fun ct' cn' hct' hcn' _ => ?_⟩
    · simp only [backsolveRewriteRandomNode, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [bindM (rd_ok (s := ⟨g, rng⟩) hrc)]
      simp only [hd0, ↓reduceIte]
      rw [bindM hsamp, bindM hinv]
      simp only [hen, ↓reduceIte]
      rw [bindM hcxt, bindM hcxn]
      simp only [hb, ↓reduceIte]
      rw [bindM hfitM]
      simp only
      rw [bindM hfpM]
      simp only
      rw [bindM hset]
      rfl
    · obtain ⟨rfl, rfl⟩ := hcx' ct' cn' hct' hcn'
      refine ⟨fun h => absurd h hb, fun _ o' g2' hft' => ?_⟩
      rw [hiv] at hft'
      rw [hft] at hft'; cases hft'
      refine ⟨(fun h => by cases h), fun n' u F hn hnu hfr => ?_⟩
      cases hn
      have hvq' : g'.view.cells q =
          some { cq.toCell with children := cq.toCell.children.set i n } :=
        view_setChild hq' hact' hdeg' hop' hcst' hval' hfeat'
      have hnr : ¬ Graph.Reachable g2.view n q := by
        intro hr
        rcases hfr q hr with h | ⟨R, hR⟩
        · omega
        · have hqq : Graph.Path g.view q (i :: R) q :=
            .cons (view_cells hcq) (by simpa [SCell.toCell] using hi') hR
          have := hna.acyclic q ⟨Q, hQ⟩ _ hqq
          simp at this
      have hnu' : Graph.unfold g'.view F n = some u := by
        rw [unfold_agree F n (fun z hz => view_oth hoth z (fun hzq => hnr (hzq ▸ hz)))]
        exact hnu
      exact repl_heap g2.view g'.view q n i cq.toCell u F (view_cells hcq2)
        (by simp [SCell.toCell]; omega) hvq' (view_oth hoth) hnu' fuel tree t hu2 hna2' Q
        (replaceAt t k u) hQ2 (hrepl u)

end SymReg.Mutations
