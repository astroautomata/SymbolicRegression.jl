import SymReg.Mutations.Lemmas

/-!
Lemmas shared by the mutation proofs: steps of the `M` monad, filtered sampling, rewriting
one subtree of an alias-free heap tree, `any` with a pure predicate, and `replaceAt` on trees.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### The `M` monad -/

theorem bindM {α β : Type} {x : M T α} {f : α → M T β} {s : St T} {a : α} {s' : St T}
    (h : x s = .ok (a, s')) : (x >>= f) s = f a s' := by
  show (x s >>= fun p => f p.1 p.2) = _
  rw [h]; rfl

theorem bindM_err {α β : Type} {x : M T α} {f : α → M T β} {s : St T} {e : JlError}
    (h : x s = .error e) : (x >>= f) s = .error e := by
  show (x s >>= fun p => f p.1 p.2) = _
  rw [h]; rfl

theorem pureM {α : Type} (a : α) (s : St T) : (pure a : M T α) s = .ok (a, s) := rfl

theorem randElem_ok (xs : List Nat) (h : xs ≠ []) (s : St T) :
    randElem (T := T) xs s =
      .ok ((xs[(s.rng.indexDraws (xs.length - 1) s.rng.cursor).val]?).getD 0,
        { s with rng := adv s.rng }) := by
  simp [randElem, h]

/-- `rand(rng, 1:n)` for `n ≥ 1`. -/
theorem randRange_ok (n : Nat) (hn : 1 ≤ n) (s : St T) :
    randRange (T := T) n s =
      .ok ((s.rng.indexDraws (n - 1) s.rng.cursor).val + 1, { s with rng := adv s.rng }) := by
  simp [randRange, show n ≠ 0 by omega]

theorem randBool_ok (s : St T) :
    randBool (T := T) s = .ok ((s.rng.indexDraws 1 s.rng.cursor).val = 1, { s with rng := adv s.rng }) :=
  rfl

theorem randU_ok (s : St T) :
    randU (T := T) s = .ok (s.rng.draws s.rng.cursor, { s with rng := adv s.rng }) := rfl

theorem rd_ok {s : St T} {a : Addr} {c : SCell T} (h : s.g.cells a = some c) :
    rd a s = .ok (c, s) := by
  simp [rd, onG, Heap.read, h, Except.map]

/-! ### Lists -/

/-- Filtering a list by a predicate that agrees with an index predicate keeps exactly the
elements at the selected indices. -/
theorem filter_map_idx {α : Type} (F : α → Bool) (d : α) :
    ∀ (xs : List α) (E : Nat → Bool), (∀ k x, xs[k]? = some x → F x = E k) →
      xs.filter F = ((List.range xs.length).filter E).map (fun k => (xs[k]?).getD d) := by
  intro xs
  induction xs with
  | nil => intro E _; rfl
  | cons x xs ih =>
    intro E hE
    have h0 : F x = E 0 := hE 0 x rfl
    have hr := ih (fun k => E (k + 1)) (fun k y hy => hE (k + 1) y (by simpa using hy))
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons, h0,
      List.filter_map, hr]
    have hc : (E ∘ Nat.succ) = (fun k => E (k + 1)) := rfl
    rw [hc]
    cases E 0 <;> simp [List.map_map, Function.comp_def]

/-- Indices `k < n` selected by `E`, in increasing order. -/
def eligIdx (n : Nat) (E : Nat → Bool) : List Nat := (List.range n).filter E

theorem mem_eligIdx {n : Nat} {E : Nat → Bool} {k : Nat} :
    k ∈ eligIdx n E ↔ k < n ∧ E k = true := by
  simp [eligIdx]

theorem eligIdx_ne_nil {n : Nat} {E : Nat → Bool} {k : Nat} (hk : k < n) (he : E k = true) :
    eligIdx n E ≠ [] := by
  intro h
  have : k ∈ eligIdx n E := mem_eligIdx.mpr ⟨hk, he⟩
  rw [h] at this
  simp at this

/-! ### Cells of unfolded objects -/

theorem cell_of_unfold {g : SGraph T} {f : Nat} {x : Addr} {s : Tree T}
    (h : Graph.unfold g.view f x = some s) :
    ∃ c, g.cells x = some c ∧ c.active.length = c.degree ∧ c.degree = s.degree ∧
      ((c.degree = 0 ∧ ((c.constant = true ∧ ∃ v, c.val = some v ∧ s = .const v) ∨
          (c.constant = false ∧ s = .feature c.feature))) ∨
       (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view (f - 1)) = some ts ∧
          s = .branch c.op ts)) := by
  cases f with
  | zero => simp [Graph.unfold] at h
  | succ f =>
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succ h
    refine ⟨c, hc, hl, ?_, ?_⟩
    · rcases hcase with ⟨hd, hk, hf⟩ | ⟨hd, ts, hts, rfl⟩
      · cases hcst : c.constant
        · rw [hf hcst]; simp [Tree.degree, hd]
        · obtain ⟨v, _, rfl⟩ := hk hcst; simp [Tree.degree, hd]
      · simp [Tree.degree, mapM_length _ _ _ hts, hl]
    · rcases hcase with ⟨hd, hk, hf⟩ | ⟨hd, ts, hts, rfl⟩
      · left
        refine ⟨hd, ?_⟩
        cases hcst : c.constant
        · exact Or.inr ⟨rfl, hf hcst⟩
        · exact Or.inl ⟨rfl, hk hcst⟩
      · exact Or.inr ⟨hd, ts, by simpa using hts, rfl⟩

/-- A cell predicate that reads only `degree` and `constant` agrees with the matching tree
predicate on every unfolded object. -/
def LeafKind (P : SCell T → Bool) (Q : Tree T → Bool) : Prop :=
  ∀ (c : SCell T) (s : Tree T), c.degree = s.degree →
    (c.degree = 0 → ((c.constant = true ∧ ∃ v, s = .const v) ∨
      (c.constant = false ∧ ∃ i, s = .feature i))) → P c = Q s

theorem cellP_of_unfold {P : SCell T → Bool} {Q : Tree T → Bool} (hPQ : LeafKind P Q)
    {g : SGraph T} {f : Nat} {x : Addr} {s : Tree T} (h : Graph.unfold g.view f x = some s) :
    cellP P g x = Q s := by
  obtain ⟨c, hc, _, hd, hcase⟩ := cell_of_unfold h
  simp only [cellP, hc]
  apply hPQ c s hd
  intro h0
  rcases hcase with ⟨_, ⟨hk, v, _, rfl⟩ | ⟨hk, rfl⟩⟩ | ⟨hd', _⟩
  · exact Or.inl ⟨hk, v, rfl⟩
  · exact Or.inr ⟨hk, _, rfl⟩
  · exact absurd h0 hd'

/-! ### Filtered sampling -/

theorem occurrences_view (g : SGraph T) (fuel a : Nat) (t : Tree T)
    (hu : Graph.unfold g.view fuel a = some t) :
    ∃ xs, Expressions.Sampling.occurrences g.view fuel a = .ok xs ∧ OccSpec g.view fuel a t xs :=
  occ_spec g.view fuel a t hu

/-- `rand(rng, NodeSampler(; tree, filter))` on an alias-free plain `Node` tree: with `E k`
the filter's value at the `k`-th node in preorder, the sample is the node at preorder index
`(eligIdx t.size E)[j]`, `j` the index draw. -/
theorem sample_spec (s : St T) (fuel a : Nat) (t : Tree T) (F : SGraph T → Addr → Bool)
    (E : Nat → Bool) (hu : Graph.unfold s.g.view fuel a = some t)
    (hFE : ∀ k x P u, Graph.Path s.g.view a P x → (preorder t)[k]? = some u →
      Graph.unfold s.g.view (fuel - P.length) x = some u → (P = [] ↔ k = 0) → F s.g x = E k)
    (hne : eligIdx t.size E ≠ []) :
    ∃ k x P u, (eligIdx t.size E)[(s.rng.indexDraws ((eligIdx t.size E).length - 1)
        s.rng.cursor).val]? = some k ∧
      sampleM fuel false a F s = .ok (x, { s with rng := adv s.rng }) ∧
      Graph.Path s.g.view a P x ∧ (preorder t)[k]? = some u ∧
      Graph.unfold s.g.view (fuel - P.length) x = some u ∧
      (∀ u', ReplPath t P u' (replaceAt t k u')) ∧ (P = [] ↔ k = 0) ∧
      (∃ xs, Expressions.Sampling.occurrences s.g.view fuel a = .ok xs ∧ xs[k]? = some x) := by
  obtain ⟨xs, hocc, hlen, hspec⟩ := occurrences_view s.g fuel a t hu
  have hsize : xs.length = t.size := by rw [hlen, preorder_length]
  have hfilt : xs.filter (F s.g) = (eligIdx t.size E).map (fun k => (xs[k]?).getD 0) := by
    rw [← hsize]
    apply filter_map_idx
    intro k x hx
    obtain ⟨P, u, hP, hpu, hun, _, hPk⟩ := hspec k x hx
    exact hFE k x P u hP hpu hun hPk
  have hpos : 0 < (eligIdx t.size E).length := List.length_pos_iff.mpr hne
  have hmemL : ∀ k, k ∈ eligIdx t.size E → k < t.size := fun k hk => (mem_eligIdx.mp hk).1
  generalize hL : eligIdx t.size E = L at hfilt hpos hmemL ⊢
  have hjl0 := (s.rng.indexDraws (L.length - 1) s.rng.cursor).isLt
  generalize hj : (s.rng.indexDraws (L.length - 1) s.rng.cursor).val = j at hjl0 ⊢
  have hjl : j < L.length := by omega
  obtain ⟨k, hk⟩ : ∃ k, L[j]? = some k := ⟨L[j], List.getElem?_eq_getElem hjl⟩
  have hkt : k < t.size := hmemL k (List.mem_of_getElem? hk)
  have hkl : k < xs.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, xs[k]? = some x := ⟨xs[k], List.getElem?_eq_getElem hkl⟩
  obtain ⟨P, u, hP, hpu, hun, hrepl, hPk⟩ := hspec k x hx
  refine ⟨k, x, P, u, hk, ?_, hP, hpu, hun, hrepl, hPk, ⟨xs, hocc, hx⟩⟩
  have hm : Expressions.Sampling.matching
      ({ graph := s.g.view, root := a, fuel := fuel, filter := F s.g,
         preserveSharing := false } : Expressions.Sampling.NodeSampler T) =
      .ok (L.map (fun k => (xs[k]?).getD 0)) := by
    rw [← hfilt]
    simp [Expressions.Sampling.matching, Expressions.Sampling.traversal, hocc]
    rfl
  have hjx : (L.map (fun k => (xs[k]?).getD 0))[j]? = some x := by
    rw [List.getElem?_map, hk]; simp [hx]
  cases hLm : L.map (fun k => (xs[k]?).getD 0) with
  | nil => rw [hLm] at hjx; simp at hjx
  | cons y ys =>
    have hyl : ys.length = L.length - 1 := by
      have := congrArg List.length hLm; simp at this; omega
    rw [hLm] at hm hjx
    simp only [sampleM, sampleMState, Expressions.Sampling.rand, hm]
    rw [hyl, hj]
    simp [Expressions.Sampling.getNode, hjx, Except.map]
    rfl

/-! ### Rewriting one subtree -/

/-- If a new heap agrees with the old one outside the subtree of `n`, and `n` unfolds to `u`
in the new heap, the root unfolds to the old tree with `n`'s subtree replaced by `u`. -/
theorem rewrite_sub (G G' : Graph T) (n : Addr) (u : Tree T) (F : Nat)
    (hn : Graph.unfold G' F n = some u) :
    ∀ f a t, Graph.unfold G f a = some t → Graph.NoAlias G a →
      (∀ b, Graph.Reachable G a b → ¬ Graph.Reachable G n b → G'.cells b = G.cells b) →
      ∀ P t', Graph.Path G a P n → ReplPath t P u t' → Graph.unfold G' (f + F) a = some t' := by
  intro f
  induction f with
  | zero => intro a t hu; simp [Graph.unfold] at hu
  | succ f ih =>
    intro a t hu hna hfr P t' hP hR
    cases P with
    | nil =>
      have hap := path_nil_inv hP
      subst hap
      have := replPath_nil_inv hR
      subst this
      exact unfold_mono _ _ _ hn _ (by omega)
    | cons i P' =>
      obtain ⟨c, hc, hl, hcase⟩ := unfold_succG hu
      obtain ⟨c0, b, hc0, hb, hP'⟩ := path_cons_inv hP
      rw [hc] at hc0; cases hc0
      have hnra : ¬ Graph.Reachable G n a := by
        intro ⟨Q, hQ⟩
        have hcyc := hna.acyclic a (reach_refl _ _) _ (hP.append hQ)
        simp at hcyc
      have hca : G'.cells a = some c := by rw [hfr a (reach_refl _ _) hnra, hc]
      obtain ⟨o, cs, ci, ci', rfl, hci, hRi, rfl⟩ := replPath_cons_inv hR
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, heq⟩
      · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hb; simp at hb
      · cases heq
        rw [show f + 1 + F = (f + F) + 1 by omega]
        refine unfold_of_cell hca hl (Or.inr ⟨hd, cs.set i ci', ?_, rfl⟩)
        apply mapM_of_get _ _ _ (by simp [mapM_length _ _ _ hts])
        intro m y v hy hv
        by_cases hmi : i = m
        · subst hmi
          rw [hb] at hy; cases hy
          obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts i b hb
          rw [hci] at hv'; cases hv'
          have hic : i < cs.length := (List.getElem?_eq_some_iff.mp hci).1
          simp [hic] at hv
          subst hv
          exact ih b ci hyv (noAlias_child hna hc (List.mem_of_getElem? hb))
            (fun z hz hnz => hfr z (reach_trans (reach_child hc hb) hz) hnz) P' _ hP' hRi
        · simp [hmi] at hv
          obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts m y hy
          rw [hv] at hv'; cases hv'
          have hag : ∀ z, Graph.Reachable G y z → G'.cells z = G.cells z := by
            intro z hz
            apply hfr z (reach_trans (reach_child hc hy) hz)
            intro ⟨Q, hQ⟩
            obtain ⟨Q', hQ'⟩ := hz
            have := hna (m :: Q') ((i :: P') ++ Q) z (.cons hc hy hQ')
              ((Graph.Path.cons hc hb hP').append hQ)
            simp at this
            exact hmi this.1.symm
          rw [unfold_agree (f + F) y hag]
          exact unfold_mono _ _ _ hyv _ (by omega)

/-! ### `any` with a pure predicate -/

theorem preorderF_any (Q : Tree T → Bool) :
    ∀ ts : List (Tree T), (preorder.preorderF ts).any Q = ts.any (fun c => (preorder c).any Q) := by
  intro ts
  induction ts with
  | nil => rfl
  | cons c cs ih => rw [preorderF_cons, List.any_append, ih, List.any_cons]

theorem preorder_any_branch (Q : Tree T → Bool) (o : Nat) (ts : List (Tree T)) :
    (preorder (.branch o ts)).any Q = (Q (.branch o ts) || ts.any (fun c => (preorder c).any Q)) := by
  rw [preorder_branch, List.any_cons, preorderF_any]

theorem anyH_pred (h : SGraph T) (D : Nat) (f : Addr → SCell T → Bool) (Q : Tree T → Bool) :
    ∀ fu a t, Graph.unfold h.view fu a = some t → DegLe D t →
      (∀ x c s fx, Graph.Reachable h.view a x → h.cells x = some c →
        Graph.unfold h.view fx x = some s → f x c = Q s) →
      (anyH (σ := Unit) h D (fun x c => pure (f x c)) fu a).run () = .ok ((preorder t).any Q, ()) := by
  intro fu
  induction fu with
  | zero => intro a t hu; simp [Graph.unfold] at hu
  | succ fu ih =>
    intro a t hu hdeg hf
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succ hu
    have hfa := hf a c t (fu + 1) (reach_refl _ _) hc hu
    have hv : h.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    rcases hcase with ⟨hd, hk, hft⟩ | ⟨hd, ts, hts, rfl⟩
    · have hpre : preorder t = [t] := by
        cases hcst : c.constant
        · rw [hft hcst]; rfl
        · obtain ⟨v, _, rfl⟩ := hk hcst; rfl
      rw [anyH_leaf h D _ fu a c hc hd (), hpre]
      simp [hfa]
      rfl
    · simp only [DegLe] at hdeg
      have htl := mapM_length _ _ _ hts
      have hlenD : c.degree ≤ D := by omega
      have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlenD]
      have hcs : getChildren h D a (nifDeg D c.degree) = .ok c.active := by
        rw [hnif]; exact getChildren_active hc hl hlenD
      rw [preorder_any_branch]
      cases hq : Q (.branch c.op ts)
      · have hF : ((fun x c => (pure (f x c) : StateT Unit Jl Bool)) a c).run () = .ok (false, ()) := by
          simp [hfa, hq]; rfl
        rw [anyH_branch_false h D _ fu a c c.active hc hd hF hcs]
        simp only [Bool.false_or]
        -- the children
        have hkids : ∀ (xs : List Addr) (us : List (Tree T)), xs.mapM (Graph.unfold h.view fu) = some us →
            (∀ x ∈ xs, Graph.Reachable h.view a x) → (∀ u ∈ us, DegLe D u) →
            (xs.anyM (fun x => anyH (σ := Unit) h D (fun x c => pure (f x c)) fu x)).run () =
              .ok (us.any (fun c => (preorder c).any Q), ()) := by
          intro xs
          induction xs with
          | nil => intro us hm _ _; simp at hm; subst hm; rfl
          | cons x xs ihx =>
            intro us hm hr hus
            obtain ⟨u, us', hu', hus', rfl⟩ := (mapM_cons _ x xs us).mp hm
            have hx := ih x u hu' (hus u List.mem_cons_self)
              (fun y cy sy fy hy hcy huy => hf y cy sy fy (reach_trans (hr x List.mem_cons_self) hy) hcy huy)
            simp only [List.anyM, StateT.run_bind] at *
            rw [hx]
            cases hpu : (preorder u).any Q
            · simp only [ok_bind, List.any_cons, hpu, Bool.false_or]
              exact ihx us' hus' (fun y hy => hr y (List.mem_cons_of_mem _ hy))
                (fun v hv => hus v (List.mem_cons_of_mem _ hv))
            · simp [ok_bind, List.any_cons, hpu]
              rfl
        exact hkids c.active ts hts (fun x hx => reach_mem hv hx) hdeg.2
      · have hF : ((fun x c => (pure (f x c) : StateT Unit Jl Bool)) a c).run () = .ok (true, ()) := by
          simp [hfa, hq]; rfl
        rw [anyH_branch_true h D _ fu a c hc hd hF]
        simp

/-! ### Trees -/

/-- Replace the subtree at preorder index `k` by `f` of it. -/
def modifyAt (t : Tree T) (k : Nat) (f : Tree T → Tree T) : Tree T :=
  match (preorder t)[k]? with
  | some s => replaceAt t k (f s)
  | none => t

theorem modifyAt_eq {t s : Tree T} {k : Nat} (f : Tree T → Tree T) (h : (preorder t)[k]? = some s) :
    modifyAt t k f = replaceAt t k (f s) := by
  simp [modifyAt, h]

/-- `replaceAt` changes the node count by the difference of the two subtrees. -/
theorem replaceAt_size :
    ∀ (t : Tree T) (k : Nat) (s u : Tree T), (preorder t)[k]? = some s →
      (replaceAt t k u).size + s.size = t.size + u.size := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro k s u h
    cases k with
    | zero => simp [preorder] at h; subst h; rw [replaceAt_zero]; omega
    | succ k => simp [preorder] at h
  | hf i =>
    intro k s u h
    cases k with
    | zero => simp [preorder] at h; subst h; rw [replaceAt_zero]; omega
    | succ k => simp [preorder] at h
  | hb o cs ih =>
    intro k s u h
    cases k with
    | zero => simp [preorder_branch] at h; subst h; rw [replaceAt_zero]; omega
    | succ k =>
      rw [preorder_branch, List.getElem?_cons_succ] at h
      rw [replaceAt_succ, Tree.size_branch, Tree.size_branch]
      suffices hF : ∀ (ds : List (Tree T)), (∀ d ∈ ds, d ∈ cs) → ∀ k,
          (preorder.preorderF ds)[k]? = some s →
          ((replaceF ds k u).map Tree.size).sum + s.size = (ds.map Tree.size).sum + u.size by
        have := hF cs (fun d hd => hd) k h
        omega
      intro ds
      induction ds with
      | nil => intro _ k h; simp [preorder.preorderF] at h
      | cons d ds ihd =>
        intro hsub k h
        rw [preorderF_cons] at h
        rw [replaceF_cons]
        by_cases hk : k < (preorder d).length
        · rw [if_pos hk]
          rw [List.getElem?_append_left hk] at h
          have := ih d (hsub d List.mem_cons_self) k s u h
          simp only [List.map_cons, List.sum_cons]
          omega
        · rw [if_neg hk]
          rw [List.getElem?_append_right (by omega)] at h
          have := ihd (fun e he => hsub e (List.mem_cons_of_mem _ he)) _ h
          simp only [List.map_cons, List.sum_cons]
          omega

/-- `replaceAt` keeps a hereditary property of nodes when the new subtree has it. -/
theorem replaceAt_wf {D : Nat} {nops : Nat → Nat} {nf : Nat} :
    ∀ (t : Tree T) (k : Nat) (u : Tree T), t.WF D nops nf → u.WF D nops nf →
      (replaceAt t k u).WF D nops nf := by
  intro t
  induction t using Tree.induction with
  | hc v => intro k u _ hu; cases k <;> simp [replaceAt, *]
  | hf i => intro k u ht hu; cases k <;> simp [replaceAt, *]
  | hb o cs ih =>
    intro k u ht hu
    cases k with
    | zero => rw [replaceAt_zero]; exact hu
    | succ k =>
      rw [replaceAt_succ]
      simp only [Tree.WF] at ht ⊢
      suffices hF : ∀ (ds : List (Tree T)), (∀ d ∈ ds, d ∈ cs) → ∀ k,
          (replaceF ds k u).length = ds.length ∧
          ((∀ d ∈ ds, d.WF D nops nf) → ∀ d ∈ replaceF ds k u, d.WF D nops nf) by
        obtain ⟨hl, hw⟩ := hF cs (fun d hd => hd) k
        rw [hl]
        exact ⟨ht.1, ht.2.1, hw ht.2.2⟩
      intro ds
      induction ds with
      | nil => intro _ k; simp [replaceF]
      | cons d ds ihd =>
        intro hsub k
        rw [replaceF_cons]
        obtain ⟨hl, hw⟩ := ihd (fun e he => hsub e (List.mem_cons_of_mem _ he)) (k - (preorder d).length)
        split
        · refine ⟨by simp, ?_⟩
          intro hall e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ih d (hsub d List.mem_cons_self) k u (hall d List.mem_cons_self) hu
          · exact hall e (List.mem_cons_of_mem _ he)
        · refine ⟨by simp [hl], ?_⟩
          intro hall e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hall _ List.mem_cons_self
          · exact hw (fun x hx => hall x (List.mem_cons_of_mem _ hx)) e he

/-! ### Paths bounded by the unfolding fuel -/

/-- Every child path below a successfully unfolded object is shorter than the fuel. -/
theorem path_lt_fuel {G : Graph T} :
    ∀ f a t, Graph.unfold G f a = some t → ∀ P z, Graph.Path G a P z → P.length < f := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t hu P z hP
    cases P with
    | nil => simp
    | cons i P' =>
      obtain ⟨c, hc, hl, hcase⟩ := unfold_succG hu
      obtain ⟨c0, b, hc0, hb, hP'⟩ := path_cons_inv hP
      rw [hc] at hc0; cases hc0
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, _⟩
      · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hb; simp at hb
      · obtain ⟨y, _, hy⟩ := mapM_get _ _ _ hts i b hb
        have := ih b y hy P' z hP'
        simp only [List.length_cons]
        omega

/-- A successfully unfolded object has no reachable child cycle. -/
theorem acyclic_of_unfold {G : Graph T} {f a} {t : Tree T} (h : Graph.unfold G f a = some t) :
    Graph.Acyclic G a := by
  intro x ⟨p, hp⟩ q hq
  cases q with
  | nil => rfl
  | cons i q =>
    exfalso
    have pump : ∀ n, ∃ r : List Nat, n ≤ r.length ∧ Graph.Path G a r x := by
      intro n
      induction n with
      | zero => exact ⟨p, Nat.zero_le _, hp⟩
      | succ n ih =>
        obtain ⟨r, hr, hpr⟩ := ih
        refine ⟨r ++ i :: q, ?_, hpr.append hq⟩
        simp only [List.length_append, List.length_cons]
        omega
    obtain ⟨r, hr, hpr⟩ := pump f
    have := path_lt_fuel f a t h r x hpr
    omega

end SymReg.Mutations
