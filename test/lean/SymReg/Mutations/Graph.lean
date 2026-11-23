import SymReg.Mutations.Gen
import DynExpr.NodeBase.IterateLength

/-!
`get_two_nodes_without_loop`, `form_random_connection!` and `break_random_connection!`
(`src/MutationFunctions.jl:543-586`), for plain `Node` and `GraphNode` trees: statements and
proofs.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ## Statements -/

/-- `get_two_nodes_without_loop(tree, rng; max_attempts)` on a finite well-formed tree whose root
is an operator, for `Node` (`isGraph = false`) and `GraphNode` (`isGraph = true`): it succeeds
without changing the heap and either gives up with `(tree, tree, true)` or returns
`(parent, new_child, false)` where `parent` is a reachable operator node, `new_child` a
reachable node other than the root, and `parent` is not reachable from `new_child`. -/
private def sampledPair (g : SGraph T) (fuel : Nat) (isGraph : Bool) (tree : Addr)
    (rng : RNG) (i : Nat) (p c : Addr) : Prop :=
  let start : RNG := { rng with cursor := rng.cursor + 2 * i }
  sampleM fuel isGraph tree (cellP (fun a => a.degree != 0)) ⟨g, start⟩ =
    .ok (p, ⟨g, adv start⟩) ∧
  sampleM fuel isGraph tree (fun _ a => decide (a ≠ tree)) ⟨g, adv start⟩ =
    .ok (c, ⟨g, adv (adv start)⟩)

private def firstSafePair (g : SGraph T) (fuel : Nat) (isGraph : Bool) (tree : Addr)
    (rng : RNG) (n : Nat) (p c : Addr) (b : Bool) (after : RNG) : Prop :=
  let rejectedBefore := fun k => ∀ i < k, ∃ p' c',
    sampledPair g fuel isGraph tree rng i p' c' ∧ Graph.Reachable g.view c' p'
  if b then rejectedBefore n
  else ∃ k < n, rejectedBefore k ∧ sampledPair g fuel isGraph tree rng k p c ∧
    after.cursor = rng.cursor + 2 * (k + 1)

private theorem sampledPair_succ (g : SGraph T) (fuel : Nat) (isGraph : Bool)
    (tree : Addr) (rng : RNG) (i : Nat) (p c : Addr) :
    sampledPair g fuel isGraph tree rng (i + 1) p c ↔
      sampledPair g fuel isGraph tree (adv (adv rng)) i p c := by
  have h : rng.cursor + 2 * (i + 1) = rng.cursor + 1 + 1 + 2 * i := by omega
  simp only [sampledPair, adv, h]

private def connectionPairsSpec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (isGraph : Bool) (n : Nat)
    (rng : RNG),
    Graph.unfold g.view fuel tree = some t → t.WF D (fun _ => 255) 65535 → t.degree ≠ 0 →
    ∃ (p c : Addr) (b : Bool) (rng' : RNG),
      tryConnectionPairs D fuel isGraph tree n ⟨g, rng⟩ = .ok ((p, c, b), ⟨g, rng'⟩) ∧
      (b = true → p = tree ∧ c = tree ∧ rng'.cursor = rng.cursor + 2 * n) ∧
      (b = false → Graph.Reachable g.view tree p ∧ Graph.Reachable g.view tree c ∧ c ≠ tree ∧
        (∃ cp, g.cells p = some cp ∧ cp.degree ≠ 0) ∧ ¬ Graph.Reachable g.view c p) ∧
      firstSafePair g fuel isGraph tree rng n p c b rng'

def get_two_nodes_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (isGraph : Bool) (n : Int)
    (rng : RNG),
    (n ≤ 0 → getTwoNodesWithoutLoop D fuel isGraph tree n ⟨g, rng⟩ =
      .ok ((tree, tree, true), ⟨g, rng⟩)) ∧
    (Graph.unfold g.view fuel tree = some t → t.WF D (fun _ => 255) 65535 →
      t.degree ≠ 0 → ∃ p c b rng',
        getTwoNodesWithoutLoop D fuel isGraph tree n ⟨g, rng⟩ =
          .ok ((p, c, b), ⟨g, rng'⟩) ∧
        (b = true → p = tree ∧ c = tree ∧ rng'.cursor = rng.cursor + 2 * n.toNat) ∧
        (b = false → Graph.Reachable g.view tree p ∧ Graph.Reachable g.view tree c ∧ c ≠ tree ∧
          (∃ cp, g.cells p = some cp ∧ cp.degree ≠ 0) ∧ ¬ Graph.Reachable g.view c p) ∧
        firstSafePair g fuel isGraph tree rng n.toNat p c b rng')
    ∧ (Graph.unfold g.view fuel tree = some t → t.degree = 0 → 0 < n →
      ∃ e, getTwoNodesWithoutLoop D fuel isGraph tree n ⟨g, rng⟩ = .error e)

/-- `form_random_connection!(tree, rng)` on a finite well-formed tree (`Node` or `GraphNode`)
never creates a cycle: whenever it returns, it returns the same root object and the heap
reachable from it is still acyclic, a finite expression. -/
def form_random_connection_acyclic : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (isGraph : Bool) (rng : RNG)
    (r : Addr) (s' : St T),
    Graph.unfold g.view fuel tree = some t → t.WF D (fun _ => 255) 65535 → SlotsLe D 0 g →
    formRandomConnection D fuel isGraph tree ⟨g, rng⟩ = .ok (r, s') →
    r = tree ∧ Graph.Acyclic s'.g.view tree ∧
    (∃ t', Graph.unfold s'.g.view (fuel + fuel) tree = some t') ∧
    (∀ n, lengthH g D isGraph fuel tree = .ok n → n < 5 → s' = ⟨g, rng⟩) ∧
    (∀ n p c b after, lengthH g D isGraph fuel tree = .ok n → 5 ≤ n →
      getTwoNodesWithoutLoop D fuel isGraph tree 10 ⟨g, rng⟩ =
        .ok ((p, c, b), ⟨g, after⟩) →
      if b then s' = ⟨g, after⟩ else ∃ cp j,
        g.cells p = some cp ∧ j = (after.indexDraws (cp.degree - 1) after.cursor).val ∧
        s'.g.view.cells p = some { cp.toCell with children := cp.toCell.children.set j c } ∧
        ∀ a, a ≠ p → s'.g.cells a = g.cells a)

/-- The selected edge is redirected to fresh storage; other existing cells and
the unfolded expression are preserved. -/
def breakBitsConnectionSpec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (isGraph : Bool) (rng : RNG),
    Graph.unfold g.view fuel tree = some t → t.WF D (fun _ => 255) 65535 → SlotsLe D 0 g →
    ∃ s', breakRandomConnection D fuel isGraph tree none ⟨g, rng⟩ = .ok (tree, s') ∧
      Graph.unfold s'.g.view (fuel + fuel) tree = some t ∧
      (∀ c, g.cells tree = some c → c.degree = 0 → s' = ⟨g, rng⟩) ∧
      (∀ c, g.cells tree = some c → c.degree ≠ 0 → ∃ p j cp ch r tc,
        Graph.Reachable g.view tree p ∧ g.cells p = some cp ∧ cp.active[j]? = some ch ∧
        s'.g.view.cells p = some { cp.toCell with children := cp.toCell.children.set j r } ∧
        (∀ b < g.next, b ≠ p → s'.g.cells b = g.cells b) ∧
        g.next ≤ r ∧
        g.view.unfold fuel ch = some tc ∧ s'.g.view.unfold fuel r = some tc)

def break_random_connection_spec : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel tree : Nat) (t : Tree T) (isGraph : Bool) (rng : RNG)
    (cv : Option (T → StateT (SGraph T) Jl T)) (r : Addr) (s' : St T),
    Graph.unfold g.view fuel tree = some t → DegLe D t → SlotsLe D 0 g →
    breakRandomConnection D fuel isGraph tree cv ⟨g, rng⟩ = .ok (r, s') →
    r = tree ∧
    (t.degree = 0 → s' = ⟨g, rng⟩) ∧
    (t.degree ≠ 0 → ∃ p j cp ch fresh before after,
      Graph.Reachable g.view tree p ∧ g.cells p = some cp ∧ cp.active[j]? = some ch ∧
      s'.g.view.cells p = some { cp.toCell with children := cp.toCell.children.set j fresh } ∧
      g.next ≤ fresh ∧
      g.view.unfold fuel ch = some before ∧ s'.g.view.unfold fuel fresh = some after ∧
      before.size = after.size ∧ before.depth = after.depth)

/-! ## Sampling and `any` on finite trees -/

theorem sampleM_ok {fuel : Nat} {b : Bool} {a : Addr} {F : SGraph T → Addr → Bool} {s : St T}
    {xs : List Addr} (ho : Expressions.Sampling.occurrences s.g.view fuel a = .ok xs)
    (hx : ∃ x ∈ xs, F s.g x = true) :
    ∃ x, sampleM fuel b a F s = .ok (x, { s with rng := adv s.rng }) := by
  have hm : Expressions.Sampling.matching
      ({ graph := s.g.view, root := a, fuel := fuel, filter := F s.g,
         preserveSharing := b } : Expressions.Sampling.NodeSampler T) =
      .ok ((if b then xs.eraseDups else xs).filter (F s.g)) := by
    cases b <;> (simp [Expressions.Sampling.matching, Expressions.Sampling.traversal, ho]; rfl)
  obtain ⟨x, hxs, hfx⟩ := hx
  have hin : x ∈ (if b then xs.eraseDups else xs).filter (F s.g) := by
    rw [List.mem_filter]
    refine ⟨?_, hfx⟩
    cases b
    · exact hxs
    · exact List.mem_eraseDups.mpr hxs
  generalize hL : (if b then xs.eraseDups else xs).filter (F s.g) = L at hm hin
  cases L with
  | nil => simp at hin
  | cons y ys =>
    exact ⟨_, by simp only [sampleM, sampleMState, Expressions.Sampling.rand, hm, Except.map]; rfl⟩

theorem sampleM_none {fuel : Nat} {b : Bool} {a : Addr} {F : SGraph T → Addr → Bool} {s : St T}
    {xs : List Addr} (ho : Expressions.Sampling.occurrences s.g.view fuel a = .ok xs)
    (hx : ∀ x ∈ xs, F s.g x = false) : ∃ e, sampleM fuel b a F s = .error e := by
  have hm : Expressions.Sampling.matching
      ({ graph := s.g.view, root := a, fuel := fuel, filter := F s.g,
         preserveSharing := b } : Expressions.Sampling.NodeSampler T) = .ok [] := by
    have : (if b then xs.eraseDups else xs).filter (F s.g) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy
      have hy' : y ∈ xs := by
        cases b
        · exact hy
        · exact List.mem_eraseDups.mp hy
      simp [hx y hy']
    rw [← this]
    cases b <;> (simp [Expressions.Sampling.matching, Expressions.Sampling.traversal, ho]; rfl)
  exact ⟨_, by simp only [sampleM, sampleMState, Expressions.Sampling.rand, hm, Except.map]; rfl⟩

/-- The occurrences of a finite tree start with the root and, below an operator root, contain
an object other than the root. -/
theorem occ_root {g : SGraph T} {fuel a : Nat} {t : Tree T} {xs : List Addr}
    (hu : Graph.unfold g.view fuel a = some t)
    (ho : Expressions.Sampling.occurrences g.view fuel a = .ok xs) :
    a ∈ xs ∧ (t.degree ≠ 0 → ∃ x ∈ xs, x ≠ a) := by
  obtain ⟨xs', ho', hlen, hspec⟩ := occ_spec g.view fuel a t hu
  rw [ho] at ho'; cases ho'
  rw [preorder_length] at hlen
  have hsz := Tree.size_pos t
  obtain ⟨x0, hx0⟩ : ∃ x, xs[0]? = some x := ⟨xs[0], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨P0, _, hP0, _, _, _, hPk0⟩ := hspec 0 x0 hx0
  have hP0n : P0 = [] := hPk0.mpr rfl
  subst hP0n
  have := path_nil_inv hP0
  subst this
  refine ⟨List.mem_of_getElem? hx0, fun hd => ?_⟩
  have hsz2 : 2 ≤ t.size := by
    cases t with
    | const v => simp [Tree.degree] at hd
    | feature i => simp [Tree.degree] at hd
    | branch o cs =>
      cases cs with
      | nil => simp [Tree.degree] at hd
      | cons c cs => have := Tree.size_pos c; simp [Tree.size_branch]; omega
  obtain ⟨x1, hx1⟩ : ∃ x, xs[1]? = some x := ⟨xs[1], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨P1, _, hP1, _, _, _, hPk1⟩ := hspec 1 x1 hx1
  refine ⟨x1, List.mem_of_getElem? hx1, fun he => ?_⟩
  subst he
  have hne : P1 ≠ [] := fun h => absurd (hPk1.mp h) (by decide)
  exact hne (acyclic_of_unfold hu x1 (reach_refl _ _) P1 hP1)

/-- `any(t -> t === p, c)` on a finite tree is reachability of `p` from `c`. -/
theorem anyM_reach (s : St T) (D fuel c p : Nat) (u : Tree T)
    (hu : Graph.unfold s.g.view fuel c = some u) (hdeg : DegLe D u) :
    ∃ b, anyM D fuel c (fun a _ => decide (a = p)) s = .ok (b, s) ∧
      (b = true ↔ Graph.Reachable s.g.view c p) := by
  have h := anyH_spec s.g D (fun a _ => (pure (decide (a = p)) : StateT Unit Jl Bool)) p () fuel c u
    hu hdeg (fun x _ _ _ hxq s => by rw [show decide (x = p) = false from decide_eq_false hxq]; rfl)
    (fun _ _ s => by rw [show decide (p = p) = true from decide_eq_true rfl]; rfl) ()
  by_cases hr : Graph.Reachable s.g.view c p
  · have h1 := h.1 hr
    refine ⟨true, ?_, iff_of_true rfl hr⟩
    simp only [anyM, onG, StateT.run']
    rw [show anyH s.g D (fun a _ => (pure (decide (a = p)) : StateT Unit Jl Bool)) fuel c () =
      .ok (true, ()) from h1]
    rfl
  · have h1 := h.2 hr
    refine ⟨false, ?_, iff_of_false (by simp) hr⟩
    simp only [anyM, onG, StateT.run']
    rw [show anyH s.g D (fun a _ => (pure (decide (a = p)) : StateT Unit Jl Bool)) fuel c () =
      .ok (false, ()) from h1]
    rfl

/-! ## Rewriting one child slot of a finite graph -/

theorem mapM_some {α β : Type} (F : α → Option β) :
    ∀ l : List α, (∀ y ∈ l, ∃ v, F y = some v) → ∃ vs, l.mapM F = some vs := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons y ys ih =>
    intro h
    obtain ⟨v, hv⟩ := h y List.mem_cons_self
    obtain ⟨vs, hvs⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact ⟨v :: vs, by rw [List.mapM_cons, hv, hvs]; rfl⟩

/-- Pointing child slot `j` of `p` at an object that unfolds keeps every finite unfolding
finite. -/
theorem unfold_setChild_fin {G G' : Graph T} {p x : Addr} {j F : Nat} {cp : Cell T}
    (hp : G.cells p = some cp) (hj : j < cp.children.length)
    (hp' : G'.cells p = some { cp with children := cp.children.set j x })
    (hoth : ∀ b, b ≠ p → G'.cells b = G.cells b) (hx : ∃ tx, Graph.unfold G' F x = some tx) :
    ∀ f a (t : Tree T), Graph.unfold G f a = some t → ∃ t', Graph.unfold G' (f + F) a = some t' := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG h
    rw [show f + 1 + F = (f + F) + 1 by omega]
    by_cases hap : a = p
    · subst hap
      rw [hp] at hc; cases hc
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, rfl⟩
      · omega
      · obtain ⟨vs, hvs⟩ := mapM_some (Graph.unfold G' (f + F)) (cp.children.set j x) (by
          intro y hy
          rcases mem_set_of_mem hy with hy | rfl
          · obtain ⟨ty, _, hty⟩ := mapM_mem _ _ _ hts y hy
            exact ih y ty hty
          · obtain ⟨tx, htx⟩ := hx
            exact ⟨tx, unfold_mono _ _ _ htx _ (by omega)⟩)
        exact ⟨_, unfold_of_cell hp' (by simp [hl]) (Or.inr ⟨hd, vs, hvs, rfl⟩)⟩
    · have hca : G'.cells a = some c := by rw [hoth a hap, hc]
      rcases hcase with hleaf | ⟨hd, ts, hts, rfl⟩
      · exact ⟨t, unfold_of_cell hca hl (Or.inl hleaf)⟩
      · obtain ⟨vs, hvs⟩ := mapM_some (Graph.unfold G' (f + F)) c.children (by
          intro y hy
          obtain ⟨ty, _, hty⟩ := mapM_mem _ _ _ hts y hy
          exact ih y ty hty)
        exact ⟨_, unfold_of_cell hca hl (Or.inr ⟨hd, vs, hvs, rfl⟩)⟩

/-- Pointing child slot `j` of `p` at an object that unfolds to the same tree as the old child
keeps every unfolding. -/
theorem unfold_setChild_same {G G' : Graph T} {p x : Addr} {j F : Nat} {cp : Cell T}
    (hp : G.cells p = some cp) (hj : j < cp.children.length)
    (hp' : G'.cells p = some { cp with children := cp.children.set j x })
    (hoth : ∀ b, b ≠ p → G'.cells b = G.cells b)
    (hx : ∀ y f tb, cp.children[j]? = some y → Graph.unfold G f y = some tb →
      Graph.unfold G' (f + F) x = some tb) :
    ∀ f a (t : Tree T), Graph.unfold G f a = some t → Graph.unfold G' (f + F) a = some t := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG h
    rw [show f + 1 + F = (f + F) + 1 by omega]
    by_cases hap : a = p
    · subst hap
      rw [hp] at hc; cases hc
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, rfl⟩
      · omega
      · refine unfold_of_cell hp' (by simp [hl]) (Or.inr ⟨hd, ts, ?_, rfl⟩)
        apply mapM_of_get _ _ _ (by simp [mapM_length _ _ _ hts])
        intro m y v hy hv
        by_cases hmj : j = m
        · subst hmj
          simp [hj] at hy
          subst hy
          obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts j (cp.children[j]) (List.getElem?_eq_getElem hj)
          rw [hv] at hv'; cases hv'
          exact hx _ f v (List.getElem?_eq_getElem hj) hyv
        · simp [hmj] at hy
          obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts m y hy
          rw [hv] at hv'; cases hv'
          exact ih y v hyv
    · have hca : G'.cells a = some c := by rw [hoth a hap, hc]
      refine unfold_of_cell hca hl ?_
      rcases hcase with hleaf | ⟨hd, ts, hts, rfl⟩
      · exact Or.inl hleaf
      · refine Or.inr ⟨hd, ts, ?_, rfl⟩
        apply mapM_of_get _ _ _ (mapM_length _ _ _ hts).symm
        intro m y v hy hv
        obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts m y hy
        rw [hv] at hv'; cases hv'
        exact ih y v hyv

/-- Every object on a path of a finite tree unfolds with the remaining fuel. -/
theorem unfold_path {G : Graph T} {a z : Addr} {P : List Nat} (hp : Graph.Path G a P z) :
    ∀ f (t : Tree T), Graph.unfold G f a = some t → ∃ u, Graph.unfold G (f - P.length) z = some u := by
  induction hp with
  | nil a => intro f t h; exact ⟨t, by simpa using h⟩
  | @cons a b z i p c hc hi _ ih =>
    intro f t h
    cases f with
    | zero => simp [Graph.unfold] at h
    | succ f =>
      obtain ⟨c', hc', hl, hcase⟩ := unfold_succG h
      rw [hc] at hc'; cases hc'
      rcases hcase with ⟨hd, _⟩ | ⟨_, ts, hts, _⟩
      · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hi; simp at hi
      · obtain ⟨y, _, hy⟩ := mapM_get _ _ _ hts i b hi
        obtain ⟨u, hu⟩ := ih f y hy
        exact ⟨u, by rw [List.length_cons, Nat.add_sub_add_right]; exact hu⟩

theorem unfold_det {G : Graph T} {f f' a : Nat} {t t' : Tree T} (h : Graph.unfold G f a = some t)
    (h' : Graph.unfold G f' a = some t') : t = t' := by
  have h1 := unfold_mono _ _ _ h (max f f') (Nat.le_max_left _ _)
  have h2 := unfold_mono _ _ _ h' (max f f') (Nat.le_max_right _ _)
  rw [h1] at h2
  cases h2
  rfl

theorem bindM_inv {α β : Type} {x : M T α} {f : α → M T β} {s : St T} {b : β} {s' : St T}
    (h : (x >>= f) s = .ok (b, s')) : ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok (b, s') := by
  have e : (x >>= f) s = (x s >>= fun p => f p.1 p.2) := rfl
  rw [e] at h
  cases hx : x s with
  | error e' => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

/-- The cell after `set_child!` in the graph view. -/
theorem view_setChild {g' : SGraph T} {p x j : Nat} {cp c' : SCell T}
    (hc' : g'.cells p = some c') (hact : c'.active = cp.active.set j x) (hdeg : c'.degree = cp.degree)
    (hop : c'.op = cp.op) (hcst : c'.constant = cp.constant) (hval : c'.val = cp.val)
    (hfeat : c'.feature = cp.feature) :
    g'.view.cells p = some { cp.toCell with children := cp.toCell.children.set j x } := by
  rw [view_cells hc']
  simp only [SCell.toCell, hact, hdeg, hop, hcst, hval, hfeat]

/-! ## Proofs -/

private theorem connectionPairsSpec_holds : connectionPairsSpec := by
  intro T g D fuel tree t isGraph n rng hu hwf hdeg
  obtain ⟨xs, ho, _⟩ := occ_spec g.view fuel tree t hu
  obtain ⟨hroot, hsec⟩ := occ_root hu ho
  obtain ⟨x1, hx1, hx1t⟩ := hsec hdeg
  obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
  have hdl := degLe_of_WF t hwf
  induction n generalizing rng with
  | zero =>
    exact ⟨tree, tree, true, rng, rfl, fun _ => ⟨rfl, rfl, rfl⟩, (fun h => by cases h),
      fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩
  | succ n ih =>
    obtain ⟨p, hsp⟩ := sampleM_ok (b := isGraph) (s := ⟨g, rng⟩)
      (F := cellP (fun c => c.degree != 0)) ho ⟨tree, hroot, by simp [cellP, hrc, hrdeg, hdeg]⟩
    obtain ⟨_, ho1, hpx, hpf, _⟩ := sampleM_mem hsp
    rw [ho] at ho1; cases ho1
    obtain ⟨c, hsc⟩ := sampleM_ok (b := isGraph) (s := ⟨g, adv rng⟩)
      (F := fun _ a => decide (a ≠ tree)) ho ⟨x1, hx1, by simp [hx1t]⟩
    obtain ⟨_, ho2, hcx, hcf, _⟩ := sampleM_mem hsc
    rw [ho] at ho2; cases ho2
    obtain ⟨_, Pp, _, _, hPp, _⟩ := occ_reach hu ho hpx
    obtain ⟨kc, Pc, uc, hkc, hPc, huc⟩ := occ_reach hu ho hcx
    have hucd : DegLe D uc := degLe_of_WF uc (preorder_wf t hwf uc (preorder_mem hkc))
    obtain ⟨w, hany, hw⟩ := anyM_reach ⟨g, adv (adv rng)⟩ D fuel c p uc
      (unfold_mono _ _ _ huc fuel (Nat.sub_le _ _)) hucd
    have hpc : ∃ cp, g.cells p = some cp ∧ cp.degree ≠ 0 := by
      simp only [cellP] at hpf
      cases hcp : g.cells p with
      | none => rw [hcp] at hpf; cases hpf
      | some cp => rw [hcp] at hpf; exact ⟨cp, rfl, by simpa using hpf⟩
    have hct : c ≠ tree := by simpa using hcf
    have hpair : sampledPair g fuel isGraph tree rng 0 p c := by
      simpa [sampledPair] using And.intro hsp hsc
    simp only [tryConnectionPairs]
    rw [bindM hsp, bindM hsc, bindM hany]
    cases w
    · have hr : ¬ Graph.Reachable g.view c p := fun h => by simp at hw; exact hw h
      exact ⟨p, c, false, adv (adv rng), rfl, (fun h => by cases h),
        (fun _ => ⟨⟨Pp, hPp⟩, ⟨Pc, hPc⟩, hct, hpc, hr⟩),
        ⟨0, by omega, fun _ hi => False.elim (Nat.not_lt_zero _ hi), hpair, rfl⟩⟩
    · obtain ⟨p', c', b, rng', h, hf, hs, hfirst⟩ := ih (adv (adv rng))
      have hr : Graph.Reachable g.view c p := by simpa using hw.mp rfl
      have extend (k : Nat) (prev : ∀ i < k, ∃ a d,
          sampledPair g fuel isGraph tree (adv (adv rng)) i a d ∧ Graph.Reachable g.view d a) :
          ∀ i < k + 1, ∃ a d,
            sampledPair g fuel isGraph tree rng i a d ∧ Graph.Reachable g.view d a := by
        intro i hi
        cases i with
        | zero => exact ⟨p, c, hpair, hr⟩
        | succ i =>
          obtain ⟨a, d, ha, hd⟩ := prev i (by omega)
          exact ⟨a, d, (sampledPair_succ g fuel isGraph tree rng i a d).mpr ha, hd⟩
      refine ⟨p', c', b, rng', h, ?_, hs, ?_⟩
      · intro hb
        obtain ⟨hp, hc, hcursor⟩ := hf hb
        refine ⟨hp, hc, ?_⟩
        simp only [adv] at hcursor
        omega
      · cases b with
        | true => exact extend n hfirst
        | false =>
          obtain ⟨k, hk, hprev, hchosen, hcursor⟩ := hfirst
          refine ⟨k + 1, by omega, extend k hprev,
            (sampledPair_succ g fuel isGraph tree rng k p' c').mpr hchosen, ?_⟩
          simp only [adv] at hcursor
          omega

private theorem leafParentError (g : SGraph T) (fuel tree : Nat) (isGraph : Bool)
    (rng : RNG) (t : Tree T) (hu : Graph.unfold g.view fuel tree = some t)
    (hd0 : t.degree = 0) :
    ∃ e, sampleM fuel isGraph tree (cellP (fun c => c.degree != 0)) ⟨g, rng⟩ = .error e := by
    obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
    obtain ⟨xs, ho, hlen', hspec⟩ := occ_spec g.view fuel tree t hu
    have hsz : t.size = 1 := by
      cases t with
      | const v => simp [Tree.size]
      | feature i => simp [Tree.size]
      | branch o cs => simp [Tree.degree] at hd0; subst hd0; simp [Tree.size]
    rw [preorder_length, hsz] at hlen'
    have hnone : ∀ x ∈ xs, cellP (fun c => c.degree != 0) g x = false := by
      intro x hx
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      have hk0 : k = 0 := by
        have := (List.getElem?_eq_some_iff.mp hk).1; omega
      subst hk0
      obtain ⟨P, _, hP, _, _, _, hPk⟩ := hspec 0 x hk
      have := path_nil_inv (hPk.mpr rfl ▸ hP)
      subst this
      simp [cellP, hrc, hrdeg, hd0]
    exact sampleM_none (b := isGraph) (s := ⟨g, rng⟩) ho hnone

private theorem leafRetryError (g : SGraph T) (D fuel tree : Nat) (isGraph : Bool)
    (rng : RNG) (t : Tree T) (hu : Graph.unfold g.view fuel tree = some t)
    (hd0 : t.degree = 0) (n : Int) (hn : 0 < n) :
    ∃ e, getTwoNodesWithoutLoop D fuel isGraph tree n ⟨g, rng⟩ = .error e := by
  obtain ⟨e, he⟩ := leafParentError g fuel tree isGraph rng t hu hd0
  obtain ⟨k, hk⟩ : ∃ k : Nat, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
  refine ⟨e, ?_⟩
  simp only [getTwoNodesWithoutLoop, hk, tryConnectionPairs]
  rw [bindM_err he]

theorem get_two_nodes_spec_holds : get_two_nodes_spec := by
  intro T g D fuel tree t isGraph n rng
  constructor
  · intro hn
    have hz : n.toNat = 0 := by omega
    simp only [getTwoNodesWithoutLoop, hz, tryConnectionPairs]
    rfl
  · exact ⟨connectionPairsSpec_holds T g D fuel tree t isGraph n.toNat rng,
      fun hu hd hn => leafRetryError g D fuel tree isGraph rng t hu hd n hn⟩

theorem form_random_connection_acyclic_holds : form_random_connection_acyclic := by
  intro T g D fuel tree t isGraph rng r s' hu hwf hsl h
  have hdl := degLe_of_WF t hwf
  obtain ⟨l, _, hlen⟩ := iterate_length_holds T g D fuel tree isGraph t hu hwf
  have hlenM : onG (fun g => lengthH g D isGraph fuel tree) (⟨g, rng⟩ : St T) =
      .ok (l.length, ⟨g, rng⟩) := by simp [onG, hlen, Except.map]
  have hfin : ∀ s : St T, s.g = g → r = tree → s' = s →
      r = tree ∧ Graph.Acyclic s'.g.view tree ∧
        (∃ t', Graph.unfold s'.g.view (fuel + fuel) tree = some t') ∧
        s'.g = g := by
    intro s hs hr hs'
    subst hs'; rw [hs]
    exact ⟨hr, acyclic_of_unfold hu, ⟨t, unfold_mono _ _ _ hu _ (Nat.le_add_right _ _)⟩, rfl⟩
  unfold formRandomConnection at h
  rw [bindM hlenM] at h
  by_cases h5 : l.length < 5
  · simp only [h5, ↓reduceIte] at h
    cases h
    obtain ⟨hr, ha, ht, _⟩ := hfin ⟨g, rng⟩ rfl rfl rfl
    refine ⟨hr, ha, ht, fun _ _ _ => rfl, ?_⟩
    intro n p c b after hl hn
    rw [hlen] at hl
    cases hl
    omega
  simp only [h5, ↓reduceIte] at h
  obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
  by_cases hd0 : t.degree = 0
  · -- a leaf root has no operator node to sample: the parent draw throws
    exfalso
    obtain ⟨_, _, h2, _⟩ := bindM_inv h
    obtain ⟨e, he⟩ := leafRetryError g D fuel tree isGraph rng t hu hd0 10 (by decide)
    rw [he] at h2
    cases h2
  obtain ⟨p, c, b, rng', hrun, hb1, hb0, _⟩ :=
    (get_two_nodes_spec_holds T g D fuel tree t isGraph 10 rng).2.1 hu hwf hd0
  rw [bindM hrun] at h
  cases b
  · obtain ⟨hrp, hrcR, _, ⟨cp, hcp, hcpd⟩, hnr⟩ := hb0 rfl
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨cp', hcp', hpl, hpD⟩ := good_reach g D fuel tree t hu hdl p hrp
    rw [hcp] at hcp'; cases hcp'
    rw [bindM (rd_ok hcp)] at h
    have hdpos : 1 ≤ cp.degree := by omega
    rw [bindM (randRange_ok _ hdpos _)] at h
    have hjlt := (rng'.indexDraws (cp.degree - 1) rng'.cursor).isLt
    generalize hj : (rng'.indexDraws (cp.degree - 1) rng'.cursor).val = j at hjlt h
    have hjd : j < cp.degree := by omega
    obtain ⟨g', c', hset, hoth, _, hc', hact, hdeg', hop, hcst, hval, hfeat, _⟩ :=
      setChildM_ok (s := ⟨g, adv rng'⟩) (x := c) hcp hpl hpD hjd (fun sl hs => hsl p cp sl (Nat.zero_le _) hcp hs)
    rw [bindM hset] at h
    cases h
    refine ⟨rfl, ?_⟩
    have hp' := view_setChild hc' hact hdeg' hop hcst hval hfeat
    have hothv : ∀ b, b ≠ p → g'.view.cells b = g.view.cells b := by
      intro b hb; rw [DynExpr.NoAlias.view_cells, DynExpr.NoAlias.view_cells, hoth b hb]
    obtain ⟨Pc, hPc⟩ := hrcR
    obtain ⟨uc, huc⟩ := unfold_path hPc fuel t hu
    have hx : ∃ tx, Graph.unfold g'.view fuel c = some tx := by
      refine ⟨uc, ?_⟩
      rw [unfold_agree fuel c (fun y hy => hothv y (fun he => hnr (he ▸ hy)))]
      exact unfold_mono _ _ _ huc fuel (Nat.sub_le _ _)
    have hj' : j < cp.toCell.children.length := by simp [SCell.toCell, hpl]; omega
    obtain ⟨t', ht'⟩ := unfold_setChild_fin (view_cells hcp) hj' hp' hothv hx fuel tree t hu
    refine ⟨acyclic_of_unfold ht', ⟨t', ht'⟩, ?_, ?_⟩
    · intro n hl hn
      rw [hlen] at hl
      cases hl
      omega
    · intro n pp cc b after _ _ hpairs
      rw [hrun] at hpairs
      cases hpairs
      exact ⟨cp, j, hcp, hj.symm, hp', hoth⟩
  · obtain ⟨rfl, rfl, _⟩ := hb1 rfl
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases h
    obtain ⟨hr, ha, ht, _⟩ := hfin ⟨g, rng'⟩ rfl rfl rfl
    refine ⟨hr, ha, ht, ?_, ?_⟩
    · intro n hl hn
      rw [hlen] at hl
      cases hl
      omega
    · intro n pp cc b after _ _ hpairs
      rw [hrun] at hpairs
      cases hpairs
      rfl

theorem breakBitsConnectionSpec_holds : breakBitsConnectionSpec := by
  intro T g D fuel tree t isGraph rng hu hwf hsl
  have hdl := degLe_of_WF t hwf
  obtain ⟨rc, hrc, _, hrdeg, _⟩ := cell_of_unfold hu
  by_cases hd0 : rc.degree = 0
  · refine ⟨⟨g, rng⟩, ?_, unfold_mono _ _ _ hu _ (Nat.le_add_right _ _), fun _ _ _ => rfl, ?_⟩
    · simp only [breakRandomConnection]
      rw [bindM (rd_ok (s := ⟨g, rng⟩) hrc)]
      simp only [hd0, ↓reduceIte]
      rfl
    · intro c hc hn
      rw [hrc] at hc
      cases hc
      exact False.elim (hn hd0)
  obtain ⟨xs, ho, _⟩ := occ_spec g.view fuel tree t hu
  have hroot := (occ_root hu ho).1
  obtain ⟨p, hsp⟩ := sampleM_ok (b := isGraph) (s := ⟨g, rng⟩)
    (F := cellP (fun c => c.degree != 0)) ho ⟨tree, hroot, by simp [cellP, hrc, hd0]⟩
  obtain ⟨_, ho1, hpx, hpf, _⟩ := sampleM_mem hsp
  rw [ho] at ho1; cases ho1
  obtain ⟨k, P, sp, hk, hP, hsu⟩ := occ_reach hu ho hpx
  obtain ⟨cp, hcp, hpl, hpD⟩ := good_reach g D fuel tree t hu hdl p ⟨P, hP⟩
  have hcpd : cp.degree ≠ 0 := by simpa [cellP, hcp] using hpf
  obtain ⟨cp', hcp', _, _, hcase⟩ := cell_of_unfold hsu
  rw [hcp] at hcp'; cases hcp'
  obtain ⟨ts, hts, hspe⟩ : ∃ ts, cp.active.mapM (Graph.unfold g.view (fuel - P.length - 1)) = some ts ∧
      sp = .branch cp.op ts := by
    rcases hcase with ⟨h0, _⟩ | ⟨_, ts, hts, he⟩
    · exact absurd h0 hcpd
    · exact ⟨ts, hts, he⟩
  have hdpos : 1 ≤ cp.degree := by omega
  have hjlt := ((adv rng).indexDraws (cp.degree - 1) (adv rng).cursor).isLt
  generalize hj : ((adv rng).indexDraws (cp.degree - 1) (adv rng).cursor).val = j at hjlt
  have hjd : j < cp.degree := by omega
  have hja : j < cp.active.length := by omega
  generalize hch : cp.active[j] = ch
  have hchg : cp.active[j]? = some ch := by rw [List.getElem?_eq_getElem hja, hch]
  obtain ⟨tch, htch, huch⟩ := mapM_get _ _ _ hts j ch hchg
  have hwfsp := preorder_wf t hwf sp (preorder_mem hk)
  have hwfch : tch.WF D (fun _ => 255) 65535 := by
    rw [hspe] at hwfsp
    simp only [Tree.WF] at hwfsp
    exact hwfsp.2.2 tch (List.mem_of_getElem? htch)
  have huch' : Graph.unfold g.view fuel ch = some tch :=
    unfold_mono _ _ _ huch fuel (by omega)
  obtain ⟨r, h, hcpy, hpres, hur, hfr, _, _⟩ :=
    copy_node_heap_holds T g D fuel ch tch isGraph false huch' hwfch
  have hrlt : r < h.next := closed_lt (closed_unfold fuel r tch hur) (reach_refl _ _)
  have hext : Ext g h := ⟨Nat.le_trans (hfr r (reach_refl _ _)) (Nat.le_of_lt hrlt), hpres⟩
  have hplt : @LT.lt Nat _ p g.next := closed_lt (closed_unfold fuel tree t hu) ⟨P, hP⟩
  have hcph : h.cells p = some cp := by rw [hpres p hplt, hcp]
  obtain ⟨g', c', hset, hoth, _, hc', hact, hdeg', hop, hcst, hval, hfeat, _⟩ :=
    setChildM_ok (s := ⟨h, adv (adv rng)⟩) (x := r) hcph hpl hpD hjd
      (fun sl hs => hsl p cp sl (Nat.zero_le _) hcp hs)
  refine ⟨⟨g', adv (adv rng)⟩, ?_, ?_, ?_, ?_⟩
  · simp only [breakRandomConnection]
    rw [bindM (rd_ok (s := ⟨g, rng⟩) hrc)]
    simp only [hd0, ↓reduceIte]
    rw [bindM hsp, bindM (rd_ok (s := ⟨g, adv rng⟩) hcp), bindM (randRange_ok _ hdpos _), hj]
    rw [bindM (getChildM_ok (s := ⟨g, adv (adv rng)⟩) hcp hpl hpD hjd)]
    rw [show (cp.active[j]?).getD 0 = ch by rw [hchg]; rfl]
    rw [bindM (show copyM D isGraph fuel ch (⟨g, adv (adv rng)⟩ : St T) = .ok (r, ⟨h, adv (adv rng)⟩) by
      simp [copyM, liftG, hcpy, Except.map])]
    rw [bindM hset]
    rfl
  · have hp' := view_setChild hc' hact hdeg' hop hcst hval hfeat
    have hothv : ∀ b, b ≠ p → g'.view.cells b = h.view.cells b := by
      intro b hb; rw [DynExpr.NoAlias.view_cells, DynExpr.NoAlias.view_cells, hoth b hb]
    have hj' : j < cp.toCell.children.length := by simp [SCell.toCell]; omega
    have hx : ∀ y f tb, cp.toCell.children[j]? = some y → Graph.unfold h.view f y = some tb →
        Graph.unfold g'.view (f + fuel) r = some tb := by
      intro y f tb hy hyu
      have hy' : y = ch := by
        simp only [SCell.toCell] at hy; rw [hchg] at hy; cases hy; rfl
      subst hy'
      have huh : Graph.unfold h.view fuel y = some tch := by
        rw [(ext_tree hext (closed_unfold fuel y tch huch')).1 fuel]; exact huch'
      have := unfold_det hyu huh
      subst this
      have hag : Graph.unfold g'.view fuel r = Graph.unfold h.view fuel r :=
        unfold_agree fuel r (fun z hz => hothv z (fun he => by
          have := hfr z hz; rw [he] at this; omega))
      exact unfold_mono _ _ _ (hag.trans hur) _ (Nat.le_add_left _ _)
    have huh : Graph.unfold h.view fuel tree = some t := by
      rw [(ext_tree hext (closed_unfold fuel tree t hu)).1 fuel]; exact hu
    exact unfold_setChild_same (view_cells hcph) hj' hp' hothv hx fuel tree t huh
  · intro c hc ht
    rw [hrc] at hc
    cases hc
    exact False.elim (hd0 ht)
  · intro _ _ _
    refine ⟨p, j, cp, ch, r, tch, ⟨P, hP⟩, hcp, hchg,
      view_setChild hc' hact hdeg' hop hcst hval hfeat, ?_, ?_, huch', ?_⟩
    · intro b hb hbp
      rw [hoth b hbp, hpres b hb]
    · exact hfr r (reach_refl _ _)
    · change g'.view.unfold fuel r = some tch
      have hag : ∀ b, Graph.Reachable h.view r b → g'.view.cells b = h.view.cells b := by
        intro b hb
        have hbp : b ≠ p := fun he => Nat.not_le_of_gt hplt (he ▸ hfr b hb)
        rw [DynExpr.NoAlias.view_cells, DynExpr.NoAlias.view_cells, hoth b hbp]
      exact (unfold_agree (g := h.view) (G := g'.view) fuel r hag).trans hur

end SymReg.Mutations
