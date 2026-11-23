import SymReg.Mutations.Props

/-!
Sampling a node by a cell predicate, `any` by a cell predicate, and `get_child`/`set_child!`
on the sampled node.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

theorem preorder_zero (t : Tree T) : (preorder t)[0]? = some t := by
  cases t <;> rfl

theorem preorder_mem {t s : Tree T} {k : Nat} (h : (preorder t)[k]? = some s) : s ∈ preorder t :=
  List.mem_of_getElem? h

/-- A node predicate selected at index `k` of `eligT`. -/
theorem elig_pick {P : Tree T → Bool} {t : Tree T} {k : Nat} (h : k ∈ eligT P t) :
    ∃ u, (preorder t)[k]? = some u ∧ P u = true := by
  obtain ⟨hk, he⟩ := mem_eligIdx.mp h
  have hk' : k < (preorder t).length := by rw [preorder_length]; exact hk
  refine ⟨(preorder t)[k], List.getElem?_eq_getElem hk', ?_⟩
  simpa [List.getElem?_eq_getElem hk'] using he

/-- Some node satisfies `Q` exactly when the eligible index list is nonempty. -/
theorem eligT_ne_nil {Q : Tree T → Bool} {t : Tree T} (h : (preorder t).any Q = true) :
    eligT Q t ≠ [] := by
  obtain ⟨u, hu, hq⟩ := List.any_eq_true.mp h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  apply eligIdx_ne_nil (k := k) (by rw [← preorder_length]; exact hk)
  simp [List.getElem?_eq_getElem hk, hq]

theorem eligT_nil {Q : Tree T → Bool} {t : Tree T} (h : (preorder t).any Q = false) :
    eligT Q t = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  obtain ⟨u, hu, hq⟩ := elig_pick hk
  have := List.any_eq_false.mp h u (preorder_mem hu)
  rw [hq] at this
  exact this rfl

/-- The fuel left at the end of a path is positive. -/
theorem fuel_sub_pos {g : SGraph T} {f x : Nat} {P : List Nat} {u : Tree T}
    (h : Graph.unfold g.view (f - P.length) x = some u) : ∃ f', f - P.length = f' + 1 := by
  cases hf : f - P.length with
  | zero => rw [hf] at h; simp [Graph.unfold] at h
  | succ f' => exact ⟨f', rfl⟩

/-! ### Cell predicates and their tree counterparts -/

/-- Leaves. -/
def isLeafT (s : Tree T) : Bool := s.degree == 0

theorem lk_const : LeafKind (T := T) (fun c => c.degree == 0 && c.constant) isConstT := by
  intro c s hd hk
  by_cases h0 : c.degree = 0
  · rcases hk h0 with ⟨hc, v, rfl⟩ | ⟨hc, i, rfl⟩ <;> simp [isConstT, h0, hc]
  · have hs : s.degree ≠ 0 := by rw [← hd]; exact h0
    cases s <;> simp_all [isConstT, Tree.degree]

theorem lk_feature : LeafKind (T := T) (fun c => c.degree == 0 && !c.constant) isFeatureT := by
  intro c s hd hk
  by_cases h0 : c.degree = 0
  · rcases hk h0 with ⟨hc, v, rfl⟩ | ⟨hc, i, rfl⟩ <;> simp [isFeatureT, h0, hc]
  · have hs : s.degree ≠ 0 := by rw [← hd]; exact h0
    cases s <;> simp_all [isFeatureT, Tree.degree]

theorem lk_leaf : LeafKind (T := T) (fun c => c.degree == 0) isLeafT := by
  intro c s hd _
  simp [isLeafT, hd]

theorem lk_branch : LeafKind (T := T) (fun c => c.degree != 0) isBranchT := by
  intro c s hd _
  simp [isBranchT, hd]

theorem lk_pos : LeafKind (T := T) (fun c => decide (c.degree > 0)) isBranchT := by
  intro c s hd _
  simp only [isBranchT, hd]
  cases s.degree <;> simp

theorem lk_multi : LeafKind (T := T) (fun c => decide (c.degree > 1)) isMultiT := by
  intro c s hd _
  simp [isMultiT, hd]

/-- `rand(rng, NodeSampler(; tree, filter=t -> P(t)))` for a predicate of `degree` and
`constant` that holds somewhere in the tree. -/
theorem sample_kind (s : St T) (fuel a : Nat) (t : Tree T) (Pc : SCell T → Bool)
    (Q : Tree T → Bool) (hPQ : LeafKind Pc Q) (hu : Graph.unfold s.g.view fuel a = some t)
    (hany : (preorder t).any Q = true) :
    ∃ x P u f', drawAt s.rng s.rng.cursor (eligT Q t) ∈ eligT Q t ∧
      sampleM fuel false a (cellP Pc) s = .ok (x, { s with rng := adv s.rng }) ∧
      Graph.Path s.g.view a P x ∧ (preorder t)[drawAt s.rng s.rng.cursor (eligT Q t)]? = some u ∧
      Q u = true ∧ fuel - P.length = f' + 1 ∧
      Graph.unfold s.g.view (f' + 1) x = some u ∧
      (∀ u', ReplPath t P u' (replaceAt t (drawAt s.rng s.rng.cursor (eligT Q t)) u')) ∧
      (P = [] ↔ drawAt s.rng s.rng.cursor (eligT Q t) = 0) ∧
      (∃ xs, Expressions.Sampling.occurrences s.g.view fuel a = .ok xs ∧
        xs[drawAt s.rng s.rng.cursor (eligT Q t)]? = some x) := by
  have hne := eligT_ne_nil hany
  have hFE : ∀ k x P u, Graph.Path s.g.view a P x → (preorder t)[k]? = some u →
      Graph.unfold s.g.view (fuel - P.length) x = some u → (P = [] ↔ k = 0) →
      cellP Pc s.g x = ((preorder t)[k]?).any Q := by
    intro k x P u _ hpu hun _
    rw [cellP_of_unfold hPQ hun, hpu]; rfl
  obtain ⟨k, x, P, u, hk, hsamp, hP, hpu, hun, hrepl, hPk, haddr⟩ :=
    sample_spec s fuel a t (cellP Pc) _ hu hFE hne
  have hku : drawAt s.rng s.rng.cursor (eligT Q t) = k := by
    simp only [drawAt, eligT]; rw [hk]; rfl
  have hkE : k ∈ eligT Q t := List.mem_of_getElem? hk
  obtain ⟨u0, hu0, hq⟩ := elig_pick hkE
  rw [hpu] at hu0; cases hu0
  obtain ⟨f', hf'⟩ := fuel_sub_pos hun
  rw [hku]
  exact ⟨x, P, u, f', hkE, hsamp, hP, hpu, hq, hf', hf' ▸ hun, hrepl, hPk, haddr⟩

/-- `any(t -> P(t), tree)` for a predicate of `degree` and `constant`. -/
theorem anyM_kind (s : St T) (D fuel a : Nat) (t : Tree T) (f : Addr → SCell T → Bool)
    (Q : Tree T → Bool) (hf : ∀ x c, f x c = f 0 c) (hPQ : LeafKind (f 0) Q)
    (hu : Graph.unfold s.g.view fuel a = some t) (hdeg : DegLe D t) :
    anyM D fuel a f s = .ok ((preorder t).any Q, s) := by
  have h := anyH_pred s.g D f Q fuel a t hu hdeg (fun x c u fx _ hc hux => by
    rw [hf, ← cellP_of_unfold hPQ hux]; simp [cellP, hc])
  have h' : anyH (σ := Unit) s.g D (fun a c => pure (f a c)) fuel a () =
      .ok ((preorder t).any Q, ()) := h
  simp only [anyM, onG, StateT.run', h']
  rfl

/-! ### `get_child` and `set_child!` on an object with `D` slots -/

theorem getChildM_ok {s : St T} {D x i : Nat} {c : SCell T} (hc : s.g.cells x = some c)
    (hl : c.active.length = c.degree) (hD : c.degree ≤ D) (hi : i < c.degree) :
    getChildM D x (i + 1) s = .ok ((c.active[i]?).getD 0, s) := by
  simp [getChildM, onG, getChild_active hc hl hD i hi, Except.map]

theorem setChild_cell (h : SGraph T) (D p x j : Nat) (c : SCell T)
    (hc : h.cells p = some c) (hl : c.active.length = c.degree) (hD : c.degree ≤ D)
    (hj : j < c.degree) (hsl : ∀ s, c.slots = some s → s.length ≤ D) :
    ∃ (h' : SGraph T) (c' : SCell T), setChild h D p x (j + 1) = .ok (x, h') ∧
      (∀ b, b ≠ p → h'.cells b = h.cells b) ∧ h'.next = h.next ∧ h'.cells p = some c' ∧
      c'.active = c.active.set j x ∧ c'.degree = c.degree ∧ c'.op = c.op ∧
      c'.constant = c.constant ∧ c'.val = c.val ∧ c'.feature = c.feature ∧
      (∀ s, c'.slots = some s → s.length ≤ D) := by
  cases hs : c.slots with
  | none =>
    have : c.active = [] := by simp [SCell.active, hs]
    rw [this] at hl; simp at hl; omega
  | some s =>
    have hw : ∃ h' : SGraph T, h.write p { c with slots := some (slotsOf D (s.set j (some x))) } = .ok h' ∧
        h'.cells p = some { c with slots := some (slotsOf D (s.set j (some x))) } ∧
        (∀ b, b ≠ p → h'.cells b = h.cells b) ∧ h'.next = h.next := by
      unfold Heap.write
      rw [dite_eq_right (by simp [hc])]
      exact ⟨_, rfl, by simp, by intro b hb; simp [hb], rfl⟩
    obtain ⟨h', hw, hp', hoth, hnext⟩ := hw
    refine ⟨h', _, ?_, hoth, hnext, hp', ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · have h4 : 1 ≤ j + 1 ∧ j + 1 ≤ D := by omega
      have hle : ¬ D < s.length := Nat.not_lt.mpr (hsl s hs)
      simp [setChild, setChildrenRaw, Heap.read, hc, hs, h4, hw, ok_bind, hle]
      rfl
    · simp only [SCell.active, Option.getD_some]
      exact slots_set s c.degree D j x c.active (by simp [SCell.active, hs]) hl hD hj
    · intro s' hs'; cases hs'; simp [slotsOf]

theorem setChildM_ok {s : St T} {D p x j : Nat} {c : SCell T} (hc : s.g.cells p = some c)
    (hl : c.active.length = c.degree) (hD : c.degree ≤ D) (hj : j < c.degree)
    (hsl : ∀ sl, c.slots = some sl → sl.length ≤ D) :
    ∃ (g' : SGraph T) (c' : SCell T), setChildM D p x (j + 1) s = .ok ((), { s with g := g' }) ∧
      (∀ b, b ≠ p → g'.cells b = s.g.cells b) ∧ g'.next = s.g.next ∧ g'.cells p = some c' ∧
      c'.active = c.active.set j x ∧ c'.degree = c.degree ∧ c'.op = c.op ∧
      c'.constant = c.constant ∧ c'.val = c.val ∧ c'.feature = c.feature ∧
      (∀ sl, c'.slots = some sl → sl.length ≤ D) := by
  obtain ⟨g', c', hset, rest⟩ := setChild_cell s.g D p x j c hc hl hD hj hsl
  refine ⟨g', c', ?_, rest⟩
  simp [setChildM, liftG, hset, Except.map]

/-! ### `mapM` over a modified children list -/

theorem mapM_set {α β : Type} (F : α → Option β) (l : List α) (ts : List β) (i : Nat) (y : α)
    (v : β) (hm : l.mapM F = some ts) (hi : i < l.length) (hy : F y = some v) :
    (l.set i y).mapM F = some (ts.set i v) := by
  apply mapM_of_get _ _ _ (by simp [mapM_length _ _ _ hm])
  intro m a b ha hb
  by_cases hmi : i = m
  · subst hmi
    have hit : i < ts.length := by rw [mapM_length _ _ _ hm]; exact hi
    simp [hi] at ha; simp [hit] at hb
    subst ha; subst hb; exact hy
  · simp [hmi] at ha hb
    obtain ⟨b', hb', hab⟩ := mapM_get _ _ _ hm m a ha
    rw [hb] at hb'; cases hb'; exact hab

/-- Children that do not reach a rewritten object unfold as before. -/
theorem mapM_agree {g g' : SGraph T} {x f : Nat} (l : List Addr)
    (hoth : ∀ b, b ≠ x → g'.cells b = g.cells b)
    (hnr : ∀ y ∈ l, ¬ Graph.Reachable g.view y x) :
    l.mapM (Graph.unfold g'.view f) = l.mapM (Graph.unfold g.view f) := by
  apply mapM_congr'
  intro y hy
  apply unfold_agree
  intro z hz
  simp only [SGraph.view]
  rw [hoth z (fun hzx => hnr y hy (hzx ▸ hz))]

end SymReg.Mutations
