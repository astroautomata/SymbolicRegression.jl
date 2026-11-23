import DynExpr.NodeBase.Traverse

/-!
General lemmas about DynamicExpressions' heap model (`DynExpr.NodeBase`), shared by the
SymbolicRegression slices. The DE formalization proves the same facts privately in
`DynExpr/NodeBase/TraverseCount.lean`; they are restated here because private lemmas
cannot be imported.
-/

namespace SymReg.HeapLemmas
open DynExpr DynExpr.NodeBase

variable {T : Type}

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem o_none {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := rfl

theorem o_some {α β : Type} (a : α) (f : α → Option β) : ((some a : Option α) >>= f) = f a :=
  rfl

theorem o_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

theorem mapM_cons {α β : Type} (F : α → Option β) (x : α) (xs : List α) (ys : List β) :
    (x :: xs).mapM F = some ys ↔ ∃ y ys', F x = some y ∧ xs.mapM F = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons]
  cases hx : F x with
  | none => simp [o_none]
  | some y =>
    cases hxs : xs.mapM F with
    | none => simp [o_some, o_none]
    | some ys' =>
      simp only [o_some, o_pure, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨y, ys', rfl, rfl, rfl⟩
      · rintro ⟨y1, ys1, h1, h2, rfl⟩
        subst h1; subst h2; rfl

theorem mapM_mem {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ∀ x ∈ xs, ∃ y ∈ ys, F x = some y := by
  intro xs
  induction xs with
  | nil => intro ys _ x hx; simp at hx
  | cons a as ih =>
    intro ys h x hx
    obtain ⟨y, ys', hy, hys, rfl⟩ := (mapM_cons F a as ys).mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨z, hz, hfz⟩ := ih ys' hys x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

theorem mapM_length {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons a as ih =>
    intro ys h
    obtain ⟨y, ys', _, hys, rfl⟩ := (mapM_cons F a as ys).mp h
    simp [ih ys' hys]

theorem filterMap_full {α : Type} :
    ∀ l : List (Option α), (l.filterMap id).length = l.length → l = (l.filterMap id).map some := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o l ih =>
    intro h
    cases o with
    | none =>
      have := List.length_filterMap_le id l
      rw [List.filterMap_cons_none rfl] at h
      simp at h
      omega
    | some x =>
      have e : (some x :: l).filterMap id = x :: l.filterMap id := rfl
      rw [e] at h ⊢
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.map_cons]
      exact congrArg _ (ih h)

theorem mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
    ∀ k, (∀ i, i < k → f i = .ok (h i)) → (List.range k).mapM f = .ok ((List.range k).map h) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hf
    rw [List.range_succ, List.mapM_append, ih (fun i hi => hf i (by omega))]
    simp [List.mapM_cons, hf k (by omega)]
    rfl

/-- One step of `Graph.unfold` on the projected heap. -/
theorem unfold_succ {g : SGraph T} {f : Nat} {a : Addr} {t : Tree T}
    (h : Graph.unfold g.view (f + 1) a = some t) :
    ∃ c, g.cells a = some c ∧ c.active.length = c.degree ∧
      ((c.degree = 0 ∧ (c.constant = true → ∃ v, c.val = some v ∧ t = .const v) ∧
          (c.constant = false → t = .feature c.feature)) ∨
       (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view f) = some ts ∧
          t = .branch c.op ts)) := by
  cases hc : g.cells a with
  | none =>
    have hv : g.view.cells a = none := by simp [SGraph.view, hc]
    simp only [Graph.unfold, hv, o_none] at h
    cases h
  | some c =>
    have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    refine ⟨c, rfl, ?_⟩
    simp only [Graph.unfold, hv, o_some, SCell.toCell] at h
    by_cases hlen : c.active.length = c.degree
    · refine ⟨hlen, ?_⟩
      by_cases hd : c.degree = 0
      · left
        refine ⟨hd, ?_, ?_⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
          cases hval : c.val with
          | none => simp only [hval, o_none] at h; cases h
          | some v =>
            simp only [hval, o_some, o_pure, Option.some.injEq] at h
            exact ⟨v, rfl, h.symm⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte, o_pure,
            Bool.false_eq_true, Option.some.injEq] at h
          exact h.symm
      · right
        refine ⟨hd, ?_⟩
        simp only [hlen, hd, ne_eq, not_true_eq_false, ↓reduceIte] at h
        cases hm : c.active.mapM (Graph.unfold g.view f) with
        | none => simp only [hm, o_none] at h; cases h
        | some ts =>
          simp only [hm, o_some, o_pure, Option.some.injEq] at h
          exact ⟨ts, rfl, h.symm⟩
    · simp only [hlen, ne_eq, not_false_eq_true, ↓reduceIte] at h
      cases h

/-- `get_children` returns the active children of a node whose active slots are all set. -/
theorem getChildren_active {g : SGraph T} {D a : Nat} {c : SCell T}
    (hc : g.cells a = some c) (hlen : c.active.length = c.degree) (hD : c.degree ≤ D) :
    getChildren g D a c.degree = .ok c.active := by
  have hget : ∀ i, i < c.degree → getChild g D a (i + 1) = .ok ((c.active[i]?).getD 0) := by
    intro i hi
    cases hs : c.slots with
    | none =>
      have : c.active = [] := by simp [SCell.active, hs]
      rw [this] at hlen
      simp at hlen
      omega
    | some s =>
      have h1 : c.active = (s.take c.degree).filterMap id := by
        simp only [SCell.active, hs, Option.getD_some]
      have h2 : c.active.length ≤ (s.take c.degree).length := by
        rw [h1]; exact List.length_filterMap_le _ _
      have h3 : (s.take c.degree).length ≤ c.degree := by simp; omega
      have hfull : s.take c.degree = c.active.map some := by
        rw [h1]
        apply filterMap_full
        rw [← h1]
        omega
      have hsi : s[i]? = some (some ((c.active[i]?).getD 0)) := by
        have e1 : (s.take c.degree)[i]? = s[i]? := by simp [hi]
        rw [← e1, hfull]
        have hi' : i < c.active.length := by omega
        simp [List.getElem?_map, List.getElem?_eq_getElem hi']
      have h4 : 1 ≤ i + 1 ∧ i + 1 ≤ D := by omega
      simp [getChild, Heap.read, hc, hs, h4, hsi, ok_bind]
      rfl
  unfold getChildren
  rw [mapM_range_ok _ _ c.degree hget]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- Well-formed trees have degrees at most `D`. -/
theorem degLe_of_WF {D : Nat} {nops : Nat → Nat} {nf : Nat} :
    ∀ t : Tree T, t.WF D nops nf → DegLe D t := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; simp [DegLe]
  | hf i => intro _; simp [DegLe]
  | hb op cs ih =>
    intro h
    simp only [Tree.WF] at h
    simp only [DegLe]
    exact ⟨h.1.2.1, fun c hc => ih c hc (h.2.2 c hc)⟩

/-- The tree a degree-zero cell denotes, as `Graph.unfold` reads it (`src/Node.jl:95-98`). -/
def leafOf (c : SCell T) : Option (Tree T) :=
  if c.constant then c.val.map .const else some (.feature c.feature)

variable {R B : Type}

/-- Without the identity map (plain `Node`, or `break_sharing = Val(true)`), the heap
`tree_mapreduce` with stateless callbacks computes exactly the `Tree` traversal `tmrT`
on the unfolded tree, including which callback error (if any) is raised, and leaves the
cache untouched. The heap callbacks must agree with the tree callbacks on each node:
leaves through `leafOf`, branches through their operator and unfolded children. -/
theorem tmrH_plain (g : SGraph T) (D : Nat) (fL : SCell T → Jl R) (fB : SCell T → Jl B)
    (op : B → List R → Jl R) (fos : R → Bool → R) (FL : Tree T → Jl R) (FB : Tree T → Jl B)
    (hL : ∀ c l, c.degree = 0 → leafOf c = some l → fL c = FL l)
    (hB : ∀ c (ts : List (Tree T)), c.degree = ts.length → 0 < ts.length →
      fB c = FB (.branch c.op ts)) :
    ∀ fuel a (t : Tree T) (C : Cache R), Graph.unfold g.view fuel a = some t → DegLe D t →
      (tmrH (σ := Unit) g D false (fun _ c => StateT.lift (fL c)) (fun _ c => StateT.lift (fB c))
        (fun b rs => StateT.lift (op b rs)) fos fuel a C).run () =
        (tmrT (m := Jl) D FL FB op t).map (fun r => ((r, C), ())) := by
  intro fuel
  induction fuel with
  | zero => intro a t C h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t C h hdeg
    obtain ⟨c, hc, hlen, hcase⟩ := unfold_succ h
    rcases hcase with ⟨hd, hcst, hfeat⟩ | ⟨hd, ts, hts, rfl⟩
    · -- leaf
      have hl : ∃ l, leafOf c = some l ∧ t = l ∧ tmrT (m := Jl) D FL FB op l = FL l := by
        cases hk : c.constant
        · exact ⟨.feature c.feature, by simp [leafOf, hk], hfeat hk, rfl⟩
        · obtain ⟨v, hv, rfl⟩ := hcst hk
          exact ⟨.const v, by simp [leafOf, hk, hv], rfl, rfl⟩
      obtain ⟨l, hlo, htl', htl⟩ := hl
      rw [htl', htl, ← hL c l hd hlo]
      simp only [tmrH, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        Heap.read, hc, ok_bind, pure_ok, hd]
      cases fL c <;> rfl
    · -- branch
      simp only [DegLe] at hdeg
      have htl := mapM_length _ _ _ hts
      have hlenD : c.degree ≤ D := by omega
      have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlenD]
      have hcs : getChildren g D a (nifDeg D c.degree) = .ok c.active := by
        rw [hnif]; exact getChildren_active hc hlen hlenD
      have htspos : 0 < ts.length := by omega
      have hb := hB c ts (by omega) htspos
      -- the children fold agrees with `tmrF`
      have hfold : ∀ (xs : List Addr) (us : List (Tree T)) (acc : List R),
          xs.mapM (Graph.unfold g.view f) = some us → (∀ u ∈ us, DegLe D u) →
          ((xs.foldlM (fun (acc : List R × Cache R) x => do
              let (r, c2) ← tmrH (σ := Unit) g D false (fun _ c => StateT.lift (fL c))
                (fun _ c => StateT.lift (fB c)) (fun b rs => StateT.lift (op b rs)) fos f x acc.2
              pure (acc.1 ++ [r], c2)) (acc, C)).run ()) =
            (tmrF (m := Jl) D FL FB op us.length us).map (fun rs => ((acc ++ rs, C), ())) := by
        intro xs
        induction xs with
        | nil =>
          intro us acc hm _
          simp only [List.mapM_nil, o_pure, Option.some.injEq] at hm
          subst hm
          simp [tmrF, Except.map, pure_ok]
        | cons x xs ihx =>
          intro us acc hm hus
          obtain ⟨u, us', hu, hus', rfl⟩ := (mapM_cons _ x xs us).mp hm
          have hx := ih x u C hu (hus u List.mem_cons_self)
          simp only [List.foldlM_cons, StateT.run_bind, List.length_cons, tmrF]
          rw [hx]
          cases hr : tmrT (m := Jl) D FL FB op u with
          | error e => rfl
          | ok r =>
            have := ihx us' (acc ++ [r]) hus' (fun v hv => hus v (List.mem_cons_of_mem _ hv))
            simp only [Except.map, ok_bind, StateT.run_pure, pure_ok]
            rw [this]
            cases tmrF (m := Jl) D FL FB op us'.length us' with
            | error e => rfl
            | ok rs => simp only [Except.map, List.append_assoc, List.singleton_append]; rfl
      have hf := hfold c.active ts [] hts hdeg.2
      simp only [List.nil_append] at hf
      have hts0 : ts.length ≠ 0 := by omega
      have hknif : nifDeg D ts.length = ts.length := by simp [nifDeg]; omega
      simp only [tmrT, hts0, ↓reduceIte, hknif]
      rw [← hb]
      cases hfb : fB c with
      | error e =>
        simp only [tmrH, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          Heap.read, hc, ok_bind, pure_ok, hd, hfb]
        rfl
      | ok b =>
        simp only [tmrH, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          Heap.read, hc, ok_bind, pure_ok, hd, hfb, hcs]
        erw [hf]
        cases tmrF (m := Jl) D FL FB op ts.length ts with
        | error e => rfl
        | ok rs =>
          simp only [Except.map, ok_bind]
          cases op b rs <;> rfl
