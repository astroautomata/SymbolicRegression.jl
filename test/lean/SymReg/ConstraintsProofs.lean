import SymReg.Constraints

/-! Proof of `constraints_accept` (`src/CheckConstraints.jl`). -/

namespace SymReg.Constraints
open DynExpr DynExpr.NodeBase SymReg.Complexity SymReg.HeapLemmas

variable {T : Type}

/-! ### Generic traversal facts -/

theorem anyListM_ok {α : Type} (f : α → Jl Bool) (p : α → Bool) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (p x)) → anyListM f xs = .ok (xs.any p)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [anyListM]
    rw [h x List.mem_cons_self, ok_bind]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons, hp, Bool.false_or]
      exact anyListM_ok f p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    · simp [List.any_cons, hp]
      rfl

theorem mapM_ok {α β : Type} (f : α → Jl β) (q : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (q x)) → xs.mapM f = .ok (xs.map q)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, ok_bind,
      mapM_ok f q xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

private theorem preorder_branch (o : Nat) (cs : List (Tree T)) :
    preorder (.branch o cs) = .branch o cs :: preorder.preorderF cs := rfl

private theorem preorderF_cons (c : Tree T) (cs : List (Tree T)) :
    preorder.preorderF (c :: cs) = preorder c ++ preorder.preorderF cs := rfl

private theorem anyMF_ok (D : Nat) (f : Tree T → Jl Bool) (p : Tree T → Bool) :
    ∀ cs : List (Tree T), (∀ c ∈ cs, anyM D f c = .ok ((preorder c).any p)) →
      anyMF D f cs.length cs = .ok ((preorder.preorderF cs).any p)
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.length_cons, anyMF]
    rw [h c List.mem_cons_self, ok_bind, preorderF_cons, List.any_append]
    cases hp : (preorder c).any p
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      exact anyMF_ok D f p cs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    · simp
      rfl

/-- `any` over a tree with a predicate that succeeds on every node is `List.any` over the
preorder. -/
theorem anyM_ok (D : Nat) (f : Tree T → Jl Bool) (p : Tree T → Bool) (t : Tree T)
    (hd : DegLe D t) (h : ∀ s ∈ preorder t, f s = .ok (p s)) :
    anyM D f t = .ok ((preorder t).any p) := by
  induction t using Tree.induction with
  | hc v => simp only [anyM, preorder, h (.const v) (by simp [preorder])]; simp
  | hf i => simp only [anyM, preorder, h (.feature i) (by simp [preorder])]; simp
  | hb o cs ih =>
    simp only [DegLe] at hd
    have hself := h (.branch o cs) (by simp [preorder])
    by_cases h0 : cs.length = 0
    · have : cs = [] := List.length_eq_zero_iff.mp h0
      subst this
      simp only [anyM, List.length_nil, ↓reduceIte, hself, preorder_branch]
      simp [preorder.preorderF]
    · have hnif : nifDeg D cs.length = cs.length := by simp [nifDeg, hd.1]
      simp only [anyM, h0, ↓reduceIte, hnif, hself, ok_bind, preorder_branch, List.any_cons]
      cases hp : p (.branch o cs)
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
        apply anyMF_ok D f p cs
        intro c hc
        refine ih c hc (hd.2 c hc) (fun s hs => h s ?_)
        rw [preorder_branch]
        apply List.mem_cons_of_mem
        clear ih hd hself hnif h0 hp h
        induction cs with
        | nil => simp at hc
        | cons d ds ihd =>
          rw [preorderF_cons]
          rcases List.mem_cons.mp hc with rfl | hc
          · exact List.mem_append_left _ hs
          · exact List.mem_append_right _ (ihd hc)
      · simp
        rfl

private theorem foldSpecF_map {R B : Type} (fl : Tree T → R) (fb : Tree T → B) (op : B → List R → R)
    (cs : List (Tree T)) : foldSpec.foldSpecF fl fb op cs = cs.map (foldSpec fl fb op) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [foldSpec.foldSpecF, ih]

/-- `max(c...)` of casts is the cast of the list maximum, for nonempty lists. -/
theorem maxList_map_cast : ∀ xs : List Nat, xs ≠ [] →
    maxList (xs.map (fun (n : Nat) => (n : Int))) = ((xs.foldr max 0 : Nat) : Int) := by
  have aux : ∀ (xs : List Nat) (x : Nat),
      (xs.map (fun (n : Nat) => (n : Int))).foldl max (x : Int) =
        ((max x (xs.foldr max 0) : Nat) : Int) := by
    intro xs
    induction xs with
    | nil => intro x; simp
    | cons y ys ih =>
      intro x
      simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
      have : max (x : Int) (y : Int) = ((max x y : Nat) : Int) := by omega
      rw [this, ih (max x y)]
      omega
  intro xs hne
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs =>
    simp only [List.map_cons, maxList, List.foldr_cons]
    exact aux xs x

/-! ### Depth and nesting -/

theorem countDepth_eq (D : Nat) (t : Tree T) (hd : DegLe D t) (hr : t.Representable) :
    countDepth D t = (t.depth : Int) := by
  unfold countDepth
  rw [show Id.run (tmrT D (fun _ => pure (1 : Int)) (fun _ => pure (1 : Int))
      (fun p cs => pure (p + maxList cs)) t) = foldSpec (fun _ => (1 : Int)) (fun _ => (1 : Int))
      (fun p cs => p + maxList cs) t from
    tree_mapreduce_fold_holds T Int Int D (fun _ => 1) (fun _ => 1) (fun p cs => p + maxList cs) t hd]
  clear hd
  induction t using Tree.induction with
  | hc v => simp [foldSpec, Tree.depth]
  | hf i => simp [foldSpec, Tree.depth]
  | hb o cs ih =>
    simp only [Tree.Representable] at hr
    have h0 : cs.length ≠ 0 := by omega
    simp only [foldSpec, h0, ↓reduceIte, foldSpecF_map, Tree.depth]
    have hm : cs.map (foldSpec (fun _ => (1 : Int)) (fun _ => (1 : Int)) (fun p cs => p + maxList cs)) =
        (cs.map Tree.depth).map (fun (n : Nat) => (n : Int)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact ih c hc (hr.2 c hc)
    have hcs : cs ≠ [] := by intro h; simp [h] at h0
    rw [hm, maxList_map_cast _ (by simpa using hcs)]
    push_cast
    rfl

/-- Nesting count of `(nd, no)` along the most crowded path of the unfolded tree. -/
theorem nest_fold (nd no : Nat) (t : Tree T) (hr : t.Representable) :
    foldSpec (fun _ => (0 : Int)) (fun s => if s.degree = nd ∧ opOf s = no then (1 : Int) else 0)
      (fun p cs => p + maxList cs) t = (pathCount nd no t : Int) := by
  induction t using Tree.induction with
  | hc v => simp [foldSpec, pathCount]
  | hf i => simp [foldSpec, pathCount]
  | hb o cs ih =>
    simp only [Tree.Representable] at hr
    have h0 : cs.length ≠ 0 := by omega
    simp only [foldSpec, h0, ↓reduceIte, foldSpecF_map]
    have hm : cs.map (foldSpec (fun _ => (0 : Int))
        (fun s => if s.degree = nd ∧ opOf s = no then (1 : Int) else 0) (fun p cs => p + maxList cs)) =
        (cs.map (pathCount nd no)).map (fun (n : Nat) => (n : Int)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      exact ih c hc (hr.2 c hc)
    have hcs : cs ≠ [] := by intro h; simp [h] at h0
    rw [hm, maxList_map_cast _ (by simpa using hcs)]
    simp only [pathCount, Tree.degree, opOf]
    by_cases hc : cs.length = nd ∧ o = no <;> simp [hc]

theorem countMaxNestedness_eq (D : Nat) (s : Tree T) (nd no : Nat) (hnd : 1 ≤ nd)
    (hd : DegLe D s) (hr : s.Representable) :
    countMaxNestedness D s nd no = (nestBelow nd no s : Int) := by
  unfold countMaxNestedness
  simp only
  rw [show Id.run (tmrT D (fun _ => pure (0 : Int))
      (fun s => pure (if s.degree = nd ∧ opOf s = no then (1 : Int) else 0))
      (fun p cs => pure (p + maxList cs)) s) = foldSpec (fun _ => (0 : Int))
      (fun s => if s.degree = nd ∧ opOf s = no then (1 : Int) else 0)
      (fun p cs => p + maxList cs) s from
    tree_mapreduce_fold_holds T Int Int D _ _ _ s hd, nest_fold nd no s hr]
  cases s with
  | const v => simp [pathCount, nestBelow, kids, Tree.degree]; omega
  | feature i => simp [pathCount, nestBelow, kids, Tree.degree]; omega
  | branch o cs =>
    simp only [pathCount, nestBelow, kids, Tree.degree, opOf]
    by_cases hc : cs.length = nd ∧ o = no <;> simp [hc] <;> omega

/-! ### Subtrees -/

theorem mem_preorder_child {s c : Tree T} {o : Nat} {cs : List (Tree T)} (hc : c ∈ cs)
    (hs : s ∈ preorder c) : s ∈ preorder (.branch o cs) := by
  rw [preorder_branch]
  apply List.mem_cons_of_mem
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    rw [preorderF_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_append_left _ hs
    · exact List.mem_append_right _ (ih hc)

private theorem mem_preorderF {s : Tree T} {cs : List (Tree T)}
    (hs : s ∈ preorder.preorderF cs) : ∃ c ∈ cs, s ∈ preorder c := by
  induction cs with
  | nil => simp [preorder.preorderF] at hs
  | cons d ds ih =>
    rw [preorderF_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ⟨d, List.mem_cons_self, hs⟩
    · obtain ⟨c, hc, hsc⟩ := ih hs
      exact ⟨c, List.mem_cons_of_mem _ hc, hsc⟩

/-- Preorder membership is transitive and well-formedness passes to subtrees. -/
theorem preorder_sub (t : Tree T) : ∀ s ∈ preorder t, (∀ u ∈ preorder s, u ∈ preorder t) ∧
    (t.WF D nops nf → s.WF D nops nf) := by
  induction t using Tree.induction with
  | hc v => intro s hs; simp [preorder] at hs; subst hs; exact ⟨fun u hu => hu, id⟩
  | hf i => intro s hs; simp [preorder] at hs; subst hs; exact ⟨fun u hu => hu, id⟩
  | hb o cs ih =>
    intro s hs
    rw [preorder_branch, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨fun u hu => hu, id⟩
    · obtain ⟨c, hc, hsc⟩ := mem_preorderF hs
      obtain ⟨h1, h2⟩ := ih c hc s hsc
      refine ⟨fun u hu => mem_preorder_child hc (h1 u hu), fun hw => h2 ?_⟩
      simp only [Tree.WF] at hw
      exact hw.2.2 c hc

/-! ### Per-operator constraints -/

/-- Whether the zero-based argument `i` of `s` exceeds its limit in `cons`. -/
def argViol (o : Opts) (s : Tree T) (cons : List Int) (i : Nat) : Bool :=
  match cons[i]?, (kids s)[i]? with
  | some ci, some c => decide (ci ≠ -1) && decide (ci < signedWeight (wsize o.cmap c))
  | _, _ => false

private theorem checkOpCons_ok (D : Nat) (o : Opts) (s : Tree T) (cons : List Int)
    (hw : s.WF D (fun _ => 255) 65535) (hcov : Covers o.cmap s) (hd1 : 1 ≤ s.degree)
    (hlen : cons.length = s.degree) :
    checkOpCons D o s s.degree cons =
      .ok ((List.range' 1 s.degree).any (fun i => argViol o s cons (i - 1))) := by
  cases s with
  | const v => simp [Tree.degree] at hd1
  | feature i => simp [Tree.degree] at hd1
  | branch op cs =>
    simp only [Tree.degree] at hd1 hlen ⊢
    have h0 : cs.length ≠ 0 := by omega
    simp only [checkOpCons, h0, ↓reduceIte]
    apply anyListM_ok
    intro i hi
    rw [List.mem_range'] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [Nat.one_mul, Nat.add_comm 1 k, Nat.add_sub_cancel]
    have hci : cons[k]? = some (cons[k]'(by omega)) := List.getElem?_eq_getElem _
    have hck : cs[k]? = some (cs[k]'(by omega)) := List.getElem?_eq_getElem _
    have hcm : cs[k]'(by omega) ∈ cs := List.getElem_mem _
    simp only [hci, argViol, kids, hck]
    by_cases hm : cons[k]'(by omega) = -1
    · simp [hm, pure_ok, ok_bind]
    · have hg : getChildT (Tree.branch op cs) (k + 1) = .ok (cs[k]'(by omega)) := by
        simp [getChildT, kids, hck]
        rfl
      simp only [Tree.WF] at hw
      have hcw := hw.2.2 _ hcm
      have hcc : Covers o.cmap (cs[k]'(by omega)) := fun hu u hu' =>
        hcov hu u (mem_preorder_child hcm hu')
      simp only [pure_ok, ok_bind, hm, not_false_eq_true, ↓reduceIte, hg, pastLimit,
        computeComplexityT_eq D o.cmap _ hcw hcc, ne_eq, decide_true, Bool.true_and]

/-- One-based `enumerate` membership. -/
theorem mem_enum1 {α : Type} (xs : List α) (d : Nat) (x : α) :
    (d, x) ∈ enum1 xs ↔ 1 ≤ d ∧ xs[d - 1]? = some x := by
  have gen : ∀ (ys : List α) (s : Nat), (d, x) ∈ (List.range' s ys.length).zip ys ↔
      s ≤ d ∧ ys[d - s]? = some x := by
    intro ys
    induction ys with
    | nil => intro s; simp
    | cons y ys ih =>
      intro s
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.mem_cons,
        Prod.mk.injEq, ih (s + 1)]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨h1, h2⟩)
        · simp
        · refine ⟨by omega, ?_⟩
          rw [show d - s = (d - (s + 1)) + 1 by omega, List.getElem?_cons_succ]
          exact h2
      · rintro ⟨h1, h2⟩
        by_cases hds : d = s
        · subst hds
          simp at h2
          exact Or.inl ⟨rfl, h2.symm⟩
        · right
          refine ⟨by omega, ?_⟩
          rw [show d - s = (d - (s + 1)) + 1 by omega, List.getElem?_cons_succ] at h2
          exact h2
  exact gen xs 1

/-- Some constrained argument of some node exceeds its limit. -/
def OpViolation (o : Opts) (t : Tree T) : Prop :=
  ∃ s ∈ preorder t, ∃ cons, consOf o s = some cons ∧
    ∃ (i : Nat) (c : Tree T) (ci : Int), (kids s)[i]? = some c ∧ cons[i]? = some ci ∧ ci ≠ -1 ∧
      ci < signedWeight (wsize o.cmap c)

/-- The per-degree flags of `check_constraints`. -/
private theorem invalid_ok (D : Nat) (o : Opts) (t : Tree T) (hw : t.WF D (fun _ => 255) 65535)
    (hcov : Covers o.cmap t) (hshape : OptsShape o) :
    ∃ L : List Bool, (enum1 o.opCons).mapM (degreeFlag D o t) = .ok L ∧
      (L.any id = true ↔ OpViolation o t) := by
  have hd := degLe_of_WF t hw
  let pOp : Nat → Nat → List Int → Tree T → Bool := fun d oi cons s =>
    decide (s.degree = d ∧ opOf s = oi) && (List.range' 1 d).any (fun i => argViol o s cons (i - 1))
  let q : Nat × List (List Int) → Bool := fun x =>
    (enum1 x.2).any (fun y => y.2.any (· ≠ -1) && (preorder t).any (pOp x.1 y.1 y.2))
  refine ⟨(enum1 o.opCons).map q, ?_, ?_⟩
  · apply mapM_ok
    rintro ⟨d, dc⟩ hx
    obtain ⟨hd1, hdc⟩ := (mem_enum1 _ _ _).mp hx
    unfold degreeFlag
    apply anyListM_ok
    rintro ⟨oi, cons⟩ hy
    obtain ⟨_, hcons⟩ := (mem_enum1 _ _ _).mp hy
    have hlen : cons.length = d := by
      have := hshape.1 (d - 1) dc hdc cons (List.mem_of_getElem? hcons)
      omega
    by_cases ha : cons.any (· ≠ -1) = true
    · simp only [ha, ↓reduceIte, Bool.true_and]
      apply anyM_ok D _ _ t hd
      intro s hs
      obtain ⟨hsub, hwf⟩ := preorder_sub t s hs
      by_cases hm : s.degree = d ∧ opOf s = oi
      · simp only [hm, and_self, ↓reduceIte, pOp, decide_true, Bool.true_and]
        rw [← hm.1]
        exact checkOpCons_ok D o s cons (hwf hw) (fun hu u hu' => hcov hu u (hsub u hu'))
          (by omega) (by omega)
      · simp only [hm, ↓reduceIte, pOp, decide_false, Bool.false_and]
        rfl
    · simp only [Bool.not_eq_true] at ha
      simp only [ha, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      rfl
  · rw [List.any_map]
    simp only [Function.comp_def, id, q, pOp, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Prod.exists]
    constructor
    · rintro ⟨d, dc, hx, oi, cons, hy, -, s, hs, ⟨hdeg, hop⟩, i, hi, hv⟩
      obtain ⟨hd1, hdc⟩ := (mem_enum1 _ _ _).mp hx
      obtain ⟨ho1, hcons⟩ := (mem_enum1 _ _ _).mp hy
      refine ⟨s, hs, cons, ?_, ?_⟩
      · simp only [consOf, hdeg, hop, hd1, ho1, and_self, ↓reduceIte, hdc, Option.getD_some]
        exact hcons
      · simp only [argViol] at hv
        split at hv
        · next ci c h1 h2 =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
          exact ⟨i - 1, c, ci, h2, h1, hv.1, hv.2⟩
        · simp at hv
    · rintro ⟨s, hs, cons, hc, i, c, ci, hk, hci, hne, hlt⟩
      simp only [consOf] at hc
      split at hc
      · next hpos =>
        cases hdc : o.opCons[s.degree - 1]? with
        | none => simp [hdc] at hc
        | some dc =>
          simp only [hdc, Option.getD_some] at hc
          refine ⟨s.degree, dc, (mem_enum1 _ _ _).mpr ⟨hpos.1, hdc⟩, opOf s, cons,
            (mem_enum1 _ _ _).mpr ⟨hpos.2, hc⟩, ?_, s, hs, ⟨rfl, rfl⟩, i + 1, ?_, ?_⟩
          · exact ⟨ci, List.mem_of_getElem? hci, hne⟩
          · have hlen : cons.length = s.degree := by
              have := hshape.1 (s.degree - 1) dc hdc cons (List.mem_of_getElem? hc)
              omega
            have := (List.getElem?_eq_some_iff.mp hci).1
            rw [List.mem_range']
            exact ⟨i, by omega, by omega⟩
          · simp only [Nat.add_sub_cancel, argViol, hci, hk, decide_eq_true_eq, Bool.and_eq_true]
            exact ⟨by simpa using hne, hlt⟩
      · simp at hc

/-! ### Nested constraints -/

/-- Some nested-operator count exceeds its limit. -/
def NestViolation (o : Opts) (t : Tree T) : Prop :=
  ∃ ncs, o.nested = some ncs ∧ ∃ s ∈ preorder t, ∃ d oi inner, (d, oi, inner) ∈ ncs ∧
    s.degree = d ∧ opOf s = oi ∧ ∃ nd no mx, (nd, no, mx) ∈ inner ∧ mx < (nestBelow nd no s : Int)

private theorem nests_iff (D : Nat) (o : Opts) (t : Tree T) (hw : t.WF D (fun _ => 255) 65535)
    (hshape : OptsShape o) : flagIllegalNests D o t = true ↔ NestViolation o t := by
  have hd := degLe_of_WF t hw
  unfold flagIllegalNests NestViolation
  cases hn : o.nested with
  | none => simp
  | some ncs =>
    simp only
    rw [(traversal_tree_holds T Unit D t hd).2.2.2.2.2]
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Prod.exists,
      Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨s, hs, d, oi, inner, hm, ⟨hdeg, hop⟩, nd, no, mx, hin, hgt⟩
      obtain ⟨hsub, hwf⟩ := preorder_sub t s hs
      have hsw := hwf hw
      have hnd := ((hshape.2 ncs hn d oi inner hm).2.2 nd no mx hin).1
      rw [countMaxNestedness_eq D s nd no hnd (degLe_of_WF s hsw) (Tree.WF.representable s hsw)] at hgt
      exact ⟨s, hs, d, oi, inner, hm, hdeg, hop, nd, no, mx, hin, hgt⟩
    · rintro ⟨s, hs, d, oi, inner, hm, hdeg, hop, nd, no, mx, hin, hgt⟩
      obtain ⟨hsub, hwf⟩ := preorder_sub t s hs
      have hsw := hwf hw
      have hnd := ((hshape.2 ncs hn d oi inner hm).2.2 nd no mx hin).1
      refine ⟨s, hs, d, oi, inner, hm, ⟨hdeg, hop⟩, nd, no, mx, hin, ?_⟩
      rw [countMaxNestedness_eq D s nd no hnd (degLe_of_WF s hsw) (Tree.WF.representable s hsw)]
      exact hgt

/-! ### Main theorem -/

theorem constraints_accept_holds : constraints_accept := by
  intro T D o maxsize cached t hw hcov hshape hcached
  have hd := degLe_of_WF t hw
  have hsize : cachedSize D o cached t = .ok (signedWeight (wsize o.cmap t)) := by
    rcases hcached with rfl | rfl
    · exact computeComplexityT_eq D o.cmap t hw hcov
    · rfl
  have hdepth := countDepth_eq D t hd (Tree.WF.representable t hw)
  obtain ⟨L, hL, hLiff⟩ := invalid_ok D o t hw hcov hshape
  have hnest := nests_iff D o t hw hshape
  have hA3 : (∀ s ∈ preorder t, ∀ cons, consOf o s = some cons →
      ∀ (i : Nat) c ci, (kids s)[i]? = some c → cons[i]? = some ci → ci ≠ -1 →
        signedWeight (wsize o.cmap c) ≤ ci) ↔ ¬ OpViolation o t := by
    unfold OpViolation
    constructor
    · rintro h ⟨s, hs, cons, hc, i, c, ci, hk, hci, hne, hlt⟩
      have := h s hs cons hc i c ci hk hci hne
      omega
    · intro h s hs cons hc i c ci hk hci hne
      apply Int.not_lt.mp
      intro hlt
      exact h ⟨s, hs, cons, hc, i, c, ci, hk, hci, hne, hlt⟩
  have hA4 : (∀ ncs, o.nested = some ncs → ∀ s ∈ preorder t, ∀ d oi inner, (d, oi, inner) ∈ ncs →
      s.degree = d → opOf s = oi → ∀ nd no mx, (nd, no, mx) ∈ inner →
        (nestBelow nd no s : Int) ≤ mx) ↔ ¬ NestViolation o t := by
    unfold NestViolation
    constructor
    · rintro h ⟨ncs, hn, s, hs, d, oi, inner, hm, hdeg, hop, nd, no, mx, hin, hgt⟩
      have := h ncs hn s hs d oi inner hm hdeg hop nd no mx hin
      omega
    · intro h ncs hn s hs d oi inner hm hdeg hop nd no mx hin
      apply Int.not_lt.mp
      intro hgt
      exact h ⟨ncs, hn, s, hs, d, oi, inner, hm, hdeg, hop, nd, no, mx, hin, hgt⟩
  unfold checkConstraints
  rw [hsize, ok_bind, hdepth]
  simp only [hL, ok_bind, Accepts]
  by_cases h1 : signedWeight (wsize o.cmap t) > maxsize
  · simp only [h1, ↓reduceIte]
    exact ⟨false, rfl, by simp; omega⟩
  · by_cases h2 : (t.depth : Int) > o.maxdepth
    · simp only [h1, h2, ↓reduceIte]
      exact ⟨false, rfl, by simp; omega⟩
    · by_cases h3 : L.any id = true
      · simp only [h1, h2, h3, ↓reduceIte]
        refine ⟨false, rfl, ?_⟩
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro _ _ h3' _
        exact hA3.mp h3' (hLiff.mp h3)
      · by_cases h4 : flagIllegalNests D o t = true
        · simp only [h1, h2, h3, h4, ↓reduceIte]
          refine ⟨false, rfl, ?_⟩
          simp only [Bool.false_eq_true, false_iff, not_and]
          intro _ _ _ h4'
          exact hA4.mp h4' (hnest.mp h4)
        · simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]
          refine ⟨true, rfl, ?_⟩
          simp only [true_iff]
          exact ⟨by omega, by omega, hA3.mpr (fun hv => h3 (hLiff.mpr hv)),
            hA4.mpr (fun hv => h4 (hnest.mpr hv))⟩

theorem constraints_accept_exact (D : Nat) (o : Opts) (maxsize : Int)
    (cached : Option Int) (t : Tree T) (hw : t.WF D (fun _ => 255) 65535)
    (hcov : Covers o.cmap t) (hshape : OptsShape o)
    (fits : ∀ s ∈ preorder t, -2^63 ≤ wsize o.cmap s ∧ wsize o.cmap s < 2^63)
    (hc : cached = none ∨ cached = some (wsize o.cmap t)) :
    ∃ b, checkConstraints D o maxsize cached t = .ok b ∧ (b = true ↔
      wsize o.cmap t ≤ maxsize ∧ (t.depth : Int) ≤ o.maxdepth ∧
      (∀ s ∈ preorder t, ∀ cons, consOf o s = some cons →
        ∀ (i : Nat) c ci, (kids s)[i]? = some c → cons[i]? = some ci → ci ≠ -1 → wsize o.cmap c ≤ ci) ∧
      (∀ ncs, o.nested = some ncs → ∀ s ∈ preorder t, ∀ d oi inner, (d, oi, inner) ∈ ncs →
        s.degree = d → opOf s = oi → ∀ nd no mx, (nd, no, mx) ∈ inner → (nestBelow nd no s : Int) ≤ mx)) := by
  have wrap s (hs : s ∈ preorder t) : signedWeight (wsize o.cmap s) = wsize o.cmap s :=
    signedWeight_eq_of_fits (fits s hs).1 (fits s hs).2
  have ht := wrap t (Complexity.self_mem_preorder t)
  have hcache : cached = none ∨ cached = some (signedWeight (wsize o.cmap t)) := by
    rwa [ht]
  obtain ⟨b, hb, ha⟩ := constraints_accept_holds T D o maxsize cached t hw hcov hshape hcache
  refine ⟨b, hb, ha.trans ?_⟩
  unfold Accepts
  rw [ht]
  have childWrap (s : Tree T) (hs : s ∈ preorder t) (i : Nat) (c : Tree T)
      (hk : (kids s)[i]? = some c) :
      signedWeight (wsize o.cmap c) = wsize o.cmap c := by
    refine wrap c ((preorder_sub (D := D) (nops := fun _ => 255) (nf := 65535) t s hs).1 c ?_)
    cases s with
    | const v => simp [kids] at hk
    | feature f => simp [kids] at hk
    | branch op cs =>
      change cs[i]? = some c at hk
      exact mem_preorder_child (o := op) (List.mem_of_getElem? hk) (Complexity.self_mem_preorder c)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun s hs cons hcons i c ci hk hci hne =>
      childWrap s hs i c hk ▸ h3 s hs cons hcons i c ci hk hci hne, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun s hs cons hcons i c ci hk hci hne => by
      rw [childWrap s hs i c hk]
      exact h3 s hs cons hcons i c ci hk hci hne, h4⟩

/-- Example options: `sin` (unary op 1) may wrap complexity at most 3, the second argument
of `+` (binary op 1) at most 1, and `sin` may not nest inside `sin`. -/
def exOpts : Opts where
  cmap := { use := false, opC := [], varC := .scalar 1, constC := 1 }
  maxdepth := 10
  opCons := [[[3]], [[-1, 1]]]
  nested := some [(1, 1, [(1, 1, 0)])]

/-- The preconditions of `constraints_accept` are satisfiable. -/
example : (Tree.branch 1 [Tree.feature 1, Tree.const (2 : Nat)]).WF 2 (fun _ => 255) 65535 ∧
    Covers exOpts.cmap (Tree.branch 1 [Tree.feature 1, Tree.const (2 : Nat)]) ∧
    OptsShape exOpts := by
  refine ⟨by simp [Tree.WF], fun h => by simp [exOpts] at h, ?_, ?_⟩
  · intro d dc hdc cons hc
    rcases d with _ | _ | d
    · simp [exOpts] at hdc; subst hdc; simp at hc; subst hc; rfl
    · simp [exOpts] at hdc; subst hdc; simp at hc; subst hc; rfl
    · simp [exOpts] at hdc
  · intro ncs hn d oi inner hm
    simp [exOpts] at hn; subst hn
    simp at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro nd no mx hin
    simp at hin
    omega

end SymReg.Constraints
