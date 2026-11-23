import SymReg.Mutations.Model
import DynExpr.NoAlias.Core

/-!
Heap, path, occurrence and `set_child!` lemmas for the mutation proofs. Most are the
lemmas of `SymReg/CrossoverProofs.lean` (private there), restated here.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase SymReg.HeapLemmas DynExpr.NoAlias SymReg.Crossover

variable {T : Type}

/-! ### Lists -/

theorem mapM_get {α β : Type} (F : α → Option β) :
    ∀ (l : List α) (ts : List β), l.mapM F = some ts →
      ∀ (i : Nat) x, l[i]? = some x → ∃ y, ts[i]? = some y ∧ F x = some y := by
  intro l
  induction l with
  | nil => intro ts _ i x h; simp at h
  | cons a as ih =>
    intro ts h i x hx
    obtain ⟨y, ys', hy, hys, rfl⟩ := (mapM_cons F a as ts).mp h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨y, rfl, hy⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx ⊢
      exact ih ys' hys i x hx

theorem mapM_of_get {α β : Type} (F : α → Option β) :
    ∀ (l : List α) (ts : List β), l.length = ts.length →
      (∀ (i : Nat) x y, l[i]? = some x → ts[i]? = some y → F x = some y) → l.mapM F = some ts := by
  intro l
  induction l with
  | nil => intro ts hl _; cases ts with | nil => rfl | cons _ _ => simp at hl
  | cons a as ih =>
    intro ts hl h
    cases ts with
    | nil => simp at hl
    | cons y ys =>
      have h0 := h 0 a y rfl rfl
      have hr := ih ys (by simpa using hl)
        (fun i x z hx hz => h (i + 1) x z (by simpa using hx) (by simpa using hz))
      rw [List.mapM_cons, h0, hr]
      rfl

/-! ### Unfolding on a `Graph` -/

theorem unfold_succG {G : Graph T} {f a t} (hu : Graph.unfold G (f + 1) a = some t) :
    ∃ c, G.cells a = some c ∧ c.children.length = c.degree ∧
      ((c.degree = 0 ∧ ((c.constant = true ∧ ∃ v, c.val = some v ∧ t = .const v) ∨
          (c.constant = false ∧ t = .feature c.feature))) ∨
        (c.degree ≠ 0 ∧ ∃ ts, c.children.mapM (Graph.unfold G f) = some ts ∧
          t = .branch c.op ts)) := by
  cases hc : G.cells a with
  | none => simp [Graph.unfold, hc] at hu
  | some c =>
    refine ⟨c, rfl, ?_⟩
    by_cases hl : c.children.length = c.degree
    case neg => simp [Graph.unfold, hc, hl] at hu
    refine ⟨hl, ?_⟩
    by_cases hd : c.degree = 0
    · left
      refine ⟨hd, ?_⟩
      cases hcs : c.constant
      · right
        refine ⟨rfl, ?_⟩
        simp [Graph.unfold, hc, hl, hd, hcs] at hu
        cases hu; rfl
      · left
        refine ⟨rfl, ?_⟩
        cases hv : c.val with
        | none => simp [Graph.unfold, hc, hl, hd, hcs, hv] at hu
        | some v =>
          simp [Graph.unfold, hc, hl, hd, hcs, hv] at hu
          exact ⟨v, rfl, by cases hu; rfl⟩
    · right
      refine ⟨hd, ?_⟩
      cases hm : c.children.mapM (Graph.unfold G f) with
      | none => simp [Graph.unfold, hc, hl, hd, hm] at hu
      | some ts =>
        simp [Graph.unfold, hc, hl, hd, hm] at hu
        exact ⟨ts, rfl, by cases hu; rfl⟩

theorem unfold_of_cell {G : Graph T} {f a t} {c : Cell T} (hc : G.cells a = some c)
    (hl : c.children.length = c.degree)
    (hcase : (c.degree = 0 ∧ ((c.constant = true ∧ ∃ v, c.val = some v ∧ t = .const v) ∨
          (c.constant = false ∧ t = .feature c.feature))) ∨
        (c.degree ≠ 0 ∧ ∃ ts, c.children.mapM (Graph.unfold G f) = some ts ∧
          t = .branch c.op ts)) :
    Graph.unfold G (f + 1) a = some t := by
  rcases hcase with ⟨hd, ⟨hk, v, hv, rfl⟩ | ⟨hk, rfl⟩⟩ | ⟨hd, ts, hm, rfl⟩
  · simp [Graph.unfold, hc, hl, hd, hk, hv]
  · simp [Graph.unfold, hc, hl, hd, hk]
  · simp [Graph.unfold, hc, hl, hd, hm]

theorem unfold_mono {G : Graph T} :
    ∀ f a t, Graph.unfold G f a = some t → ∀ f', f ≤ f' → Graph.unfold G f' a = some t := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h f' hf
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG h
    refine unfold_of_cell hc hl ?_
    rcases hcase with hleaf | ⟨hd, ts, hm, rfl⟩
    · exact Or.inl hleaf
    · refine Or.inr ⟨hd, ts, ?_, rfl⟩
      apply mapM_of_get _ _ _ (mapM_length _ _ _ hm).symm
      intro i x y hx hy
      obtain ⟨y', hy', hfx⟩ := mapM_get _ _ _ hm i x hx
      rw [hy] at hy'
      cases hy'
      exact ih x y hfx f'' (by omega)

/-- A successful unfolding visits only existing objects. -/
theorem closed_unfold {G : Graph T} :
    ∀ (fuel : Nat) (a : Addr) (t : Tree T), G.unfold fuel a = some t → Closed G a := by
  intro fuel
  induction fuel with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG h
    intro z hz
    rcases reach_inv hz with rfl | ⟨c', b, hc', hb, hbz⟩
    · simp [hc]
    · rw [hc] at hc'; cases hc'
      rcases hcase with ⟨hd, _⟩ | ⟨_, ts, hm, _⟩
      · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hb; simp at hb
      · obtain ⟨t', _, ht'⟩ := mapM_mem _ _ _ hm b hb
        exact ih b t' ht' z hbz

theorem mapM_congr' {α β : Type} (f h : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = h x) → l.mapM f = l.mapM h := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hx
    simp [List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]

/-- Unfolding only reads the objects reachable from the root. -/
theorem unfold_agree {g G : Graph T} :
    ∀ (fuel : Nat) (a : Addr), (∀ x, Graph.Reachable g a x → G.cells x = g.cells x) →
      G.unfold fuel a = g.unfold fuel a := by
  intro fuel
  induction fuel with
  | zero => intro a _; rfl
  | succ f ih =>
    intro a h
    have hview : G.cells a = g.cells a := h a (reach_refl g a)
    simp only [Graph.unfold, hview]
    cases hc : g.cells a with
    | none => rfl
    | some c =>
      have hch : ∀ b ∈ c.children, G.unfold f b = g.unfold f b := fun b hb =>
        ih b (fun x hx => h x (reach_trans (reach_mem hc hb) hx))
      simp only [bind, Option.bind]
      rw [mapM_congr' _ _ c.children hch]

theorem sameKids_of_agree {g G : Graph T} {a : Addr}
    (h : ∀ x, Graph.Reachable g a x → G.cells x = g.cells x) : SameKidsOn g G a :=
  fun x hx => by simp [kids, h x hx]

/-! ### Paths -/

theorem path_func {G : Graph T} :
    ∀ {a P b}, Graph.Path G a P b → ∀ {b'}, Graph.Path G a P b' → b = b' := by
  intro a P b hp
  induction hp with
  | nil => intro b' h; exact path_nil_inv h
  | @cons a b z i p c hc hi _ ih =>
    intro b' h
    obtain ⟨c', b2, hc', hi', hp'⟩ := path_cons_inv h
    rw [hc] at hc'; cases hc'
    rw [hi] at hi'; cases hi'
    exact ih hp'

theorem path_snoc_inv {G : Graph T} :
    ∀ (P : List Nat) {a j n}, Graph.Path G a (P ++ [j]) n →
      ∃ q c, Graph.Path G a P q ∧ G.cells q = some c ∧ c.children[j]? = some n := by
  intro P
  induction P with
  | nil =>
    intro a j n h
    obtain ⟨c, b, hc, hi, hp⟩ := path_cons_inv h
    cases path_nil_inv hp
    exact ⟨a, c, .nil a, hc, hi⟩
  | cons i P ih =>
    intro a j n h
    obtain ⟨c, b, hc, hi, hp⟩ := path_cons_inv h
    obtain ⟨q, c', hq, hc', hj⟩ := ih hp
    exact ⟨q, c', .cons hc hi hq, hc', hj⟩

theorem path_snoc {G : Graph T} {a q n : Addr} {P : List Nat} {c : Cell T} {j : Nat}
    (hp : Graph.Path G a P q) (hc : G.cells q = some c) (hj : c.children[j]? = some n) :
    Graph.Path G a (P ++ [j]) n :=
  hp.append (.cons hc hj (.nil n))

theorem exists_snoc {α : Type} : ∀ (l : List α), l ≠ [] → ∃ L b, l = L ++ [b]
  | [], h => absurd rfl h
  | [b], _ => ⟨[], b, rfl⟩
  | a :: b :: l, _ => by
    obtain ⟨L, c, hL⟩ := exists_snoc (b :: l) (by simp)
    exact ⟨a :: L, c, by rw [hL]; rfl⟩

/-- In an alias-free tree, the parent and slot of a node are unique. -/
theorem noAlias_parent {G : Graph T} {a x q n : Addr} {Px Pq : List Nat}
    {cx cq : Cell T} {m j : Nat} (hna : Graph.NoAlias G a)
    (hx : Graph.Path G a Px x) (hcx : G.cells x = some cx) (hm : cx.children[m]? = some n)
    (hq : Graph.Path G a Pq q) (hcq : G.cells q = some cq) (hj : cq.children[j]? = some n) :
    x = q ∧ m = j := by
  have heq := hna _ _ _ (path_snoc hx hcx hm) (path_snoc hq hcq hj)
  obtain ⟨h1, h2⟩ := List.append_inj' heq rfl
  subst h1
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨path_func hx hq, h2⟩

/-! ### Trees -/

/-- `ReplPath t P u t'`: replacing the subtree of `t` at child path `P` by `u` gives `t'`. -/
inductive ReplPath : Tree T → List Nat → Tree T → Tree T → Prop
  | nil (t u : Tree T) : ReplPath t [] u u
  | cons {o : Nat} {cs : List (Tree T)} {i : Nat} {c : Tree T} {P : List Nat} {u c' : Tree T} :
      cs[i]? = some c → ReplPath c P u c' →
      ReplPath (.branch o cs) (i :: P) u (.branch o (cs.set i c'))

theorem replaceAt_zero (t u : Tree T) : replaceAt t 0 u = u := by
  cases t <;> simp [replaceAt]

theorem replaceAt_succ (o : Nat) (cs : List (Tree T)) (k : Nat) (u : Tree T) :
    replaceAt (.branch o cs) (k + 1) u = .branch o (replaceF cs k u) := by
  simp [replaceAt]

theorem replaceF_cons (c : Tree T) (cs : List (Tree T)) (k : Nat) (u : Tree T) :
    replaceF (c :: cs) k u = if k < (preorder c).length then replaceAt c k u :: cs
      else c :: replaceF cs (k - (preorder c).length) u := by
  simp [replaceF]

theorem preorder_branch (o : Nat) (cs : List (Tree T)) :
    preorder (.branch o cs) = .branch o cs :: preorder.preorderF cs := rfl

theorem preorderF_cons (c : Tree T) (cs : List (Tree T)) :
    preorder.preorderF (c :: cs) = preorder c ++ preorder.preorderF cs := rfl

theorem preorder_length (t : Tree T) : (preorder t).length = t.size := by
  induction t using Tree.induction with
  | hc v => simp [preorder, Tree.size]
  | hf i => simp [preorder, Tree.size]
  | hb o cs ih =>
    rw [preorder_branch, Tree.size_branch, List.length_cons]
    have : (preorder.preorderF cs).length = (cs.map Tree.size).sum := by
      clear o
      induction cs with
      | nil => rfl
      | cons c cs ihc =>
        rw [preorderF_cons, List.length_append, ih c (by simp),
          ihc (fun d hd => ih d (by simp [hd]))]
        simp
    omega

theorem preorder_wf {D : Nat} {nops : Nat → Nat} {nf : Nat} (t : Tree T) :
    t.WF D nops nf → ∀ x ∈ preorder t, x.WF D nops nf := by
  induction t using Tree.induction with
  | hc v => intro h x hx; simp [preorder] at hx; subst hx; exact h
  | hf i => intro h x hx; simp [preorder] at hx; subst hx; exact h
  | hb o cs ih =>
    intro h x hx
    rw [preorder_branch] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h
    · simp only [Tree.WF] at h
      have forest : ∀ ds : List (Tree T), (∀ d ∈ ds, d.WF D nops nf → ∀ x ∈ preorder d,
          x.WF D nops nf) → (∀ d ∈ ds, d.WF D nops nf) →
          ∀ x ∈ preorder.preorderF ds, x.WF D nops nf := by
        intro ds
        induction ds with
        | nil => intro _ _ x hx; simp [preorder.preorderF] at hx
        | cons d ds ihd =>
          intro hi hw x hx
          rw [preorderF_cons] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hi d (by simp) (hw d (by simp)) x hx
          · exact ihd (fun e he => hi e (by simp [he])) (fun e he => hw e (by simp [he])) x hx
      exact forest cs ih h.2.2 x hx

theorem replPath_nil_inv {t u t' : Tree T} (h : ReplPath t [] u t') : t' = u := by
  cases h; rfl

theorem replPath_cons_inv {t u t' : Tree T} {i : Nat} {P : List Nat}
    (h : ReplPath t (i :: P) u t') :
    ∃ o cs c c', t = .branch o cs ∧ cs[i]? = some c ∧ ReplPath c P u c' ∧
      t' = .branch o (cs.set i c') := by
  cases h with
  | cons hc hr => exact ⟨_, _, _, _, rfl, hc, hr, rfl⟩

/-! ### Occurrences -/

def OccSpec (G : Graph T) (f : Nat) (a : Addr) (t : Tree T) (xs : List Addr) : Prop :=
  xs.length = (preorder t).length ∧
  ∀ (k : Nat) x, xs[k]? = some x → ∃ P s, Graph.Path G a P x ∧ (preorder t)[k]? = some s ∧
    Graph.unfold G (f - P.length) x = some s ∧ (∀ u, ReplPath t P u (replaceAt t k u)) ∧
    (P = [] ↔ k = 0)

theorem occ_forest (G : Graph T) (f : Nat)
    (ih : ∀ a t, Graph.unfold G f a = some t →
      ∃ xs, Expressions.Sampling.occurrences G f a = .ok xs ∧ OccSpec G f a t xs) :
    ∀ (as : List Addr) (ts : List (Tree T)), as.mapM (Graph.unfold G f) = some ts →
      ∃ yss, as.mapM (Expressions.Sampling.occurrences G f) = .ok yss ∧
        yss.flatten.length = (preorder.preorderF ts).length ∧
        ∀ (k : Nat) x, yss.flatten[k]? = some x → ∃ (i : Nat) (b : Addr) (P : List Nat) (s tb : Tree T), as[i]? = some b ∧
          ts[i]? = some tb ∧ Graph.Path G b P x ∧ (preorder.preorderF ts)[k]? = some s ∧
          Graph.unfold G (f - P.length) x = some s ∧
          ∀ u, ∃ tb', ReplPath tb P u tb' ∧ replaceF ts k u = ts.set i tb' := by
  intro as
  induction as with
  | nil =>
    intro ts h
    simp only [List.mapM_nil, o_pure, Option.some.injEq] at h
    subst h
    refine ⟨[], rfl, rfl, ?_⟩
    intro k x hx; simp at hx
  | cons b bs ihb =>
    intro ts h
    obtain ⟨tb, tbs, htb, htbs, rfl⟩ := (mapM_cons _ b bs ts).mp h
    obtain ⟨ys, hys, hlen, hspec⟩ := ih b tb htb
    obtain ⟨yss, hyss, hlen', hspec'⟩ := ihb tbs htbs
    refine ⟨ys :: yss, ?_, ?_, ?_⟩
    · rw [List.mapM_cons, hys, hyss]; rfl
    · simp [List.flatten_cons, preorderF_cons, hlen, hlen']
    · intro k x hx
      rw [List.flatten_cons] at hx
      by_cases hk : k < ys.length
      · rw [List.getElem?_append_left hk] at hx
        obtain ⟨P, s, hP, hs, hu, hr, -⟩ := hspec k x hx
        refine ⟨0, b, P, s, tb, rfl, rfl, hP, ?_, hu, ?_⟩
        · rw [preorderF_cons, List.getElem?_append_left (by omega)]; exact hs
        · intro u
          refine ⟨replaceAt tb k u, hr u, ?_⟩
          rw [replaceF_cons, if_pos (by omega)]; rfl
      · rw [List.getElem?_append_right (by omega)] at hx
        obtain ⟨i, b', P, s, tb', hb', htb', hP, hs, hu, hr⟩ := hspec' (k - ys.length) x hx
        refine ⟨i + 1, b', P, s, tb', by simpa using hb', by simpa using htb', hP, ?_, hu, ?_⟩
        · rw [preorderF_cons, List.getElem?_append_right (by omega), ← hlen]; exact hs
        · intro u
          obtain ⟨tb'', hR, heq⟩ := hr u
          refine ⟨tb'', hR, ?_⟩
          rw [replaceF_cons, if_neg (by omega), ← hlen, heq]; rfl

theorem occ_spec (G : Graph T) :
    ∀ f a t, Graph.unfold G f a = some t →
      ∃ xs, Expressions.Sampling.occurrences G f a = .ok xs ∧ OccSpec G f a t xs := by
  intro f
  induction f with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t hu
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG hu
    have hread : G.read a = .ok c := by simp [Heap.read, hc]
    rcases hcase with ⟨hd, hleaf⟩ | ⟨hd, ts, hm, rfl⟩
    · have hnil : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hpre : preorder t = [t] := by rcases hleaf with ⟨_, v, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl
      refine ⟨[a], ?_, ?_⟩
      · simp [Expressions.Sampling.occurrences, hread, hnil, ok_bind]; rfl
      · refine ⟨by simp [hpre], ?_⟩
        intro k x hx
        cases k with
        | zero =>
          simp at hx; subst hx
          exact ⟨[], t, .nil _, by simp [hpre], by simpa using hu,
            fun u => by rw [replaceAt_zero]; exact .nil t u, by simp⟩
        | succ k => simp at hx
    · obtain ⟨yss, hyss, hlen, hspec⟩ := occ_forest G f ih c.children ts hm
      refine ⟨a :: yss.flatten, ?_, ?_⟩
      · simp only [Expressions.Sampling.occurrences, hread, ok_bind, hyss]; rfl
      · refine ⟨by simp [preorder_branch, hlen], ?_⟩
        intro k x hx
        cases k with
        | zero =>
          simp at hx; subst hx
          exact ⟨[], .branch c.op ts, .nil _, by simp [preorder_branch], by simpa using hu,
            fun u => by rw [replaceAt_zero]; exact .nil _ u, by simp⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨i, b, P, s, tb, hb, htb, hP, hs, hu', hr⟩ := hspec k x hx
          refine ⟨i :: P, s, .cons hc hb hP, by simpa [preorder_branch] using hs, ?_, ?_, by simp⟩
          · simpa using hu'
          · intro u
            obtain ⟨tb', hR, heq⟩ := hr u
            rw [replaceAt_succ, heq]
            exact .cons htb hR

/-! ### `anyH` -/

theorem anyH_leaf {σ : Type} (h : SGraph T) (D : Nat)
    (F : Addr → SCell T → StateT σ Jl Bool) (f : Nat) (a : Addr) (c : SCell T)
    (hc : h.cells a = some c) (hd : c.degree = 0) (s : σ) :
    (anyH h D F (f + 1) a).run s = (F a c).run s := by
  simp [anyH, StateT.run_bind, StateT.run_lift, Heap.read, hc, hd, ok_bind]

theorem anyH_branch_true {σ : Type} (h : SGraph T) (D : Nat)
    (F : Addr → SCell T → StateT σ Jl Bool) (f : Nat) (a : Addr) (c : SCell T)
    (hc : h.cells a = some c) (hd : c.degree ≠ 0) {s s' : σ}
    (hF : (F a c).run s = .ok (true, s')) :
    (anyH h D F (f + 1) a).run s = .ok (true, s') := by
  simp [anyH, StateT.run_bind, StateT.run_lift, Heap.read, hc, hd, ok_bind, hF]
  rfl

theorem anyH_branch_false {σ : Type} (h : SGraph T) (D : Nat)
    (F : Addr → SCell T → StateT σ Jl Bool) (f : Nat) (a : Addr) (c : SCell T) (cs : List Addr)
    (hc : h.cells a = some c) (hd : c.degree ≠ 0) {s : σ}
    (hF : (F a c).run s = .ok (false, s))
    (hcs : getChildren h D a (nifDeg D c.degree) = .ok cs) :
    (anyH h D F (f + 1) a).run s = (cs.anyM (fun x => anyH h D F f x)).run s := by
  simp [anyH, StateT.run_bind, StateT.run_lift, Heap.read, hc, hd, ok_bind, hF, hcs]

theorem anyM_spec {σ : Type} (G : Addr → StateT σ Jl Bool) (R : Addr → Prop) (sq : σ) :
    ∀ (l : List Addr), (∀ x ∈ l, ∀ s, (R x → (G x).run s = .ok (true, sq)) ∧
        (¬ R x → (G x).run s = .ok (false, s))) →
      ∀ s, ((∃ x ∈ l, R x) → (l.anyM G).run s = .ok (true, sq)) ∧
        ((¬ ∃ x ∈ l, R x) → (l.anyM G).run s = .ok (false, s)) := by
  intro l
  induction l with
  | nil => intro _ s; exact ⟨fun ⟨x, hx, _⟩ => by simp at hx, fun _ => rfl⟩
  | cons y ys ih =>
    intro hG s
    have ⟨h1, h2⟩ := hG y (by simp) s
    by_cases hy : R y
    · have e : (List.anyM G (y :: ys)).run s = .ok (true, sq) := by
        simp [List.anyM, StateT.run_bind, h1 hy, ok_bind]
        rfl
      exact ⟨fun _ => e, fun hn => absurd ⟨y, by simp, hy⟩ hn⟩
    · have e : (List.anyM G (y :: ys)).run s = (List.anyM G ys).run s := by
        simp [List.anyM, StateT.run_bind, h2 hy, ok_bind]
      have ⟨i1, i2⟩ := ih (fun x hx => hG x (by simp [hx])) s
      rw [e]
      refine ⟨fun ⟨x, hx, hr⟩ => i1 ⟨x, ?_, hr⟩,
        fun hn => i2 (fun ⟨x, hx, hr⟩ => hn ⟨x, by simp [hx], hr⟩)⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hr hy
      · exact hx

theorem anyH_spec {σ : Type} (h : SGraph T) (D : Nat)
    (F : Addr → SCell T → StateT σ Jl Bool) (q : Addr) (sq : σ) :
    ∀ f a t, Graph.unfold h.view f a = some t → DegLe D t →
      (∀ x c, Graph.Reachable h.view a x → h.cells x = some c → x ≠ q →
        ∀ s, (F x c).run s = .ok (false, s)) →
      (∀ c, h.cells q = some c → ∀ s, (F q c).run s = .ok (true, sq)) →
      ∀ s, (Graph.Reachable h.view a q → (anyH h D F f a).run s = .ok (true, sq)) ∧
        (¬ Graph.Reachable h.view a q → (anyH h D F f a).run s = .ok (false, s)) := by
  intro f
  induction f with
  | zero => intro a t hu; simp [Graph.unfold] at hu
  | succ f ih =>
    intro a t hu hdeg hF hq s
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succ hu
    have hv : h.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    by_cases haq : a = q
    · subst haq
      have hr : Graph.Reachable h.view a a := reach_refl _ _
      refine ⟨fun _ => ?_, fun hn => absurd hr hn⟩
      by_cases hd : c.degree = 0
      · rw [anyH_leaf h D F f a c hc hd s]; exact hq c hc s
      · exact anyH_branch_true h D F f a c hc hd (hq c hc s)
    · have hFa := hF a c (reach_refl _ _) hc haq s
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, rfl⟩
      · rw [anyH_leaf h D F f a c hc hd s, hFa]
        refine ⟨fun hr => ?_, fun _ => rfl⟩
        exfalso
        rcases reach_inv hr with h' | ⟨c', b, hc', hb, _⟩
        · exact haq h'.symm
        · rw [hv] at hc'; cases hc'
          have : c.active = [] := List.eq_nil_of_length_eq_zero (by omega)
          simp [SCell.toCell, this] at hb
      · simp only [DegLe] at hdeg
        have htl := mapM_length _ _ _ hts
        have hlenD : c.degree ≤ D := by omega
        have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlenD]
        have hcs : getChildren h D a (nifDeg D c.degree) = .ok c.active := by
          rw [hnif]; exact getChildren_active hc hl hlenD
        rw [anyH_branch_false h D F f a c c.active hc hd hFa hcs]
        have hchild : ∀ x ∈ c.active, ∀ s,
            (Graph.Reachable h.view x q → (anyH h D F f x).run s = .ok (true, sq)) ∧
            (¬ Graph.Reachable h.view x q → (anyH h D F f x).run s = .ok (false, s)) := by
          intro x hx s
          obtain ⟨tx, htx, hux⟩ := mapM_mem _ _ _ hts x hx
          have hxr : Graph.Reachable h.view a x := reach_mem hv hx
          exact ih x tx hux (hdeg.2 tx htx) (fun y cy hy => hF y cy (reach_trans hxr hy)) hq s
        have ⟨i1, i2⟩ := anyM_spec (fun x => anyH h D F f x)
          (fun x => Graph.Reachable h.view x q) sq c.active hchild s
        refine ⟨fun hr => i1 ?_, fun hn => i2 ?_⟩
        · rcases reach_inv hr with h' | ⟨c', b, hc', hb, hbq⟩
          · exact absurd h'.symm haq
          · rw [hv] at hc'; cases hc'; exact ⟨b, hb, hbq⟩
        · exact fun ⟨x, hx, hxq⟩ => hn (reach_trans (reach_mem hv hx) hxq)

/-! ### `_find_parent` and `_random_node_and_parent` -/

/-- Every object reachable from a well-formed unfolding root exists, has all its active
slots set and degree at most `D`. -/
theorem good_reach (h : SGraph T) (D : Nat) :
    ∀ f a t, Graph.unfold h.view f a = some t → DegLe D t → ∀ x, Graph.Reachable h.view a x →
      ∃ c, h.cells x = some c ∧ c.active.length = c.degree ∧ c.degree ≤ D := by
  intro f
  induction f with
  | zero => intro a t hu; simp [Graph.unfold] at hu
  | succ f ih =>
    intro a t hu hdeg x hx
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succ hu
    have hv : h.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    rcases reach_inv hx with rfl | ⟨c', b, hc', hb, hbx⟩
    · refine ⟨c, hc, hl, ?_⟩
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, rfl⟩
      · omega
      · simp only [DegLe] at hdeg; have := mapM_length _ _ _ hts; omega
    · rw [hv] at hc'; cases hc'
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, rfl⟩
      · have : c.active = [] := List.eq_nil_of_length_eq_zero (by omega)
        simp [SCell.toCell, this] at hb
      · simp only [DegLe] at hdeg
        obtain ⟨tb, htb, hub⟩ := mapM_mem _ _ _ hts b hb
        exact ih b tb hub (hdeg.2 tb htb) x hbx

theorem getChild_active {h : SGraph T} {D x : Nat} {c : SCell T}
    (hc : h.cells x = some c) (hlen : c.active.length = c.degree) (hD : c.degree ≤ D) :
    ∀ i, i < c.degree → getChild h D x (i + 1) = .ok ((c.active[i]?).getD 0) := by
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

theorem scan_false (h : SGraph T) (D : Nat) (n x : Addr) (c : SCell T)
    (hc : h.cells x = some c) (hl : c.active.length = c.degree) (hD : c.degree ≤ D) :
    ∀ is : List Nat, (∀ i ∈ is, 1 ≤ i ∧ i ≤ c.degree ∧ c.active[i - 1]? ≠ some n) →
      ∀ s, (scanChildren h D n x is).run s = .ok (false, s) := by
  intro is
  induction is with
  | nil => intro _ s; rfl
  | cons i is ih =>
    intro hi s
    obtain ⟨h1, h2, h3⟩ := hi i (by simp)
    have hg := getChild_active hc hl hD (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hg
    have hlt : i - 1 < c.active.length := by omega
    have hne : (c.active[i - 1]?).getD 0 ≠ n := by
      rw [List.getElem?_eq_getElem hlt] at h3 ⊢
      simpa using h3
    simp [scanChildren, StateT.run_bind, StateT.run_lift, hg, ok_bind, hne]
    exact ih (fun j hj => hi j (by simp [hj])) s

theorem scan_true (h : SGraph T) (D : Nat) (n x : Addr) (c : SCell T)
    (hc : h.cells x = some c) (hl : c.active.length = c.degree) (hD : c.degree ≤ D) (i0 : Nat)
    (hi0 : c.active[i0 - 1]? = some n) :
    ∀ is : List Nat, (∀ i ∈ is, 1 ≤ i ∧ i ≤ c.degree ∧ (c.active[i - 1]? = some n → i = i0)) →
      i0 ∈ is → ∀ s, (scanChildren h D n x is).run s = .ok (true, some (x, i0)) := by
  intro is
  induction is with
  | nil => intro _ hm; simp at hm
  | cons i is ih =>
    intro hi hm s
    obtain ⟨h1, h2, h3⟩ := hi i (by simp)
    have hg := getChild_active hc hl hD (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hg
    have hlt : i - 1 < c.active.length := by omega
    by_cases heq : c.active[i - 1]? = some n
    · have hii := h3 heq
      subst hii
      have hgn : (c.active[i - 1]?).getD 0 = n := by rw [heq]; rfl
      simp [scanChildren, StateT.run_bind, StateT.run_lift, hg, ok_bind, hgn]
      rfl
    · have hne : (c.active[i - 1]?).getD 0 ≠ n := by
        rw [List.getElem?_eq_getElem hlt] at heq ⊢; simpa using heq
      have hm' : i0 ∈ is := by
        rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd hi0 heq
        · exact hm
      simp [scanChildren, StateT.run_bind, StateT.run_lift, hg, ok_bind, hne]
      exact ih (fun j hj => hi j (by simp [hj])) hm' s

theorem findParent_spec (h : SGraph T) (D f : Nat) (a n q : Addr) (t : Tree T)
    (P : List Nat) (j : Nat) (cq : SCell T)
    (hu : Graph.unfold h.view f a = some t) (hdeg : DegLe D t) (hna : Graph.NoAlias h.view a)
    (hP : Graph.Path h.view a P q) (hq : h.cells q = some cq) (hj : cq.active[j]? = some n) :
    findParent h D f a n = .ok (q, j + 1) := by
  have hvq : h.view.cells q = some cq.toCell := by simp [SGraph.view, hq]
  have hgood := good_reach h D f a t hu hdeg
  have hspec := anyH_spec h D (parentPred h D n) q (some (q, j + 1)) f a t hu hdeg ?_ ?_ none
  · have hrun := hspec.1 ⟨P, hP⟩
    simp [findParent, hrun, ok_bind]
    rfl
  · intro x c hx hc hxq s
    obtain ⟨c', hc', hl, hD⟩ := hgood x hx
    rw [hc] at hc'; cases hc'
    obtain ⟨Px, hPx⟩ := hx
    unfold parentPred
    by_cases hd : c.degree > 0
    · rw [if_pos hd]
      apply scan_false h D n x c hc hl hD
      intro i hi
      rw [List.mem_range'_1] at hi
      refine ⟨hi.1, by omega, fun heq => hxq ?_⟩
      have hvx : h.view.cells x = some c.toCell := by simp [SGraph.view, hc]
      exact (noAlias_parent hna hPx hvx heq hP hvq hj).1
    · rw [if_neg hd]; rfl
  · intro c hc s
    rw [hq] at hc; cases hc
    obtain ⟨c', hc', hl, hD⟩ := hgood q ⟨P, hP⟩
    rw [hq] at hc'; cases hc'
    obtain ⟨hjl, _⟩ := List.getElem?_eq_some_iff.mp hj
    unfold parentPred
    rw [if_pos (by omega)]
    apply scan_true h D n q cq hq hl hD (j + 1) (by simpa using hj)
    · intro i hi
      rw [List.mem_range'_1] at hi
      refine ⟨hi.1, by omega, fun heq => ?_⟩
      have := (noAlias_parent hna hP hvq heq hP hvq hj).2
      omega
    · rw [List.mem_range'_1]; omega

theorem rnp_spec (h : SGraph T) (D fuel : Nat) (a : Addr) (s : Tree T)
    (rng : Expressions.Sampling.RNG) (k : Nat)
    (hk : k = (rng.indexDraws (s.size - 1) rng.cursor).val)
    (hu : Graph.unfold h.view fuel a = some s) (hwf : s.WF D (fun _ => 255) 65535)
    (hna : Graph.NoAlias h.view a) :
    ∃ (n p i : Nat) (u : Tree T), randomNodeAndParent h D fuel a rng =
        (.ok (n, p, i), { rng with cursor := rng.cursor + 1 }) ∧
      (preorder s)[k]? = some u ∧ Graph.unfold h.view fuel n = some u ∧
      Graph.Reachable h.view a n ∧
      ((i = 0 ∧ k = 0 ∧ n = a ∧ p = a) ∨
       (i ≠ 0 ∧ ∃ P cp, Graph.Path h.view a P p ∧ h.cells p = some cp ∧
          cp.active[i - 1]? = some n ∧ ∀ u', ReplPath s (P ++ [i - 1]) u' (replaceAt s k u'))) := by
  obtain ⟨xs, hocc, hlen, hspec⟩ := occ_spec h.view fuel a s hu
  have hsize : xs.length = s.size := by rw [hlen, preorder_length]
  have hkl : k < xs.length := by
    have := (rng.indexDraws (s.size - 1) rng.cursor).isLt
    have := Tree.size_pos s
    omega
  obtain ⟨n, hn⟩ : ∃ n, xs[k]? = some n := ⟨xs[k], List.getElem?_eq_getElem hkl⟩
  obtain ⟨P, u, hP, hpu, hun, hrepl, hPk⟩ := hspec k n hn
  have hun' : Graph.unfold h.view fuel n = some u := unfold_mono _ _ _ hun _ (by omega)
  have hsample : sampleNode h fuel a rng = (.ok n, { rng with cursor := rng.cursor + 1 }) := by
    cases xs with
    | nil => simp at hkl
    | cons x0 rest =>
      have hm : Expressions.Sampling.matching
          ({ graph := h.view, root := a, fuel := fuel } : Expressions.Sampling.NodeSampler T) =
          .ok (x0 :: rest) := by
        simp [Expressions.Sampling.matching, Expressions.Sampling.traversal, hocc]
        simp only [Functor.map, Except.map]
        rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
      have hrl : rest.length = s.size - 1 := by simp at hsize; omega
      simp only [sampleNode, Expressions.Sampling.rand, hm]
      rw [hrl, ← hk]
      simp [Expressions.Sampling.getNode, hn]
  have hdeg := degLe_of_WF s hwf
  refine ⟨n, ?_⟩
  by_cases hk0 : k = 0
  · have hPn : P = [] := hPk.mpr hk0
    subst hPn
    have hna' := path_nil_inv hP
    subst hna'
    refine ⟨a, 0, u, ?_, hpu, hun', reach_refl _ _, Or.inl ⟨rfl, hk0, rfl, rfl⟩⟩
    simp [randomNodeAndParent, hsample]
  · have hPne : P ≠ [] := fun he => hk0 (hPk.mp he)
    have hna_ne : n ≠ a := by
      intro he
      subst he
      exact hPne (hna.acyclic n (reach_refl _ _) P hP)
    obtain ⟨Q, j, rfl⟩ := exists_snoc P hPne
    obtain ⟨q, cq', hQ, hcq', hj⟩ := path_snoc_inv Q hP
    obtain ⟨cq, hcq, rfl⟩ : ∃ cq, h.cells q = some cq ∧ cq' = cq.toCell := by
      cases hc : h.cells q with
      | none => simp [SGraph.view, hc] at hcq'
      | some cq => simp [SGraph.view, hc] at hcq'; exact ⟨cq, rfl, hcq'.symm⟩
    have hfp := findParent_spec h D fuel a n q s Q j cq hu hdeg hna hQ hcq hj
    refine ⟨q, j + 1, u, ?_, hpu, hun', ⟨_, hP⟩, Or.inr ⟨by omega, Q, cq, hQ, hcq, by simp only [Nat.add_sub_cancel]; exact hj,
      by simpa using hrepl⟩⟩
    simp [randomNodeAndParent, hsample, hna_ne, hfp, Except.map]

/-! ### `set_child!` -/

theorem slots_set (s : List (Option Addr)) (d D j : Nat) (x : Addr) (act : List Addr)
    (hact : (s.take d).filterMap id = act) (hl : act.length = d) (hD : d ≤ D) (hj : j < d) :
    ((slotsOf D (s.set j (some x))).take d).filterMap id = act.set j x := by
  have hlen_take : (s.take d).length = d := by
    have h2 : act.length ≤ (s.take d).length := by rw [← hact]; exact List.length_filterMap_le _ _
    have h3 : (s.take d).length ≤ d := by simp; omega
    omega
  have hfull : s.take d = act.map some := by
    have := filterMap_full (s.take d) (by rw [hact, hl, hlen_take])
    rw [hact] at this; exact this
  have hsl : d ≤ s.length := by have := hlen_take; simp at this; omega
  have key : (slotsOf D (s.set j (some x))).take d = (act.set j x).map some := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < d
    · have hiD : i < D := by omega
      have hia : i < act.length := by omega
      have hsi : s[i]? = some (some act[i]) := by
        have e1 : (s.take d)[i]? = s[i]? := by simp [hi]
        rw [← e1, hfull]; simp [hia]
      by_cases hij : j = i
      · subst hij
        simp [slotsOf, hi, hiD, List.getElem?_set, hia, show j < s.length by omega]
      · simp [slotsOf, hi, hiD, List.getElem?_set, hij, hsi, hia]
    · simp [hi, hl]; omega
  have fm : ∀ l : List Addr, (l.map some).filterMap id = l := by
    intro l
    induction l with
    | nil => rfl
    | cons y ys ih => exact congrArg (y :: ·) ih
  rw [key, fm]

theorem setChild_spec (h : SGraph T) (D p x j : Nat) (c : SCell T)
    (hc : h.cells p = some c) (hl : c.active.length = c.degree) (hD : c.degree ≤ D)
    (hj : j < c.degree) (hsl : ∀ s, c.slots = some s → s.length ≤ D) :
    ∃ h', setChild h D p x (j + 1) = .ok (x, h') ∧ (∀ b, b ≠ p → h'.cells b = h.cells b) ∧
      h'.next = h.next ∧
      h'.view.cells p = some { c.toCell with children := c.toCell.children.set j x } := by
  cases hs : c.slots with
  | none =>
    have : c.active = [] := by simp [SCell.active, hs]
    rw [this] at hl; simp at hl; omega
  | some s =>
    have hw : ∃ h', h.write p { c with slots := some (slotsOf D (s.set j (some x))) } = .ok h' ∧
        h'.cells p = some { c with slots := some (slotsOf D (s.set j (some x))) } ∧
        (∀ b, b ≠ p → h'.cells b = h.cells b) ∧ h'.next = h.next := by
      unfold Heap.write
      rw [dite_eq_right (by simp [hc])]
      exact ⟨_, rfl, by simp, by intro b hb; simp [hb], rfl⟩
    obtain ⟨h', hw, hp', hoth, hnext⟩ := hw
    refine ⟨h', ?_, hoth, hnext, ?_⟩
    · have h4 : 1 ≤ j + 1 ∧ j + 1 ≤ D := by omega
      have hle : ¬ D < s.length := Nat.not_lt.mpr (hsl s hs)
      simp [setChild, setChildrenRaw, Heap.read, hc, hs, h4, hw, ok_bind, hle]
      rfl
    · have hact : SCell.active { c with slots := some (slotsOf D (s.set j (some x))) } =
          c.active.set j x := by
        simp only [SCell.active, Option.getD_some]
        exact slots_set s c.degree D j x c.active (by simp [SCell.active, hs]) hl hD hj
      simp [SGraph.view, hp', SCell.toCell, hact]

/-! ### Children tuples of fresh objects have at most `D` slots -/

/-- Every object at or above `N` whose children tuple is set has at most `D` slots, as
every `NTuple{D}` children field does in Julia. -/
def SlotsLe (D N : Nat) (h : SGraph T) : Prop :=
  ∀ (a : Nat) c s, N ≤ a → h.cells a = some c → c.slots = some s → s.length ≤ D

theorem slotsLe_fresh (D : Nat) (g : SGraph T) : SlotsLe D g.next g := by
  intro a c s ha hc _
  rw [g.fresh a ha] at hc; cases hc

theorem slotsLe_alloc {D N : Nat} {h : SGraph T} (hI : SlotsLe D N h) (v : SCell T)
    (hv : ∀ s, v.slots = some s → s.length ≤ D) : SlotsLe D N (h.alloc v).2 := by
  intro a c s ha hc hs
  simp only [Heap.alloc] at hc
  split at hc
  · cases hc; exact hv s hs
  · exact hI a c s ha hc hs

theorem slotsLe_write {D N : Nat} {h h' : SGraph T} {n : Addr} {v : SCell T}
    (hI : SlotsLe D N h) (hw : h.write n v = .ok h')
    (hv : ∀ s, v.slots = some s → s.length ≤ D) : SlotsLe D N h' := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw
    intro a c s ha hc hs
    simp only at hc
    split at hc
    · cases hc; exact hv s hs
    · exact hI a c s ha hc hs

theorem ex_bind_ok {ε α β : Type} {e : Except ε α} {k : α → Except ε β} {y : β}
    (h : (e >>= k) = .ok y) : ∃ p, e = .ok p ∧ k p = .ok y := by
  cases e with
  | error x => cases h
  | ok p => exact ⟨p, rfl, h⟩

theorem slotsLe_setChildrenRaw {D N : Nat} {h h' : SGraph T} {n : Addr}
    {cs : List (Option Addr)} (hI : SlotsLe D N h) (hw : setChildrenRaw h D n cs = .ok h') :
    SlotsLe D N h' := by
  unfold setChildrenRaw at hw
  split at hw
  · cases hw
  · obtain ⟨c, _, hw⟩ := ex_bind_ok hw
    exact slotsLe_write hI hw (fun s hs => by cases hs; simp [slotsOf])

/-- The branch constructor used by `branch_copy` (`src/base.jl:508-510` of DynamicExpressions.jl). -/
theorem slotsLe_ctor {D N o : Nat} {h h' : SGraph T} {r : Addr} {rs : List Addr}
    (hI : SlotsLe D N h) (hk : ctor h D true { op := some o, children := some rs } = .ok (r, h')) :
    SlotsLe D N h' := by
  by_cases h1 : rs.length > D
  · simp [ctor, h1] at hk
  by_cases h2 : o > 255
  · simp [ctor, h1, h2] at hk
  simp only [ctor, pure_bind, h1, h2, ↓reduceIte] at hk
  obtain ⟨g2, hg2, hk⟩ := ex_bind_ok hk
  cases hk
  unfold setChildren at hg2
  exact slotsLe_setChildrenRaw (slotsLe_alloc hI _ (fun s hs => by cases hs)) hg2

/-- `tree_mapreduce` preserves any state invariant that every callback preserves. -/
theorem tmrH_inv {σ R B : Type} (g : SGraph T) (D : Nat) (sh : Bool)
    (fL : Addr → SCell T → StateT σ Jl R) (fB : Addr → SCell T → StateT σ Jl B)
    (op : B → List R → StateT σ Jl R) (fos : R → Bool → R) (I : σ → Prop)
    (hL : ∀ a c s y, I s → (fL a c).run s = .ok y → I y.2)
    (hB : ∀ a c s y, I s → (fB a c).run s = .ok y → I y.2)
    (hO : ∀ b rs s y, I s → (op b rs).run s = .ok y → I y.2) :
    ∀ fuel a C s y, I s → (tmrH g D sh fL fB op fos fuel a C).run s = .ok y → I y.2 := by
  intro fuel
  induction fuel with
  | zero => intro a C s y _ h; cases h
  | succ f ih =>
    intro a C s y hs h
    simp only [tmrH] at h
    split at h
    · cases h; exact hs
    · simp only [StateT.run_bind, StateT.run_lift] at h
      obtain ⟨⟨c, s0⟩, hc, h⟩ := ex_bind_ok h
      obtain ⟨c', _, he⟩ := ex_bind_ok hc
      cases he
      obtain ⟨⟨rc, s1⟩, hrc, h⟩ := ex_bind_ok h
      have hs1 : I s1 := by
        split at hrc
        · simp only [StateT.run_bind] at hrc
          obtain ⟨⟨r, s2⟩, hr, hrc⟩ := ex_bind_ok hrc
          cases hrc
          exact hL _ _ _ _ hs hr
        · simp only [StateT.run_bind, StateT.run_lift] at hrc
          obtain ⟨⟨b, s2⟩, hb, hrc⟩ := ex_bind_ok hrc
          have hs2 := hB _ _ _ _ hs hb
          obtain ⟨⟨kids, s3⟩, hk, hrc⟩ := ex_bind_ok hrc
          obtain ⟨kids', _, hk'⟩ := ex_bind_ok hk
          cases hk'
          obtain ⟨⟨rs, s4⟩, hf, hrc⟩ := ex_bind_ok hrc
          have hfold : ∀ (xs : List Addr) (acc : List R × Cache R) (t : σ) z, I t →
              (xs.foldlM (fun (acc : List R × Cache R) x => do
                  let (r, c2) ← tmrH g D sh fL fB op fos f x acc.2
                  pure (acc.1 ++ [r], c2)) acc).run t = .ok z → I z.2 := by
            intro xs
            induction xs with
            | nil => intro acc t z ht hz; cases hz; exact ht
            | cons x xs ihx =>
              intro acc t z ht hz
              simp only [List.foldlM_cons, StateT.run_bind] at hz
              obtain ⟨⟨q, t1⟩, hq, hz⟩ := ex_bind_ok hz
              obtain ⟨⟨q', t2⟩, hq', hq⟩ := ex_bind_ok hq
              have ht2 := ih x acc.2 t (q', t2) ht hq'
              cases hq
              exact ihx _ _ _ ht2 hz
          have hs4 := hfold _ _ _ _ hs2 hf
          obtain ⟨⟨r, s5⟩, hr, hrc⟩ := ex_bind_ok hrc
          cases hrc
          exact hO _ _ _ _ hs4 hr
      split at h <;> (cases h; exact hs1)

/-- `copy_node` on a plain `Node` keeps every fresh children tuple within `D` slots. -/
theorem slotsLe_copy {D N fuel r0 r : Nat} {g h : SGraph T} (hI : SlotsLe D N g)
    (hc : copyNodeH g D false false fuel r0 = .ok (r, h)) : SlotsLe D N h := by
  unfold copyNodeH treeMapreduceH at hc
  simp only [StateT.run_bind] at hc
  obtain ⟨⟨⟨x, C⟩, h1⟩, ht, hc⟩ := ex_bind_ok hc
  cases hc
  refine tmrH_inv g D (false && !false) leafCopyH (fun a _ => pure a) (branchCopyH D)
    (fun r _ => r) (SlotsLe D N) ?_ ?_ ?_ fuel r0 [] g _ hI ht
  · intro a c s y hs hy
    unfold leafCopyH at hy
    split at hy
    · split at hy
      · cases hy; exact slotsLe_alloc hs _ (fun _ h => by cases h)
      · cases hy
    · cases hy; exact slotsLe_alloc hs _ (fun _ h => by cases h)
  · intro a c s y hs hy; cases hy; exact hs
  · intro src rs s y hs hy
    obtain ⟨c, _, hy⟩ := ex_bind_ok hy
    obtain ⟨r', h'⟩ := y
    exact slotsLe_ctor hs hy

/-! ### Replacing one child reference in an alias-free tree -/

theorem repl_heap (G G' : Graph T) (p x : Addr) (j : Nat) (cp : Cell T) (u : Tree T)
    (F : Nat) (hp : G.cells p = some cp) (hj : j < cp.children.length)
    (hp' : G'.cells p = some { cp with children := cp.children.set j x })
    (hoth : ∀ b, b ≠ p → G'.cells b = G.cells b)
    (hx : Graph.unfold G' F x = some u) :
    ∀ f a t, Graph.unfold G f a = some t → Graph.NoAlias G a → ∀ P t',
      Graph.Path G a P p → ReplPath t (P ++ [j]) u t' → Graph.unfold G' (f + F) a = some t' := by
  have frame : ∀ f b tb, Graph.unfold G f b = some tb → ¬ Graph.Reachable G b p →
      ∀ f', f ≤ f' → Graph.unfold G' f' b = some tb := by
    intro f b tb hb hnr f' hf
    have e : Graph.unfold G' f b = Graph.unfold G f b :=
      unfold_agree f b (fun y hy => hoth y (fun hyp => hnr (hyp ▸ hy)))
    exact unfold_mono _ _ _ (e.trans hb) f' hf
  intro f
  induction f with
  | zero => intro a t hu; simp [Graph.unfold] at hu
  | succ f ih =>
    intro a t hu hna P t' hP hR
    obtain ⟨c, hc, hl, hcase⟩ := unfold_succG hu
    rw [show f + 1 + F = (f + F) + 1 by omega]
    cases P with
    | nil =>
      have hap := path_nil_inv hP
      subst hap
      rw [hp] at hc; cases hc
      obtain ⟨o, cs, cj, cj', rfl, hcj, hRj, rfl⟩ := replPath_cons_inv hR
      have hcj' := replPath_nil_inv hRj
      subst hcj'
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, heq⟩
      · omega
      · cases heq
        refine unfold_of_cell hp' (by simp [hl]) (Or.inr ⟨hd, cs.set j cj', ?_, rfl⟩)
        apply mapM_of_get _ _ _ (by simp [mapM_length _ _ _ hts])
        intro m y v hy hv
        by_cases hmj : j = m
        · subst hmj
          simp [hj] at hy
          have hjc : j < cs.length := by rw [mapM_length _ _ _ hts]; exact hj
          simp [hjc] at hv
          subst hy; subst hv
          exact unfold_mono _ _ _ hx _ (by omega)
        · simp [hmj] at hy hv
          obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts m y hy
          rw [hv] at hv'; cases hv'
          exact frame f y v hyv (noAlias_child_not_reach hna hp (List.mem_of_getElem? hy)) _
            (by omega)
    | cons i P' =>
      obtain ⟨c0, b, hc0, hb, hP'⟩ := path_cons_inv hP
      rw [hc] at hc0; cases hc0
      have hap : a ≠ p := by
        intro he; subst he
        have := hna.acyclic a (reach_refl _ _) _ hP
        simp at this
      obtain ⟨o, cs, ci, ci', rfl, hci, hRi, rfl⟩ := replPath_cons_inv hR
      rcases hcase with ⟨hd, _⟩ | ⟨hd, ts, hts, heq⟩
      · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hb; simp at hb
      · cases heq
        have hca : G'.cells a = some c := by rw [hoth a hap, hc]
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
          exact ih b ci hyv (noAlias_child hna hc (List.mem_of_getElem? hb)) P' _ hP' hRi
        · simp [hmi] at hv
          obtain ⟨v', hv', hyv⟩ := mapM_get _ _ _ hts m y hy
          rw [hv] at hv'; cases hv'
          refine frame f y v hyv ?_ _ (by omega)
          intro ⟨Q, hQ⟩
          have := hna (m :: Q) (i :: P') p (.cons hc hy hQ) hP
          simp at this
          exact hmi this.1.symm

theorem reach_set (G G' : Graph T) (p x : Addr) (j : Nat) (cp : Cell T)
    (hp : G.cells p = some cp)
    (hp' : G'.cells p = some { cp with children := cp.children.set j x })
    (hoth : ∀ b, b ≠ p → G'.cells b = G.cells b) :
    ∀ {a P z}, Graph.Path G' a P z → Graph.Reachable G a z ∨ Graph.Reachable G x z := by
  intro a P z hpath
  induction hpath with
  | nil a => exact Or.inl (reach_refl _ _)
  | @cons a b z i P c hc hi _ ih =>
    by_cases hap : a = p
    · subst hap
      rw [hp'] at hc; cases hc
      by_cases hij : j = i
      · subst hij
        simp [List.getElem?_set] at hi
        obtain ⟨_, rfl⟩ := hi
        exact Or.inr (ih.elim id id)
      · have hi' : cp.children[i]? = some b := by simpa [List.getElem?_set, hij] using hi
        exact ih.elim (fun h => Or.inl (reach_trans (reach_child hp hi') h)) Or.inr
    · rw [hoth a hap] at hc
      exact ih.elim (fun h => Or.inl (reach_trans (reach_child hc hi) h)) Or.inr

/-! ### Located trees -/

/-- A tree that unfolds to `t`, is alias-free, and whose objects lie in `[lo, hi)`. -/
def Loc (h : SGraph T) (fuel : Nat) (r : Addr) (t : Tree T) (lo hi : Nat) : Prop :=
  Graph.unfold h.view fuel r = some t ∧ Graph.NoAlias h.view r ∧
    ∀ b : Nat, Graph.Reachable h.view r b → lo ≤ b ∧ b < hi

theorem loc_kids {h h' : SGraph T} {fuel r lo hi} {t : Tree T}
    (hL : Loc h fuel r t lo hi) (hp : ∀ b, lo ≤ b → b < hi → h'.cells b = h.cells b) :
    ∀ x, Graph.Reachable h.view r x → h'.view.cells x = h.view.cells x := by
  intro x hx
  have := hL.2.2 x hx
  simp [SGraph.view, hp x this.1 this.2]

theorem loc_transfer {h h' : SGraph T} {fuel r lo hi} {t : Tree T}
    (hL : Loc h fuel r t lo hi) (hp : ∀ b, lo ≤ b → b < hi → h'.cells b = h.cells b) :
    Loc h' fuel r t lo hi := by
  have hag := loc_kids hL hp
  have hs := sameKids_of_agree hag
  refine ⟨by rw [unfold_agree fuel r hag]; exact hL.1, noAlias_transfer hs hL.2.1,
    fun b hrb => hL.2.2 b ((reach_transfer hs).mp hrb)⟩

theorem loc_sub {h : SGraph T} {fuel r n lo hi} {t u : Tree T}
    (hL : Loc h fuel r t lo hi) (hrn : Graph.Reachable h.view r n)
    (hu : Graph.unfold h.view fuel n = some u) : Loc h fuel n u lo hi :=
  ⟨hu, noAlias_reach hL.2.1 hrn, fun b hb => hL.2.2 b (reach_trans hrn hb)⟩

theorem copy_spec (g : SGraph T) (D fuel r0 : Nat) (t : Tree T)
    (hu : Graph.unfold g.view fuel r0 = some t) (hw : t.WF D (fun _ => 255) 65535) :
    ∃ (r : Nat) (h : SGraph T), copyNodeH g D false false fuel r0 = .ok (r, h) ∧
      (∀ a, a < g.next → h.cells a = g.cells a) ∧ Loc h fuel r t g.next h.next ∧
      g.next ≤ h.next := by
  obtain ⟨r, h, hc, hpres, hu', hfresh, hna, _⟩ :=
    copy_node_heap_holds T g D fuel r0 t false false hu hw
  have hcl : Closed h.view r := closed_unfold fuel r t hu'
  have hlt : ∀ b : Nat, Graph.Reachable h.view r b → b < h.next := fun b hb => closed_lt hcl hb
  refine ⟨r, h, hc, hpres, ⟨hu', hna rfl, fun b hb => ⟨hfresh b hb, hlt b hb⟩⟩, ?_⟩
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hfresh r (reach_refl _ _)) (hlt r (reach_refl _ _)))

end SymReg.Mutations
