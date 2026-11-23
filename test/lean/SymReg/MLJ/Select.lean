import SymReg.MLJ.Core

namespace SymReg.MLJ
open DynExpr SymReg.HofMig
open DynExpr.Expressions.Sampling (greater)

/-! ## Order facts for JF -/

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  Rat.not_le.mp fun h => (Rat.not_le.mpr h1) (Rat.le_trans (Rat.le_of_lt h2) h)

theorem rat_lt_total {x y : Rat} (h : x ≠ y) : x < y ∨ y < x := by
  rcases Rat.le_total (a := x) (b := y) with h1 | h1
  · rcases Rat.le_iff_lt_or_eq.mp h1 with h2 | h2
    · exact .inl h2
    · exact absurd h2 h
  · rcases Rat.le_iff_lt_or_eq.mp h1 with h2 | h2
    · exact .inr h2
    · exact absurd h2.symm h

theorem less_irrefl (a : JF) : less a a = false := by
  cases a <;> simp [less, greater, Rat.lt_irrefl]

theorem less_trans {a b c : JF} (hab : less a b = true) (hbc : less b c = true) :
    less a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [less, greater] <;> exact rat_lt_trans hab hbc

theorem less_total {a b : JF} (ha : a ≠ .nan) (hb : b ≠ .nan) (hne : a ≠ b) :
    less a b = true ∨ less b a = true := by
  cases a <;> cases b <;> simp_all [less, greater]
  exact rat_lt_total hne

theorem isLess_eq {a b : JF} (ha : a ≠ .nan) (hb : b ≠ .nan) : isLess a b = less a b := by
  cases a <;> cases b <;> simp_all [isLess]

theorem isGreater_eq {a b : JF} (ha : a ≠ .nan) (hb : b ≠ .nan) : isGreater a b = less b a := by
  simp [isGreater, ha, hb, isLess_eq hb ha]

/-! ## The find fold -/

/-- A strict total order on non-NaN values, read as "`R m x`: `x` replaces `m`". -/
structure Better (R : JF → JF → Bool) : Prop where
  irrefl : ∀ a, a ≠ .nan → R a a = false
  trans : ∀ a b c, a ≠ .nan → b ≠ .nan → c ≠ .nan → R a b = true → R b c = true → R a c = true
  total : ∀ a b, a ≠ .nan → b ≠ .nan → a ≠ b → R a b = true ∨ R b a = true

theorem better_isLess : Better isLess where
  irrefl a ha := by rw [isLess_eq ha ha]; exact less_irrefl a
  trans a b c ha hb hc h1 h2 := by
    rw [isLess_eq ha hb] at h1; rw [isLess_eq hb hc] at h2; rw [isLess_eq ha hc]
    exact less_trans h1 h2
  total a b ha hb hne := by rw [isLess_eq ha hb, isLess_eq hb ha]; exact less_total ha hb hne

theorem better_isGreater : Better isGreater where
  irrefl a ha := by rw [isGreater_eq ha ha]; exact less_irrefl a
  trans a b c ha hb hc h1 h2 := by
    rw [isGreater_eq ha hb] at h1; rw [isGreater_eq hb hc] at h2; rw [isGreater_eq ha hc]
    exact less_trans h2 h1
  total a b ha hb hne := by
    rw [isGreater_eq ha hb, isGreater_eq hb ha]; exact (less_total ha hb hne).symm

/-- The fold invariant: `m` is at one-based `im`, nothing in `pre` replaces it,
and every earlier entry is replaced by it. -/
def Inv (R : JF → JF → Bool) (pre : List JF) (m : JF) (im : Nat) : Prop :=
  1 ≤ im ∧ pre[im - 1]? = some m ∧ (∀ (j : Nat) x, pre[j]? = some x → R m x = false) ∧
    (∀ (j : Nat) x, j < im - 1 → pre[j]? = some x → R x m = true)

theorem lt_of_get {l : List α} {j : Nat} {x : α} (h : l[j]? = some x) : j < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem get_snoc {pre : List α} {y x : α} {j : Nat} (h : (pre ++ [y])[j]? = some x) :
    (j < pre.length ∧ pre[j]? = some x) ∨ (j = pre.length ∧ x = y) := by
  by_cases hj : j < pre.length
  · left; rw [List.getElem?_append_left hj] at h; exact ⟨hj, h⟩
  · right
    rw [List.getElem?_append_right (by omega)] at h
    have : j - pre.length = 0 ∨ j - pre.length = (j - pre.length - 1) + 1 := by omega
    rcases this with hk | hk
    · rw [hk] at h; simp at h; exact ⟨by omega, h.symm⟩
    · rw [hk] at h; simp at h

theorem findAux_inv (R : JF → JF → Bool) (hR : Better R) : ∀ (xs pre : List JF) (m : JF) (im : Nat),
    (∀ x ∈ pre ++ xs, x ≠ .nan) → Inv R pre m im →
    Inv R (pre ++ xs) (findAux R (m, im) xs (pre.length + 1)).1
      (findAux R (m, im) xs (pre.length + 1)).2 := by
  intro xs
  induction xs with
  | nil => intro pre m im _ h; simpa [findAux] using h
  | cons y ys ih =>
    intro pre m im hn ⟨h1, h2, h3, h4⟩
    have hm : m ≠ .nan := hn m (List.mem_append_left _ (List.mem_of_getElem? h2))
    have hy : y ≠ .nan := hn y (by simp)
    have hpre : ∀ (j : Nat) (x : JF), pre[j]? = some x → x ≠ .nan := fun j x h =>
      hn x (List.mem_append_left _ (List.mem_of_getElem? h))
    have hn' : ∀ x ∈ pre ++ [y] ++ ys, x ≠ .nan := by
      intro x hx; exact hn x (by simpa using hx)
    by_cases hmy : R m y = true
    · have key : Inv R (pre ++ [y]) y (pre.length + 1) := by
        refine ⟨by omega, by simp, ?_, ?_⟩
        · intro j x hj
          rcases get_snoc hj with ⟨_, hx⟩ | ⟨_, rfl⟩
          · cases hyx : R y x
            · rfl
            · have := hR.trans m y x hm hy (hpre j x hx) hmy hyx
              rw [h3 j x hx] at this; cases this
          · exact hR.irrefl x hy
        · intro j x hj hx
          rcases get_snoc hx with ⟨_, hx⟩ | ⟨h, _⟩
          · have hxn := hpre j x hx
            by_cases hxm : x = m
            · subst hxm; exact hmy
            · rcases hR.total x m hxn hm hxm with h' | h'
              · exact hR.trans x m y hxn hm hy h' hmy
              · rw [h3 j x hx] at h'; cases h'
          · omega
      have := ih (pre ++ [y]) y (pre.length + 1) hn' key
      simpa [findAux, hmy, List.append_assoc] using this
    · have hmy' : R m y = false := by simpa using hmy
      have key : Inv R (pre ++ [y]) m im := by
        have hlt := lt_of_get h2
        refine ⟨h1, by rw [List.getElem?_append_left hlt]; exact h2, ?_, ?_⟩
        · intro j x hj
          rcases get_snoc hj with ⟨_, hx⟩ | ⟨_, rfl⟩
          · exact h3 j x hx
          · exact hmy'
        · intro j x hj hx
          rw [List.getElem?_append_left (by omega)] at hx
          exact h4 j x hj hx
      have := ih (pre ++ [y]) m im hn' key
      simpa [findAux, hmy', List.append_assoc] using this

theorem find_spec (R : JF → JF → Bool) (hR : Better R) (x : JF) (xs : List JF)
    (hn : ∀ y ∈ x :: xs, y ≠ .nan) :
    Inv R (x :: xs) (findAux R (x, 1) xs 2).1 (findAux R (x, 1) xs 2).2 := by
  have hx : x ≠ .nan := hn x (by simp)
  have := findAux_inv R hR xs [x] x 1 (by simpa using hn) ⟨Nat.le_refl _, by simp, ?_, ?_⟩
  · simpa using this
  · intro j y hj
    cases j with
    | zero => simp at hj; subst hj; exact hR.irrefl _ hx
    | succ j => simp at hj
  · intro j y hj; omega

/-- Spec of a successful find over a non-NaN list. -/
theorem find_result (R : JF → JF → Bool) (hR : Better R) (x : JF) (xs : List JF)
    (hn : ∀ y ∈ x :: xs, y ≠ .nan) :
    ∃ v, (x :: xs)[(findAux R (x, 1) xs 2).2 - 1]? = some v ∧ 1 ≤ (findAux R (x, 1) xs 2).2 ∧
      (findAux R (x, 1) xs 2).2 ≤ (x :: xs).length ∧
      (∀ (j : Nat) y, (x :: xs)[j]? = some y → R v y = false) ∧
      (∀ (j : Nat) y, j < (findAux R (x, 1) xs 2).2 - 1 → (x :: xs)[j]? = some y → R y v = true) := by
  obtain ⟨h1, h2, h3, h4⟩ := find_spec R hR x xs hn
  have := lt_of_get h2
  exact ⟨_, h2, h1, by omega, h3, h4⟩

/-! ## minimum -/

theorem jmin_eq {a b : JF} (ha : a ≠ .nan) (hb : b ≠ .nan) :
    jmin a b = if less b a then b else a := by simp [jmin, ha, hb]

theorem foldl_jmin (xs : List JF) : ∀ x, (∀ y ∈ x :: xs, y ≠ .nan) →
    xs.foldl jmin x ∈ x :: xs ∧ ∀ y ∈ x :: xs, less y (xs.foldl jmin x) = false := by
  induction xs with
  | nil => intro x _; simp [less_irrefl]
  | cons y ys ih =>
    intro x hn
    have hx := hn x (by simp)
    have hy := hn y (by simp)
    simp only [List.foldl_cons]
    by_cases hyx : less y x = true
    · rw [jmin_eq hx hy, if_pos hyx]
      obtain ⟨hm, hl⟩ := ih y (fun w hw => hn w (List.mem_cons_of_mem x hw))
      refine ⟨List.mem_cons_of_mem x hm, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with hwx | hw
      · rw [hwx]
        cases hwm : less x (ys.foldl jmin y)
        · rfl
        · have := less_trans hyx hwm; rw [hl y (by simp)] at this; cases this
      · exact hl w hw
    · rw [jmin_eq hx hy, if_neg hyx]
      have hsub : ∀ w, w ∈ x :: ys → w ∈ x :: y :: ys := by
        intro w hw
        rcases List.mem_cons.mp hw with h | h
        · rw [h]; simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      obtain ⟨hm, hl⟩ := ih x (fun w hw => hn w (hsub w hw))
      refine ⟨hsub _ hm, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with hwx | hw
      · rw [hwx]; exact hl x (by simp)
      · rcases List.mem_cons.mp hw with hwy | hw
        · rw [hwy]
          cases hwm : less y (ys.foldl jmin x)
          · rfl
          · by_cases hxy : x = y
            · rw [← hxy, hl x (by simp)] at hwm; cases hwm
            · rcases less_total hx hy hxy with h | h
              · have := less_trans h hwm; rw [hl x (by simp)] at this; cases this
              · exact absurd h hyx
        · exact hl w (List.mem_cons_of_mem _ hw)

theorem jmin_ne_nan {a b : JF} (ha : a ≠ .nan) (hb : b ≠ .nan) : jmin a b ≠ .nan := by
  rw [jmin_eq ha hb]; split <;> assumption

/-! ## The masked scores -/

def mask (t : JF) (losses scores : List JF) : List JF :=
  List.zipWith (fun l s => if lessEq l t then s else .negInf) losses scores

theorem maskScores_ok (t : JF) : ∀ (ls ss : List JF), ls.length ≤ ss.length →
    maskScores t ls ss = .ok (mask t ls ss) := by
  intro ls
  induction ls with
  | nil => intro ss _; rfl
  | cons l ls ih =>
    intro ss hlen
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      have := ih ss (by simp at hlen; omega)
      cases h : lessEq l t <;>
        simp [maskScores, mask, h, this, bind, Except.bind, pure, Except.pure] <;> rfl

theorem mask_get (t : JF) : ∀ (ls ss : List JF) (j : Nat) (l s : JF), ls[j]? = some l →
    ss[j]? = some s → (mask t ls ss)[j]? = some (if lessEq l t then s else .negInf) := by
  intro ls
  induction ls with
  | nil => intro ss j l s h; simp at h
  | cons a ls ih =>
    intro ss j l s hl hs
    cases ss with
    | nil => simp at hs
    | cons b ss =>
      cases j with
      | zero => simp at hl hs; subst hl; subst hs; simp [mask]
      | succ j => simpa [mask] using ih ss j l s (by simpa using hl) (by simpa using hs)

theorem mask_get_inv (t : JF) : ∀ (ls ss : List JF) (j : Nat) (v : JF), (mask t ls ss)[j]? = some v →
    ∃ l s, ls[j]? = some l ∧ ss[j]? = some s ∧ v = if lessEq l t then s else .negInf := by
  intro ls
  induction ls with
  | nil => intro ss j v h; simp [mask] at h
  | cons a ls ih =>
    intro ss j v h
    cases ss with
    | nil => simp [mask] at h
    | cons b ss =>
      cases j with
      | zero => simp [mask] at h; exact ⟨a, b, rfl, rfl, h.symm⟩
      | succ j => simpa using ih ss j v (by simpa [mask] using h)

/-! ## Threshold facts -/

theorem lessEq_threshold (m : JF) (hm : m ≠ .nan) (hpos : less m (.fin 0) = false) :
    lessEq m (.fin (3 / 2) * m) = true := by
  cases m with
  | nan => exact absurd rfl hm
  | posInf => decide +kernel
  | negInf => simp [less, greater] at hpos
  | fin q =>
    have hq : 0 ≤ q := by simpa [less, greater, Rat.not_lt] using hpos
    have hle : q ≤ 3 / 2 * q := by
      have := Rat.mul_le_mul_of_nonneg_left (a := 1) (b := 3 / 2) (c := q) (by decide +kernel) hq
      simpa [Rat.mul_one, Rat.mul_comm] using this
    rcases Rat.le_iff_lt_or_eq.mp hle with h | h
    · simp [lessEq, less, greater, jf_finite_mul, h]
    · simp [lessEq, jf_finite_mul, ← h]

theorem negInf_isLess {s : JF} (hs : s ≠ .nan) (hs' : s ≠ .negInf) : isLess .negInf s = true := by
  cases s <;> simp_all [isLess, less, greater]

end SymReg.MLJ
