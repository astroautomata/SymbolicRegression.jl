import SymReg.Mutations.Props

/-!
Properties of the draw-only parts of `src/MutationFunctions.jl` that need no heap reasoning:
`_arity_picker`, the degree choice of `append_random_op`/`insert_random_op`/`prepend_random_op`,
the expression wrappers and `randomize_tree`.
-/

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase

variable {T : Type}

/-! ## Statements -/

/-- `limit = min(D, remaining)` of `_arity_picker` as the length of `1:limit`. -/
def arityLimit (remaining : Int) (nops : List Nat) : Nat := (min (nops.length : Int) remaining).toNat

/-- `_arity_picker(rng, remaining, nops)` returns `0` without a draw exactly when no operator has
arity at most `min(D, remaining)`; otherwise it makes one draw `thresh` uniform in `1:total` and
returns an arity `k` with `1 ≤ k ≤ min(D, remaining)` that has at least one operator. -/
def arity_picker_spec : Prop :=
  ∀ (T : Type) (remaining : Int) (nops : List Nat) (s : St T),
    ∃ k s', arityPicker remaining nops s = .ok (k, s') ∧
      (psum nops (arityLimit remaining nops) = 0 → k = 0 ∧ s' = s) ∧
      (psum nops (arityLimit remaining nops) ≠ 0 →
        1 ≤ k ∧ (k : Int) ≤ remaining ∧ k ≤ nops.length ∧ 0 < opsOf nops k ∧
        psum nops (k - 1) < rangeAt s.rng s.rng.cursor (psum nops (arityLimit remaining nops)) ∧
        rangeAt s.rng s.rng.cursor (psum nops (arityLimit remaining nops)) ≤ psum nops k ∧
        s'.g = s.g ∧ s'.rng = adv s.rng)

/-- The arity weights of `_arity_picker`: among the `total = sum(nops[1:limit])` equally likely
values of `thresh`, exactly `nops[k]` give arity `k`, for every `k` in `1:limit`. -/
def arity_picker_weights : Prop :=
  ∀ (nops : List Nat) (limit k : Nat), limit ≤ nops.length → 1 ≤ k → k ≤ limit →
    ((List.range' 1 (psum nops limit)).filter (fun th => arityScan nops th limit == k)).length =
      opsOf nops k

/-- The `@nif` degree choice of `append_random_op`, `insert_random_op` and `prepend_random_op`
(`scaled_rand = rand(rng) * last(csum)`) picks a degree with at least one operator for every
draw `rand(rng)` in `[0, 1)` when some operator exists. -/
def pick_degree_has_operator : Prop :=
  ∀ (nops : List Nat) (u : Rat), 1 ≤ nops.length → 0 < nops.sum → 0 ≤ u → u < 1 →
    0 < opsOf nops (pickDeg nops.length nops (scaledDegreeDraw u nops))

/-- For every `scaled_rand` strictly between `0` and `last(csum)`, the `@nif` degree choice picks
the degree `i` with `csum[i] < scaled_rand ≤ csum[i + 1]`; that degree has an operator. -/
def pick_degree_interval : Prop :=
  ∀ (nops : List Nat) (x : Rat), 1 ≤ nops.length → 0 < x → x < (nops.sum : Rat) →
    1 ≤ pickDeg nops.length nops x ∧ pickDeg nops.length nops x ≤ nops.length ∧
      (psum nops (pickDeg nops.length nops x - 1) : Rat) < x ∧
      x ≤ (psum nops (pickDeg nops.length nops x) : Rat) ∧
      0 < opsOf nops (pickDeg nops.length nops x)


/-- `randomize_tree(tree, curmaxsize, options, nfeatures, rng)` ignores its input tree: for any
two inputs it behaves identically, drawing a size uniformly in `1:curmaxsize` and then running
`gen_random_tree_fixed_size` with that size. -/
def randomize_tree_spec : Prop :=
  ∀ (T : Type) (D fuel nf : Nat) (nops : List Nat) (sv : Rat → T) (cm steps : Nat)
    (t1 t2 : Addr) (s : St T), 1 ≤ cm →
    randomizeTree D fuel nf nops (sampleReal sv) cm steps t1 s = randomizeTree D fuel nf nops (sampleReal sv) cm steps t2 s ∧
    randomizeTree D fuel nf nops (sampleReal sv) cm steps t1 s =
      genRandomTreeFixedSize D fuel nf nops (sampleReal sv) (rangeAt s.rng s.rng.cursor cm) steps
        { s with rng := adv s.rng }

/-! ## Lists -/

theorem find_range'_some {p : Nat → Bool} :
    ∀ (n a i : Nat), (List.range' a n).find? p = some i →
      a ≤ i ∧ i < a + n ∧ p i = true ∧ ∀ j, a ≤ j → j < i → p j = false
  | 0, a, i, h => by simp at h
  | n + 1, a, i, h => by
    rw [List.range'_succ, List.find?_cons] at h
    by_cases hp : p a = true
    · rw [hp] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hp, fun j h1 h2 => by omega⟩
    · rw [Bool.not_eq_true] at hp
      rw [hp] at h
      obtain ⟨h1, h2, h3, h4⟩ := find_range'_some n (a + 1) i h
      refine ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
      by_cases hja : j = a
      · subst hja; exact hp
      · exact h4 j (by omega) hj2

theorem find_range'_none {p : Nat → Bool} :
    ∀ (n a : Nat), (List.range' a n).find? p = none → ∀ j, a ≤ j → j < a + n → p j = false
  | 0, a, _, j, h1, h2 => by omega
  | n + 1, a, h, j, h1, h2 => by
    rw [List.range'_succ, List.find?_cons] at h
    by_cases hp : p a = true
    · rw [hp] at h; cases h
    · rw [Bool.not_eq_true] at hp
      rw [hp] at h
      by_cases hja : j = a
      · subst hja; exact hp
      · exact find_range'_none n (a + 1) h j (by omega) (by omega)

theorem psum_mono (nops : List Nat) {a b : Nat} (h : a ≤ b) : psum nops a ≤ psum nops b := by
  unfold psum
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  omega

theorem psum_succ (nops : List Nat) {k : Nat} (h : k < nops.length) :
    psum nops (k + 1) = psum nops k + opsOf nops (k + 1) := by
  unfold psum opsOf
  rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem h]
  simp [List.getElem?_eq_getElem h]

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Rat.not_le.mp (fun h => Rat.not_le.mpr h1 (Rat.le_trans h2 h))

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

theorem psum_zero (nops : List Nat) : psum nops 0 = 0 := by simp [psum]

theorem psum_length (nops : List Nat) : psum nops nops.length = nops.sum := by
  simp [psum]

theorem filter_singleton_length (p : Nat → Bool) (x : Nat) :
    ([x].filter p).length = if p x = true then 1 else 0 := by
  by_cases h : p x = true <;> simp [h]

/-- Interval counting in `1:n`. -/
theorem count_interval (a b : Nat) :
    ∀ n, a ≤ b → b ≤ n →
      ((List.range' 1 n).filter (fun th => decide (a < th ∧ th ≤ b))).length = b - a
  | 0, h1, h2 => by simp; omega
  | n + 1, h1, h2 => by
    rw [List.range'_concat, List.filter_append, List.length_append, filter_singleton_length]
    by_cases hb : b ≤ n
    · rw [count_interval a b n h1 hb, if_neg (by simp only [decide_eq_true_eq]; omega)]
      omega
    · have hbn : b = n + 1 := by omega
      subst hbn
      by_cases ha : a = n + 1
      · subst ha
        rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
        have : ((List.range' 1 n).filter (fun th => decide (n + 1 < th ∧ th ≤ n + 1))) = [] := by
          rw [List.filter_eq_nil_iff]; intro x _; simp only [decide_eq_true_eq]; omega
        rw [this]; simp
      · rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
        rw [show ((List.range' 1 n).filter (fun th => decide (a < th ∧ th ≤ n + 1))) =
            (List.range' 1 n).filter (fun th => decide (a < th ∧ th ≤ n)) from
            List.filter_congr (fun x hx => by
              simp only [List.mem_range'] at hx
              simp only [decide_eq_decide]; omega)]
        rw [count_interval a n n (by omega) (Nat.le_refl _)]
        omega

/-! ## `_arity_picker` -/

/-- `arityScan` returns `k` exactly when `thresh` lies in the `k`-th bucket. -/
theorem arityScan_iff (nops : List Nat) (th limit k : Nat) (hth : 1 ≤ th)
    (hth' : th ≤ psum nops limit) (hk : 1 ≤ k) (hkl : k ≤ limit) :
    arityScan nops th limit = k ↔ psum nops (k - 1) < th ∧ th ≤ psum nops k := by
  unfold arityScan
  cases hf : (List.range' 1 (limit - 1)).find? (fun k => decide (th ≤ psum nops k)) with
  | some i =>
    obtain ⟨hi1, hi2, hi3, hi4⟩ := find_range'_some _ _ _ hf
    simp only [decide_eq_true_eq] at hi3
    simp only [Option.getD_some]
    constructor
    · intro hik
      subst hik
      refine ⟨?_, hi3⟩
      by_cases h1 : i = 1
      · subst h1; simp [psum_zero]; omega
      · have := hi4 (i - 1) (by omega) (by omega)
        simp only [decide_eq_false_iff_not] at this
        omega
    · intro ⟨h1, h2⟩
      by_cases hlt : k < i
      · have := hi4 k hk hlt
        simp only [decide_eq_false_iff_not] at this
        omega
      · by_cases hgt : i < k
        · have := psum_mono nops (show i ≤ k - 1 by omega)
          omega
        · omega
  | none =>
    have hn := find_range'_none _ _ hf
    simp only [Option.getD_none]
    constructor
    · intro hk'
      subst hk'
      refine ⟨?_, hth'⟩
      by_cases h1 : limit = 1
      · subst h1; simp [psum_zero]; omega
      · have := hn (limit - 1) (by omega) (by omega)
        simp only [decide_eq_false_iff_not] at this
        omega
    · intro ⟨_, h2⟩
      by_cases hlt : k < limit
      · have := hn k hk (by omega)
        simp only [decide_eq_false_iff_not] at this
        omega
      · omega

theorem arity_picker_weights_holds : arity_picker_weights := by
  intro nops limit k hl hk hkl
  rw [show (List.range' 1 (psum nops limit)).filter (fun th => arityScan nops th limit == k) =
      (List.range' 1 (psum nops limit)).filter
        (fun th => decide (psum nops (k - 1) < th ∧ th ≤ psum nops k)) from
      List.filter_congr (fun th hth => by
        simp only [List.mem_range'] at hth
        have := arityScan_iff nops th limit k (by omega) (by omega) hk hkl
        by_cases h : arityScan nops th limit = k
        · simp [h, this.mp h]
        · have h' : ¬ (psum nops (k - 1) < th ∧ th ≤ psum nops k) := fun h' => h (this.mpr h')
          simp [h, h'])]
  rw [count_interval _ _ _ (psum_mono nops (by omega)) (psum_mono nops hkl)]
  have := psum_succ nops (k := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at this
  omega

theorem arity_picker_spec_holds : arity_picker_spec := by
  intro T remaining nops s
  by_cases h0 : psum nops (arityLimit remaining nops) = 0
  · refine ⟨0, s, ?_, fun _ => ⟨rfl, rfl⟩, fun h => absurd h0 h⟩
    simp only [arityPicker]
    rw [show (min (nops.length : Int) remaining).toNat = arityLimit remaining nops from rfl, h0]
    rfl
  · have hl : 1 ≤ arityLimit remaining nops := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, psum_zero] at h0
      exact h0 rfl
    have hll : arityLimit remaining nops ≤ nops.length := by
      unfold arityLimit; omega
    have hlr : (arityLimit remaining nops : Int) ≤ remaining := by
      unfold arityLimit at hl ⊢; omega
    let th := rangeAt s.rng s.rng.cursor (psum nops (arityLimit remaining nops))
    have hth1 : 1 ≤ th := by simp [th, rangeAt]
    have hth2 : th ≤ psum nops (arityLimit remaining nops) := by
      have := (s.rng.indexDraws (psum nops (arityLimit remaining nops) - 1) s.rng.cursor).isLt
      simp only [th, rangeAt]; omega
    let k := arityScan nops th (arityLimit remaining nops)
    have hk : 1 ≤ k ∧ k ≤ arityLimit remaining nops := by
      simp only [k, arityScan]
      cases hf : (List.range' 1 (arityLimit remaining nops - 1)).find?
          (fun k => decide (th ≤ psum nops k)) with
      | some i =>
        obtain ⟨hi1, hi2, _, _⟩ := find_range'_some _ _ _ hf
        simp only [Option.getD_some]; omega
      | none => simp only [Option.getD_none]; omega
    have hbk := (arityScan_iff nops th _ k hth1 hth2 hk.1 hk.2).mp rfl
    have hpos : 0 < opsOf nops k := by
      have := psum_succ nops (k := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at this
      omega
    refine ⟨k, { s with rng := adv s.rng }, ?_, fun h => absurd h h0, fun _ =>
      ⟨hk.1, by omega, by omega, hpos, hbk.1, hbk.2, rfl, rfl⟩⟩
    simp only [arityPicker]
    rw [show (min (nops.length : Int) remaining).toNat = arityLimit remaining nops from rfl,
      if_neg h0]
    show (randRange (T := T) (psum nops (arityLimit remaining nops)) >>= fun thresh =>
      pure (arityScan nops thresh (arityLimit remaining nops))) s = _
    rw [bindM (randRange_ok _ (by omega) s)]
    rfl

/-! ## Degree choice of `append_random_op`, `insert_random_op`, `prepend_random_op` -/

theorem natCast_lt {a b : Nat} (h : (a : Rat) < (b : Rat)) : a < b :=
  Rat.natCast_lt_natCast.mp h

theorem pick_degree_interval_holds : pick_degree_interval := by
  intro nops x hD hx hxt
  let D := nops.length
  have hpD : (psum nops D : Rat) = (nops.sum : Rat) := by simp [D, psum_length]
  unfold pickDeg
  cases hf : (List.range' 1 (nops.length - 1)).find?
      (fun i => decide ((psum nops (i - 1) : Rat) < x ∧ x ≤ (psum nops i : Rat))) with
  | some i =>
    obtain ⟨hi1, hi2, hi3, _⟩ := find_range'_some _ _ _ hf
    simp only [decide_eq_true_eq] at hi3
    simp only [Option.getD_some]
    have hlt : psum nops (i - 1) < psum nops i :=
      natCast_lt (rat_lt_of_lt_of_le hi3.1 hi3.2)
    have := psum_succ nops (k := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    exact ⟨hi1, by omega, hi3.1, hi3.2, by omega⟩
  | none =>
    have hn := find_range'_none _ _ hf
    simp only [Option.getD_none]
    -- every bucket below `D` lies below `x`
    have hbelow : ∀ i, i < nops.length → (psum nops i : Rat) < x := by
      intro i
      induction i with
      | zero => intro _; simp [psum_zero]; exact hx
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have := hn (i + 1) (by omega) (by omega)
        simp only [decide_eq_false_iff_not, Nat.add_sub_cancel] at this
        exact Rat.not_le.mp (fun hle => this ⟨hprev, hle⟩)
    have hb := hbelow (nops.length - 1) (by omega)
    have hxt' : x < (psum nops nops.length : Rat) := by rw [psum_length]; exact hxt
    have hlt : psum nops (nops.length - 1) < psum nops nops.length :=
      natCast_lt (rat_lt_trans hb hxt')
    have := psum_succ nops (k := nops.length - 1) (by omega)
    rw [show nops.length - 1 + 1 = nops.length by omega] at this
    exact ⟨hD, Nat.le_refl _, hb, Rat.le_of_lt hxt', by omega⟩

/-! ## Expression wrappers and `randomize_tree` -/


theorem randomize_tree_spec_holds : randomize_tree_spec := by
  intro T D fuel nf nops sv cm steps t1 t2 s hcm
  refine ⟨rfl, ?_⟩
  simp only [randomizeTree]
  rw [bindM (randRange_ok cm hcm s)]
  rfl

end SymReg.Mutations
