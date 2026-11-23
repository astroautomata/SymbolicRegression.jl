import SymReg.Loss.Core

namespace SymReg.Loss
open DynExpr

attribute [local semireducible] Rat.add Rat.mul Rat.inv

private theorem pow2_lt {a b : Int} (h : a < b) : pow2 a < pow2 b := by
  have h₁ : pow2 a < pow2 (a + 1) := by
    rw [pow2_add, show pow2 1 = 2 by decide]
    have hp := pow2_pos a
    grind
  have hm := pow2_mono (show a + 1 ≤ b by omega)
  grind

private theorem pow2_nat (n : Nat) : pow2 (n : Int) = ((2^n : Nat) : Rat) := by
  rw [pow2_zpow, Rat.zpow_natCast, Rat.natCast_pow]
  rfl

private def floorExp (m : Rat) : Int :=
  let guess := (m.num.natAbs.log2 : Int) - (m.den.log2 : Int)
  if m < pow2 guess then guess - 1 else guess

private theorem floorExp_spec {m : Rat} (hm : 0 < m) :
    pow2 (floorExp m) ≤ m ∧ m < pow2 (floorExp m + 1) := by
  let a := m.num.natAbs
  let b := m.den
  let guess : Int := (a.log2 : Int) - (b.log2 : Int)
  have hcast : (a : Int) = m.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (Rat.le_of_lt hm))
  have hb := Rat.natCast_pos.mpr m.den_pos
  have hprod : m * (b : Rat) = (a : Rat) := by
    conv => lhs; lhs; rw [← Rat.num_divInt_den m, Rat.divInt_ofNat, Rat.mkRat_eq_div]
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hb), ← hcast, Rat.intCast_natCast]
  have hbot : ((2^b.log2 : Nat) : Rat) ≤ (b : Rat) :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le (by have := m.den_pos; omega))
  have htop : m * (b : Rat) < ((2^(a.log2 + 1) : Nat) : Rat) :=
    hprod ▸ Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  have hpow : pow2 (guess + 1) * (↑(2^b.log2 : Nat) : Rat) = (↑(2^(a.log2 + 1) : Nat) : Rat) := by
    rw [← pow2_nat, ← pow2_nat, ← pow2_add]
    congr 1
    dsimp [guess]
    omega
  change pow2 (if m < pow2 guess then guess - 1 else guess) ≤ m ∧
    m < pow2 ((if m < pow2 guess then guess - 1 else guess) + 1)
  split
  · rename_i h
    rw [show guess - 1 + 1 = guess by omega]
    exact ⟨pow2_guess_lower m hm, h⟩
  · rename_i h
    refine ⟨Rat.not_lt.mp h, (Rat.mul_lt_mul_right hb).mp ?_⟩
    have hle : m * (b : Rat) < pow2 (guess + 1) * (b : Rat) := by
      have hb' := Rat.mul_le_mul_of_nonneg_left hbot (Rat.le_of_lt (pow2_pos (guess + 1)))
      grind
    exact hle

private theorem floorExp_of_bounds {m : Rat} {e : Int} (hm : 0 < m)
    (hl : pow2 e ≤ m) (hu : m < pow2 (e + 1)) : floorExp m = e := by
  obtain ⟨hl', hu'⟩ := floorExp_spec hm
  by_cases h : floorExp m < e
  · have := pow2_mono (show floorExp m + 1 ≤ e by omega)
    grind
  · by_cases h : e < floorExp m
    · have := pow2_mono (show e + 1 ≤ floorExp m by omega)
      grind
    · omega

private def gridExp (p : LossPrecision) (m : Rat) : Int :=
  max (floorExp m) (1 - p.maxExponent)

private theorem ulp_of_nonneg (p : LossPrecision) {m : Rat} (hm : 0 ≤ m) :
    p.ulp m = pow2 (gridExp p m + 1 - (p.bits : Int)) := by
  simp [LossPrecision.ulp, gridExp, floorExp, Rat.not_lt.mpr hm]

private theorem nearest_natCast (n : Nat) : nearestEven (n : Rat) = n := by
  simp [nearestEven, Nat.mod_one]

private theorem nearest_mono {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    nearestEven a ≤ nearestEven b := by
  by_cases he : a = b
  · simp [he]
  have hlt := Rat.lt_of_le_of_ne hab he
  have ea := nearestEven_scaled_half a 1 ha (by decide)
  have eb := nearestEven_scaled_half b 1 (Rat.le_trans ha hab) (by decide)
  simp only [Rat.div_def, show (1 : Rat)⁻¹ = 1 by decide, Rat.mul_one] at ea eb
  apply Classical.byContradiction
  intro h
  have hh : nearestEven b + 1 ≤ nearestEven a := by omega
  have hstep : (nearestEven b : Rat) + 1 ≤ (nearestEven a : Rat) := by
    exact_mod_cast hh
  have la : (nearestEven a : Rat) - a ≤ 1 / 2 := by
    by_cases hna : 0 ≤ (nearestEven a : Rat) - a
    · rwa [Rat.abs_of_nonneg hna] at ea
    · have := Rat.not_le.mp hna
      have : (0 : Rat) < 1 / 2 := by decide
      grind
  have lb : b - (nearestEven b : Rat) ≤ 1 / 2 := by
    rw [Rat.abs_sub_comm] at eb
    by_cases hnb : 0 ≤ b - (nearestEven b : Rat)
    · rwa [Rat.abs_of_nonneg hnb] at eb
    · have := Rat.not_le.mp hnb
      have : (0 : Rat) < 1 / 2 := by decide
      grind
  grind

private def gridRound (p : LossPrecision) (m : Rat) : Rat :=
  (nearestEven (m / p.ulp m) : Rat) * p.ulp m

private theorem gridRound_zero (p : LossPrecision) : gridRound p 0 = 0 := by
  simp [gridRound, Rat.div_def, nearestEven]

private theorem gridRound_nonneg (p : LossPrecision) (m : Rat) : 0 ≤ gridRound p m :=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (p.ulp_pos _))

private theorem round_of_nonneg (p : LossPrecision) {m : Rat} (hm : 0 ≤ m) :
    p.round (.fin m) = if gridRound p m > p.maxFinite then .posInf else .fin (gridRound p m) := by
  by_cases hz : m = 0
  · subst m
    cases p <;> decide +kernel
  simp [LossPrecision.round, hz, Rat.not_lt.mpr hm, gridRound]

private theorem grid_multiple (p : LossPrecision) {e : Int} {n : Nat} (h : e + 1 - (p.bits : Int) + (n : Int) = e + 1) :
    ((2^n : Nat) : Rat) * pow2 (e + 1 - (p.bits : Int)) = pow2 (e + 1) := by
  rw [Rat.mul_comm, ← pow2_nat, ← pow2_add, h]

private theorem gridRound_le {m : Rat} (p : LossPrecision) (hm : 0 ≤ m) :
    gridRound p m ≤ pow2 (gridExp p m + 1) := by
  have hm' : m ≤ pow2 (gridExp p m + 1) := by
    by_cases hz : m = 0
    · rw [hz]; exact Rat.le_of_lt (pow2_pos _)
    · apply Rat.le_trans (Rat.le_of_lt (floorExp_spec (Rat.lt_of_le_of_ne hm (Ne.symm hz))).2)
      apply pow2_mono
      simp [gridExp]
      omega
  have htop : ((2^p.bits : Nat) : Rat) * p.ulp m = pow2 (gridExp p m + 1) := by
    rw [ulp_of_nonneg p hm]
    exact grid_multiple p (by omega)
  have hdiv : m / p.ulp m ≤ ((2^p.bits : Nat) : Rat) := by
    apply Rat.le_of_mul_le_mul_right _ (p.ulp_pos m)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt (p.ulp_pos m)), htop]
  have hn := nearest_mono (Rat.mul_nonneg hm (Rat.le_of_lt (Rat.inv_pos.mpr (p.ulp_pos m)))) hdiv
  rw [nearest_natCast] at hn
  unfold gridRound
  rw [← htop]
  exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hn) (Rat.le_of_lt (p.ulp_pos m))

private theorem gridRound_ge {m : Rat} (p : LossPrecision) (hm : 0 ≤ m)
    (hb : pow2 (gridExp p m) ≤ m) : pow2 (gridExp p m) ≤ gridRound p m := by
  have hbits : 1 ≤ p.bits := by cases p <;> decide
  have hbot : ((2^(p.bits - 1) : Nat) : Rat) * p.ulp m = pow2 (gridExp p m) := by
    rw [ulp_of_nonneg p hm, Rat.mul_comm, ← pow2_nat, ← pow2_add]
    congr 1
    omega
  have hdiv : ((2^(p.bits - 1) : Nat) : Rat) ≤ m / p.ulp m := by
    apply Rat.le_of_mul_le_mul_right _ (p.ulp_pos m)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt (p.ulp_pos m)), hbot]
  have hn := nearest_mono Rat.natCast_nonneg hdiv
  rw [nearest_natCast] at hn
  unfold gridRound
  rw [← hbot]
  exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hn) (Rat.le_of_lt (p.ulp_pos m))

private theorem grid_mono (p : LossPrecision) {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    gridRound p a ≤ gridRound p b := by
  have hb := Rat.le_trans ha hab
  by_cases hz : a = 0
  · subst a
    rw [gridRound_zero]
    exact gridRound_nonneg p b
  have ha' := Rat.lt_of_le_of_ne ha (Ne.symm hz)
  have hb' : 0 < b := by grind
  have hf : floorExp a ≤ floorExp b := by
    apply Classical.byContradiction
    intro h
    have hpow := pow2_mono (show floorExp b + 1 ≤ floorExp a by omega)
    have := (floorExp_spec ha').1
    have := (floorExp_spec hb').2
    grind
  have hg : gridExp p a ≤ gridExp p b := by unfold gridExp; omega
  by_cases he : gridExp p a = gridExp p b
  · have hu : p.ulp a = p.ulp b := by rw [ulp_of_nonneg p ha, ulp_of_nonneg p hb, he]
    unfold gridRound
    rw [hu]
    apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (p.ulp_pos b))
    apply Rat.natCast_le_natCast.mpr
    apply nearest_mono (Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr (p.ulp_pos b))))
    exact Rat.mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (Rat.inv_pos.mpr (p.ulp_pos b)))
  · have hg' : gridExp p a + 1 ≤ gridExp p b := by omega
    have hge : pow2 (gridExp p b) ≤ b := by
      have hemin : 1 - p.maxExponent ≤ gridExp p a := by unfold gridExp; omega
      have h : gridExp p b = floorExp b := by unfold gridExp at *; omega
      rw [h]
      exact (floorExp_spec hb').1
    exact Rat.le_trans (gridRound_le p ha) (Rat.le_trans (pow2_mono hg') (gridRound_ge p hb hge))

/-- Binary rounding is nonnegative on nonnegative inputs, including at overflow. -/
theorem LossPrecision.round_nonneg (p : LossPrecision) {m : Rat} (hm : 0 ≤ m) :
    p.round (.fin m) = .posInf ∨ ∃ r, p.round (.fin m) = .fin r ∧ 0 ≤ r := by
  rw [round_of_nonneg p hm]
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, gridRound_nonneg p m⟩

/-- If the upper rounded value is finite, nonnegative rounding cannot exceed it. -/
theorem LossPrecision.round_le_nonneg (p : LossPrecision) {a b y : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (h : p.round (.fin b) = .fin y) :
    ∃ x, p.round (.fin a) = .fin x ∧ 0 ≤ x ∧ x ≤ y := by
  have hmono := grid_mono p ha hab
  rw [round_of_nonneg p (Rat.le_trans ha hab)] at h
  split at h
  · contradiction
  · rename_i ht
    cases h
    refine ⟨_, ?_, gridRound_nonneg p a, hmono⟩
    rw [round_of_nonneg p ha, ite_eq_right (Rat.not_lt.mpr (Rat.le_trans hmono (Rat.not_lt.mp ht)))]

/-- If the lower rounded value is finite, increasing its input cannot lower it. -/
theorem LossPrecision.round_ge_nonneg (p : LossPrecision) {a b x : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (h : p.round (.fin a) = .fin x) :
    p.round (.fin b) = .posInf ∨ ∃ y, p.round (.fin b) = .fin y ∧ x ≤ y := by
  rw [round_of_nonneg p ha] at h
  split at h
  · contradiction
  · cases h
    rw [round_of_nonneg p (Rat.le_trans ha hab)]
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, grid_mono p ha hab⟩

/-- Binary rounding of a nonnegative finite result leaves it unchanged. -/
theorem LossPrecision.round_idempotent_nonneg (p : LossPrecision) {q r : Rat}
    (hq : 0 ≤ q) (hr : p.round (.fin q) = .fin r) : p.round (.fin r) = .fin r := by
  rw [round_of_nonneg p hq] at hr
  split at hr
  · contradiction
  · rename_i hmax
    cases hr
    let r := gridRound p q
    change p.round (.fin r) = .fin r
    have hr := gridRound_nonneg p q
    by_cases hz : r = 0
    · rw [hz]; rfl
    have hr' := Rat.lt_of_le_of_ne hr (Ne.symm hz)
    let e := gridExp p q
    have hu : r ≤ pow2 (e + 1) := gridRound_le p hq
    have hexact : gridRound p r = r := by
      suffices h : ∃ n : Nat, r = (n : Rat) * p.ulp r by
        obtain ⟨n, hn⟩ := h
        unfold gridRound
        have hd : r / p.ulp r = (n : Rat) := by
          conv => lhs; lhs; rw [hn]
          exact Rat.mul_div_cancel (Rat.ne_of_gt (p.ulp_pos r))
        rw [hd, nearest_natCast, ← hn]
      by_cases hb : r = pow2 (e + 1)
      · have hf : floorExp r = e + 1 :=
          floorExp_of_bounds hr' (by rw [hb]; exact Rat.le_refl) (by rw [hb]; apply pow2_lt; omega)
        have hemin : 1 - p.maxExponent ≤ e := by unfold e gridExp; omega
        have he : gridExp p r = e + 1 := by rw [gridExp, hf]; omega
        refine ⟨2^(p.bits - 1), ?_⟩
        have hbits : 1 ≤ p.bits := by cases p <;> decide
        rw [ulp_of_nonneg p hr, he, hb, Rat.mul_comm, ← pow2_nat, ← pow2_add]
        congr 1
        omega
      · have hlt : r < pow2 (e + 1) := Rat.lt_of_le_of_ne hu hb
        have hemax : floorExp r ≤ e := by
          apply Classical.byContradiction
          intro h
          have := pow2_mono (show e + 1 ≤ floorExp r by omega)
          have := (floorExp_spec hr').1
          grind
        have hemin : 1 - p.maxExponent ≤ e := by unfold e gridExp; omega
        have he : gridExp p r = e := by
          unfold gridExp
          by_cases he' : e = 1 - p.maxExponent
          · omega
          have hqe : e = floorExp q := by unfold e gridExp at *; omega
          have hq' : 0 < q := by
            apply Classical.byContradiction
            intro h
            have hzq : q = 0 := by grind
            change gridRound p q ≠ 0 at hz
            rw [hzq, gridRound_zero] at hz
            exact hz rfl
          have hlow : pow2 e ≤ r := by
            apply gridRound_ge p hq
            change pow2 e ≤ q
            rw [hqe]
            exact (floorExp_spec hq').1
          have hf : floorExp r = e := floorExp_of_bounds hr' hlow hlt
          rw [hf]
          omega
        have hqscale : p.ulp q = p.ulp r := by rw [ulp_of_nonneg p hq, ulp_of_nonneg p hr, he]
        refine ⟨nearestEven (q / p.ulp q), ?_⟩
        rw [← hqscale]
        rfl
    rw [round_of_nonneg p hr, hexact, ite_eq_right hmax]

end SymReg.Loss
