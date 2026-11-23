import SymReg.Loss.Core

namespace SymReg.Loss
open DynExpr

private theorem nearestEven_natCast (n : Nat) : nearestEven (n : Rat) = n := by
  simp [nearestEven, Nat.mod_one]

theorem LossPrecision.round_float64_int (n : Int) (hn : n.natAbs ≤ 2 ^ 53) :
    LossPrecision.float64.round (.fin (n : Rat)) = .fin (n : Rat) := by
  let q := (n : Rat)
  let a := n.natAbs
  have hm : (if q < 0 then -q else q) = (a : Rat) := by
    change (if (n : Rat) < 0 then -(n : Rat) else (n : Rat)) = (n.natAbs : Rat)
    by_cases h : n < 0
    · rw [ite_eq_left (Rat.intCast_neg_iff.mpr h), ← Rat.intCast_natCast,
        Int.ofNat_natAbs_of_nonpos (by omega), Rat.intCast_neg]
    · rw [ite_eq_right (fun hq => h (Rat.intCast_neg_iff.mp hq)), ← Rat.intCast_natCast,
        Int.natAbs_of_nonneg (by omega)]
  change LossPrecision.float64.round (.fin q) = .fin q
  by_cases hz : q = 0
  · simp [hz, LossPrecision.round]
  let p := LossPrecision.float64
  have ha0 : a ≠ 0 := by
    intro h
    have hn0 := Int.natAbs_eq_zero.mp h
    exact hz (by simp [q, hn0])
  have hs : p.ulp q = pow2 (max (a.log2 : Int) (-1022) - 52) := by
    have hlog : pow2 (a.log2 : Int) ≤ (a : Rat) := by
      rw [pow2_zpow, Rat.zpow_natCast, ← Rat.natCast_ofNat (a := 2), ← Rat.natCast_pow,
        Rat.natCast_le_natCast]
      exact Nat.log2_self_le ha0
    simp only [LossPrecision.ulp, hm, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast,
      show Nat.log2 1 = 0 by decide, Int.natCast_zero, Int.sub_zero,
      ite_eq_right (Rat.not_lt.mpr hlog)]
    change pow2 (max (a.log2 : Int) (-1022) + 1 - 53) = _
    congr 1
    omega
  have hgrid : ∃ k : Nat, (a : Rat) = (k : Rat) * p.ulp q := by
    rw [hs]
    by_cases he : a < 2 ^ 53
    · have hl : a.log2 < 53 := (Nat.log2_lt ha0).mpr he
      let e := 52 - a.log2
      have hExp : max (a.log2 : Int) (-1022) - 52 = -(e : Int) := by
        dsimp [e]
        omega
      refine ⟨a * 2 ^ e, ?_⟩
      rw [hExp, pow2_zpow, Rat.zpow_neg, Rat.zpow_natCast, Rat.natCast_mul,
        Rat.natCast_pow, Rat.natCast_ofNat, Rat.mul_assoc, Rat.mul_inv_cancel _ (by
          exact Rat.ne_of_gt (Rat.pow_pos (by decide))), Rat.mul_one]
    · have ha : a = 2 ^ 53 := by omega
      rw [ha]
      exact ⟨2 ^ 52, by decide +kernel⟩
  obtain ⟨k, hk⟩ := hgrid
  have hsteps : (a : Rat) / p.ulp q = (k : Rat) := by
    rw [hk, Rat.mul_div_cancel (Rat.ne_of_gt (p.ulp_pos q))]
  have hmax : (a : Rat) ≤ p.maxFinite := Rat.le_trans
    (Rat.natCast_le_natCast.mpr hn) (by decide +kernel)
  change (if q = 0 then .fin 0 else
    let r := (nearestEven ((if q < 0 then -q else q) / p.ulp q) : Rat) * p.ulp q
    if r > p.maxFinite then (if q < 0 then JF.negInf else JF.posInf)
    else .fin (if q < 0 then -r else r)) = .fin q
  simp only [ite_eq_right hz, hm, hsteps, nearestEven_natCast, ← hk,
    ite_eq_right (Rat.not_lt.mpr hmax)]
  by_cases h : q < 0
  · have hm' : -q = (a : Rat) := by simpa [h] using hm
    rw [ite_eq_left h, ← hm', Rat.neg_neg]
  · rw [ite_eq_right h]
    exact congrArg JF.fin (by simpa [h] using hm.symm)

/-- Rounding can use at most a sixteenth of a supplied magnitude budget as slack. -/
theorem LossPrecision.round_abs_le (p : LossPrecision) (q budget : Rat)
    (hmin : p.minNormal ≤ budget) (hq : q.abs ≤ budget)
    (hmax : budget + budget / 16 ≤ p.maxFinite) :
    ∃ r, p.round (.fin q) = .fin r ∧ r.abs ≤ budget + budget / 16 := by
  by_cases hz : q = 0
  · subst q
    refine ⟨0, by simp [LossPrecision.round], ?_⟩
    have hb : 0 ≤ budget := by simpa using hq
    have hd : 0 ≤ budget / 16 := Rat.mul_nonneg hb (by decide +kernel)
    simp only [Rat.abs_zero]
    grind
  have hb : 0 ≤ budget := Rat.le_trans Rat.abs_nonneg hq
  have hstep : p.ulp q ≤ budget * (1 / 8) := by
    have hscale : pow2 (1 - (p.bits : Int)) ≤ (1 : Rat) / 8 := by
      cases p <;> decide +kernel
    have hnonneg : 0 ≤ pow2 (1 - (p.bits : Int)) := Rat.le_of_lt (pow2_pos _)
    apply Rat.le_trans (p.ulp_le q hz)
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (by grind) hnonneg)
      (Rat.mul_le_mul_of_nonneg_left hscale hb)
  have hhalf : p.ulp q / 2 ≤ budget / 16 := by
    have h := Rat.mul_le_mul_of_nonneg_right hstep
      (show (0 : Rat) ≤ (2 : Rat)⁻¹ by decide +kernel)
    rw [Rat.mul_assoc, show (1 / 8 : Rat) * (2 : Rat)⁻¹ = (16 : Rat)⁻¹ by decide +kernel] at h
    exact h
  have hhead : q.abs + p.ulp q / 2 ≤ p.maxFinite := by grind
  obtain ⟨r, hr⟩ := p.round_finite_of_headroom q hhead
  refine ⟨r, hr, ?_⟩
  have he := p.round_error hr
  have interval (x : Rat) : -x.abs ≤ x ∧ x ≤ x.abs := by
    by_cases hn : 0 ≤ x
    · rw [Rat.abs_of_nonneg hn]
      grind
    · rw [Rat.abs_of_nonpos (by grind : x ≤ 0)]
      grind
  obtain ⟨hl, hu⟩ := interval (r - q)
  obtain ⟨hql, hqu⟩ := interval q
  by_cases h : 0 ≤ r
  · rw [Rat.abs_of_nonneg h]; grind
  · rw [Rat.abs_of_nonpos (by grind : r ≤ 0)]; grind

/-- In the positive normal range, a single operation costs at most half the
relative grid spacing and stays finite when its exact result is below half max. -/
theorem LossPrecision.round_normal_relative (p : LossPrecision) (q : Rat)
    (hmin : p.minNormal ≤ q) (hmax : q ≤ p.maxFinite / 2) :
    ∃ r, p.round (.fin q) = .fin r ∧
      (r - q).abs ≤ q * pow2 (1 - (p.bits : Int)) / 2 := by
  have hm : 0 < p.minNormal := pow2_pos _
  have hq : 0 < q := by grind
  have hu := p.ulp_le q (Rat.ne_of_gt hq)
  have hbound : max q p.minNormal = q := by grind
  rw [Rat.abs_of_nonneg (Rat.le_of_lt hq), hbound] at hu
  have hh := Rat.mul_le_mul_of_nonneg_right hu (show (0 : Rat) ≤ (2 : Rat)⁻¹ by decide +kernel)
  change p.ulp q / 2 ≤ q * pow2 (1 - (p.bits : Int)) / 2 at hh
  have hunit : pow2 (1 - (p.bits : Int)) ≤ 1 := by cases p <;> decide +kernel
  have hrel := Rat.mul_le_mul_of_nonneg_left hunit (Rat.le_of_lt hq)
  rw [Rat.mul_one] at hrel
  have hhalf := Rat.mul_le_mul_of_nonneg_right hrel (show (0 : Rat) ≤ (2 : Rat)⁻¹ by decide +kernel)
  change q * pow2 (1 - (p.bits : Int)) / 2 ≤ q / 2 at hhalf
  have hhead : q.abs + p.ulp q / 2 ≤ p.maxFinite := by
    rw [Rat.abs_of_nonneg (Rat.le_of_lt hq)]
    grind
  obtain ⟨r, hr⟩ := p.round_finite_of_headroom q hhead
  exact ⟨r, hr, Rat.le_trans (p.round_error hr) hh⟩

end SymReg.Loss
