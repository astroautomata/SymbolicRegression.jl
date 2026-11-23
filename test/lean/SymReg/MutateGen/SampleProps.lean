import SymReg.MutateGen.Sample
import SymReg.Loss.RoundOrder

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw greater)

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-! ## Specification side -/

/-- Every weight is a finite nonnegative number. -/
def FinNonneg (ws : List (Kind × JF)) : Prop := ∀ p ∈ ws, ∃ q, p.2 = .fin q ∧ 0 ≤ q

/-! ## Properties -/

/-- `_sample_mutation` rejects a weight that is negative, negative infinity or NaN with
`ArgumentError("Weights must be nonnegative.")`, and nonnegative weights summing to zero
with `ArgumentError("At least one weight must be positive.")`, in both cases before
drawing from the RNG. -/
def sample_errors : Prop := ∀ (ws : List (Kind × JF)) (rng : RNG),
  ((∃ p ∈ ws, geZero p.2 = false) →
    sampleMutationR ws rng = (.error (.argumentError "Weights must be nonnegative."), rng)) ∧
  ((∀ p ∈ ws, p.2 = .fin 0) →
    sampleMutationR ws rng = (.error (.argumentError "At least one weight must be positive."), rng))

private theorem checked_bad : ∀ (ws : List (Kind × JF)) (a : JF), (∃ p ∈ ws, geZero p.2 = false) →
    checkedTotal a ws = .error (.argumentError "Weights must be nonnegative.")
  | [], _, ⟨_, hp, _⟩ => by simp at hp
  | (k, w) :: ws, a, ⟨p, hp, hb⟩ => by
    simp only [checkedTotal]
    by_cases hw : geZero w = true
    · simp only [hw, if_true]
      apply checked_bad ws
      rcases List.mem_cons.mp hp with rfl | hp'
      · simp [hw] at hb
      · exact ⟨p, hp', hb⟩
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      rfl

private theorem checked_zero : ∀ (ws : List (Kind × JF)), (∀ p ∈ ws, p.2 = .fin 0) →
    checkedTotal (.fin 0) ws = .ok (.fin 0)
  | [], _ => rfl
  | (k, w) :: ws, h => by
    have hw : w = .fin 0 := h (k, w) List.mem_cons_self
    subst hw
    have hg : geZero (.fin 0) = true := by decide
    simp only [checkedTotal, hg, if_true]
    have hadd : weightAdd (.fin 0) (.fin 0) = .fin 0 := by decide
    rw [hadd]
    exact checked_zero ws (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem sample_errors_holds : sample_errors := by
  intro ws rng
  constructor
  · intro h
    simp [sampleMutationR, checked_bad ws _ h]
  · intro h
    have hz := checked_zero ws h
    have hg : greater (.fin 0) (.fin 0) = false := by decide
    simp [sampleMutationR, hz, hg]

/-- A possible draw from `rand()` for the task-local Float64 Xoshiro generator. -/
def unitDraw (k : Fin (2^53)) : Rat := (k.val : Rat) / (2^53 : Rat)

open SymReg.Loss in
/-- A draw on the Xoshiro grid cannot round up to a large enough normal
total. At the top draw, the gap is one relative half-step of the total;
the threshold's own grid step is strictly smaller than that bound. -/
theorem threshold_below_normal (k : Fin (2^53)) (total : Rat)
    (hn : LossPrecision.minNormal .float64 < total)
    (hh : 2 * total ≤ LossPrecision.maxFinite .float64) :
    ∃ t, weightThreshold (unitDraw k) (.fin total) = .fin t ∧ t < total := by
  let eps : Rat := 1 / (2 : Rat)^53
  have he : 0 < eps := by decide
  have hp : 0 < total := by
    have hn0 : 0 < LossPrecision.minNormal .float64 := by decide +kernel
    grind
  have hu0 : 0 ≤ unitDraw k := Rat.mul_nonneg Rat.natCast_nonneg (by decide)
  have hu : unitDraw k ≤ 1 - eps := by
    have hk : k.val ≤ 2^53 - 1 := by have := k.isLt; omega
    have hb := Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hk)
      (Rat.le_of_lt he)
    have hc : (((2^53 - 1 : Nat) : Rat) * eps) = 1 - eps := by decide +kernel
    rw [hc] at hb
    exact hb
  let q := unitDraw k * total
  have hq0 : 0 ≤ q := Rat.mul_nonneg hu0 (Rat.le_of_lt hp)
  have hgap : q ≤ total - eps * total := by
    have h := Rat.mul_le_mul_of_nonneg_right hu (Rat.le_of_lt hp)
    simpa only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.one_mul, Rat.neg_mul] using h
  have hq : q < total := by
    have := Rat.mul_pos he hp
    grind
  by_cases hz : q = 0
  · refine ⟨0, ?_, hp⟩
    change LossPrecision.round .float64 (.fin q) = .fin 0
    rw [hz]
    rfl
  have hul := LossPrecision.ulp_le .float64 q hz
  have hrel : (1 / (2 : Rat)^52) = eps + eps := by decide
  change LossPrecision.ulp .float64 q ≤ max q.abs (LossPrecision.minNormal .float64) *
    (1 / (2 : Rat)^52) at hul
  rw [Rat.abs_of_nonneg hq0, hrel] at hul
  have hm : max q (LossPrecision.minNormal .float64) < total := by grind
  have hhalf : LossPrecision.ulp .float64 q / 2 < eps * total := by
    have hm' := Rat.mul_lt_mul_of_pos_right hm he
    simp only [Rat.div_def] at *
    rw [Rat.mul_add] at hul
    grind
  have hhead : q.abs + LossPrecision.ulp .float64 q / 2 ≤ LossPrecision.maxFinite .float64 := by
    rw [Rat.abs_of_nonneg hq0]
    grind
  obtain ⟨t, ht⟩ := LossPrecision.round_finite_of_headroom .float64 q hhead
  refine ⟨t, ht, ?_⟩
  have herr := LossPrecision.round_error .float64 ht
  have hle : t - q ≤ (t - q).abs := by
    by_cases hp : 0 ≤ t - q
    · rw [Rat.abs_of_nonneg hp]; exact Rat.le_refl
    · have := Rat.abs_nonneg (x := t - q)
      grind
  grind

/-- A successful sampler picks the first crossing, or the last index if none crosses. -/
def selectedPrefix (ws : List (Kind × JF)) (threshold : JF) (i : Nat) : Prop :=
  let sumAt (j : Nat) := (ws.take j).foldl (fun a p => weightAdd a p.2) (.fin 0)
  ((0 < i ∧ i ≤ ws.length ∧ jlt threshold (sumAt i) = true ∧
    ∀ j, 0 < j → j < i → jlt threshold (sumAt j) = false) ∨
   (i = ws.length ∧ ∀ j, 0 < j → j ≤ ws.length → jlt threshold (sumAt j) = false))

def sample_interval : Prop :=
  ∀ (ws : List (Kind × JF)) (total : JF) (k : Fin (2^53)) (i : Nat),
    (∀ p ∈ ws, weightAdd (.fin 0) p.2 = p.2) →
    checkedTotal (.fin 0) ws = .ok total → greater total (.fin 0) = true →
    (sampleMutationCore ws (unitDraw k) = .ok i ↔ selectedPrefix ws (weightThreshold (unitDraw k) total) i)

def sample_reachable : Prop :=
  ∀ (ws : List (Kind × JF)) (total : JF) (i : Nat),
    (∀ p ∈ ws, weightAdd (.fin 0) p.2 = p.2) →
    checkedTotal (.fin 0) ws = .ok total → greater total (.fin 0) = true →
    ((∃ k, sampleMutationCore ws (unitDraw k) = .ok i) ↔
     ∃ k, selectedPrefix ws (weightThreshold (unitDraw k) total) i)

private def sumAt (ws : List (Kind × JF)) (acc : JF) (j : Nat) : JF :=
  (ws.take j).foldl (fun a p => weightAdd a p.2) acc

private theorem sumAt_succ (w : Kind × JF) (ws : List (Kind × JF)) (acc : JF) (j : Nat) :
    sumAt (w :: ws) acc (j + 1) = sumAt ws (weightAdd acc w.2) j := rfl

private theorem select_correct (t : JF) (ws : List (Kind × JF)) (acc : JF) (start last : Nat) :
    let i := selectIdx t last start acc ws
    (∃ j, 0 < j ∧ j ≤ ws.length ∧ i = start + (j - 1) ∧ jlt t (sumAt ws acc j) = true ∧
      ∀ k, 0 < k → k < j → jlt t (sumAt ws acc k) = false) ∨
    (i = last ∧ ∀ j, 0 < j → j ≤ ws.length → jlt t (sumAt ws acc j) = false) := by
  induction ws generalizing acc start with
  | nil => exact Or.inr ⟨rfl, fun _ h1 h2 => by simp at h2; omega⟩
  | cons w ws ih =>
    obtain ⟨kind, weight⟩ := w
    by_cases h : jlt t (weightAdd acc weight) = true
    · simp only [selectIdx, h, if_true]
      exact Or.inl ⟨1, by decide, by simp, by simp, h, fun _ h1 h2 => by omega⟩
    · have hf : jlt t (weightAdd acc weight) = false := Bool.eq_false_iff.mpr h
      simp only [selectIdx, hf, Bool.false_eq_true, ↓reduceIte]
      rcases ih (weightAdd acc weight) (start + 1) with ⟨j, h1, h2, he, hc, hprior⟩ | ⟨he, hall⟩
      · refine Or.inl ⟨j + 1, by omega, by simp; omega, by omega,
          by rwa [sumAt_succ], ?_⟩
        intro k hk hk'
        cases k with
        | zero => omega
        | succ k =>
          rw [sumAt_succ]
          cases k with
          | zero => exact hf
          | succ k => exact hprior (k + 1) (by omega) (by omega)
      · refine Or.inr ⟨he, ?_⟩
        intro j hj hlen
        cases j with
        | zero => omega
        | succ j =>
          rw [sumAt_succ]
          cases j with
          | zero => exact hf
          | succ j => exact hall (j + 1) (by omega) (by simp at hlen; omega)

/-- If the terminal prefix crosses the threshold, the scan cannot fall back.
If a zero step preserves each prefix, the first crossing cannot be a zero step. -/
theorem selectIdx_positive_of_crossing (t : JF) (ws : List (Kind × JF))
    (acc : JF) (start fallback : Nat)
    (hbefore : jlt t acc = false)
    (hfinal : jlt t (sumAt ws acc ws.length) = true)
    (hstep : ∀ j, j < ws.length → ∀ p, ws[j]? = some p →
      greater p.2 (.fin 0) = false → sumAt ws acc (j + 1) = sumAt ws acc j) :
    ∃ j p, j < ws.length ∧ ws[j]? = some p ∧
      selectIdx t fallback start acc ws = start + j ∧ greater p.2 (.fin 0) = true := by
  induction ws generalizing start acc with
  | nil => exact Bool.noConfusion (hbefore.symm.trans hfinal)
  | cons p ws ih =>
    have h' : jlt t (weightAdd acc p.2) = true ∨
        jlt t (weightAdd acc p.2) = false := by
      cases jlt t (weightAdd acc p.2) <;> simp
    rcases h' with hcross | hstay
    · refine ⟨0, p, by simp, rfl, by simp [selectIdx, hcross], ?_⟩
      cases hp : greater p.2 (.fin 0)
      · have he := hstep 0 (by simp) p rfl hp
        change weightAdd acc p.2 = acc at he
        rw [he, hbefore] at hcross
        contradiction
      · rfl
    · obtain ⟨j, q, hj, hq, hi, hp⟩ := ih (weightAdd acc p.2) (start + 1) hstay
        (by simpa only [List.length_cons, sumAt_succ] using hfinal)
        (fun j hj q hq hzero => by
          have he := hstep (j + 1) (by simp; omega) q hq hzero
          simpa only [sumAt_succ] using he)
      exact ⟨j + 1, q, by simp; omega, hq, by simpa [selectIdx, hstay, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi, hp⟩

private def minWeight : Rat := 1 / (2 : Rat)^510
private def maxWeight : Rat := (2 : Rat)^511
private def sumCap : Rat := (2 : Rat)^576

open SymReg.Loss (LossPrecision)

/-- Possible prefixes of the stock Float64 summation with normal-range weights. -/
private def NormalPrefix (a : Rat) : Prop :=
  (a = 0 ∨ minWeight ≤ a) ∧ a ≤ sumCap ∧ LossPrecision.round .float64 (.fin a) = .fin a

private theorem normalPrefix_zero : NormalPrefix 0 := by
  exact ⟨Or.inl rfl, by decide +kernel, rfl⟩

private theorem normalWeight_nonneg {w : Rat} (hw : w = 0 ∨ minWeight ≤ w ∧ w < maxWeight) :
    0 ≤ w := by
  rcases hw with rfl | hw
  · exact Rat.le_refl
  · exact Rat.le_trans (by decide +kernel : (0 : Rat) ≤ minWeight) hw.1

private theorem normalPrefix_step {a w : Rat} (ha : NormalPrefix a)
    (hw : w = 0 ∨ minWeight ≤ w ∧ w < maxWeight) :
    ∃ b, weightAdd (.fin a) (.fin w) = .fin b ∧ NormalPrefix b := by
  obtain ⟨ha0, hab, haf⟩ := ha
  rcases hw with rfl | hw
  · exact ⟨a, by change LossPrecision.round .float64 (.fin (a + 0)) = .fin a; rwa [Rat.add_zero],
      ha0, hab, haf⟩
  have hmin : (0 : Rat) < minWeight := by decide +kernel
  have han : 0 ≤ a := by rcases ha0 with rfl | h <;> grind
  have hlow : minWeight ≤ a + w := by grind
  have hhigh : a + w ≤ sumCap + maxWeight := by grind
  -- At the cap, even the largest allowed addend is less than half a grid step.
  have hcap : LossPrecision.round .float64 (.fin (sumCap + maxWeight)) = .fin sumCap := by
    decide +kernel
  obtain ⟨b, hb, -, hbc⟩ := LossPrecision.float64.round_le_nonneg (by grind : 0 ≤ a + w) hhigh hcap
  have hfloor : LossPrecision.round .float64 (.fin minWeight) = .fin minWeight := by decide +kernel
  have hlo := LossPrecision.float64.round_ge_nonneg (Rat.le_of_lt hmin) hlow hfloor
  rw [hb] at hlo
  have hbm : minWeight ≤ b := by
    rcases hlo with h | ⟨b', h, hle⟩
    · cases h
    · cases h; exact hle
  exact ⟨b, hb, Or.inr hbm, hbc,
    LossPrecision.float64.round_idempotent_nonneg (by grind : 0 ≤ a + w) hb⟩

private def NormalWeights (ws : List (Kind × JF)) : Prop :=
  ∀ p ∈ ws, ∃ q, p.2 = .fin q ∧ (q = 0 ∨ minWeight ≤ q ∧ q < maxWeight)

private theorem normal_total (ws : List (Kind × JF)) (hws : NormalWeights ws)
    (a : Rat) (ha : NormalPrefix a) :
    ∃ b, checkedTotal (.fin a) ws = .ok (.fin b) ∧
      ws.foldl (fun a p => weightAdd a p.2) (.fin a) = .fin b ∧ NormalPrefix b := by
  induction ws generalizing a with
  | nil => exact ⟨a, rfl, rfl, ha⟩
  | cons p ws ih =>
    obtain ⟨q, hq, hnd⟩ := hws p (by simp)
    have hge : geZero p.2 = true := by rw [hq]; exact decide_eq_true (normalWeight_nonneg hnd)
    obtain ⟨b, hb, hbnd⟩ := normalPrefix_step ha hnd
    obtain ⟨c, hct, hcf, hc⟩ := ih (fun p hp => hws p (List.mem_cons_of_mem _ hp)) b hbnd
    refine ⟨c, ?_, ?_, hc⟩
    · rw [show checkedTotal (.fin a) (p :: ws) =
        (if geZero p.2 then checkedTotal (weightAdd (.fin a) p.2) ws
        else .error (.argumentError "Weights must be nonnegative.")) by cases p; rfl,
        ite_eq_left hge, hq, hb, hct]
    · simpa only [List.foldl_cons, hq, hb] using hcf

/-- Julia's normally returning sampler never selects a zero-weight slot in this range. -/
theorem sample_positive_normal (ws : List (Kind × JF)) (rng rng' : RNG)
    (k : Fin (2^53)) (i : Nat) (hd : rng.draws rng.cursor = unitDraw k)
    (hw : ∀ p ∈ ws, ∃ q, p.2 = .fin q ∧
      (q = 0 ∨ 1 / (2 : Rat)^510 ≤ q ∧ q < (2 : Rat)^511))
    (hi : sampleMutationR ws rng = (.ok i, rng')) :
    ∃ p, ws[i - 1]? = some p ∧ greater p.2 (.fin 0) = true := by
  have hnorm : NormalWeights ws := hw
  obtain ⟨total, ht, hfold, htot⟩ := normal_total ws hnorm 0 normalPrefix_zero
  simp only [sampleMutationR, ht] at hi
  cases hg : greater (.fin total) (.fin 0)
  · simp [hg] at hi
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, draw, hd,
    Prod.mk.injEq, Except.ok.injEq] at hi
  have hpos : 0 < total := of_decide_eq_true hg
  have hmin : LossPrecision.minNormal .float64 < total := by
    rcases htot.1 with hzero | hmin
    · rw [hzero] at hpos; exact (Rat.lt_irrefl hpos).elim
    · have : LossPrecision.minNormal .float64 < minWeight := by decide +kernel
      grind
  have hmax : 2 * total ≤ LossPrecision.maxFinite .float64 := by
    have ht := htot.2.1
    have : (2 : Rat) * sumCap ≤ LossPrecision.maxFinite .float64 := by decide +kernel
    have := Rat.mul_le_mul_of_nonneg_left ht (by decide : (0 : Rat) ≤ 2)
    grind
  obtain ⟨t, htr, htlt⟩ := threshold_below_normal k total hmin hmax
  have hunit : 0 ≤ unitDraw k := Rat.mul_nonneg Rat.natCast_nonneg (by decide)
  have htn : 0 ≤ t := by
    have h := LossPrecision.float64.round_nonneg
      (Rat.mul_nonneg hunit (Rat.le_of_lt hpos))
    change LossPrecision.round .float64 (.fin (unitDraw k * total)) = .fin t at htr
    rw [htr] at h
    rcases h with h | ⟨u, h, hn⟩
    · cases h
    · cases h; exact hn
  have hbefore : jlt (.fin t) (.fin 0) = false := decide_eq_false (Rat.not_lt.mpr htn)
  have hfinal : jlt (.fin t) (sumAt ws (.fin 0) ws.length) = true := by
    simpa only [sumAt, List.take_length, hfold, jlt, greater] using decide_eq_true htlt
  have hstep j (_ : j < ws.length) p (hp : ws[j]? = some p)
      (hz : greater p.2 (.fin 0) = false) :
      sumAt ws (.fin 0) (j + 1) = sumAt ws (.fin 0) j := by
    obtain ⟨q, hq, hq'⟩ := hw p (List.mem_of_getElem? hp)
    have hzero : q = 0 := by
      have hqn := normalWeight_nonneg hq'
      rw [hq] at hz
      have hlt : ¬ (0 : Rat) < q := of_decide_eq_false hz
      grind
    obtain ⟨a, -, hfold, ha⟩ := normal_total (ws.take j)
      (fun p hp => hw p (List.mem_of_mem_take hp)) 0 normalPrefix_zero
    unfold sumAt
    rw [List.take_add_one, hp, Option.toList_some, List.foldl_append, hfold, List.foldl_cons,
      List.foldl_nil, hq, hzero]
    change LossPrecision.round .float64 (.fin (a + 0)) = .fin a
    rw [Rat.add_zero]
    exact ha.2.2
  obtain ⟨j, p, -, hp, hsel, hpos⟩ :=
    selectIdx_positive_of_crossing (.fin t) ws (.fin 0) 1 ws.length hbefore hfinal hstep
  rw [htr, hsel] at hi
  have he : i - 1 = j := by omega
  exact ⟨p, he ▸ hp, hpos⟩

private theorem selectedPrefix_unique (ws : List (Kind × JF)) (t : JF) (i j : Nat) :
    selectedPrefix ws t i → selectedPrefix ws t j → i = j := by
  intro hi hj
  rcases hi with ⟨hi0, hin, hc, hp⟩ | ⟨rfl, hall⟩
  · rcases hj with ⟨hj0, hjn, hc', hp'⟩ | ⟨rfl, hall⟩
    · by_cases hij : i < j
      · exact Bool.noConfusion (hc.symm.trans (hp' i hi0 hij))
      · by_cases hji : j < i
        · exact Bool.noConfusion (hc'.symm.trans (hp j hj0 hji))
        · omega
    · exact Bool.noConfusion (hc.symm.trans (hall i hi0 hin))
  · rcases hj with ⟨hj0, hjn, hc', _⟩ | ⟨rfl, _⟩
    · exact Bool.noConfusion (hc'.symm.trans (hall j hj0 hjn))
    · rfl

theorem sample_interval_holds : sample_interval := by
  intro ws total k i _ hv hp
  simp only [sampleMutationCore, hv, hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq]
  generalize ht : weightThreshold (unitDraw k) total = t
  let r := selectIdx t ws.length 1 (.fin 0) ws
  have hs : selectedPrefix ws t r := by
    rcases select_correct t ws (.fin 0) 1 ws.length with ⟨j, h1, h2, he, hc, hprior⟩ | ⟨he, hall⟩
    · have hr : r = j := by change r = 1 + (j - 1) at he; omega
      rw [hr]
      exact Or.inl ⟨h1, h2, hc, hprior⟩
    · exact Or.inr ⟨he, hall⟩
  exact ⟨fun h => h ▸ hs, fun h => selectedPrefix_unique ws t r i hs h⟩

theorem sample_reachable_holds : sample_reachable := by
  intro ws total i hw hv hp
  exact ⟨fun ⟨k, h⟩ => ⟨k, (sample_interval_holds ws total k i hw hv hp).mp h⟩,
    fun ⟨k, h⟩ => ⟨k, (sample_interval_holds ws total k i hw hv hp).mpr h⟩⟩

example : sampleMutationCore
    [(Kind.operator, .fin (1 / (2 : Rat)^1074)), (.constant, .fin 0)] (3 / 4) = .ok 2 := by
  decide +kernel

/-- Extending `sample_interval` to infinite weights: for nonnegative non-NaN weights with a
positive total and any draw in `[0, 1)`, the index `_sample_mutation` returns has a
positive weight. -/
def sample_positive_extended : Prop := ∀ (ws : List (Kind × JF)) (u : Rat) (total : JF),
  checkedTotal (.fin 0) ws = .ok total → greater total (.fin 0) = true → 0 ≤ u → u < 1 →
  ∀ i, sampleMutationCore ws u = .ok i → ∃ p, ws[i - 1]? = some p ∧ greater p.2 (.fin 0) = true

theorem sample_positive_extended_refuted : ¬ sample_positive_extended := by
  intro h
  have := h [(.operator, .posInf), (.constant, .fin 0)] (1 / 2) .posInf (by decide) (by decide)
    (by decide) (by decide) 2 (by decide)
  obtain ⟨p, hp, hg⟩ := this
  simp at hp
  subst hp
  exact absurd hg (by decide)

/-- `sample_mutation` (the exported StatsBase-based sampler) returns only mutations with a
positive weight, for finite nonnegative weights with at least one positive weight and
draws in `[0, 1)`. -/
def exported_positive : Prop := ∀ (ms : List (Kind × JF)) (rng : RNG) (k : Kind),
  FinNonneg ms → (∃ p ∈ ms, ∃ q, p.2 = .fin q ∧ 0 < q) →
  (∀ n, 0 ≤ rng.draws n ∧ rng.draws n < 1) →
  (sampleMutationExported ms rng).1 = .ok k → ∃ p ∈ ms, p.1 = k ∧ ∃ q, p.2 = .fin q ∧ 0 < q

theorem exported_positive_refuted : ¬ exported_positive := by
  intro h
  have hfin : FinNonneg [(.operator, .fin 0), (.constant, .fin 1)] := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact ⟨0, rfl, by decide⟩
    · exact ⟨1, rfl, by decide⟩
  have := h [(.operator, .fin 0), (.constant, .fin 1)] { draws := fun _ => 0 } .operator hfin
    ⟨(.constant, .fin 1), by simp, 1, rfl, by decide⟩
    (fun _ => ⟨Rat.le_refl, (by decide : (0 : Rat) < 1)⟩) (by decide)
  obtain ⟨p, hp, hk, q, hq, hpos⟩ := this
  simp at hp
  rcases hp with rfl | rfl
  · simp at hq; subst hq; exact absurd hpos (by decide)
  · simp at hk

end SymReg.MutateGen
