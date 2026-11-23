import SymReg.Plugins.Parsimony
import SymReg.Loss.RoundOrder
import SymReg.Loss.Core

/-!
`src/plugins/SimulatedAnnealing.jl`. LinRange is its exact finite linear
interpolation; floating interpolation rounding is outside the schedule proofs.
The exponential shares the supplied scalar service with adaptive parsimony.
-/
namespace SymReg.Plugins
open DynExpr

attribute [local semireducible] Rat.add Rat.mul Rat.inv Rat.sub

private def alphaError := JlError.argumentError "`alpha` must be finite and positive."

/- Source: src/plugins/SimulatedAnnealing.jl:41-46
function SimulatedAnnealingPlugin(; alpha::Real=0.1)::SimulatedAnnealingPlugin
    converted_alpha = Float64(alpha)
    isfinite(converted_alpha) && converted_alpha > 0 ||
        throw(ArgumentError("`alpha` must be finite and positive."))
    return SimulatedAnnealingPlugin(converted_alpha)
end
-/
def makeAnnealing {A W : Type} (cast : A → W → Jl JF × W) (input : A)
    (w : W) : Jl JF × W :=
  match cast input w with
  | (.error e, w') => (.error e, w')
  | (.ok (.fin alpha), w') =>
    if 0 < alpha then (.ok (.fin alpha), w') else (.error alphaError, w')
  | (.ok _, w') => (.error alphaError, w')

/- Source: src/plugins/SimulatedAnnealing.jl:96-102
@stable(
    default_union_limit = 2,
    function default_simulated_annealing_plugin(; annealing::Bool, alpha::Real)
        annealing || return nothing
        return SimulatedAnnealingPlugin(; alpha=Float64(alpha))
    end
)
-/
def defaultAnnealing {A W : Type} (enabled : Bool) (cast : A → W → Jl JF × W)
    (alpha : A) (w : W) : Jl (Option JF) × W :=
  if !enabled then (.ok none, w) else
  match cast alpha w with
  | (.error e, w') => (.error e, w')
  | (.ok value, w') =>
    let (p, w'') := makeAnnealing (fun v state => (.ok v, state)) value w'
    (p.map some, w'')

-- Source: src/plugins/SimulatedAnnealing.jl:60-62
def initTemperature (_alpha : JF) : JF := .fin 1

/-- `src/plugins/SimulatedAnnealing.jl:64-73`. Cycles are one based; singleton
and nonpositive ncycles take the source's constant-one branch. -/
def cycleTemperature (cycle ncycles : Int) : Jl Rat :=
  if 1 < ncycles then
    if 1 ≤ cycle ∧ cycle ≤ ncycles then
      pure (((ncycles - cycle : Int) : Rat) / ((ncycles - 1 : Int) : Rat))
    else throw .boundsError
  else pure 1

/-- `src/plugins/SimulatedAnnealing.jl:75-84`: ConstantMutationContext.scale update. -/
def conditionConstant (scale temperature : Rat) : Rat := scale * temperature

/- Source: src/plugins/SimulatedAnnealing.jl:86-94
function mutation_acceptance_multiplier(
    s::SimulatedAnnealingState,
    p::SimulatedAnnealingPlugin,
    ctx::MutationAcceptanceContext,
    options::AbstractOptions,
)
    delta = ctx.after_cost - ctx.before_cost
    return exp(-delta / (s.temperature * p.alpha))
end
-/
private def negative (x : JF) (negativeZero : Bool) : Bool :=
  match x with
  | .fin q => if q = 0 then negativeZero else decide (q < 0)
  | .negInf => true
  | _ => false

def annealingAcceptance (rt : FloatServices) (precision : SymReg.Loss.LossPrecision)
    (temperature alpha : JF) (negativeTemperatureZero negativeAlphaZero : Bool)
    (before after : JF) : JF :=
  let round64 := SymReg.Loss.LossPrecision.float64.round
  let delta := precision.round (after - before)
  let product := round64 (temperature * alpha)
  let negativeDenominator := negative temperature negativeTemperatureZero !=
    negative alpha negativeAlphaZero
  let numerator := if product = .fin 0 ∧ negativeDenominator = true then delta else -delta
  exponential rt (round64 (numerator / product))

def annealing_constructor : Prop := ∀ (A W : Type) (cast : A → W → Jl JF × W)
    input world,
  defaultAnnealing false cast input world = (.ok none, world) ∧
  (∀ e w', cast input world = (.error e, w') →
    makeAnnealing cast input world = (.error e, w') ∧
    defaultAnnealing true cast input world = (.error e, w')) ∧
  ∀ alpha w', cast input world = (.ok alpha, w') →
    (∀ q, alpha = .fin q → 0 < q →
      makeAnnealing cast input world = (.ok alpha, w') ∧
      defaultAnnealing true cast input world = (.ok (some alpha), w') ∧
      initTemperature alpha = .fin 1) ∧
    ((¬ ∃ q, alpha = .fin q ∧ 0 < q) →
      makeAnnealing cast input world = (.error alphaError, w') ∧
      defaultAnnealing true cast input world = (.error alphaError, w'))

theorem annealing_constructor_holds : annealing_constructor := by
  intro A W cast input world
  refine ⟨rfl, ?_, ?_⟩
  · intro e w' h; simp [makeAnnealing, defaultAnnealing, h]
  · intro alpha w' h
    constructor
    · intro q hq hp; simp [makeAnnealing, defaultAnnealing, h, hq, hp, initTemperature, Except.map]
    · intro bad
      cases alpha <;> simp_all [makeAnnealing, defaultAnnealing, Except.map]

def schedule_endpoints : Prop := ∀ (ncycles : Int),
  1 < ncycles → cycleTemperature 1 ncycles = .ok 1 ∧
    cycleTemperature ncycles ncycles = .ok 0

theorem schedule_endpoints_holds : schedule_endpoints := by
  intro n hn
  have hpos : (0 : Rat) < (n : Rat) - 1 := by
    have h := Rat.intCast_pos.mpr (show 0 < n - 1 by omega)
    simpa only [Rat.intCast_sub, Rat.intCast_one] using h
  have hnq : (n : Rat) - 1 ≠ 0 := Rat.ne_of_gt hpos
  simp [cycleTemperature, hn, show 1 ≤ n by omega, ratDivSelf _ hnq, ratZeroDiv,
    pure, Except.pure]

def schedule_singleton : Prop := ∀ (cycle ncycles : Int),
  ncycles ≤ 1 → cycleTemperature cycle ncycles = .ok 1

theorem schedule_singleton_holds : schedule_singleton := by
  intro cycle n hn
  simp [cycleTemperature, show ¬ 1 < n by omega, pure, Except.pure]

def schedule_monotone : Prop := ∀ (i j n : Int),
  1 ≤ i → i ≤ j → j ≤ n → 1 < n →
  ∃ ti tj, cycleTemperature i n = .ok ti ∧ cycleTemperature j n = .ok tj ∧
    0 ≤ tj ∧ tj ≤ ti ∧ ti ≤ 1

theorem schedule_monotone_holds : schedule_monotone := by
  intro i j n hi hij hjn hn
  let den : Rat := ((n - 1 : Int) : Rat)
  have hd : 0 < den := by
    change 0 < ((n - 1 : Int) : Rat)
    exact Rat.intCast_pos.mpr (by omega)
  have hnumj : (0 : Rat) ≤ ((n - j : Int) : Rat) := Rat.intCast_nonneg.mpr (by omega)
  have hnums : ((n - j : Int) : Rat) ≤ ((n - i : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr (by omega)
  have hnumi : ((n - i : Int) : Rat) ≤ den := Rat.intCast_le_intCast.mpr (by omega)
  refine ⟨((n - i : Int) : Rat) / den, ((n - j : Int) : Rat) / den, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cycleTemperature, den, hn, hi, show i ≤ n by omega, pure, Except.pure]
  · simp [cycleTemperature, den, hn, show 1 ≤ j by omega, hjn, pure, Except.pure]
  · rw [Rat.div_def]
    exact Rat.mul_nonneg hnumj (Rat.le_of_lt (Rat.inv_pos.mpr hd))
  · exact ratDivMono hd hnums
  · exact (ratDivLe hd).mpr (by simpa [Rat.one_mul] using hnumi)

def constant_scale_schedule : Prop := ∀ (scale t : Rat),
  0 ≤ scale → 0 ≤ t → t ≤ 1 →
  0 ≤ conditionConstant scale t ∧ conditionConstant scale t ≤ scale ∧
  conditionConstant scale 0 = 0 ∧ conditionConstant scale 1 = scale

theorem constant_scale_schedule_holds : constant_scale_schedule := by
  intro scale t hs ht h1
  refine ⟨Rat.mul_nonneg hs ht, ?_, ?_, ?_⟩
  · have h := Rat.mul_le_mul_of_nonneg_left h1 hs
    simpa [conditionConstant, Rat.mul_one] using h
  · simp [conditionConstant]
  · simp [conditionConstant]

/-- Finite exponential contract on nonpositive arguments. This states the
external scalar fact, without inventing an implementation of Julia's libm. -/
def NonpositiveExp (rt : FloatServices) : Prop :=
  ∀ x, x < 0 → ∃ q, rt.expFinite x = .fin q ∧ 0 ≤ q ∧ q ≤ 1

open SymReg.Loss (LossPrecision)

def acceptance_probability_range : Prop := ∀ (rt : FloatServices) (precision : LossPrecision)
    (temperature alpha before after : Rat),
  NonpositiveExp rt → 0 < temperature → 0 < alpha → before ≤ after →
  let out := annealingAcceptance rt precision (.fin temperature) (.fin alpha) false false
    (.fin before) (.fin after)
  let delta := precision.round (.fin (after - before))
  let denominator := LossPrecision.float64.round (.fin (temperature * alpha))
  (delta = .fin 0 → denominator = .fin 0 → out = .nan) ∧
  (delta = .posInf → denominator = .posInf → out = .nan) ∧
  (¬ (delta = .fin 0 ∧ denominator = .fin 0) →
    ¬ (delta = .posInf ∧ denominator = .posInf) →
    ∃ q, out = .fin q ∧ 0 ≤ q ∧ q ≤ 1)

def annealing_zero_tie : Prop := ∀ (rt : FloatServices) (temperature alpha cost : Rat),
  0 ≤ temperature → 0 < alpha →
  annealingAcceptance rt .float64 (.fin temperature) (.fin alpha) false false
    (.fin cost) (.fin cost) = .fin 1

theorem annealing_zero_tie_refuted : ¬ annealing_zero_tie := by
  intro hp
  let rt : FloatServices := { expFinite := fun _ => .fin 1 }
  have h := hp rt 0 (3602879701896397 / 36028797018963968) 1 (by decide) (by decide)
  have hn : annealingAcceptance rt .float64 (.fin 0) (.fin (3602879701896397 / 36028797018963968))
      false false (.fin 1) (.fin 1) ≠ .fin 1 := by decide
  exact hn h

/-- Both zero signs arise from valid state objects; LinRange supplies +0.0. -/
def zero_temperature_limits : Prop := ∀ (rt : FloatServices) (precision : LossPrecision)
    (alpha before after : Rat) (negativeZero : Bool),
  0 < alpha →
  let delta := precision.round (.fin (after - before))
  let out := annealingAcceptance rt precision (.fin 0) (.fin alpha) negativeZero false
    (.fin before) (.fin after)
  (delta = .fin 0 → out = .nan) ∧
  ((delta = .posInf ∨ ∃ q, delta = .fin q ∧ 0 < q) →
    out = if negativeZero then .posInf else .fin 0) ∧
  ((delta = .negInf ∨ ∃ q, delta = .fin q ∧ q < 0) →
    out = if negativeZero then .fin 0 else .posInf)

private theorem finite_div_zero_pos {q : Rat} (hq : 0 < q) :
    JF.fin q / .fin 0 = .posInf := by
  have hn : ¬ q.num < 0 := by have := Rat.num_nonneg.mpr (Rat.le_of_lt hq); omega
  change (if q = 0 then JF.nan else if decide (q.num < 0) then .negInf else .posInf) = _
  simp [Rat.ne_of_gt hq, hn]

private theorem finite_div_zero_neg {q : Rat} (hq : q < 0) :
    JF.fin q / .fin 0 = .negInf := by
  have hnum : q.num < 0 := by
    by_cases h : 0 ≤ q.num
    · have := Rat.num_nonneg.mp h; grind
    · omega
  change (if q = 0 then JF.nan else if decide (q.num < 0) then .negInf else .posInf) = _
  simp [Rat.ne_of_lt hq, hnum]

theorem zero_temperature_limits_holds : zero_temperature_limits := by
  intro rt precision alpha before after nz ha
  dsimp only
  have hne := Rat.ne_of_gt ha
  have hn : ¬ alpha < 0 := by grind
  have ha : LossPrecision.float64.round (.fin 0) = .fin 0 := rfl
  let d := precision.round (.fin (after - before))
  have hval : annealingAcceptance rt precision (.fin 0) (.fin alpha) nz false (.fin before) (.fin after) =
      exponential rt (LossPrecision.float64.round ((if nz then d else -d) / .fin 0)) := by
    simp [annealingAcceptance, Rat.zero_mul, ha, negative, hne, hn, d]
  change (d = .fin 0 → _) ∧ _
  rw [hval]
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    cases nz <;> rw [hd] <;> rfl
  · intro hd
    rcases hd with hd | ⟨q, hq, hpos⟩
    · change d = .posInf at hd
      cases nz <;> rw [hd] <;> rfl
    · have hm : -q < 0 := by grind
      change d = .fin q at hq
      cases nz <;> rw [hq] <;>
        simp [finite_div_zero_pos hpos, finite_div_zero_neg hm, LossPrecision.round, exponential]
  · intro hd
    rcases hd with hd | ⟨q, hq, hneg⟩
    · change d = .negInf at hd
      cases nz <;> rw [hd] <;> rfl
    · have hm : 0 < -q := by grind
      change d = .fin q at hq
      cases nz <;> rw [hq] <;>
        simp [finite_div_zero_neg hneg, finite_div_zero_pos hm, LossPrecision.round, exponential]

private theorem round_neg_nonneg (p : LossPrecision) {q : Rat} (hq : 0 ≤ q) :
    p.round (.fin (-q)) = -(p.round (.fin q)) := by
  by_cases hz : q = 0
  · subst q; rfl
  have hp : 0 < q := Rat.lt_of_le_of_ne hq (Ne.symm hz)
  have hneg : -q < 0 := by grind
  have hpos : ¬ q < 0 := Rat.not_lt.mpr hq
  have hn : -q ≠ 0 := by grind
  have hu : p.ulp (-q) = p.ulp q := by simp [LossPrecision.ulp, hneg, hpos, Rat.neg_neg]
  simp only [LossPrecision.round, hz, hn, hneg, hpos, ↓reduceIte, Rat.neg_neg, hu]
  split <;> rfl
private theorem exp_nonpositive (rt : FloatServices) (h : NonpositiveExp rt) {q : Rat}
    (hq : 0 ≤ q) : ∃ p, exponential rt (LossPrecision.float64.round (.fin (-q))) = .fin p ∧
      0 ≤ p ∧ p ≤ 1 := by
  rw [round_neg_nonneg .float64 hq]
  rcases LossPrecision.float64.round_nonneg hq with hr | ⟨r, hr, hn⟩
  · rw [hr]

    exact ⟨0, rfl, Rat.le_refl, by decide⟩
  · rw [hr, jfFiniteNeg]
    by_cases hz : r = 0
    · subst r
      exact ⟨1, rfl, by decide, Rat.le_refl⟩
    · obtain ⟨p, hp, hp0, hp1⟩ := h (-r) (by grind)
      exact ⟨p, by simp [exponential, hp, show -r ≠ 0 by grind], hp0, hp1⟩

theorem acceptance_probability_range_holds : acceptance_probability_range := by
  intro rt precision temperature alpha before after hexp ht ha hba
  dsimp only
  let d := precision.round (.fin (after - before))
  let den := LossPrecision.float64.round (.fin (temperature * alpha))
  have hT := Rat.ne_of_gt ht
  have hA := Rat.ne_of_gt ha
  have hnT : ¬ temperature < 0 := by grind
  have hnA : ¬ alpha < 0 := by grind
  have hcalc : annealingAcceptance rt precision (.fin temperature) (.fin alpha) false false
      (.fin before) (.fin after) = exponential rt (LossPrecision.float64.round (-d / den)) := by
    simp [annealingAcceptance, negative, hT, hA, hnT, hnA, d, den]
  change (d = .fin 0 → den = .fin 0 → _) ∧ (d = .posInf → den = .posInf → _) ∧ _
  rw [hcalc]
  refine ⟨fun hd hden => by rw [hd, hden]; rfl,
    fun hd hden => by rw [hd, hden]; rfl, ?_⟩
  intro hz hInf
  have hd : 0 ≤ after - before := by grind
  have hden := Rat.le_of_lt (Rat.mul_pos ht ha)
  change ¬ (d = .fin 0 ∧ den = .fin 0) at hz
  change ¬ (d = .posInf ∧ den = .posInf) at hInf
  rcases precision.round_nonneg hd with hd | ⟨q, hd, hq⟩ <;>
    rcases LossPrecision.float64.round_nonneg hden with hden | ⟨r, hden, hr⟩
  · exact False.elim (hInf ⟨hd, hden⟩)
  · rw [show d = .posInf from hd, show den = .fin r from hden]
    have hn : ¬ r.num < 0 := by have := Rat.num_nonneg.mpr hr; omega
    refine ⟨0, ?_, Rat.le_refl, by decide⟩
    change exponential rt (LossPrecision.float64.round
      (if (true != decide (r.num < 0)) then .negInf else .posInf)) = .fin 0
    simp [hn, LossPrecision.round, exponential]
  · rw [show d = .fin q from hd, show den = .posInf from hden]
    exact ⟨1, rfl, by decide, Rat.le_refl⟩
  · by_cases hrz : r = 0
    · subst r
      have hqn : q ≠ 0 := fun he => hz ⟨he ▸ hd, hden⟩
      have hq' : -q < 0 := by grind
      rw [show d = .fin q from hd, show den = .fin 0 from hden, jfFiniteNeg,
        finite_div_zero_neg hq']
      exact ⟨0, rfl, Rat.le_refl, by decide⟩
    · have hr' : 0 < r := by grind
      rw [show d = .fin q from hd, show den = .fin r from hden,
        jfFiniteNeg, jfFiniteDiv _ _ hrz]
      have hqr : 0 ≤ q / r := Rat.mul_nonneg hq (Rat.le_of_lt (Rat.inv_pos.mpr hr'))
      rw [Rat.div_def, Rat.neg_mul, ← Rat.div_def]
      exact exp_nonpositive rt hexp hqr


example : 1 ≤ (1 : Int) ∧ (1 : Int) ≤ 2 ∧ (2 : Int) ≤ 3 ∧ 1 < (3 : Int) := by decide
example : NonpositiveExp { expFinite := fun _ => .fin (1 / 2) } := by
  intro x hx
  exact ⟨1 / 2, rfl, by decide, by decide⟩
example : 0 < (1 / 2 : Rat) ∧ 0 < (1 / 10 : Rat) ∧ 0 ≤ (1 : Rat) := by decide

end SymReg.Plugins
