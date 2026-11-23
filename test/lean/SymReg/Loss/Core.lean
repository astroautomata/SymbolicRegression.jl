import DynExpr.Eval.Scalars
import SymReg.Complexity

/-!
Mirrors of `src/LossFunctions.jl` at 103f5d42. Scalars use DE's `JF` with
separate IEEE rounding for floating costs; signed zeros are identified.
Columns are lists in sample order. Callback functions are arbitrary `Jl` functions;
the original options argument is held fixed by partial application. Evaluation is
abstract, with an adapter from DE's `eval_tree_array` output and completion flag.
-/

namespace SymReg.Loss
open DynExpr

inductive LossPrecision where
  | float16 | float32 | float64
  deriving DecidableEq

def pow2 (e : Int) : Rat :=
  if e < 0 then 1 / (2 : Rat)^e.natAbs else (2 : Rat)^e.natAbs

def LossPrecision.bits : LossPrecision → Nat
  | .float16 => 11
  | .float32 => 24
  | .float64 => 53

def LossPrecision.maxExponent : LossPrecision → Int
  | .float16 => 15
  | .float32 => 127
  | .float64 => 1023

def LossPrecision.maxFinite (p : LossPrecision) : Rat :=
  pow2 (p.maxExponent + 1) - pow2 (p.maxExponent + 1 - (p.bits : Int))

def LossPrecision.minNormal (p : LossPrecision) : Rat :=
  pow2 (1 - p.maxExponent)

def nearestEven (steps : Rat) : Nat :=
  let n := steps.num.natAbs / steps.den
  let remainder := steps.num.natAbs % steps.den
  if 2 * remainder > steps.den || (2 * remainder == steps.den && n % 2 == 1)
  then n + 1 else n

/-- Spacing of the rounding grid at `|q|`, clamped to the subnormal spacing. -/
def LossPrecision.ulp (p : LossPrecision) (q : Rat) : Rat :=
  let magnitude := if q < 0 then -q else q
  let guess := (magnitude.num.natAbs.log2 : Int) - (magnitude.den.log2 : Int)
  let exponent := if magnitude < pow2 guess then guess - 1 else guess
  pow2 (max exponent (1 - p.maxExponent) + 1 - (p.bits : Int))

/-- IEEE rounding to nearest, ties to even, including subnormals and overflow. -/
def LossPrecision.round (p : LossPrecision) : JF → JF
  | .fin q =>
    if q = 0 then .fin 0 else
    let magnitude := if q < 0 then -q else q
    let scale := p.ulp q
    let rounded := (nearestEven (magnitude / scale) : Rat) * scale
    if rounded > p.maxFinite then (if q < 0 then .negInf else .posInf)
    else .fin (if q < 0 then -rounded else rounded)
  | v => v

/-- The IEEE value projection with the two zeros distinguished. NaN payloads
are outside the scalar projection. -/
inductive SignedFloat where
  | ordinary (value : JF)
  | negativeZero
  deriving DecidableEq, Repr

def SignedFloat.value : SignedFloat → JF
  | .ordinary v => v
  | .negativeZero => .fin 0

def SignedFloat.signbit (x : SignedFloat) : Bool :=
  match x with
  | .negativeZero | .ordinary .negInf => true
  | .ordinary (.fin q) => decide (q < 0)
  | _ => false

def SignedFloat.roundResult (p : LossPrecision) (exact : JF) (negative : Bool) :
    SignedFloat :=
  let v := p.round exact
  if v = .fin 0 && negative then .negativeZero else .ordinary v

def SignedFloat.convert (p : LossPrecision) (x : SignedFloat) : SignedFloat :=
  roundResult p x.value x.signbit

def SignedFloat.Representable (p : LossPrecision) (x : SignedFloat) : Prop :=
  p.round x.value = x.value

-- Source: Julia v1.12.0 base/float.jl:495-498
def SignedFloat.add (p : LossPrecision) (x y : SignedFloat) : SignedFloat :=
  roundResult p (x.value + y.value)
    (x == .negativeZero && y == .negativeZero)

def SignedFloat.mul (p : LossPrecision) (x y : SignedFloat) : SignedFloat :=
  roundResult p (x.value * y.value) (x.signbit != y.signbit)

def SignedFloat.div (p : LossPrecision) (x y : SignedFloat) : SignedFloat :=
  let exact := JF.div (if y = .negativeZero then JF.neg x.value else x.value) y.value
  roundResult p exact (x.signbit != y.signbit)

example : SignedFloat.div .float32 (.ordinary (.fin (-1))) (.ordinary .posInf) =
    .negativeZero := by decide

example : SignedFloat.add .float32 .negativeZero .negativeZero = .negativeZero := by decide +kernel

example : SignedFloat.add .float32 .negativeZero (.ordinary (.fin 0)) =
    .ordinary (.fin 0) := by decide +kernel

private theorem nearestEven_half (steps : Rat) (hs : 0 ≤ steps) :
    ((nearestEven steps : Rat) - steps).abs ≤ 1 / 2 := by
  let a := steps.num.natAbs
  let d := steps.den
  let n := a / d
  let r := a % d
  have hnum : (a : Int) = steps.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hs)
  have hd : 0 < d := steps.den_pos
  have hdR : 0 < (d : Rat) := Rat.natCast_pos.mpr hd
  have hsteps : steps * (d : Rat) = (a : Rat) := by
    conv => lhs; lhs; rw [← Rat.num_divInt_den steps, Rat.divInt_ofNat, Rat.mkRat_eq_div]
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hdR), ← hnum, Rat.intCast_natCast]
  have hmod := Nat.mod_lt a hd
  have hsplit := Nat.div_add_mod a d
  change d * n + r = a at hsplit
  have hdecomp : (d : Rat) * (n : Rat) + (r : Rat) = (a : Rat) := by
    exact_mod_cast hsplit
  suffices h : (↑(nearestEven steps) - steps).abs * (d : Rat) ≤ 1 / 2 * (d : Rat) from
    Rat.le_of_mul_le_mul_right h hdR
  change ((↑(if 2 * r > d || (2 * r == d && n % 2 == 1) then n + 1 else n) :
    Rat) - steps).abs * (d : Rat) ≤ 1 / 2 * (d : Rat)
  split <;> rename_i h <;> simp only [Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  · have hlarge : (d : Rat) ≤ 2 * (r : Rat) := by
      rw [← Rat.natCast_ofNat (a := 2), ← Rat.natCast_mul, Rat.natCast_le_natCast]
      change d ≤ 2 * r
      omega
    have hr : (r : Rat) ≤ (d : Rat) := Rat.natCast_le_natCast.mpr (Nat.le_of_lt hmod)
    rw [Rat.natCast_add]
    have hn : 0 ≤ (n : Rat) + (1 : Nat) - steps := by
      apply Rat.le_of_mul_le_mul_right _ hdR
      grind
    rw [Rat.abs_of_nonneg hn]
    grind
  · have hsmall : 2 * (r : Rat) ≤ (d : Rat) := by
      rw [← Rat.natCast_ofNat (a := 2), ← Rat.natCast_mul, Rat.natCast_le_natCast]
      change 2 * r ≤ d
      omega
    have hr : 0 ≤ (r : Rat) := Rat.natCast_nonneg
    have hn : (n : Rat) - steps ≤ 0 := by
      apply Rat.le_of_mul_le_mul_right _ hdR
      grind
    rw [Rat.abs_of_nonpos hn]
    grind

theorem pow2_pos (e : Int) : 0 < pow2 e := by
  have hp : 0 < (2 : Rat) ^ e.natAbs := Rat.pow_pos (by decide)
  unfold pow2
  split
  · exact Rat.mul_pos (show (0 : Rat) < 1 by decide) (Rat.inv_pos.mpr hp)
  · exact hp

theorem LossPrecision.ulp_pos (p : LossPrecision) (q : Rat) : 0 < p.ulp q :=
  pow2_pos _

private theorem abs_mul_nonneg (a b : Rat) (hb : 0 ≤ b) :
    (a * b).abs = a.abs * b := by
  by_cases ha : 0 ≤ a
  · rw [Rat.abs_of_nonneg ha, Rat.abs_of_nonneg (Rat.mul_nonneg ha hb)]
  · have ha' : a ≤ 0 := by grind
    have hm := Rat.mul_le_mul_of_nonneg_right ha' hb
    rw [Rat.zero_mul] at hm
    rw [Rat.abs_of_nonpos ha', Rat.abs_of_nonpos hm, Rat.neg_mul]

theorem nearestEven_scaled_half (m scale : Rat) (hm : 0 ≤ m) (hs : 0 < scale) :
    ((nearestEven (m / scale) : Rat) * scale - m).abs ≤ scale / 2 := by
  have hsteps : 0 ≤ m / scale := Rat.mul_nonneg hm (Rat.le_of_lt (Rat.inv_pos.mpr hs))
  have he := Rat.mul_le_mul_of_nonneg_right (nearestEven_half (m / scale) hsteps)
    (Rat.le_of_lt hs)
  rw [← abs_mul_nonneg _ _ (Rat.le_of_lt hs), Rat.sub_eq_add_neg, Rat.add_mul,
    Rat.neg_mul, Rat.div_mul_cancel (Rat.ne_of_gt hs), ← Rat.sub_eq_add_neg] at he
  change ((nearestEven (m / scale) : Rat) * scale - m).abs ≤ scale * (2 : Rat)⁻¹
  rw [Rat.mul_comm scale]
  simpa only [Rat.div_def, Rat.one_mul] using he

/-- Every finite rounded result has at most half a grid step of absolute error. -/
theorem LossPrecision.round_error (p : LossPrecision) {q rounded : Rat}
    (h : p.round (.fin q) = .fin rounded) : (rounded - q).abs ≤ p.ulp q / 2 := by
  by_cases hz : q = 0
  · subst q
    have hr : rounded = 0 := by simpa [LossPrecision.round] using h.symm
    subst rounded
    simp only [Rat.sub_self, Rat.abs_zero]
    exact Rat.mul_nonneg (Rat.le_of_lt (p.ulp_pos 0))
      (Rat.le_of_lt (Rat.inv_pos.mpr (show (0 : Rat) < 2 by decide)))
  let magnitude := if q < 0 then -q else q
  let scale := p.ulp q
  have hs : 0 < scale := p.ulp_pos q
  have hm : 0 ≤ magnitude := by
    unfold magnitude
    split <;> grind
  have he := nearestEven_scaled_half magnitude scale hm hs
  let n : Rat := ↑(nearestEven (magnitude / scale))
  change (n * scale - magnitude).abs ≤ scale / 2 at he
  simp only [LossPrecision.round, ite_eq_right hz] at h
  change (if n * scale > p.maxFinite then (if q < 0 then JF.negInf else JF.posInf)
    else .fin (if q < 0 then -(n * scale) else n * scale)) = .fin rounded at h
  split at h
  · split at h <;> contradiction
  · injection h with hr
    rw [← hr]
    by_cases hq : q < 0
    · rw [ite_eq_left hq, show - (n * scale) - q = -(n * scale - magnitude) by
        simp only [magnitude, ite_eq_left hq]; grind, Rat.abs_neg]
      exact he
    · change ((if q < 0 then -(n * scale) else n * scale) - q).abs ≤ scale / 2
      rw [ite_eq_right hq]
      simpa only [magnitude, ite_eq_right hq] using he

/-- A half-step of headroom suffices to keep round-to-nearest finite. -/
theorem LossPrecision.round_finite_of_headroom (p : LossPrecision) (q : Rat)
    (h : q.abs + p.ulp q / 2 ≤ p.maxFinite) :
    ∃ rounded : Rat, p.round (.fin q) = .fin rounded := by
  by_cases hz : q = 0
  · subst q
    exact ⟨0, by simp [LossPrecision.round]⟩
  let m := if q < 0 then -q else q
  let scale := p.ulp q
  have hm : m = q.abs := by
    unfold m
    by_cases hq : q < 0
    · rw [ite_eq_left hq, Rat.abs_of_nonpos (Rat.le_of_lt hq)]
    · have hn : 0 ≤ q := by grind
      rw [ite_eq_right hq, Rat.abs_of_nonneg hn]
  let r : Rat := (nearestEven (m / scale) : Rat) * scale
  have hd : (r - m).abs ≤ scale / 2 :=
    nearestEven_scaled_half m scale (hm ▸ Rat.abs_nonneg) (p.ulp_pos q)
  have hle : r - m ≤ (r - m).abs := by
    by_cases hn : 0 ≤ r - m
    · rw [Rat.abs_of_nonneg hn]
      exact Rat.le_refl
    · have hn' : r - m ≤ 0 := by grind
      exact Rat.le_trans hn' Rat.abs_nonneg
  have hs := Rat.le_trans hle hd
  have hr : r ≤ p.maxFinite := by
    change q.abs + scale / 2 ≤ p.maxFinite at h
    grind
  refine ⟨if q < 0 then -r else r, ?_⟩
  have hnr : ¬ r > p.maxFinite := by grind
  simp only [LossPrecision.round, ite_eq_right hz]
  change (if r > p.maxFinite then _ else _) = _
  rw [ite_eq_right hnr]

theorem pow2_zpow (e : Int) : pow2 e = (2 : Rat) ^ e := by
  cases e with
  | ofNat n => simp [pow2, Rat.zpow_natCast, Int.not_lt.mpr (Int.natCast_nonneg n)]
  | negSucc n =>
    have he : Int.negSucc n = -(↑(n + 1) : Int) := by omega
    rw [he, Rat.zpow_neg, Rat.zpow_natCast]
    have hn : (-(↑(n + 1) : Int)) < 0 := by omega
    rw [pow2, ite_eq_left hn, Rat.div_def, Rat.one_mul, Int.natAbs_neg]
    rfl

theorem pow2_add (a b : Int) : pow2 (a + b) = pow2 a * pow2 b := by
  simp only [pow2_zpow]
  exact Rat.zpow_add (by decide) a b

theorem pow2_mono {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  let n := (b - a).toNat
  have hb : b = a + (n : Int) := by omega
  have hp (k : Nat) : (1 : Rat) ≤ (2 : Rat) ^ k := by
    induction k with
    | zero => exact Rat.le_refl
    | succ k ih =>
      rw [Rat.pow_succ]
      have hmul := Rat.mul_le_mul_of_nonneg_right ih (show (0 : Rat) ≤ 2 by decide)
      rw [Rat.one_mul] at hmul
      exact Rat.le_trans (by decide) hmul
  have hmul := Rat.mul_le_mul_of_nonneg_left (hp n) (Rat.le_of_lt (pow2_pos a))
  rw [Rat.mul_one] at hmul
  rwa [hb, pow2_add, pow2_zpow (n : Int)]

theorem pow2_guess_lower (m : Rat) (hm : 0 < m) :
    pow2 ((m.num.natAbs.log2 : Int) - (m.den.log2 : Int) - 1) ≤ m := by
  let a := m.num.natAbs
  let b := m.den
  have hnonneg : 0 ≤ m.num := Rat.num_nonneg.mpr (Rat.le_of_lt hm)
  have hcast : (a : Int) = m.num := Int.natAbs_of_nonneg hnonneg
  have ha : a ≠ 0 := by
    intro hz
    apply Rat.ne_of_gt hm
    apply Rat.num_eq_zero.mp
    omega
  have hb : 0 < b := m.den_pos
  let e := (a.log2 : Int) - (b.log2 : Int) - 1
  have he : e + (b.log2 + 1 : Nat) = (a.log2 : Int) := by
    dsimp [e]
    omega
  have htop : pow2 e * ((2 ^ (b.log2 + 1) : Nat) : Rat) = ((2 ^ a.log2 : Nat) : Rat) := by
    rw [show ((2 ^ (b.log2 + 1) : Nat) : Rat) = pow2 (↑(b.log2 + 1) : Int) by
      rw [pow2_zpow, Rat.zpow_natCast, Rat.natCast_pow]; rfl, ← pow2_add, he]
    simp [pow2_zpow, Rat.zpow_natCast]
  have hd : m * (b : Rat) = (a : Rat) := by
    conv => lhs; lhs; rw [← Rat.num_divInt_den m, Rat.divInt_ofNat, Rat.mkRat_eq_div]
    rw [Rat.div_mul_cancel (Rat.ne_of_gt (Rat.natCast_pos.mpr hb)), ← hcast,
      Rat.intCast_natCast]
  apply Rat.le_of_mul_le_mul_right _ (Rat.natCast_pos.mpr hb)
  rw [hd]
  have hdlog : (b : Rat) ≤ ((2 ^ (b.log2 + 1) : Nat) : Rat) :=
    Rat.natCast_le_natCast.mpr (Nat.le_of_lt Nat.lt_log2_self)
  apply Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hdlog (Rat.le_of_lt (pow2_pos e)))
  rw [htop]
  exact Rat.natCast_le_natCast.mpr (Nat.log2_self_le ha)

/-- Above the smallest normal magnitude, the spacing is at most the relative
step of the precision. The clamped step below it uses `minNormal` instead. -/
theorem LossPrecision.ulp_le (p : LossPrecision) (q : Rat) (hq : q ≠ 0) :
    p.ulp q ≤ max q.abs p.minNormal * pow2 (1 - (p.bits : Int)) := by
  let m := if q < 0 then -q else q
  have hm : m = q.abs := by
    unfold m
    by_cases hq : q < 0
    · rw [ite_eq_left hq, Rat.abs_of_nonpos (Rat.le_of_lt hq)]
    · have hn : 0 ≤ q := by grind
      rw [ite_eq_right hq, Rat.abs_of_nonneg hn]
  let guess := (m.num.natAbs.log2 : Int) - (m.den.log2 : Int)
  let e := if m < pow2 guess then guess - 1 else guess
  let emin := 1 - p.maxExponent
  change pow2 (max e emin + 1 - (p.bits : Int)) ≤ _
  rw [show max e emin + 1 - (p.bits : Int) = max e emin + (1 - (p.bits : Int)) by omega,
    pow2_add]
  apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (pow2_pos _))
  by_cases h : e ≤ emin
  · have hmax : max e emin = emin := by omega
    rw [hmax]
    change p.minNormal ≤ max q.abs p.minNormal
    grind
  · have hmax : max e emin = e := by omega
    rw [hmax]
    have hpos : 0 < m := hm ▸ Rat.abs_pos_iff.mpr hq
    have he : pow2 e ≤ m := by
      unfold e
      split
      · exact pow2_guess_lower m hpos
      · grind
    rw [← hm]
    exact Rat.le_trans he (by grind)

/-- The literal is parsed as Float64 before Julia converts it to `L`. -/
def LossPrecision.floor : LossPrecision → Rat
  | .float16 => 1311 / 131072
  | .float32 => 5368709 / 536870912
  | .float64 => 5764607523034235 / 576460752303423488


/-- Dataset fields read by losses (`src/Dataset.jl:65-81`). -/
structure Basic where
  columns : List (List JF)
  y : Option (List JF)
  weights : Option (List JF) := none
  targetSameType : Bool := true
  weightsSameType : Bool := true
  avgY : Option JF := none
  useBaseline : Bool := true
  baselineLoss : JF := .fin 1
  lossPrecision : LossPrecision := .float64
  xUnits : Bool := false
  yUnits : Bool := false

/-- BasicDataset or a SubDataset view (`src/Dataset.jl:90-96,258-259`). -/
structure Dataset where
  full : Basic
  indices : Option (List Nat) := none

/-- Checked one-based array indexing used by the loss closures (`src/LossFunctions.jl:60,71`). -/
def at1 {T : Type} (xs : List T) (i : Nat) : Jl T :=
  match (if i = 0 then none else xs[i - 1]?) with
  | some x => .ok x
  | none => .error .boundsError

/-- View indexing preserves order and repeated indices (`src/Dataset.jl:97-107`). -/
def selected {T : Type} (xs : List T) : Option (List Nat) → Jl (List T)
  | none => .ok xs
  | some indices => indices.mapM (at1 xs)

/-- `.X` returns precisely the selected columns (`src/Dataset.jl:98-99`). -/
def getX (d : Dataset) : Jl (List (List JF)) := selected d.full.columns d.indices

/-- Optional `.y`/`.weights` views (`src/Dataset.jl:100-105`). -/
def selectedOptional (xs : Option (List JF)) (indices : Option (List Nat)) :
    Jl (Option (List JF)) :=
  match xs with
  | none => .ok none
  | some xs => (selected xs indices).map some

/-- Dataset weights, including the SubDataset view (`src/Dataset.jl:103-105,255`). -/
def getWeights (d : Dataset) : Jl (Option (List JF)) := selectedOptional d.full.weights d.indices

-- Source: src/Dataset.jl:100-102
-- elseif prop == :y
--     y = get_full_dataset(d).y
--     return isnothing(y) ? y : view(y, get_indices(d))
def getTarget (d : Dataset) : Jl (Option (List JF)) := selectedOptional d.full.y d.indices

/-- The target array assertion in `_eval_loss` (`src/LossFunctions.jl:132,137`). -/
def getY (d : Dataset) : Jl (List JF) := do
  match ← getTarget d with
  | some y => pure y
  | none => throw (.errorException "TypeError: dataset.y is not an AbstractArray")

/-- `is_weighted` (`src/Dataset.jl:255`); SubDataset forwards absence unchanged. -/
def isWeighted (d : Dataset) : Jl Bool := (getWeights d).map Option.isSome

/-- Floating sum used by `mean`/`sum` (`src/LossFunctions.jl:58-72`). -/
def sumF (xs : List JF) : JF := xs.foldl JF.add (.fin 0)

-- Source: Julia base/reduce.jl:245-274, 419-433 (linear array, default block size)
def pairwiseSum (p : LossPrecision) (xs : List JF) : JF :=
  go xs.length xs
where
  go : Nat → List JF → JF
    | 0, _ => .fin 0
    | fuel + 1, xs =>
      let add := fun a b => p.round (a + b)
      match xs with
      | [] => .fin 0
      | x :: rest =>
        if xs.length ≤ 1024 then rest.foldl add x
        else
          let middle := (xs.length + 1) / 2
          add (go fuel (xs.take middle)) (go fuel (xs.drop middle))

def floatCount (p : LossPrecision) (n : Nat) : JF := p.round (.fin (n : Rat))

/-- Elementwise function versus SupervisedLoss (`src/LossFunctions.jl:54-74`).
Custom weighted functions receive the weight themselves, with no extra multiplication. -/
inductive Elementwise where
  | supervised (f : JF → JF → Jl JF)
  | custom (f : JF → JF → Jl JF) (weighted : JF → JF → JF → Jl JF)

/-- Unweighted elementwise call (`src/LossFunctions.jl:57-62`). -/
def element (l : Elementwise) (x y : JF) : Jl JF :=
  match l with
  | .supervised f | .custom f _ => f x y

/-- SupervisedLoss weights multiply the binary loss; custom losses take three arguments
(`src/LossFunctions.jl:68-72`, LossFunctions `sum(...; normalize=true)`). -/
def weightedElement (l : Elementwise) (x y w : JF)
    (p : LossPrecision := .float64) : Jl JF :=
  match l with
  | .supervised f => (f x y).map (fun v => p.round (w * v))
  | .custom _ f => f x y w

/-- SupervisedLoss uses `eachindex` of all arrays and checks matching axes
(`src/LossFunctions.jl:58,69`; LossFunctions `src/losses.jl:48-60`). -/
def matchingAxes (l : Elementwise) (x y : List JF) (w : Option (List JF) := none) : Bool :=
  match l with
  | .custom _ _ => true
  | .supervised _ => decide (x.length = y.length) &&
      (w.map (fun ws => decide (x.length = ws.length))).getD true

def lossTypeDispatch {m : Type → Type} [MonadExceptOf JlError m] {R : Type}
    (sameType : Bool) (diagnostic : Unit → String) (same : Unit → m R) : m R :=
  if sameType then same () else throw (.errorException (diagnostic ()))

-- Source: src/LossFunctions.jl:38-52
-- function _loss(
--     ::AbstractArray{T1}, ::AbstractArray{T2}, ::LT
-- ) where {T1,T2,LT<:Union{Function,SupervisedLoss}}
--     return error(
--         "Element type of `x` is $(T1) is different from element type of `y` which is $(T2)."
--     )
-- end
-- function _weighted_loss(
--     ::AbstractArray{T1}, ::AbstractArray{T2}, ::AbstractArray{T3}, ::LT
-- ) where {T1,T2,T3,LT<:Union{Function,SupervisedLoss}}
--     return error(
--         "Element type of `x` is $(T1), element type of `y` is $(T2), and element type of `w` is $(T3). " *
--         "All element types must be the same.",
--     )
-- end
def arrayLossDispatch {m : Type → Type} [MonadExceptOf JlError m] {R : Type}
    (elementType : Nat → Nat) (render : Nat → String) (x y : Nat)
    (same : Nat → Nat → m R) : m R :=
  let tx := elementType x
  let ty := elementType y
  lossTypeDispatch (tx == ty)
    (fun _ => s!"Element type of `x` is {render tx} is different from element type of `y` which is {render ty}.")
    (fun _ => same x y)

def weightedArrayLossDispatch {m : Type → Type} [MonadExceptOf JlError m] {R : Type}
    (elementType : Nat → Nat) (render : Nat → String) (x y w : Nat)
    (same : Nat → Nat → Nat → m R) : m R :=
  let tx := elementType x
  let ty := elementType y
  let tw := elementType w
  lossTypeDispatch (tx == ty && tx == tw)
    (fun _ => s!"Element type of `x` is {render tx}, element type of `y` is {render ty}, and element type of `w` is {render tw}. All element types must be the same.")
    (fun _ => same x y w)

-- Source: src/LossFunctions.jl:54-63
-- function _loss(
--     x::AbstractArray{T}, y::AbstractArray{T}, loss::LT
-- ) where {T,LT<:Union{Function,SupervisedLoss}}
--     if loss isa SupervisedLoss
--         return LossFunctions.mean(loss, x, y)
--     else
--         l(i) = loss(x[i], y[i])
--         return LossFunctions.mean(l, eachindex(x))
--     end
-- end
-- For an array mean, Statistics probes f(first(A))/1 before the mapped sum.
-- On the homogeneous floating path the probe does not change the accumulator type.
def lossArray (x y : List JF) (l : Elementwise) (sameType : Bool := true)
    (p : LossPrecision := .float64) : Jl JF := do
  lossTypeDispatch sameType (fun _ => "Element types of x and y differ") (fun _ => pure ())
  if !matchingAxes l x y then throw (.errorException "DimensionMismatch")
  if x.isEmpty then throw (.argumentError "reducing over an empty collection is not allowed")
  let point := fun (i : Nat) => do
    let xi ← at1 x (i + 1)
    let yi ← at1 y (i + 1)
    element l xi yi
  let _ ← point 0
  let values ← (List.range x.length).mapM point
  pure (p.round (pairwiseSum p values / floatCount p x.length))

-- Source: src/LossFunctions.jl:65-74
-- function _weighted_loss(
--     x::AbstractArray{T}, y::AbstractArray{T}, w::AbstractArray{T}, loss::LT
-- ) where {T,LT<:Union{Function,SupervisedLoss}}
--     if loss isa SupervisedLoss
--         return sum(loss, x, y, w; normalize=true)
--     else
--         l(i) = loss(x[i], y[i], w[i])
--         return sum(l, eachindex(x)) / sum(w)
--     end
-- end
def weightedLoss (x y w : List JF) (l : Elementwise) (sameType : Bool := true)
    (p : LossPrecision := .float64) : Jl JF := do
  lossTypeDispatch sameType (fun _ => "Element types of x, y and w differ") (fun _ => pure ())
  if !matchingAxes l x y (some w) then throw (.errorException "DimensionMismatch")
  if x.isEmpty then throw (.argumentError "reducing over an empty collection is not allowed")
  let values ← (List.range x.length).mapM (fun i => do
    match l with
    | .supervised f =>
      let wi ← at1 w (i + 1)
      let xi ← at1 x (i + 1)
      let yi ← at1 y (i + 1)
      weightedElement (.supervised f) xi yi wi p
    | .custom _ f =>
      let xi ← at1 x (i + 1)
      let yi ← at1 y (i + 1)
      let wi ← at1 w (i + 1)
      f xi yi wi)
  pure (p.round (pairwiseSum p values / pairwiseSum p w))

/-- Expression wrappers retain metadata; nodes pass directly (`src/LossFunctions.jl:180-186`). -/
inductive Expr where
  | node (tree : Tree JF)
  | expression (tree : Tree JF) (metadata : Nat)

def Expr.tree : Expr → Tree JF
  | .node t | .expression t _ => t

def Expr.isExpression : Expr → Bool
  | .expression _ _ => true
  | .node _ => false

/-- A PopMember tree field or a direct expression (`src/LossFunctions.jl:194-196`). -/
inductive Member where
  | direct (tree : Expr)
  | population (tree : Expr) (cachedComplexity : Int)

/-- `get_tree_from_member`, both methods (`src/LossFunctions.jl:195-196`). -/
def getTreeFromMember : Member → Expr
  | .direct t | .population t _ => t

abbrev Context := DynExpr.Eval.EvalContext JF
abbrev Reply := Option (JVec JF) × Bool
abbrev Run := Expr → List (List JF) → Option Context → Jl (Reply × Option Context)

/-- Adapter from DE's actual `eval_tree_array` return contract
(`src/LossFunctions.jl:87-94,103-110`). -/
def fromDE (r : Jl (JVec JF × Bool)) : Jl Reply :=
  r.map (fun (x, complete) => (some x, complete))

/-- Both `eval_tree_dispatch` methods preserve an array's completion flag and force
`false` when the expression implementation returns `nothing` (`src/LossFunctions.jl:80-111`). -/
def dispatchReply (r : Reply) : Reply :=
  match r.1 with
  | none => (none, false)
  | some x => (some x, r.2)

/-- Partially applied objective methods; method availability remains arbitrary
(`src/LossFunctions.jl:148-164`). -/
structure Objective where
  accepts4 : Expr → Basic → Option (List Nat) → Bool
  call3 : Expr → Dataset → Jl JF
  call4 : Expr → Basic → Option (List Nat) → Jl JF

-- Source: src/LossFunctions.jl:155-163
-- full_dataset = get_full_dataset(dataset)
-- idx = @something(idx, get_indices(dataset), Some(nothing))
-- if hasmethod(f, typeof((tree, full_dataset, options, idx)))
--     return f(tree, full_dataset, options, idx)
-- else
--     return f(tree, dataset, options)
-- end
def evaluatorWith {E D F O I L : Type} (getFull : D → F) (getIndices : D → Option I)
    (hasMethod : E → F → O → Option I → Bool) (call3 : E → D → O → Jl L)
    (call4 : E → F → O → Option I → Jl L)
    (tree : E) (d : D) (options : O) (idx : Option I) : Jl L :=
  let full := getFull d
  let resolved := idx.or (getIndices d)
  if hasMethod tree full options resolved then call4 tree full options resolved
  else call3 tree d options

/-- Value projection for the default dataset and partially applied options. -/
def evaluator (f : Objective) (tree : Expr) (d : Dataset) (idx : Option (List Nat)) : Jl JF :=
  evaluatorWith Dataset.full Dataset.indices (fun e full _ i => f.accepts4 e full i)
    (fun e original _ => f.call3 e original) (fun e full _ i => f.call4 e full i) tree d () idx

/-- Loss-related option projections (`src/LossFunctions.jl:29-35,129-142,179-188,218-220,282`). -/
structure Options where
  elementwise : Elementwise
  run : Run
  lossFunction : Option Objective := none
  lossFunctionExpression : Option Objective := none
  parsimony : JF := .fin 0
  penalty : Option JF := none
  dimensionalCheck : Expr → Dataset → Jl Bool := fun _ _ => .ok false
  complexity : Member → Jl Int := fun _ => .ok 1
  createExpression : JF → Dataset → Jl Expr := fun v _ => .ok (.expression (.const v) 0)
  bumper : Bool := false
  takesContext : Bool := true
  turbo : Bool := false

/-- `create_eval_context`; allocation uses DE's uninitialised-zero abstraction
(`src/LossFunctions.jl:29-36`; DE `Eval/Scalars.lean:10-22`). -/
def createEvalContext (d : Dataset) (o : Options) (numArrays : Int) : Jl (Option Context) := do
  if o.bumper || !o.takesContext then return none
  let columns ← getX d
  let arrays := Array.replicate numArrays.toNat (Array.replicate columns.length (JF.fin 0))
  pure (some ⟨o.turbo, false, true, .vec arrays 0, true⟩)

/-- `reset_index!` before evaluation (`src/LossFunctions.jl:123`). -/
def resetBuffer : DynExpr.Eval.Buf JF → DynExpr.Eval.Buf JF
  | .none => .none
  | .mat a _ => .mat a 0
  | .vec arrays _ => .vec arrays 0

def resetContext : Option Context → Option Context
  | none => none
  | some c => some { c with buffer := resetBuffer c.buffer }

-- Source: src/LossFunctions.jl:274-283
-- if !violates_dimensional_constraints(tree, dataset, options)
--     return zero(L)
-- end
-- return convert(L, something(options.dimensional_constraint_penalty, 1000))
def dimensionalRegularizationWith {L : Type} (violates : Unit → Jl Bool)
    (getZero convertPenalty : Unit → Jl L) : Jl L := do
  if ← violates () then convertPenalty () else getZero ()

-- Source: src/DimensionalAnalysis.jl:223-230,258-275
-- X = dataset.X
-- return violates_dimensional_constraints(
--     tree, dataset.X_units, dataset.y_units, (@view X[:, 1]), options
-- )
def nodeDimensionalCheck (columns : Jl (List (List JF))) (xUnits yUnits : Bool)
    (check : List JF → Jl Bool) : Jl Bool := do
  let x ← columns
  let first ← at1 x 1
  if xUnits then check first
  else if yUnits then
    throw (.errorException "This should never happen. Please submit a bug report.")
  else pure false

-- Source: src/TemplateExpression.jl:909-916
-- @assert !has_units(dataset)
-- return false
def templateDimensionalCheck (xUnits yUnits : Bool) : Jl Bool :=
  if xUnits || yUnits then .error (.assertionError "!has_units(dataset)") else .ok false

-- Source: src/DimensionalAnalysis.jl:231-235
-- return violates_dimensional_constraints(get_tree(tree), dataset, options)
def expressionDimensionalCheck {E : Type} (getTree : E → Jl (Tree JF)) (e : E)
    (columns : Unit → Jl (List (List JF))) (xUnits yUnits : Bool)
    (check : Tree JF → List JF → Jl Bool) : Jl Bool := do
  let tree ← getTree e
  nodeDimensionalCheck (columns ()) xUnits yUnits (check tree)

/-- Value projection for the node check and the default IEEE zero. -/
def dimensionalRegularization (tree : Expr) (d : Dataset) (o : Options) : Jl JF :=
  dimensionalRegularizationWith (fun _ =>
    nodeDimensionalCheck (getX d) d.full.xUnits d.full.yUnits (fun _ => o.dimensionalCheck tree d))
    (fun _ => .ok (.fin 0))
    (fun _ => .ok (d.full.lossPrecision.round (o.penalty.getD (.fin 1000))))

-- Source: src/LossFunctions.jl:80-111
-- A = expected_array_type(dataset.X, typeof(tree))
-- out, complete = eval_tree_array(tree, dataset.X, options; eval_context=eval_context)
-- if isnothing(out)
--     return out, false
-- else
--     return out::A, complete::Bool
-- end
def evalDispatchWith {m : Type → Type} [Monad m] {X A Raw Flag P : Type}
    (readX : Unit → m X) (expectedType : X → m A)
    (evaluate : X → m (Option Raw × Flag))
    (assertOutput : A → Raw → m P) (assertBool : Flag → m Bool) :
    m (Option P × Bool) := do
  let expected ← expectedType (← readX ())
  let (out, flag) ← evaluate (← readX ())
  match out with
  | none => pure (none, false)
  | some raw =>
    let checked ← assertOutput expected raw
    let complete ← assertBool flag
    pure (some checked, complete)

-- Source: src/LossFunctions.jl:116-145
-- eval_context === nothing || reset_index!(eval_context.buffer)
-- (prediction, completion) = eval_tree_dispatch(tree, dataset, options, eval_context)
-- if !completion || isnothing(prediction)
--     return L(Inf)
-- end
-- loss_val = if is_weighted(dataset)
--     _weighted_loss(prediction, dataset.y::AbstractArray, dataset.weights, options.elementwise_loss)
-- else
--     _loss(prediction, dataset.y::AbstractArray, options.elementwise_loss)
-- end
-- if regularization
--     loss_val += dimensional_regularization(tree, dataset, options)
-- end
-- return loss_val
def evalLossDefaultWith {m : Type → Type} [Monad m] {P V L : Type}
    (reset : Unit → m Unit) (dispatch : Unit → m (Option P × Bool))
    (infinity : Unit → m L) (aggregate : P → m V) (regularization : Bool)
    (addPenalty : V → m V) (convert : V → m L) : m L := do
  reset ()
  let (prediction, complete) ← dispatch ()
  if !complete then return ← infinity ()
  match prediction with
  | none => infinity ()
  | some out =>
    let loss ← aggregate out
    let penalized ← if regularization then addPenalty loss else pure loss
    convert penalized

/-- The homogeneous floating projection with DE's typed array result. -/
def evalLossDefault (tree : Expr) (d : Dataset) (o : Options) (regularization : Bool)
    (context : Option Context) : Jl (JF × Option Context) :=
  (evalLossDefaultWith (m := StateT (Option Context) Jl)
    (fun _ => modify resetContext)
    (fun _ => evalDispatchWith (fun _ => StateT.lift (getX d)) (fun _ => pure ())
      (fun columns => do
        let (reply, after) ← StateT.lift (o.run tree columns (← get))
        set after
        pure reply)
      (fun _ out => pure out) pure)
    (fun _ => pure .posInf)
    (fun x => StateT.lift (do
      if ← isWeighted d then
        let y ← getY d
        let weights ← getWeights d
        weightedLoss x.toList y (weights.getD []) o.elementwise
          (d.full.targetSameType && d.full.weightsSameType)
      else
        let y ← getY d
        lossArray x.toList y o.elementwise d.full.targetSameType))
    regularization (fun loss => StateT.lift (do
      let penalty ← dimensionalRegularization tree d o
      pure (d.full.lossPrecision.round (loss + penalty))))
    (fun loss => pure (d.full.lossPrecision.round loss))).run context

-- Source: src/InterfaceDynamicExpressions.jl:25-42
-- `depwarn` is the Base logging call, which can throw under --depwarn=error.
def processContext {A : Type} (context deprecated : Option A)
    (depwarn : String → String → Jl Unit) (functionName : String) : Jl (Option A) := do
  match deprecated with
  | none => pure context
  | some c =>
    depwarn "The `eval_options` keyword is deprecated; use `eval_context` instead." functionName
    if context.isSome then
      throw (.assertionError "Cannot use both `eval_context` and deprecated `eval_options`.")
    else pure (some c)

/-- `eval_loss`, custom-objective priority and expression assertion included
(`src/LossFunctions.jl:167-192`). `idx` is passed only to custom objectives. -/
def evalLoss (tree : Expr) (d : Dataset) (o : Options) (regularization : Bool := true)
    (idx : Option (List Nat) := none) (context deprecated : Option Context := none)
    (unknownKeywords : List String := [])
    (depwarn : String → String → Jl Unit := fun _ _ => .ok ()) : Jl (JF × Option Context) := do
  let context ← processContext context deprecated depwarn "eval_loss"
  if !unknownKeywords.isEmpty then throw (.methodError "unknown loss keyword")
  match o.lossFunction with
  | some f => return (← evaluator f (.node tree.tree) d idx, context)
  | none => match o.lossFunctionExpression with
    | some f =>
      if !tree.isExpression then throw (.assertionError "tree isa AbstractExpression")
      return (← evaluator f tree d idx, context)
    | none => evalLossDefault tree d o regularization context

/-- Julia comparison `baseline >= L(0.01)`; NaN compares false
(`src/LossFunctions.jl:212`). -/
def baselineEligible (precision : LossPrecision) : JF → Bool
  | .fin b => decide (precision.floor ≤ b)
  | .posInf => true
  | .nan | .negInf => false

/-- The positive floor applies even when baseline use is disabled
(`src/LossFunctions.jl:212-216`). -/
def normalization (useBaseline : Bool) (baseline : JF)
    (precision : LossPrecision := .float64) : JF :=
  if baselineEligible precision baseline && useBaseline then baseline else .fin precision.floor

-- Source: src/PopMember.jl:187-201
-- complexity = getfield(member, :complexity)
-- complexity == -1 && return recompute_complexity!(member, options; break_sharing)
-- return complexity
-- complexity = compute_complexity(member.tree, options; break_sharing)
-- setfield!(member, :complexity, complexity)
-- return complexity
def memberCostSize (compute : Member → Jl Int) (member : Member) : Jl Int × Member :=
  match member with
  | .direct _ => (compute member, member)
  | .population tree cached =>
    if cached = -1 then
      match compute (.direct tree) with
      | .error err => (.error err, member)
      | .ok size => (.ok size, .population tree size)
    else (.ok cached, member)

def costAfterDivisor {F I S : Type}
    (divide add : F → F → F) (penalty : I → F)
    (getSize : S → Jl I × S) (loss divisor : F) (complexity : Option I)
    (s : S) : Jl F × S :=
  let normalized := divide loss divisor
  let (size, after) := match complexity with
    | some n => ((Except.ok n : Jl I), s)
    | none => getSize s
  (size.map (fun n => add normalized (penalty n)), after)

-- Source: src/LossFunctions.jl:203-223
-- function loss_to_cost(
--     loss::L,
--     use_baseline::Bool,
--     baseline::L,
--     member,
--     options::AbstractOptions,
--     complexity::Union{Int,Nothing}=nothing,
-- )::L where {L<:LOSS_TYPE}
--     # TODO: Come up with a more general normalization scheme.
--     normalization = if baseline >= L(0.01) && use_baseline
--         baseline
--     else
--         L(0.01)
--     end
--     loss_val = loss / normalization
--     size = @something(complexity, compute_complexity(member, options))
--     parsimony_term = size * options.parsimony
--     loss_val += L(parsimony_term)
--
--     return loss_val
-- end
def lossToCost (loss : JF) (useBaseline : Bool) (baseline : JF) (member : Member)
    (o : Options) (complexity : Option Int := none)
    (precision : LossPrecision := .float64) : Jl JF :=
  (costAfterDivisor (fun a b => precision.round (a / b))
    (fun a b => precision.round (a + b))
    (fun n => precision.round (LossPrecision.float64.round
      (LossPrecision.float64.round (.fin (n : Rat)) * o.parsimony)))
    (fun s => ((memberCostSize o.complexity member).1, s))
    loss (normalization useBaseline baseline precision) complexity ()).1

/-- IEEE specialization of `loss_to_cost`, with the member cache owned by
`compute_complexity` when no explicit complexity is supplied. -/
def lossToCostIEEE {S : Type} (p : LossPrecision) (loss : SignedFloat)
    (useBaseline : Bool) (baseline parsimony : SignedFloat) (member : Nat)
    (compute : Nat → S → Jl Int64 × S) (complexity : Option Int64)
    (s : S) : Jl SignedFloat × S :=
  let divisor := if baselineEligible p baseline.value && useBaseline
    then baseline else .ordinary (.fin p.floor)
  costAfterDivisor (SignedFloat.div p) (SignedFloat.add p)
    (fun (n : Int64) =>
      let size64 := SignedFloat.ordinary (LossPrecision.float64.round (.fin (n.toInt : Rat)))
      (SignedFloat.mul .float64 size64 parsimony).convert p)
    (compute member) loss divisor complexity s

/-- `eval_cost` returns `(cost, loss)` and keeps the evaluation context's mutations
(`src/LossFunctions.jl:226-247`). -/
def evalCost (d : Dataset) (member : Member) (o : Options) (complexity : Option Int := none)
    (context deprecated : Option Context := none) (unknownKeywords : List String := [])
    (depwarn : String → String → Jl Unit := fun _ _ => .ok ()) :
    Jl ((JF × JF) × Option Context) := do
  let context ← processContext context deprecated depwarn "eval_cost"
  if !unknownKeywords.isEmpty then throw (.methodError "unknown cost keyword")
  let (loss, context') ← evalLoss (getTreeFromMember member) d o true none context
  let cost ← lossToCost loss d.full.useBaseline d.full.baselineLoss member o complexity
    d.full.lossPrecision
  pure ((cost, loss), context')

/-- Finite baselines, including zero and negative values, enable normalization;
NaN and either infinity store one and disable it (`src/LossFunctions.jl:264-270`). -/
def updateFromValue (d : Basic) (value : JF) : Basic :=
  if value.valid then { d with baselineLoss := value, useBaseline := true }
  else { d with baselineLoss := .fin 1, useBaseline := false }

abbrev LossEffect (S A : Type) := S → Jl A × S

/-- A basic dataset's field store is separate from storage reached through its
constant fields, which callbacks can still mutate. -/
structure BaselineFields (R L : Type) where
  references : R
  loss : L
  enabled : Bool

-- Source: src/LossFunctions.jl:257-272
/-
function update_baseline_loss!(
    dataset::Dataset{T,L}, options::AbstractOptions
) where {T<:DATA_TYPE,L<:LOSS_TYPE}
    example_tree = create_expression(init_value(T), options, dataset)
    baseline_loss = eval_loss(example_tree, dataset, options)
    if isfinite(baseline_loss)
        dataset.baseline_loss = baseline_loss
        dataset.use_baseline = true
    else
        dataset.baseline_loss = one(L)
        dataset.use_baseline = false
    end
    return nothing
end
-/
def updateBaselineFields {S D T E L : Type}
    (init : LossEffect S T) (create : T → D → LossEffect S E)
    (eval : E → D → LossEffect S L) (isfinite : L → LossEffect S Bool)
    (one : LossEffect S L) (putLoss : D → L → LossEffect S Unit)
    (putEnabled : D → Bool → LossEffect S Unit) (dataset : D) : LossEffect S Unit :=
  fun s =>
    match init s with
    | (.error e, s') => (.error e, s')
    | (.ok initial, s') =>
      match create initial dataset s' with
      | (.error e, s'') => (.error e, s'')
      | (.ok exampleTree, s'') =>
        match eval exampleTree dataset s'' with
        | (.error e, s''') => (.error e, s''')
        | (.ok loss, s''') =>
          match isfinite loss s''' with
          | (.error e, checked) => (.error e, checked)
          | (.ok finite, checked) =>
            let (value, ready) := if finite then (.ok loss, checked) else one checked
            match value with
            | .error e => (.error e, ready)
            | .ok baseline =>
              match putLoss dataset baseline ready with
              | (.error e, after) => (.error e, after)
              | (.ok (), after) => putEnabled dataset finite after

-- Source: src/InterfaceDataTypes.jl:11-14
-- init_value(::Type{T}) where {T<:Number} = zero(T)
-- function init_value(::Type{T}) where {T}
--     return error("No `init_value` method defined for type $T. Please define one.")
-- end
inductive InitValueMethod (S T : Type) where
  | numeric (zero : LossEffect S T)
  | extension (f : LossEffect S T)
  | unsupported (typeName : String)

def initValue {S T : Type} : InitValueMethod S T → LossEffect S T
  | .numeric zero => zero
  | .extension f => f
  | .unsupported name => fun s =>
    (.error (.errorException s!"No `init_value` method defined for type {name}. Please define one."), s)

private def basicBaselineWrite (f : Basic → Basic) : LossEffect Dataset Unit :=
  fun d => if d.indices.isSome then (.error (.errorException "setfield!: immutable SubDataset"), d)
    else (.ok (), { d with full := f d.full })

/-- Numeric projection used by the baseline-average counterexample. -/
def updateBaselineLoss (d : Dataset) (o : Options) : Jl Dataset :=
  let (out, after) := updateBaselineFields
    (initValue (.numeric (fun s => (.ok (.fin 0), s))))
    (fun val _ s => (o.createExpression val s, s))
    (fun e _ s => ((evalLoss e s o).map Prod.fst, s))
    (fun value s => (.ok value.valid, s))
    (fun s => (.ok (.fin 1), s))
    (fun _ value => basicBaselineWrite fun d => { d with baselineLoss := value })
    (fun _ enabled => basicBaselineWrite fun d => { d with useBaseline := enabled })
    () d
  out.map (fun _ => after)

-- Source: src/LossFunctions.jl:249-250; src/deprecates.jl:31-39
-- Base's generated deprecated method warns before forwarding.
def scoreFunc (d : Dataset) (member : Member) (o : Options)
    (complexity : Option Int := none)
    (depwarn : Jl Unit := .ok ()) : Jl ((JF × JF) × Option Context) := do
  depwarn
  evalCost d member o complexity

end SymReg.Loss
