import SymReg.Operators.Core

namespace SymReg.Operators
open DynExpr
open DynExpr.Expressions.Sampling (greater)
open SymReg.HofMig (less greaterEqual)

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-- An error from the underlying operator can reach the caller only inside
the guarded domain. -/
private def unaryGuardsContract : Prop := ∀ (base : Unary → JF → Jl JF) (op : Unary) (x : JF),
  safeUnary base true op x = if domain op x then base op x else .ok .nan

private theorem unaryGuardsContract_holds : unaryGuardsContract := safeUnary_float

private def unaryGuardsLaw : Prop := ∀ (base : Unary → JF → Jl JF) (op : Unary) (x : JF),
  (domain op x = false → ∀ alternate, safeUnary alternate true op x = .ok .nan) ∧
  (domain op x = true → ∀ reply, safeUnary base true op x = reply ↔ base op x = reply)

private theorem unaryGuardsLaw_holds : unaryGuardsLaw := by
  intro base op x
  constructor
  · intro h alternate
    simp [safeUnary_float, h]
  · intro h reply
    simp [safeUnary_float, h]

def unaryGuards : Prop := unaryGuardsContract ∧ unaryGuardsLaw

theorem unaryGuards_holds : unaryGuards := ⟨unaryGuardsContract_holds, unaryGuardsLaw_holds⟩

private def admitted {A B R : Type} (rt : UnaryRuntime A B R) (x : A) : Unary → Prop
  | .log | .log2 | .log10 => rt.greaterZero x = .ok true
  | .log1p => rt.greaterNegUnit x = .ok true
  | .asin | .acos | .atanh => rt.atLeastNegUnit x = .ok true ∧ rt.atMostUnit x = .ok true
  | .acosh => rt.atLeastUnit x = .ok true
  | .sqrt => rt.atLeastZero x = .ok true

private def rejected {A B R : Type} (rt : UnaryRuntime A B R) (x : A) : Unary → Prop
  | .log | .log2 | .log10 => rt.greaterZero x = .ok false
  | .log1p => rt.greaterNegUnit x = .ok false
  | .asin | .acos | .atanh => rt.atLeastNegUnit x = .ok false ∨
      (rt.atLeastNegUnit x = .ok true ∧ rt.atMostUnit x = .ok false)
  | .acosh => rt.atLeastUnit x = .ok false
  | .sqrt => rt.atLeastZero x = .ok false

def unaryNaNCharacterization : Prop := ∀ (A B : Type) (rt : UnaryRuntime A B A) (op : Unary)
    (x nan : A),
  hasUnaryGuard rt.kind = true →
  (safeUnaryTyped rt op x = .ok nan ↔
    (rejected rt x op ∧ rt.typedNaN () = .ok nan) ∨
    (admitted rt x op ∧ ∃ v, rt.checkedBase op x = .ok v ∧ rt.convert v = .ok nan))

theorem unaryNaNCharacterization_holds : unaryNaNCharacterization := by
  intro A B rt op x nan h
  cases op <;>
    simp only [safeUnaryTyped, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind,
      Except.bind, Pure.pure, Except.pure, rejected, admitted] <;>
    repeat' (split <;> simp_all)

private def standardFloatDomain : Unary → JF → Prop
  | .log, .fin q | .log2, .fin q | .log10, .fin q => 0 < q
  | .log, .posInf | .log2, .posInf | .log10, .posInf => True
  | .log1p, .fin q => -1 < q
  | .log1p, .posInf => True
  | .asin, .fin q | .acos, .fin q | .atanh, .fin q => -1 ≤ q ∧ q ≤ 1
  | .acosh, .fin q => 1 ≤ q
  | .acosh, .posInf => True
  | .sqrt, .fin q => 0 ≤ q
  | .sqrt, .posInf => True
  | _, _ => False

def unaryNaNExactlyOutside : Prop := ∀ (base : Unary → JF → Jl JF),
  (∀ op x, standardFloatDomain op x → ∃ value, value ≠ .nan ∧ base op x = .ok value) →
  ∀ op x, safeUnary base true op x = .ok .nan ↔ ¬ standardFloatDomain op x

private theorem domain_iff_standard (op : Unary) (x : JF) :
    domain op x = true ↔ standardFloatDomain op x := by
  cases op <;> cases x <;>
    simp [domain, standardFloatDomain, greater, greaterEqual] <;> grind

theorem unaryNaNExactlyOutside_holds : unaryNaNExactlyOutside := by
  intro base h op x
  rw [safeUnary_float]
  by_cases hd : domain op x = true
  · obtain ⟨v, hn, hv⟩ := h op x ((domain_iff_standard op x).mp hd)
    simp [hd, hn, hv, ← domain_iff_standard]
  · have he : domain op x = false := Bool.eq_false_iff.mpr hd
    simp [he, hd, ← domain_iff_standard]

/-- Generic methods do not perform the FloatOrDual guards. -/
def genericFallbacks : Prop :=
  (∀ (A B R : Type) (rt : UnaryRuntime A B R) (op : Unary) x,
    rt.kind = .other ∨ rt.kind = .quantity →
    safeUnaryTyped rt op x = rt.genericBase op x) ∧
  ∀ (A B P R : Type) (rt : PowerRuntime A B P R) (x : A) (y : B),
    (rt.baseKind = .other ∨ rt.exponentKind = .other) →
    safePowTyped rt x y = rt.base x y
theorem genericFallbacks_holds : genericFallbacks := by
  constructor
  · intro A B R rt op x h
    rcases h with h | h <;> simp [safeUnaryTyped, hasUnaryGuard, h, Bind.bind, Except.bind]
  · intro A B P R rt x y h
    rcases h with h | h <;> simp [safePowTyped, hasPowerGuard, h]

/-- Logarithms agree on rejection; inverse circular and hyperbolic functions
with the closed symmetric domain also agree on rejection. -/
private def domainConventionsContract : Prop := ∀ x : JF,
  domain .log x = greater x (.fin 0) ∧
  domain .log2 x = greater x (.fin 0) ∧
  domain .log10 x = greater x (.fin 0) ∧
  domain .log1p x = greater x (.fin (-1)) ∧
  domain .asin x = (greaterEqual x (.fin (-1)) && greaterEqual (.fin 1) x) ∧
  domain .acos x = (greaterEqual x (.fin (-1)) && greaterEqual (.fin 1) x) ∧
  domain .atanh x = (greaterEqual x (.fin (-1)) && greaterEqual (.fin 1) x) ∧
  domain .acosh x = greaterEqual x (.fin 1) ∧
  domain .sqrt x = greaterEqual x (.fin 0)

private theorem domainConventionsContract_holds : domainConventionsContract := by intro x; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private def domainConventionsLaw : Prop := ∀ x : JF,
  domain .log x = domain .log2 x ∧
  domain .log x = domain .log10 x ∧
  domain .asin x = domain .acos x ∧
  domain .asin x = domain .atanh x ∧
  (domain .log x = true → domain .sqrt x = true) ∧
  (domain .acosh x = true → domain .sqrt x = true)
private theorem domainConventionsLaw_holds : domainConventionsLaw := by
  intro x
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · cases x <;> simp [domain, greater, greaterEqual]
    intro h
    exact Or.inl h
  · cases x <;> simp [domain, greater, greaterEqual]
    intro h
    rcases h with h | rfl
    · exact Or.inl (Rat.not_le.mp fun h0 =>
        (Rat.not_le.mpr (by decide : (0 : Rat) < 1)) (Rat.le_trans (Rat.le_of_lt h) h0))
    · exact Or.inl (by decide)

def domainConventions : Prop := domainConventionsContract ∧ domainConventionsLaw

theorem domainConventions_holds : domainConventions := ⟨domainConventionsContract_holds, domainConventionsLaw_holds⟩

def nanInputRejected : Prop := ∀ (base : Unary → JF → Jl JF) (op : Unary),
  safeUnary base true op .nan = .ok .nan
theorem nanInputRejected_holds : nanInputRejected := by
  intro base op; cases op <;> rfl

/-- Base endpoint values in Julia 1.12. Away from the two
atanh poles, the external implementation stays arbitrary. -/
def poleRuntime (elsewhere : Unary → JF → Jl JF) (op : Unary) (x : JF) : Jl JF :=
  if op = .atanh ∧ x = .fin 1 then .ok .posInf
  else if op = .atanh ∧ x = .fin (-1) then .ok .negInf
  else elsewhere op x

/-- Ordinary float encodings use signed endpoint results and reject all log poles. -/
def poleConventions : Prop := ∀ (elsewhere : Unary → JF → Jl JF) (op : Unary),
  (op = .log ∨ op = .log2 ∨ op = .log10 →
    safeUnary (poleRuntime elsewhere) true op (.fin 0) = .ok .nan) ∧
  safeUnary (poleRuntime elsewhere) true .log1p (.fin (-1)) = .ok .nan ∧
  ∀ positive : Bool,
    safeUnary (poleRuntime elsewhere) true .atanh (.fin (if positive then 1 else -1)) =
      .ok (if positive then .posInf else .negInf)
theorem poleConventions_holds : poleConventions := by
  intro elsewhere op
  refine ⟨?_, rfl, ?_⟩
  · rintro (rfl | rfl | rfl) <;> rfl
  · intro positive; cases positive <;> rfl

private def powerRejection {A B P R : Type} (rt : PowerRuntime A B P R) (x : A) (y : B) : Prop :=
  (rt.isInteger y = .ok true ∧ rt.negativeExponent y = .ok true ∧ rt.zeroBase x = .ok true) ∨
  (rt.isInteger y = .ok false ∧
    ((rt.positiveExponent y = .ok true ∧ rt.negativeBase x = .ok true) ∨
      (rt.positiveExponent y = .ok false ∨
        rt.positiveExponent y = .ok true ∧ rt.negativeBase x = .ok false) ∧
        rt.negativeExponent y = .ok true ∧ rt.nonpositiveBase x = .ok true))

private def powerAdmission {A B P R : Type} (rt : PowerRuntime A B P R) (x : A) (y : B) : Prop :=
  (rt.isInteger y = .ok true ∧ (rt.negativeExponent y = .ok false ∨
    rt.negativeExponent y = .ok true ∧ rt.zeroBase x = .ok false)) ∨
  (rt.isInteger y = .ok false ∧ (rt.positiveExponent y = .ok false ∨
    rt.positiveExponent y = .ok true ∧ rt.negativeBase x = .ok false) ∧
    (rt.negativeExponent y = .ok false ∨
      rt.negativeExponent y = .ok true ∧ rt.nonpositiveBase x = .ok false))

def powerGuards : Prop := ∀ (A B P R : Type) (rt : PowerRuntime A B P R) (x : A) (y : B),
  hasPowerGuard rt.baseKind = true → hasPowerGuard rt.exponentKind = true →
  (∀ e, rt.promoteType () = .error e → safePowTyped rt x y = .error e) ∧
  (∀ promoted, rt.promoteType () = .ok promoted → powerRejection rt x y →
    safePowTyped rt x y = rt.typedNaN promoted) ∧
  (∀ promoted, rt.promoteType () = .ok promoted → powerAdmission rt x y →
    safePowTyped rt x y = rt.base x y)

def powerNaNCharacterization : Prop := ∀ (A B P R : Type) (rt : PowerRuntime A B P R)
    (x : A) (y : B) (nan : R),
  hasPowerGuard rt.baseKind = true → hasPowerGuard rt.exponentKind = true →
  (safePowTyped rt x y = .ok nan ↔
    (∃ promoted, rt.promoteType () = .ok promoted ∧ powerRejection rt x y ∧
      rt.typedNaN promoted = .ok nan) ∨
    (∃ promoted, rt.promoteType () = .ok promoted ∧ powerAdmission rt x y ∧
      rt.base x y = .ok nan))

theorem powerGuards_holds : powerGuards := by
  intro A B P R rt x y hx hy
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp [safePowTyped, hx, hy, he, Bind.bind, Except.bind]
  · intro t ht h
    rcases h with ⟨hi, hy, hz⟩ | ⟨hi, ⟨hy, hneg⟩ | ⟨hp, hn, hx⟩⟩
    · simp [safePowTyped, ‹hasPowerGuard rt.baseKind = true›,
        ‹hasPowerGuard rt.exponentKind = true›, ht, hi, hy, hz, Bind.bind, Except.bind]
    · simp [safePowTyped, hx, ‹hasPowerGuard rt.exponentKind = true›,
        ht, hi, hy, hneg, Bind.bind, Except.bind]
    · rcases hp with hp | ⟨hp, hnx⟩ <;>
        simp [safePowTyped, ‹hasPowerGuard rt.baseKind = true›,
          ‹hasPowerGuard rt.exponentKind = true›, ht, hi, hp, hn, hx, *, Bind.bind, Except.bind]
  · intro t ht h
    rcases h with ⟨hi, hn | ⟨hn, hz⟩⟩ | ⟨hi, hp, hn⟩
    · simp [safePowTyped, hx, hy, ht, hi, hn, Bind.bind, Except.bind]
    · simp [safePowTyped, hx, hy, ht, hi, hn, hz, Bind.bind, Except.bind]
    · rcases hp with hp | ⟨hp, hb⟩ <;> rcases hn with hn | ⟨hn, hn'⟩ <;>
        simp [safePowTyped, hx, hy, ht, hi, hp, hn, *, Bind.bind, Except.bind]

theorem powerNaNCharacterization_holds : powerNaNCharacterization := by
  intro A B P R rt x y nan hx hy
  have ⟨_, hr, ha⟩ := powerGuards_holds A B P R rt x y hx hy
  constructor
  · intro h
    cases ht : rt.promoteType () with
    | error e => simp [safePowTyped, hx, hy, ht, Bind.bind, Except.bind] at h
    | ok t =>
      simp only [safePowTyped, hx, hy, Bool.true_and, if_true, ht, Bind.bind, Except.bind] at h
      repeat' (split at h <;> try contradiction)
      all_goals simp_all [powerRejection, powerAdmission]
  · rintro (⟨t, ht, h, hn⟩ | ⟨t, ht, h, hn⟩)
    · exact (hr t ht h).trans hn
    · exact (ha t ht h).trans hn

/-- NaN exponent fails every order test, so power delegates. Infinite exponents
reject strictly negative bases but zero with +Inf is delegated. NaN^0 also delegates. -/
def powerSpecialValues : Prop := ∀ (base : JF → JF → Jl JF) (x : JF),
  safePow base (.ok .nan) true x .nan = base x .nan ∧
  ((x = .negInf ∨ ∃ q : Rat, q < 0 ∧ x = .fin q) →
    safePow base (.ok .nan) true x .posInf = .ok .nan ∧
    safePow base (.ok .nan) true x .negInf = .ok .nan) ∧
  safePow base (.ok .nan) true (.fin 0) .posInf = base (.fin 0) .posInf ∧
  safePow base (.ok .nan) true .nan (.fin 0) = base .nan (.fin 0)
theorem powerSpecialValues_holds : powerSpecialValues := by
  intro base x
  refine ⟨?_, ?_, rfl, rfl⟩
  · cases x <;> rfl
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact ⟨rfl,rfl⟩
    · simp [safePow_float, rejectsPower, isInteger, less, greater, greaterEqual, hq,
        Rat.le_of_lt hq]

/-- Every negative integer exponent with a zero base is rejected. A floating
signed zero has the same branch tests; JF intentionally merges its two signs. -/
def zeroNegativeInteger : Prop := ∀ (base : JF → JF → Jl JF) (y : JF),
  isInteger y = true → less y (.fin 0) = true →
  safePow base (.ok .nan) true (.fin 0) y = .ok .nan
theorem zeroNegativeInteger_holds : zeroNegativeInteger := by
  intro base y hi hn
  simp [safePow_float, rejectsPower, hi, hn, SymReg.MutateGen.isZero]
example : isInteger (.fin (-2)) = true ∧ less (.fin (-2)) (.fin 0) = true := by decide

private def strongZeroContract : Prop := ∀ (x : JF) (b : Bool),
  boolMul b x = if b then x else .fin 0

private theorem strongZeroContract_holds : strongZeroContract := by intro x b; rfl

private def strongZeroLaw : Prop := ∀ x : JF,
  cond (.fin 0) x = .fin 0 ∧ cond .nan x = .fin 0 ∧
  cond .posInf x = x ∧ relu (relu x) = relu x

private theorem strongZeroLaw_holds : strongZeroLaw := by
  intro x
  exact ⟨rfl, rfl, rfl, by cases h : greater x (.fin 0) <;> simp [relu, boolMul, h]⟩

def strongZero : Prop := strongZeroContract ∧ strongZeroLaw

theorem strongZero_holds : strongZero := ⟨strongZeroContract_holds, strongZeroLaw_holds⟩

private def algebraicWrappersContract : Prop := ∀ x y : JF,
  square x = x*x ∧ cube x = (x*x)*x ∧ plus x y = x+y ∧
  sub x y = x-y ∧ mult x y = x*y ∧ neg x = -x

private theorem algebraicWrappersContract_holds : algebraicWrappersContract := by intro x y; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private def algebraicWrappersLaw : Prop := ∀ x y : Rat,
  square (.fin x) = square (neg (.fin x)) ∧
  cube (.fin x) = neg (cube (neg (.fin x))) ∧
  plus (.fin x) (.fin y) = plus (.fin y) (.fin x) ∧
  sub (.fin x) (.fin x) = .fin 0 ∧
  mult (.fin x) (.fin y) = mult (.fin y) (.fin x)

private theorem algebraicWrappersLaw_holds : algebraicWrappersLaw := by
  intro x y
  have hs : (-x) * (-x) = x * x := by simp [Rat.neg_mul, Rat.mul_neg]
  have hc : -(((-x) * (-x)) * (-x)) = x * x * x := by rw [hs]; simp [Rat.mul_neg]
  have ha : x + -x = 0 := by grind
  exact ⟨congrArg JF.fin hs.symm, congrArg JF.fin hc.symm,
    congrArg JF.fin (Rat.add_comm _ _), congrArg JF.fin ha, congrArg JF.fin (Rat.mul_comm _ _)⟩

def algebraicWrappers : Prop := algebraicWrappersContract ∧ algebraicWrappersLaw

theorem algebraicWrappers_holds : algebraicWrappers := ⟨algebraicWrappersContract_holds, algebraicWrappersLaw_holds⟩

/-- Every comparison returns the numeric Boolean indicator, including unordered NaN. -/
def comparisons : Prop := ∀ x y : JF,
  greaterOp x y = (if greater x y then .fin 1 else .fin 0) ∧
  lessOp x y = (if less x y then .fin 1 else .fin 0) ∧
  greaterEqualOp x y = (if greaterEqual x y then .fin 1 else .fin 0) ∧
  lessEqualOp x y = (if greaterEqual y x then .fin 1 else .fin 0)
theorem comparisons_holds : comparisons := by intro x y; exact ⟨rfl,rfl,rfl,rfl⟩

def conditionalLogic : Prop :=
  (∀ x y : JF,
    cond x y = (if greater x (.fin 0) then y else .fin 0) ∧
    relu x = (if greater x (.fin 0) then x else .fin 0)) ∧
  ∀ (compare : Nat → Jl Bool) (conjunction : Bool) x y,
    (∀ e, compare x = .error e →
      logicalBinary compare (fun _ => .ok 1) (fun b n => .ok (if b then n else 0))
        conjunction x y = .error e) ∧
    (∀ a e, compare x = .ok a → compare y = .error e →
      logicalBinary compare (fun _ => .ok 1) (fun b n => .ok (if b then n else 0))
        conjunction x y = .error e) ∧
    (∀ a b, compare x = .ok a → compare y = .ok b →
      logicalBinary compare (fun _ => .ok 1) (fun b n => .ok (if b then n else 0))
        conjunction x y = .ok (if (if conjunction then a ∧ b else a ∨ b) then 1 else 0))
theorem conditionalLogic_holds : conditionalLogic := by
  refine ⟨fun _ _ => ⟨rfl,rfl⟩, ?_⟩
  intro compare conjunction x y
  refine ⟨?_, ?_, ?_⟩
  · intro e h; simp [logicalBinary, h, Bind.bind, Except.bind]
  · intro a e hx hy; simp [logicalBinary, hx, hy, Bind.bind, Except.bind]
  · intro a b hx hy
    cases conjunction <;> cases a <;> cases b <;>
      simp [logicalBinary, hx, hy, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Masking is actual Julia behavior: NaN is false as a condition and an inactive
branch masks NaN/Inf in its value. No NaN-propagation claim is imposed on cond. -/
def nonfiniteConditions : Prop := ∀ y : JF,
  cond .nan y = .fin 0 ∧ relu .nan = .fin 0 ∧
  greaterOp .nan y = .fin 0 ∧ greaterOp y .nan = .fin 0 ∧
  lessOp .nan y = .fin 0 ∧ lessOp y .nan = .fin 0 ∧
  greaterEqualOp .nan y = .fin 0 ∧ greaterEqualOp y .nan = .fin 0 ∧
  lessEqualOp .nan y = .fin 0 ∧ lessEqualOp y .nan = .fin 0
theorem nonfiniteConditions_holds : nonfiniteConditions := by
  intro y; cases y <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def gammaResults : Prop := ∀ (A B : Type) (base : A → Jl B) infinite nan convert x,
  (∀ e, base x = .error e → gamma base infinite nan convert x = .error e) ∧
  (∀ out e, base x = .ok out → infinite out = .error e →
    gamma base infinite nan convert x = .error e) ∧
  (∀ out, base x = .ok out → infinite out = .ok true →
    gamma base infinite nan convert x = nan ()) ∧
  (∀ out, base x = .ok out → infinite out = .ok false →
    gamma base infinite nan convert x = convert out)
theorem gammaResults_holds : gammaResults := by
  intro A B base infinite nan convert x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e h; simpa [gamma, h, Bind.bind, Except.bind]
  · intro out e h hi; simpa [gamma, h, hi, Bind.bind, Except.bind]
  · intro out h hi; simpa [gamma, h, hi, Bind.bind, Except.bind]
  · intro out h hi; simpa [gamma, h, hi, Bind.bind, Except.bind]

/-- In Julia 1.12 with SpecialFunctions, gamma(-1.0)
raises DomainError. All other inputs are left arbitrary, rather than approximated. -/
def gammaRuntime (elsewhere : JF → Jl JF) (x : JF) : Jl JF :=
  if x = .fin (-1) then .error (.domainError "NaN result for non-NaN input") else elsewhere x

/-- Safety expectation for the package gamma wrapper: a real scalar input
produces a value (NaN at a pole), without leaking a library DomainError. -/
def gammaTotal : Prop := ∀ (elsewhere : JF → Jl JF) (x : JF),
  ∃ value, gamma (gammaRuntime elsewhere)
    (fun v => .ok (v == .posInf || v == .negInf)) (fun _ => .ok .nan) Except.ok x = .ok value
theorem gammaTotal_refuted : ¬ gammaTotal := by
  intro h
  obtain ⟨value, hv⟩ := h (fun _ => .ok (.fin 1)) (.fin (-1))
  simp [gamma, gammaRuntime, Bind.bind, Except.bind] at hv

def clippingFormula : Prop := ∀ (modulo : JF → JF → Jl JF) (atanh : JF → Jl JF) (x : Rat),
  (∀ a r : Rat, 0 ≤ r → r < 2 → (∃ k : Int, a - r = 2 * (k : Rat)) →
    modulo (.fin a) (.fin 2) = .ok (.fin r)) →
  ∀ wrapped : Rat, -1 ≤ wrapped → wrapped < 1 →
    (∃ k : Int, x - wrapped = 2 * (k : Rat)) →
    atanhClip modulo atanh (.fin x) = atanh (.fin wrapped)

theorem clippingFormula_holds : clippingFormula := by
  intro modulo atanh x hm wrapped hlo hhi hmultiples
  have hlo' : 0 ≤ wrapped + 1 := by grind
  have hhi' : wrapped + 1 < 2 := by grind
  have hm' : ∃ k : Int, x + 1 - (wrapped + 1) = 2 * (k : Rat) := by
    obtain ⟨k, hk⟩ := hmultiples
    exact ⟨k, by grind⟩
  have h := hm (x + 1) (wrapped + 1) hlo' hhi' hm'
  have hw : JF.fin (wrapped + 1) - .fin 1 = .fin wrapped := by
    change JF.fin (wrapped + 1 + -(1 : Rat)) = .fin wrapped
    congr 1
    grind
  unfold atanhClip
  change (do
    let r ← modulo (.fin (x + 1)) (.fin 2)
    let v ← atanh (r - JF.fin 1)
    (pure (v * JF.fin 1) : Jl JF)) = _
  simp only [h, Bind.bind, Except.bind, hw]
  cases he : atanh (.fin wrapped) with
  | error e => rfl
  | ok v =>
    cases v with
    | fin q => change Except.ok (JF.fin (q * 1)) = (Except.ok (.fin q) : Jl JF); rw [Rat.mul_one]
    | nan | posInf | negInf => rfl

example : -1 ≤ (-1 : Rat) ∧ (-1 : Rat) < 1 ∧
    ∃ k : Int, (1 : Rat) - (-1) = 2 * (k : Rat) := by
  exact ⟨by decide +kernel, by decide +kernel, 1, by decide +kernel⟩

/-- In Julia 1.12, mod(-1,2)=1, rem(-1,2)=-1, atanh(0)=0,
and atanh(-2) throws DomainError. Other external inputs remain arbitrary. -/
def wrappingRuntime (remainder : Bool) (elsewhere : JF → JF → Jl JF) (x y : JF) : Jl JF :=
  if x = .fin (-1) ∧ y = .fin 2 then
    .ok (if remainder then .fin (-1) else .fin 1)
  else elsewhere x y

def clippingAtanhRuntime (elsewhere : JF → Jl JF) (x : JF) : Jl JF :=
  if x = .fin 0 then .ok (.fin 0)
  else if x = .fin (-2) then .error (.domainError "atanh outside [-1,1]")
  else elsewhere x

/-- The adjacent comment `src/Operators.jl:20` claims equality with the Julia
percent/rem expression for every input, including x below -1. -/
def clippingComment : Prop := ∀ (modulo remainder : JF → JF → Jl JF)
    (atanh : JF → Jl JF) (x : JF),
  atanhClip (wrappingRuntime false modulo) (clippingAtanhRuntime atanh) x =
    (do
      let m ← wrappingRuntime true remainder (x + .fin 1) (.fin 2)
      clippingAtanhRuntime atanh (m - .fin 1))
theorem clippingComment_refuted : ¬ clippingComment := by
  intro h
  have hc := h (fun _ _ => .ok (.fin 0)) (fun _ _ => .ok (.fin 0))
    (fun _ => .ok (.fin 0)) (.fin (-2))
  have hn : atanhClip (wrappingRuntime false (fun _ _ => .ok (.fin 0)))
      (clippingAtanhRuntime (fun _ => .ok (.fin 0))) (.fin (-2)) ≠
      (do
        let m ← wrappingRuntime true (fun _ _ => .ok (.fin 0))
          (JF.fin (-2) + .fin 1) (.fin 2)
        clippingAtanhRuntime (fun _ => .ok (.fin 0)) (m - .fin 1)) := by decide
  exact hn hc

def deprecatedForwarding : Prop := ∀ (A B P R : Type) (depwarn : String → Jl Unit)
    (rt : PowerRuntime A B P R) (x : A) (y : B),
  (depwarn "pow" = .ok () → pow depwarn rt x y = safePowTyped rt x y) ∧
  (depwarn "pow_abs" = .ok () → powAbs depwarn rt x y = safePowTyped rt x y) ∧
  (∀ e, depwarn "pow" = .error e → pow depwarn rt x y = .error e) ∧
  (∀ e, depwarn "pow_abs" = .error e → powAbs depwarn rt x y = .error e)
theorem deprecatedForwarding_holds : deprecatedForwarding := by
  intro A B P R depwarn rt x y
  exact ⟨fun h => by simp [pow, h, Bind.bind, Except.bind],
    fun h => by simp [powAbs, h, Bind.bind, Except.bind],
    fun e h => by simp [pow, h, Bind.bind, Except.bind],
    fun e h => by simp [powAbs, h, Bind.bind, Except.bind]⟩

/-- Every listed unary base maps to its safe implementation and printed name;
the arity-one alias returns that same base identity. -/
def unaryTables : Prop := ∀ op : Unary,
  getSafeOp (safeId op - 99) = safeId op ∧
  printedName (safeId op) = some (unaryName op) ∧
  operatorAlias (safeId op) 1 = some (safeId op - 99)
theorem unaryTables_holds : unaryTables := by intro op; cases op <;> decide

/-- All five binary mappings and aliases agree. Their display tables distinguish
saved power names from pretty-only comparison names. -/
def binaryTables : Prop := ∀ op : Nat, 5 ≤ op → op ≤ 9 →
  let base := if op = 5 then 5 else op + 1
  getSafeOp base = op + 100 ∧ operatorAlias (op + 100) 2 = some base ∧
  (if op = 5 then printedName (op + 100) = some "^" else
    printedName (op + 100) = none ∧
    prettyName (op + 100) =
      some (if op = 6 then ">" else if op = 7 then "<" else if op = 8 then ">=" else "<="))
theorem binaryTables_holds : binaryTables := by
  intro op h₁ h₂
  have : op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 ∨ op = 9 := by omega
  rcases this with h|h|h|h|h <;> subst op <;> decide
example : 5 ≤ (5 : Nat) ∧ (5 : Nat) ≤ 9 := by decide

/-- No unlisted user function identity is changed by get_safe_op. -/
def mappingFallback : Prop := ∀ op : Nat,
  ¬ (op = 5 ∨ (7 ≤ op ∧ op ≤ 19)) → getSafeOp op = op
theorem mappingFallback_holds : mappingFallback := by
  intro op h; simp [getSafeOp, h]
example : ¬ ((200 : Nat) = 5 ∨ (7 ≤ (200 : Nat) ∧ (200 : Nat) ≤ 19)) := by decide

/-- Arity is part of alias dispatch: unary safe functions have no binary override,
and binary safe functions have no unary override. -/
def aliasArity : Prop := ∀ (op : Unary),
  operatorAlias (safeId op) 2 = none ∧ operatorAlias 105 1 = none
theorem aliasArity_holds : aliasArity := by intro op; cases op <;> decide

end SymReg.Operators
