import DynExpr.Runtime.Value
import DynExpr.Runtime.Errors
import SymReg.Loss.Core

/-!
Model of `src/InverseFunctions.jl` (SymbolicRegression.jl `upstream/master`) and of the
safe operators of `src/Operators.jl` it inverts.

Scalars are DE's `JF`: exact rationals plus `NaN` and `±Inf`, without rounding, overflow or
signed zero. Base and SpecialFunctions functions (`sin`, `acosh`, `sqrt`, `exp`, `^`, `mod`,
...) are arbitrary functions of a `Lib`, returning `Jl` so that a throwing call (`tan(Inf)`
throws `DomainError`) is representable. Properties that need a fact about one of them state
it as a hypothesis. SR's own wrappers (`safe_*`, `square`, `cube`, `neg`, `relu`,
`atanh_clip`, `exp1m`) and Base's exact arithmetic (`+`, `-`, `*`, `/`, `\`, `inv`, `abs`,
`fma`) are mirrored. User operators carry their InverseFunctions.jl inverse as an optional
function; it is chosen by the type of the function (`NoInverse` is type-based), so whether it
exists never depends on the fixed argument values.
-/

namespace SymReg.Backsolve
open DynExpr

/-! ## Julia scalar primitives on `JF` -/

/-- Float64 `<` (IEEE: every comparison with NaN is false). -/
def jlt : JF → JF → Bool
  | .fin a, .fin b => decide (a < b)
  | .nan, _ | _, .nan => false
  | .negInf, .negInf => false
  | .negInf, _ => true
  | .fin _, .posInf => true
  | _, _ => false

/-- Float64 `<=`. -/
def jle : JF → JF → Bool
  | .fin a, .fin b => decide (a ≤ b)
  | .nan, _ | _, .nan => false
  | .negInf, _ => true
  | _, .posInf => true
  | _, _ => false

/-- `isinteger(x)` for Float64: finite with an integral value. -/
def isInteger : JF → Bool
  | .fin q => q.den == 1
  | _ => false

/-- `iszero(x)`. -/
def isZero : JF → Bool
  | .fin q => q == 0
  | _ => false

/-- Exact `q^n` for a natural exponent. -/
def ratPowNat (q : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPowNat q n * q

/-- Base and SpecialFunctions scalar functions used by SR's operators and their inverses. -/
inductive BaseFn where
  | sin | cos | tan | asin | acos | atan | cosh | acosh | tanh | atanh
  | sqrt | cbrt | exp | log | log2 | exp2 | log10 | exp10 | log1p
  deriving DecidableEq, Repr

/-- The library functions: arbitrary, possibly throwing. `pow` is Base `x^y` outside the exact
integral-exponent case of `powJ`; `mod` is Base `mod` on Float64. -/
structure Lib where
  base : BaseFn → JF → Jl JF
  pow : JF → JF → Jl JF
  mod : JF → JF → Jl JF
  precision : Option SymReg.Loss.LossPrecision := none

def Lib.round (L : Lib) (v : JF) : JF :=
  match L.precision with
  | none => v
  | some p => p.round v

/-- Base `x^y` on Float64: a finite base with a finite integral exponent is the exact power
(`0^n` with `n < 0` is `Inf`); every other case is the library's `pow`. -/
def powJ (L : Lib) (x y : JF) : Jl JF :=
  match x, y with
  | .fin q, .fin e =>
    if e.den = 1 then
      if 0 ≤ e.num then pure (.fin (ratPowNat q e.num.toNat))
      else if q = 0 then pure .posInf
      else pure (.fin (1 / ratPowNat q e.num.natAbs))
    else L.pow x y
  | _, _ => L.pow x y

/-- `safe_pow(x, y)` for Float64 (`src/Operators.jl:35-48`). -/
def safePowF (L : Lib) (x y : JF) : Jl JF :=
  if isInteger y then
    if jlt y (.fin 0) && isZero x then pure .nan else powJ L x y
  else if jlt (.fin 0) y && jlt x (.fin 0) then pure .nan
  else if jlt y (.fin 0) && jle x (.fin 0) then pure .nan
  else powJ L x y

/-- `abs(x)`. -/
def jabs : JF → JF
  | .fin q => .fin (if q < 0 then -q else q)
  | .nan => .nan
  | _ => .posInf

/-! ## Operators -/

/-- Unary operators of SR's operator enum. `user f inv` is any other function, with its
InverseFunctions.jl inverse (`none` for `NoInverse`). -/
inductive UOp where
  | sin | safeAsin | cos | safeAcos | tan | atan | cosh | safeAcosh | tanh | atanhClip
  | square | safeSqrt | cube | cbrt | exp | safeLog | safeLog2 | exp2 | safeLog10 | exp10
  | safeLog1p | exp1m | neg | relu | abs | inv
  | user (f : JF → Jl JF) (ifInv : Option (JF → Jl JF))

/-- Binary operators. `user f inv1 inv2`: InverseFunctions.jl inverses of `Fix1(f, a)` and
`Fix2(f, a)`, as functions of `a`. -/
inductive BOp where
  | plus | sub | mult | div | safePow | mod
  | user (f : JF → JF → Jl JF) (ifInv1 ifInv2 : Option (JF → JF → Jl JF))

/-- Operators of degree three or above, including the dedicated `fma` overload. -/
inductive TOp where
  | fma
  | user (extraArity : Nat) (f : List JF → Jl JF)
      (ifInv : Nat → Option (List JF → JF → Jl JF))

/-- A unary operator applied to one value. Wrappers mirror `src/Operators.jl:19,50-82,95-130`
and `src/InverseFunctions.jl:107`. -/
def UOp.eval (L : Lib) : UOp → JF → Jl JF
  | .sin, x => L.base .sin x
  | .safeAsin, x =>
    if jle (.fin (-1)) x && jle x (.fin 1) then L.base .asin x else pure .nan
  | .cos, x => L.base .cos x
  | .safeAcos, x =>
    if jle (.fin (-1)) x && jle x (.fin 1) then L.base .acos x else pure .nan
  | .tan, x => L.base .tan x
  | .atan, x => L.base .atan x
  | .cosh, x => L.base .cosh x
  | .safeAcosh, x => if jle (.fin 1) x then L.base .acosh x else pure .nan
  | .tanh, x => L.base .tanh x
  | .atanhClip, x => do
    let m ← L.mod (JF.add x (.fin 1)) (JF.add (.fin 1) (.fin 1))
    let a ← L.base .atanh (JF.sub m (.fin 1))
    pure (JF.mul a (.fin 1))
  | .square, x => pure (JF.mul x x)
  | .safeSqrt, x => if jle (.fin 0) x then L.base .sqrt x else pure .nan
  | .cube, x => pure (JF.mul (JF.mul x x) x)
  | .cbrt, x => L.base .cbrt x
  | .exp, x => L.base .exp x
  | .safeLog, x => if jlt (.fin 0) x then L.base .log x else pure .nan
  | .safeLog2, x => if jlt (.fin 0) x then L.base .log2 x else pure .nan
  | .exp2, x => L.base .exp2 x
  | .safeLog10, x => if jlt (.fin 0) x then L.base .log10 x else pure .nan
  | .exp10, x => L.base .exp10 x
  | .safeLog1p, x => if jlt (.fin (-1)) x then L.base .log1p x else pure .nan
  -- Source: src/InverseFunctions.jl:107
  -- exp1m(x) = exp(x) - one(x)
  | .exp1m, x => do
    let e ← L.base .exp x
    pure (L.round (JF.sub e (.fin 1)))
  | .neg, x => pure (JF.neg x)
  | .relu, x => pure (if jlt (.fin 0) x then x else .fin 0)
  | .abs, x => pure (jabs x)
  | .inv, x => pure (JF.div (.fin 1) x)
  | .user f _, x => f x

/-- A binary operator applied to two values. -/
def BOp.eval (L : Lib) : BOp → JF → JF → Jl JF
  | .plus, x, y => pure (JF.add x y)
  | .sub, x, y => pure (JF.sub x y)
  | .mult, x, y => pure (JF.mul x y)
  | .div, x, y => pure (JF.div x y)
  | .safePow, x, y => safePowF L x y
  | .mod, x, y => L.mod x y
  | .user f _ _, x, y => f x y

/-- A ternary operator applied to its arguments. `fma(a, b, c) = a*b + c`, exact. -/
def TOp.eval : TOp → List JF → Jl JF
  | .fma, [a, b, c] => pure (JF.add (JF.mul a b) c)
  | .fma, _ => throw (.methodError "fma arity")
  | .user _ f _, args => f args

/-- An operator of the enum with its arity. -/
inductive Op where
  | u (o : UOp)
  | b (o : BOp)
  | t (o : TOp)

/-- Arity of an operator. -/
def Op.arity : Op → Nat
  | .u _ => 1
  | .b _ => 2
  | .t .fma => 3
  | .t (.user k _ _) => k + 3

/-- Apply an operator to its argument list. -/
def Op.eval (L : Lib) : Op → List JF → Jl JF
  | .u o, [x] => o.eval L x
  | .b o, [x, y] => o.eval L x y
  | .t o, args => o.eval args
  | _, _ => throw (.methodError "operator arity")

/-! ## Function values passed to `approx_inverse` -/

/-- The function values `approx_inverse` is called on: a unary operator, `Base.Fix1`,
`Base.Fix2`, or `FitExcept{I}(f, args)` (`src/InverseFunctions.jl:45-48`). -/
inductive Fn where
  | u (o : UOp)
  | fix1 (o : BOp) (a : JF)
  | fix2 (o : BOp) (a : JF)
  | fitExcept (i : Nat) (o : TOp) (args : List JF)

/-- Argument tuple of `FitExcept{I}(f, args)(x)`: `ntuple(i -> i == I ? x : f.args[i],
Val(length(f.args)))` (`src/InverseFunctions.jl:50-53`). -/
def fitExceptArgs (i : Nat) (args : List JF) (x : JF) : List JF :=
  (List.range args.length).map (fun k => if k + 1 == i then x else args.getD k .nan)

/-- Calling a function value. -/
def Fn.apply (L : Lib) : Fn → JF → Jl JF
  | .u o, x => o.eval L x
  | .fix1 o a, x => o.eval L a x
  | .fix2 o a, x => o.eval L x a
  | .fitExcept i o args, x => o.eval (fitExceptArgs i args x)

/-- `approx_inverse(f, ::Val{I}, args)` (`src/InverseFunctions.jl:62-67`): unary operators use
`approx_inverse(f)`, binary ones `Fix2(f, args[2])` for `I = 1` and `Fix1(f, args[1])` for
`I = 2`, higher arities `FitExcept{I}(f, args)`. -/
def route : Op → Nat → List JF → Fn
  | .u o, _, _ => .u o
  | .b o, i, args => if i = 1 then .fix2 o (args.getD 1 .nan) else .fix1 o (args.getD 0 .nan)
  | .t o, i, args => .fitExcept i o args

/-- `approx_inverse(f)` (`src/InverseFunctions.jl:30-34,72-150`); `none` is `nothing`. -/
def approxInv (L : Lib) : Fn → Option (JF → Jl JF)
  | .u .sin => some (UOp.safeAsin.eval L)
  | .u .safeAsin => some (UOp.sin.eval L)
  | .u .cos => some (UOp.safeAcos.eval L)
  | .u .safeAcos => some (UOp.cos.eval L)
  | .u .tan => some (UOp.atan.eval L)
  | .u .atan => some (UOp.tan.eval L)
  | .u .cosh => some (UOp.safeAcosh.eval L)
  | .u .safeAcosh => some (UOp.cosh.eval L)
  | .u .tanh => some (UOp.atanhClip.eval L)
  | .u .atanhClip => some (UOp.tanh.eval L)
  | .u .square => some (UOp.safeSqrt.eval L)
  | .u .safeSqrt => some (UOp.square.eval L)
  | .u .cube => some (UOp.cbrt.eval L)
  | .u .cbrt => some (UOp.cube.eval L)
  | .u .exp => some (UOp.safeLog.eval L)
  | .u .safeLog => some (UOp.exp.eval L)
  | .u .safeLog2 => some (UOp.exp2.eval L)
  | .u .exp2 => some (UOp.safeLog2.eval L)
  | .u .safeLog10 => some (UOp.exp10.eval L)
  | .u .exp10 => some (UOp.safeLog10.eval L)
  | .u .safeLog1p => some (UOp.exp1m.eval L)
  | .u .exp1m => some (UOp.safeLog1p.eval L)
  | .u .neg => some (UOp.neg.eval L)
  | .u .relu => none
  | .u .abs => none
  | .u .inv => some (UOp.inv.eval L)
  | .u (.user _ g) => g
  -- `Fix{N,+,-,*,/}` spelled out at `src/InverseFunctions.jl:124-131`.
  | .fix1 .plus a => some (fun x => pure (JF.sub x a))
  | .fix2 .plus a => some (fun x => pure (JF.sub x a))
  | .fix1 .sub a => some (fun x => pure (JF.sub a x))
  | .fix2 .sub a => some (fun x => pure (JF.add x a))
  | .fix1 .mult a => some (fun x => pure (JF.div x a))
  | .fix2 .mult a => some (fun x => pure (JF.div x a))
  | .fix1 .div a => some (fun x => pure (JF.div a x))
  | .fix2 .div a => some (fun x => pure (JF.mul x a))
  | .fix1 .safePow a => some (fun x => do
      let n ← UOp.safeLog.eval L x
      let d ← UOp.safeLog.eval L a
      pure (JF.div n d))
  | .fix2 .safePow a => some (fun x => safePowF L x (JF.div (.fin 1) a))
  | .fix1 .mod _ => none
  | .fix2 .mod _ => none
  | .fix1 (.user _ g _) a => g.map (fun h => h a)
  | .fix2 (.user _ _ g) a => g.map (fun h => h a)
  | .fitExcept i .fma args =>
    if i = 1 then some (fun y => pure (JF.div (JF.sub y (args.getD 2 .nan)) (args.getD 1 .nan)))
    else if i = 2 then some (fun y => pure (JF.div (JF.sub y (args.getD 2 .nan)) (args.getD 0 .nan)))
    else if i = 3 then some (fun y => pure (JF.sub y (JF.mul (args.getD 0 .nan) (args.getD 1 .nan))))
    else none
  | .fitExcept i (.user _ _ g) args => (g i).map (fun h => h args)

/-! ## Routing -/

/-- `FitExcept`'s argument tuple is `args` with slot `i` replaced. -/
theorem fitExceptArgs_eq (i : Nat) (args : List JF) (x : JF) (hi : 1 ≤ i) :
    fitExceptArgs i args x = args.set (i - 1) x := by
  apply List.ext_getElem
  · simp [fitExceptArgs]
  · intro k h1 h2
    simp only [fitExceptArgs, List.getElem_map, List.getElem_range, List.getElem_set]
    have hk : k < args.length := by simpa [fitExceptArgs] using h1
    by_cases hki : k + 1 = i
    · have : i - 1 = k := by omega
      simp [hki, this]
    · have : i - 1 ≠ k := by omega
      simp [hki, this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- `approx_inverse(f, Val(I), args)` inverts the right function: the function value it is
taken of, called on `x`, is the operator applied to `args` with slot `I` replaced by `x`.
Binary operators use `Fix2(f, args[2])` for `I = 1` and `Fix1(f, args[1])` for `I = 2`;
all operators of arity three and above use `FitExcept{I}` (`src/InverseFunctions.jl:47-69`). -/
def routing : Prop :=
  ∀ (L : Lib) (o : Op) (i : Nat) (args : List JF) (x : JF),
    args.length = o.arity → 1 ≤ i → i ≤ o.arity →
    (route o i args).apply L x = o.eval L (args.set (i - 1) x)

theorem routing_holds : routing := by
  intro L o i args x hlen hi1 hi2
  cases o with
  | u o =>
    simp only [Op.arity] at hlen hi2
    have : i = 1 := by omega
    subst this
    match args, hlen with
    | [a], _ => simp [route, Fn.apply, Op.eval]
  | b o =>
    simp only [Op.arity] at hlen hi2
    match args, hlen with
    | [a1, a2], _ =>
      by_cases h : i = 1
      · subst h; simp [route, Fn.apply, Op.eval]
      · have : i = 2 := by omega
        subst this; simp [route, Fn.apply, Op.eval]
  | t o =>
    simp only [route, Fn.apply, Op.eval]
    rw [fitExceptArgs_eq i args x hi1]

example : ([JF.fin 1] : List JF).length = (Op.u .neg).arity ∧ 1 ≤ 1 ∧ 1 ≤ (Op.u .neg).arity :=
  ⟨rfl, by decide, by decide⟩

/-- Whether an inverse exists depends only on the operator and position, never on the fixed
argument values (Julia dispatch is on the type of `Fix1`/`Fix2`/`FitExcept`). -/
theorem approxInv_route_isSome (L : Lib) (o : Op) (i : Nat) (a b : List JF) :
    (approxInv L (route o i a)).isSome = (approxInv L (route o i b)).isSome := by
  cases o with
  | u o => rfl
  | b o =>
    by_cases h : i = 1
    · cases o <;> simp [route, h, approxInv]
    · cases o <;> simp [route, h, approxInv]
  | t o =>
    cases o with
    | fma =>
      simp only [route, approxInv]
      by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> simp [h1, h2, h3]
    | user _ f g => simp [route, approxInv]

/-! ## Right inverses wherever finite -/

/-- Function values whose inverse is exact arithmetic: `neg`, `inv`, `Fix1`/`Fix2` of `+`,
`-`, `*` with a finite fixed argument, and `FitExcept` of `fma` with finite arguments. -/
def ExactArith : Fn → Prop
  | .u .neg | .u .inv => True
  | .fix1 .plus a | .fix2 .plus a | .fix1 .sub a | .fix2 .sub a
  | .fix1 .mult a | .fix2 .mult a => a.valid = true
  | .fitExcept i .fma args => args.length = 3 ∧ (∀ a ∈ args, a.valid = true) ∧ 1 ≤ i ∧ i ≤ 3
  | _ => False

/-- For the exactly invertible arithmetic function values, `approx_inverse` exists and is a
right inverse wherever it returns a finite value: for every finite target `y` with `g(y)`
finite, `f(g(y)) = y` (`src/InverseFunctions.jl:113,124-129,147-149` and the InverseFunctions.jl
inverse of `inv`). -/
def exactRightInverse : Prop :=
  ∀ (L : Lib) (f : Fn) (y v : JF), ExactArith f → y.valid = true →
    ∃ g, approxInv L f = some g ∧ (g y = .ok v → v.valid = true → f.apply L v = .ok y)

private theorem fin_of_valid {x : JF} (h : x.valid = true) : ∃ q, x = .fin q := by
  cases x <;> simp_all [JF.valid]

/-- Division by the finite zero never returns a finite value. -/
theorem div_zero_invalid (x : JF) : (JF.div x (.fin 0)).valid = false := by
  have key : ∀ b : Bool, (if b then JF.negInf else JF.posInf).valid = false := by decide
  cases x with
  | fin p =>
    by_cases hp : p = 0
    · subst hp; rfl
    · simp only [JF.div, ↓reduceIte, hp]
      exact key _
  | nan => rfl
  | posInf => decide
  | negInf => decide

theorem exactRightInverse_holds : exactRightInverse := by
  intro L f y v hf hy
  obtain ⟨p, rfl⟩ := fin_of_valid hy
  match f, hf with
  | .u .neg, _ =>
    refine ⟨_, rfl, fun hg _ => ?_⟩
    simp only [UOp.eval, pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    simp [Fn.apply, UOp.eval, JF.neg, pure, Except.pure]
  | .u .inv, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    by_cases hp : p = 0
    · subst hp; rw [div_zero_invalid] at hv; cases hv
    · have h1 : (1 : Rat) / p ≠ 0 := by grind
      have h2 : (1 : Rat) / (1 / p) = p := by grind
      simp [Fn.apply, UOp.eval, JF.div, hp, h1, h2, pure, Except.pure]
  | .fix1 .plus a, ha =>
    obtain ⟨q, rfl⟩ := fin_of_valid ha
    refine ⟨_, rfl, fun hg _ => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    have : q + (p + -q) = p := by grind
    simp [Fn.apply, BOp.eval, JF.sub, JF.add, JF.neg, pure, Except.pure, this]
  | .fix2 .plus a, ha =>
    obtain ⟨q, rfl⟩ := fin_of_valid ha
    refine ⟨_, rfl, fun hg _ => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    have : p + -q + q = p := by grind
    simp [Fn.apply, BOp.eval, JF.sub, JF.add, JF.neg, pure, Except.pure, this]
  | .fix1 .sub a, ha =>
    obtain ⟨q, rfl⟩ := fin_of_valid ha
    refine ⟨_, rfl, fun hg _ => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    have : q + -(q + -p) = p := by grind
    simp [Fn.apply, BOp.eval, JF.sub, JF.add, JF.neg, pure, Except.pure, this]
  | .fix2 .sub a, ha =>
    obtain ⟨q, rfl⟩ := fin_of_valid ha
    refine ⟨_, rfl, fun hg _ => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    have : p + q + -q = p := by grind
    simp [Fn.apply, BOp.eval, JF.sub, JF.add, JF.neg, pure, Except.pure, this]
  | .fix1 .mult a, ha =>
    obtain ⟨q, rfl⟩ := fin_of_valid ha
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    by_cases hq : q = 0
    · subst hq; rw [div_zero_invalid] at hv; cases hv
    · have : q * (p / q) = p := by grind
      simp [Fn.apply, BOp.eval, JF.div, JF.mul, hq, pure, Except.pure, this]
  | .fix2 .mult a, ha =>
    obtain ⟨q, rfl⟩ := fin_of_valid ha
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    by_cases hq : q = 0
    · subst hq; rw [div_zero_invalid] at hv; cases hv
    · have : p / q * q = p := by grind
      simp [Fn.apply, BOp.eval, JF.div, JF.mul, hq, pure, Except.pure, this]
  | .fitExcept i .fma args, ⟨hl, hargs, hi1, hi3⟩ =>
    match args, hl with
    | [a, b, c], _ =>
      obtain ⟨qa, rfl⟩ := fin_of_valid (hargs a (by simp))
      obtain ⟨qb, rfl⟩ := fin_of_valid (hargs b (by simp))
      obtain ⟨qc, rfl⟩ := fin_of_valid (hargs c (by simp))
      by_cases h1 : i = 1
      · subst h1
        refine ⟨_, rfl, fun hg hv => ?_⟩
        simp [pure, Except.pure] at hg
        subst hg
        by_cases hb : qb = 0
        · subst hb; rw [div_zero_invalid] at hv; cases hv
        · have : (p + -qc) / qb * qb + qc = p := by grind
          simp only [Fn.apply]
          rw [fitExceptArgs_eq _ _ _ (by decide)]
          simp [TOp.eval, JF.div, JF.sub, JF.add, JF.neg, JF.mul, hb, pure, Except.pure, this]
      by_cases h2 : i = 2
      · subst h2
        refine ⟨_, rfl, fun hg hv => ?_⟩
        simp [pure, Except.pure] at hg
        subst hg
        by_cases ha : qa = 0
        · subst ha; rw [div_zero_invalid] at hv; cases hv
        · have : qa * ((p + -qc) / qa) + qc = p := by grind
          simp only [Fn.apply]
          rw [fitExceptArgs_eq _ _ _ (by decide)]
          simp [TOp.eval, JF.div, JF.sub, JF.add, JF.neg, JF.mul, ha, pure, Except.pure, this]
      have h3 : i = 3 := by omega
      subst h3
      refine ⟨_, rfl, fun hg _ => ?_⟩
      simp [pure, Except.pure] at hg
      subst hg
      have : qa * qb + (p + -(qa * qb)) = p := by grind
      simp only [Fn.apply]
      rw [fitExceptArgs_eq _ _ _ (by decide)]
      simp [TOp.eval, JF.sub, JF.add, JF.neg, JF.mul, pure, Except.pure, this]

example : ExactArith (.u .neg) ∧ (JF.fin 1).valid = true := ⟨trivial, rfl⟩

/-- Library facts needed by the guarded pairs: every inverse function, where it returns a
finite value on its documented domain, is undone by the forward function (`sin(asin(q)) = q`
on `[-1, 1]`, `cosh(acosh(q)) = q` for `q >= 1`, `sqrt(q)^2 = q` for `q >= 0`,
`exp(log(q)) = q` for `q > 0`, `log(exp(q)) = q` with `exp(q) > 0`, ...). In exact arithmetic
these are the real-number identities restricted to the finite values the library returns. -/
structure LibInverseFacts (L : Lib) : Prop where
  asin : ∀ q v, -1 ≤ q → q ≤ 1 → L.base .asin (.fin q) = .ok v → v.valid = true →
    L.base .sin v = .ok (.fin q)
  acos : ∀ q v, -1 ≤ q → q ≤ 1 → L.base .acos (.fin q) = .ok v → v.valid = true →
    L.base .cos v = .ok (.fin q)
  atan : ∀ q v, L.base .atan (.fin q) = .ok v → v.valid = true → L.base .tan v = .ok (.fin q)
  acosh : ∀ q v, 1 ≤ q → L.base .acosh (.fin q) = .ok v → v.valid = true →
    L.base .cosh v = .ok (.fin q)
  sqrt : ∀ q v, 0 ≤ q → L.base .sqrt (.fin q) = .ok v → v.valid = true →
    JF.mul v v = .fin q
  cbrt : ∀ q v, L.base .cbrt (.fin q) = .ok v → v.valid = true → JF.mul (JF.mul v v) v = .fin q
  log : ∀ q v, 0 < q → L.base .log (.fin q) = .ok v → v.valid = true →
    L.base .exp v = .ok (.fin q)
  exp : ∀ q v, L.base .exp (.fin q) = .ok v → v.valid = true →
    jlt (.fin 0) v = true ∧ L.base .log v = .ok (.fin q)
  log2 : ∀ q v, 0 < q → L.base .log2 (.fin q) = .ok v → v.valid = true →
    L.base .exp2 v = .ok (.fin q)
  exp2 : ∀ q v, L.base .exp2 (.fin q) = .ok v → v.valid = true →
    jlt (.fin 0) v = true ∧ L.base .log2 v = .ok (.fin q)
  log10 : ∀ q v, 0 < q → L.base .log10 (.fin q) = .ok v → v.valid = true →
    L.base .exp10 v = .ok (.fin q)
  exp10 : ∀ q v, L.base .exp10 (.fin q) = .ok v → v.valid = true →
    jlt (.fin 0) v = true ∧ L.base .log10 v = .ok (.fin q)
  log1p : ∀ q v, -1 < q → L.base .log1p (.fin q) = .ok v → v.valid = true →
    L.base .exp v = .ok (.fin (q + 1))
  expm1 : ∀ q w, L.base .exp (.fin q) = .ok w → (JF.sub w (.fin 1)).valid = true →
    jlt (.fin (-1)) (JF.sub w (.fin 1)) = true ∧ L.base .log1p (JF.sub w (.fin 1)) = .ok (.fin q)

/-- Unary operators whose `approx_inverse` carries a domain guard matching the forward
function's range. -/
def GuardedPair : UOp → Prop
  | .sin | .cos | .tan | .cosh | .square | .cube | .exp | .safeLog | .safeLog2 | .exp2
  | .safeLog10 | .exp10 | .safeLog1p | .exp1m => True
  | _ => False

/-- For these unary operators, `approx_inverse` is a right inverse wherever it returns a finite
value: the safe wrapper's guard (`src/Operators.jl:50-76`) keeps the target inside the forward
function's range (`src/InverseFunctions.jl:72-110`). -/
def guardedRightInverse : Prop :=
  ∀ (L : Lib) (f : UOp) (y v : JF), L.precision = none → LibInverseFacts L →
    GuardedPair f → y.valid = true →
    ∃ g, approxInv L (.u f) = some g ∧ (g y = .ok v → v.valid = true → f.eval L v = .ok y)

private theorem jle_fin {a b : Rat} : jle (.fin a) (.fin b) = decide (a ≤ b) := rfl
private theorem jlt_fin {a b : Rat} : jlt (.fin a) (.fin b) = decide (a < b) := rfl

theorem guardedRightInverse_holds : guardedRightInverse := by
  intro L f y v hp hL hf hy
  obtain ⟨p, rfl⟩ := fin_of_valid hy
  have hnan : ¬ (JF.nan).valid = true := by simp [JF.valid]
  match f, hf with
  | .sin, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jle_fin] at hg
    by_cases hd : (-1 ≤ p ∧ p ≤ 1)
    · simp [hd.1, hd.2] at hg
      exact hL.asin p v hd.1 hd.2 hg hv
    · have : ¬ ((decide (-1 ≤ p) && decide (p ≤ 1)) = true) := by simpa using hd
      simp only [this, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .cos, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jle_fin] at hg
    by_cases hd : (-1 ≤ p ∧ p ≤ 1)
    · simp [hd.1, hd.2] at hg
      exact hL.acos p v hd.1 hd.2 hg hv
    · have : ¬ ((decide (-1 ≤ p) && decide (p ≤ 1)) = true) := by simpa using hd
      simp only [this, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .tan, _ => exact ⟨_, rfl, fun hg hv => hL.atan p v hg hv⟩
  | .cosh, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jle_fin] at hg
    by_cases hd : 1 ≤ p
    · simp [hd] at hg
      exact hL.acosh p v hd hg hv
    · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .square, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jle_fin] at hg
    by_cases hd : 0 ≤ p
    · simp [hd] at hg
      simp [UOp.eval, hL.sqrt p v hd hg hv, pure, Except.pure]
    · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .cube, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval] at hg
    simp [UOp.eval, hL.cbrt p v hg hv, pure, Except.pure]
  | .exp, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jlt_fin] at hg
    by_cases hd : 0 < p
    · simp [hd] at hg
      exact hL.log p v hd hg hv
    · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .safeLog, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval] at hg
    obtain ⟨hpos, hlog⟩ := hL.exp p v hg hv
    simp [UOp.eval, hpos, hlog]
  | .safeLog2, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval] at hg
    obtain ⟨hpos, hlog⟩ := hL.exp2 p v hg hv
    simp [UOp.eval, hpos, hlog]
  | .exp2, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jlt_fin] at hg
    by_cases hd : 0 < p
    · simp [hd] at hg
      exact hL.log2 p v hd hg hv
    · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .safeLog10, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval] at hg
    obtain ⟨hpos, hlog⟩ := hL.exp10 p v hg hv
    simp [UOp.eval, hpos, hlog]
  | .exp10, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jlt_fin] at hg
    by_cases hd : 0 < p
    · simp [hd] at hg
      exact hL.log10 p v hd hg hv
    · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan
  | .safeLog1p, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval] at hg
    simp only [Lib.round, hp] at hg
    cases he : L.base .exp (.fin p) with
    | error e => simp [he, bind, Except.bind] at hg
    | ok w =>
      simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      obtain ⟨hgt, hlog⟩ := hL.expm1 p w he hv
      simp [UOp.eval, hgt, hlog]
  | .exp1m, _ =>
    refine ⟨_, rfl, fun hg hv => ?_⟩
    simp only [UOp.eval, jlt_fin] at hg
    by_cases hd : -1 < p
    · simp [hd] at hg
      have he := hL.log1p p v hd hg hv
      have hq : p + 1 + -1 = p := by grind
      simp [UOp.eval, Lib.round, hp, he, bind, Except.bind, pure, Except.pure, JF.sub, JF.add, JF.neg, hq]
    · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at hg
      subst hg; exact absurd hv hnan

/-- A library that returns `NaN` for every call satisfies the inverse facts vacuously. -/
def nanLib : Lib := ⟨fun _ _ => .ok .nan, fun _ _ => .ok .nan, fun _ _ => .ok .nan, none⟩

theorem nanLib_facts : LibInverseFacts nanLib := by
  constructor <;> intros <;> simp only [nanLib, Except.ok.injEq] at * <;> subst_vars <;>
    simp_all [JF.valid, JF.sub, JF.add, JF.neg]

example : LibInverseFacts nanLib ∧ GuardedPair .sin ∧ (JF.fin 0).valid = true :=
  ⟨nanLib_facts, trivial, rfl⟩

def guardedFloatBoundary : Prop :=
  ∀ (L : Lib) (p : SymReg.Loss.LossPrecision) (y e : JF), L.precision = some p →
    (L.base .exp y = .ok e → p.round (JF.sub e (.fin 1)) = .fin (-1) →
      (approxInv L (.u .safeLog1p)).map (fun inv => inv y) = some (.ok (.fin (-1))) ∧
      UOp.safeLog1p.eval L (.fin (-1)) = .ok .nan) ∧
    ((L.base .exp y = .ok (.fin 0) →
        (approxInv L (.u .safeLog)).map (fun inv => inv y) = some (.ok (.fin 0))) ∧
      (L.base .exp2 y = .ok (.fin 0) →
        (approxInv L (.u .safeLog2)).map (fun inv => inv y) = some (.ok (.fin 0))) ∧
      (L.base .exp10 y = .ok (.fin 0) →
        (approxInv L (.u .safeLog10)).map (fun inv => inv y) = some (.ok (.fin 0))) ∧
      UOp.safeLog.eval L (.fin 0) = .ok .nan ∧
      UOp.safeLog2.eval L (.fin 0) = .ok .nan ∧
      UOp.safeLog10.eval L (.fin 0) = .ok .nan)

theorem guardedFloatBoundary_holds : guardedFloatBoundary := by
  intro L p y e hp
  refine ⟨?_, ?_⟩
  · intro he hr
    simp [approxInv, UOp.eval, he, Lib.round, hp, hr, jlt, bind, Except.bind, pure, Except.pure]
  · simp [approxInv, UOp.eval, jlt, pure, Except.pure]

example : SymReg.Loss.LossPrecision.round .float64
    (JF.sub (.fin (1 / (2 : Rat)^58)) (.fin 1)) = .fin (-1) := by decide +kernel

def guardedInverseSpec : Prop := guardedRightInverse ∧ guardedFloatBoundary

theorem guardedInverseSpec_holds : guardedInverseSpec :=
  ⟨guardedRightInverse_holds, guardedFloatBoundary_holds⟩

/-! ## The documented local-inverse contract -/

/-- Operators the `approx_inverse` docstring describes as locally invertible: its own example
`abs` ("`abs` has an `approx_inverse` of `abs`", `src/InverseFunctions.jl:16-18`) and the
guarded pairs of the method table. -/
def DocInvertible : UOp → Prop
  | .abs => True
  | f => GuardedPair f

/-- The docstring of `approx_inverse` (`src/InverseFunctions.jl:13-20`): for each documented
operator `f` it returns a function `g` that inverts `f` on `[0, ε]` for some `ε > 0`, i.e.
`g(f(x)) = x` there. -/
def docLocalInverse : Prop :=
  ∀ (L : Lib) (f : UOp), DocInvertible f →
    ∃ g, approxInv L (.u f) = some g ∧ ∃ ε : Rat, 0 < ε ∧
      ∀ q : Rat, 0 ≤ q → q ≤ ε → (f.eval L (.fin q) >>= g) = .ok (.fin q)

theorem docLocalInverse_refuted : ¬ docLocalInverse := by
  intro h
  obtain ⟨g, hg, _⟩ := h nanLib .abs trivial
  simp [approxInv] at hg

/-! ## Completeness of the power inverse -/

/-- `approx_inverse(Fix2(safe_pow, a)) = Fix2(safe_pow, inv(a))`
(`src/InverseFunctions.jl:139`) should return a finite value on every target the power
actually attains: for finite `a ≠ 0` and finite `x` with `safe_pow(x, a)` finite, `g(x^a)` is
finite. The library's `^` is assumed finite on positive bases. -/
def powInverseComplete : Prop :=
  ∀ (L : Lib) (a x y : Rat), (∀ p e : Rat, 0 < p → ∃ w : Rat, L.pow (.fin p) (.fin e) = .ok (.fin w)) →
    a ≠ 0 → safePowF L (.fin x) (.fin a) = .ok (.fin y) →
    ∃ g, approxInv L (.fix2 .safePow (.fin a)) = some g ∧ ∃ v, g (.fin y) = .ok v ∧ v.valid = true

/-- A library whose `^` returns `1` on every call. -/
def oneLib : Lib := ⟨fun _ _ => .ok .nan, fun _ _ => .ok (.fin 1), fun _ _ => .ok .nan, none⟩

theorem powInverseComplete_refuted : ¬ powInverseComplete := by
  intro h
  have hpow : safePowF oneLib (.fin (-2)) (.fin 3) = .ok (.fin (-8)) := by
    have h1 : ¬ ((3 : Rat) < 0 ∧ (-2 : Rat) = 0) := by grind
    have h2 : (-2 : Rat) * -2 * -2 = -8 := by grind
    simp [safePowF, isInteger, jlt, isZero, powJ, ratPowNat, h1, h2, pure, Except.pure]
  obtain ⟨g, hg, v, hv, hval⟩ := h oneLib 3 (-2) (-8) (fun _ _ _ => ⟨1, rfl⟩) (by decide) hpow
  simp only [approxInv, Option.some.injEq] at hg
  subst hg
  have hthird : JF.div (.fin 1) (.fin 3) = .fin (1 / 3) := by simp [JF.div]
  have hden : ((1 : Rat) / 3).den ≠ 1 := by
    rw [show (1 : Rat) / 3 = (3 : Rat)⁻¹ by grind, Rat.den_inv]
    decide
  have hnan : safePowF oneLib (.fin (-8)) (.fin (1 / 3)) = .ok .nan := by
    have h0 : (0 : Rat) < 1 / 3 := by grind
    have h8 : (-8 : Rat) < 0 := by grind
    simp [safePowF, isInteger, hden, jlt, h0, h8, pure, Except.pure]
  simp only [hthird] at hv
  rw [hnan] at hv
  cases hv
  simp [JF.valid] at hval

end SymReg.Backsolve
