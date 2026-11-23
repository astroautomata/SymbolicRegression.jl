import SymReg.Options.Core
import SymReg.HofMig.Core
import SymReg.MutateGen.Sample

/-!
Scalar operators in `src/Operators.jl`. Scalars reuse DE's exact-finite JF model,
including its exclusion of rounding, overflow and signed zero. External numerical
functions are arbitrary exception-valued callbacks. Source guards give the same
decisions for positive and negative zero; sign-dependent base results are outside
JF's scope. Dual derivatives and quantity dimensions are external callback behavior;
the scalar dispatch and guards are modelled here.
-/
namespace SymReg.Operators
open DynExpr
open DynExpr.Expressions.Sampling (greater)
open SymReg.HofMig (less greaterEqual)

/-- Nine guarded unary methods, `src/Operators.jl:50-76`. -/
inductive Unary where
  | log | log2 | log10 | log1p | asin | acos | acosh | atanh | sqrt
  deriving DecidableEq, Repr

/-- Domain tests copied from `src/Operators.jl:50-76`, with unordered NaN comparisons. -/
def domain : Unary → JF → Bool
  | .log, x | .log2, x | .log10, x => greater x (.fin 0)
  | .log1p, x => greater x (.fin (-1))
  | .asin, x | .acos, x | .atanh, x =>
      greaterEqual x (.fin (-1)) && greaterEqual (.fin 1) x
  | .acosh, x => greaterEqual x (.fin 1)
  | .sqrt, x => greaterEqual x (.fin 0)



/-- Runtime `isinteger` for JF; infinities and NaN are not integers. The rational
representation is reduced, so denominator one characterizes integer values. -/
def isInteger : JF → Bool
  | .fin q => q.den == 1
  | _ => false

inductive OperandKind where
  | abstractFloat | dual | quantity | other
  deriving DecidableEq

def hasUnaryGuard : OperandKind → Bool
  | .abstractFloat | .dual => true
  | _ => false

structure UnaryRuntime (A B R : Type) where
  kind : OperandKind
  greaterZero : A → Jl Bool
  greaterNegUnit : A → Jl Bool
  atLeastNegUnit : A → Jl Bool
  atMostUnit : A → Jl Bool
  atLeastUnit : A → Jl Bool
  atLeastZero : A → Jl Bool
  typedNaN : Unit → Jl R
  convert : B → Jl R
  checkedBase : Unary → A → Jl B
  genericBase : Unary → A → Jl R

-- Source: src/Operators.jl:50-76,88-96
-- return x > zero(x) ? log(x) : T(NaN)
-- return x > zero(x) ? log2(x) : T(NaN)
-- return x > zero(x) ? log10(x) : T(NaN)
-- return x > -oneunit(x) ? log1p(x) : T(NaN)
-- return -oneunit(x) <= x <= oneunit(x) ? asin(x) : T(NaN)
-- return -oneunit(x) <= x <= oneunit(x) ? acos(x) : T(NaN)
-- return x >= oneunit(x) ? acosh(x) : T(NaN)
-- return -oneunit(x) <= x <= oneunit(x) ? atanh(x) : T(NaN)
-- return x >= zero(x) ? sqrt(x) : T(NaN)
def safeUnaryTyped {A B R : Type} (rt : UnaryRuntime A B R) (op : Unary) (x : A) : Jl R := do
  if !hasUnaryGuard rt.kind then return ← rt.genericBase op x
  let accepted ← match op with
    | .log | .log2 | .log10 => rt.greaterZero x
    | .log1p => rt.greaterNegUnit x
    | .asin | .acos | .atanh =>
      if ← rt.atLeastNegUnit x then rt.atMostUnit x else pure false
    | .acosh => rt.atLeastUnit x
    | .sqrt => rt.atLeastZero x
  if accepted then rt.convert (← rt.checkedBase op x) else rt.typedNaN ()

def safeUnary (base : Unary → JF → Jl JF) (specialized : Bool) (op : Unary) (x : JF) : Jl JF :=
  safeUnaryTyped
    { kind := if specialized then .abstractFloat else .other
      greaterZero := fun v => .ok (greater v (.fin 0))
      greaterNegUnit := fun v => .ok (greater v (.fin (-1)))
      atLeastNegUnit := fun v => .ok (greaterEqual v (.fin (-1)))
      atMostUnit := fun v => .ok (greaterEqual (.fin 1) v)
      atLeastUnit := fun v => .ok (greaterEqual v (.fin 1))
      atLeastZero := fun v => .ok (greaterEqual v (.fin 0))
      typedNaN := fun _ => .ok .nan, convert := Except.ok
      checkedBase := base, genericBase := base } op x

theorem safeUnary_float (base : Unary → JF → Jl JF) (op : Unary) (x : JF) :
    safeUnary base true op x = (if domain op x then base op x else .ok .nan) := by
  unfold safeUnary safeUnaryTyped domain
  cases hb : base op x <;> cases op <;>
    simp [hasUnaryGuard, Bind.bind, Except.bind, Pure.pure, Except.pure, hb] <;>
    split <;> simp_all

def hasPowerGuard : OperandKind → Bool
  | .abstractFloat | .dual | .quantity => true
  | .other => false

structure PowerRuntime (A B P R : Type) where
  baseKind : OperandKind
  exponentKind : OperandKind
  promoteType : Unit → Jl P
  isInteger : B → Jl Bool
  negativeExponent : B → Jl Bool
  positiveExponent : B → Jl Bool
  zeroBase : A → Jl Bool
  negativeBase : A → Jl Bool
  nonpositiveBase : A → Jl Bool
  typedNaN : P → Jl R
  base : A → B → Jl R

-- Source: src/Operators.jl:35-49,87
-- function safe_pow(
--     x::T1, y::T2
-- ) where {
--     T1<:Union{FloatOrDual,UnionAbstractQuantity},
--     T2<:Union{FloatOrDual,UnionAbstractQuantity},
-- }
--     T = promote_type(T1, T2)
--     if isinteger(y)
--         y < zero(y) && iszero(x) && return T(NaN)
--     else
--         y > zero(y) && x < zero(x) && return T(NaN)
--         y < zero(y) && x <= zero(x) && return T(NaN)
--     end
--     return x^y
-- end
-- safe_pow(x, y) = x^y
def safePowTyped {A B P R : Type} (rt : PowerRuntime A B P R) (x : A) (y : B) : Jl R := do
  if hasPowerGuard rt.baseKind && hasPowerGuard rt.exponentKind then
    let t ← rt.promoteType ()
    if ← rt.isInteger y then
      if ← rt.negativeExponent y then
        if ← rt.zeroBase x then return ← rt.typedNaN t
    else
      if ← rt.positiveExponent y then
        if ← rt.negativeBase x then return ← rt.typedNaN t
      if ← rt.negativeExponent y then
        if ← rt.nonpositiveBase x then return ← rt.typedNaN t
  rt.base x y

/-- The exact two branches in `src/Operators.jl:42-47`. Quantities use this same
method; their comparison, conversion and power operations remain external services. -/
def rejectsPower (x y : JF) : Bool :=
  if isInteger y then less y (.fin 0) && SymReg.MutateGen.isZero x
  else (greater y (.fin 0) && less x (.fin 0)) ||
       (less y (.fin 0) && greaterEqual (.fin 0) x)

/-- The standard Float specialization uses JF's IEEE predicates. -/
def safePow (base : JF → JF → Jl JF) (promotedNaN : Jl JF)
    (specialized : Bool) (x y : JF) : Jl JF :=
  let kind := if specialized then OperandKind.abstractFloat else OperandKind.other
  safePowTyped
    { baseKind := kind, exponentKind := kind, promoteType := fun _ => .ok ()
      isInteger := fun v => .ok (isInteger v)
      negativeExponent := fun v => .ok (less v (.fin 0))
      positiveExponent := fun v => .ok (greater v (.fin 0))
      zeroBase := fun v => .ok (SymReg.MutateGen.isZero v)
      negativeBase := fun v => .ok (less v (.fin 0))
      nonpositiveBase := fun v => .ok (greaterEqual (.fin 0) v)
      typedNaN := fun _ => promotedNaN, base } x y

theorem safePow_float (base : JF → JF → Jl JF) (nan : Jl JF) (x y : JF) :
    safePow base nan true x y = (if rejectsPower x y then nan else base x y) := by
  unfold safePow safePowTyped rejectsPower
  simp only [hasPowerGuard, Bool.true_and, ite_true, Bind.bind, Except.bind]
  cases isInteger y <;> cases less y (.fin 0) <;> cases greater y (.fin 0) <;>
    cases SymReg.MutateGen.isZero x <;> cases less x (.fin 0) <;>
    cases greaterEqual (.fin 0) x <;> cases nan <;> rfl

/-- Julia Bool-times-float multiplication has a strong zero:
`false * NaN == 0.0`. This is distinct from JF's float-times-float multiplication. -/
def boolMul (b : Bool) (x : JF) : JF := if b then x else .fin 0

/-- Algebraic wrappers `src/Operators.jl:81-85,98-100`. -/
def square (x : JF) := x * x
def cube (x : JF) := (x * x) * x
def plus (x y : JF) := x + y
def sub (x y : JF) := x - y
def mult (x y : JF) := x * y
def neg (x : JF) := -x

/-- Comparison/logic wrappers `src/Operators.jl:101-124`; one(x) is the
scalar unit one, including for NaN/Inf. -/
def greaterOp (x y : JF) := boolMul (greater x y) (.fin 1)
def lessOp (x y : JF) := boolMul (less x y) (.fin 1)
def greaterEqualOp (x y : JF) := boolMul (greaterEqual x y) (.fin 1)
def lessEqualOp (x y : JF) := boolMul (greaterEqual y x) (.fin 1)
def cond (x y : JF) := boolMul (greater x (.fin 0)) y
def relu (x : JF) := boolMul (greater x (.fin 0)) x
-- Source: src/Operators.jl:119-124
-- function logical_or(x, y)
--     return ((x > zero(x)) | (y > zero(y))) * one(x)
-- end
-- function logical_and(x, y)
--     return ((x > zero(x)) & (y > zero(y))) * one(x)
-- end
def logicalBinary {A : Type} (compare : A → Jl Bool) (one : A → Jl A)
    (scale : Bool → A → Jl A) (conjunction : Bool) (x y : A) : Jl A := do
  let a ← compare x
  let b ← compare y
  let unit ← one x
  scale (if conjunction then a && b else a || b) unit

-- Source: src/Operators.jl:14-17
-- function gamma(x::T)::T where {T<:Number}
--     out = SpecialFunctions.gamma(x)
--     return isinf(out) ? T(NaN) : out
-- end
def gamma {A B : Type} (base : A → Jl B) (infinite : B → Jl Bool)
    (nan : Unit → Jl A) (convert : B → Jl A) (x : A) : Jl A := do
  let out ← base x
  if ← infinite out then nan () else convert out

/-- `atanh_clip`, `src/Operators.jl:19`: external Base mod/atanh calls may throw.
The source comment uses `%`, while execution uses mod. -/
def atanhClip (modulo : JF → JF → Jl JF) (atanh : JF → Jl JF) (x : JF) : Jl JF := do
  let wrapped ← modulo (x + .fin 1) (.fin 1 + .fin 1)
  let out ← atanh (wrapped - .fin 1)
  return out * .fin 1

-- Source: src/Operators.jl:163-168; Julia base/deprecated.jl
-- @deprecate pow(x, y) safe_pow(x, y)
-- @deprecate pow_abs(x, y) safe_pow(x, y)
-- @ignore pow(x, y) = safe_pow(x, y)
-- @ignore pow_abs(x, y) = safe_pow(x, y)
def pow {A B P R : Type} (depwarn : String → Jl Unit) (rt : PowerRuntime A B P R)
    (x : A) (y : B) : Jl R := do
  depwarn "pow"
  safePowTyped rt x y
def powAbs {A B P R : Type} (depwarn : String → Jl Unit) (rt : PowerRuntime A B P R)
    (x : A) (y : B) : Jl R := do
  depwarn "pow_abs"
  safePowTyped rt x y

/-- `get_safe_op`, `src/Operators.jl:171-185`, reusing Options' existing function
identities and normalization. Unlike Options.opmap it does not map plus/mult/sub/div/pow. -/
def getSafeOp (op : Nat) : Nat :=
  if op = 5 ∨ (7 ≤ op ∧ op ≤ 19) then SymReg.Options.opmap op else op

/-- Safe function identity for each unary method, `src/Operators.jl:173-181`. -/
def safeId : Unary → Nat
  | .log => 110 | .log10 => 111 | .log2 => 112 | .log1p => 113
  | .sqrt => 114 | .asin => 115 | .acos => 116 | .acosh => 117 | .atanh => 118

/-- Base names are separate from the printed override table, `src/Operators.jl:128-137`. -/
def unaryName : Unary → String
  | .log => "log" | .log2 => "log2" | .log10 => "log10" | .log1p => "log1p"
  | .asin => "asin" | .acos => "acos" | .acosh => "acosh" | .atanh => "atanh" | .sqrt => "sqrt"

def printedName : Nat → Option String
  | 105 => some "^" | 110 => some "log" | 111 => some "log10" | 112 => some "log2"
  | 113 => some "log1p" | 114 => some "sqrt" | 115 => some "asin" | 116 => some "acos"
  | 117 => some "acosh" | 118 => some "atanh" | _ => none

/-- Pretty-only comparison names, `src/Operators.jl:141-144`. -/
def prettyName : Nat → Option String
  | 106 => some ">" | 107 => some "<" | 108 => some ">=" | 109 => some "<=" | _ => none

/-- Explicit aliases by arity, `src/Operators.jl:147-160`. An absent override leaves
DE's generic alias behavior outside this table. -/
def operatorAlias (op arity : Nat) : Option Nat :=
  match arity with
  | 1 => if 110 ≤ op ∧ op ≤ 118 then some (op - 99) else none
  | 2 => if 105 ≤ op ∧ op ≤ 109 then some (if op = 105 then 5 else op - 99) else none
  | _ => none

end SymReg.Operators
