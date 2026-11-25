import DynExpr.NodeBase.TreeOps
import SymReg.Complexity
import SymReg.Loss.Core

/-!
Units slice: `src/DimensionalAnalysis.jl` (dimensional-analysis evaluation of trees with
`WildcardQuantity`) and `src/InterfaceDynamicQuantities.jl` (unit parsing helpers),
SymbolicRegression.jl `upstream/master` edbe678e, with DynamicQuantities.jl 1.x.

Dimensions are the seven SI exponent vectors of `DynamicQuantities.Dimensions{FRInt32}`.
Exponents are rationals; DynamicQuantities stores them as `FixedRational{Int32,25200}`
(`DEFAULT_DIM_BASE_TYPE`), so a rational power truncates the scaled numerator toward zero
(`Dim.fr`; for example, `dimension(u"m")^(1//32)` is `m^(787/25200)`,
`dimension(u"m^-1")^(1//32)` is `m^(-787/25200)`, `^(1//64)` gives `393/25200`, `^(1//27)`
gives `933/25200`). Addition of exponents is exact; Int32 numerator overflow (exponents
beyond 85217) is outside the model.

Scalar arithmetic on stripped values (`Float64` `+`, `sqrt`, `safe_pow`, ...) is the
arbitrary library function `Scalars`, except the feature scaling `x[f] * x_units[f]`,
which is `JF` multiplication.
-/

namespace SymReg.Units
open DynExpr DynExpr.NodeBase

/-! ## Dimensions -/

/-- `Dimensions{FRInt32}`: exponents of length, mass, time, current, temperature,
luminosity and amount. -/
structure Dim where
  length : Rat
  mass : Rat
  time : Rat
  current : Rat
  temperature : Rat
  luminosity : Rat
  amount : Rat
  deriving DecidableEq, Repr

namespace Dim

/-- Componentwise map. -/
def map (f : Rat → Rat) (a : Dim) : Dim :=
  ⟨f a.length, f a.mass, f a.time, f a.current, f a.temperature, f a.luminosity, f a.amount⟩

/-- Componentwise binary map. -/
def map2 (f : Rat → Rat → Rat) (a b : Dim) : Dim :=
  ⟨f a.length b.length, f a.mass b.mass, f a.time b.time, f a.current b.current,
    f a.temperature b.temperature, f a.luminosity b.luminosity, f a.amount b.amount⟩

/-- `Dimensions()`: dimensionless (`iszero(dimension(x))`, `src/DimensionalAnalysis.jl:60`). -/
def one : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- Dimensions of a product. -/
def mul (a b : Dim) : Dim := map2 (· + ·) a b

/-- Dimensions of a quotient. -/
def div (a b : Dim) : Dim := map2 (· - ·) a b

/-- Dimensions of `inv`. -/
def inv (a : Dim) : Dim := map (fun e => -e) a

/-- Exact rational scaling of every exponent (the physical rule for roots). -/
def scale (q : Rat) (a : Dim) : Dim := map (· * q) a

/-- Storage of a rational exponent as `FixedRational{Int32,25200}`: the numerator over
25200 is truncated toward zero. -/
def fr (q : Rat) : Rat := ((q * 25200).num.tdiv ((q * 25200).den : Int) : Int) / 25200

/-- `dimension(x)^(1//n)` as computed by DynamicQuantities for `sqrt` (`n = 2`) and
`cbrt` (`n = 3`): every exponent `e` becomes `fr (e / n)`. -/
def root (n : Rat) (a : Dim) : Dim := map (fun e => fr (e / n)) a

/-- No exponent is truncated by the root. -/
def RootExact (n : Rat) (a : Dim) : Prop := root n a = scale (1 / n) a

end Dim

/-- `Quantity{T,Dimensions{FRInt32}}`: a stripped value and its dimensions. -/
structure Q where
  val : JF
  dim : Dim
  deriving DecidableEq, Repr

/-! ## WildcardQuantity, src/DimensionalAnalysis.jl:39-116 -/

/-- `WildcardQuantity{Q}` (`src/DimensionalAnalysis.jl:46-50`). -/
structure WQ where
  val : JF
  dim : Dim
  wildcard : Bool
  violates : Bool
  deriving DecidableEq, Repr

/-- `Base.one(W) = W(one(Q), false, false)` (`src/DimensionalAnalysis.jl:56`). -/
def WQ.one : WQ := ⟨.fin 1, Dim.one, false, false⟩

/-- `W(one(Q), false, true)`, the violation marker of `src/DimensionalAnalysis.jl:88,101,145,193`. -/
def WQ.bad : WQ := ⟨.fin 1, Dim.one, false, true⟩

/-- `valid(x) = !x.violates` (`src/DimensionalAnalysis.jl:54`). -/
def WQ.valid (w : WQ) : Bool := !w.violates

/-- The operators with a fixed meaning in the dimensional check. `neg` stands for the
generic one-argument methods whose body needs `-x` or `zero(x)` (`neg`, `relu`,
`src/Operators.jl:98-120`); `fn k n` for `n`-ary functions with only `Number` methods
(`cos`, `exp`, `sin`, ...); `safeFn k n` for the generic forwarding methods `safe_log`,
`safe_log2`, ... (`src/Operators.jl:88-95`); `cmp k` for `greater`, `less`,
`greater_equal`, `less_equal` (`src/Operators.jl:101-112`). `pow` is `safe_pow` and
`sqrt` is `safe_sqrt` (`Options` maps `^` and `sqrt` to them, `src/Options.jl:186-196`). -/
inductive Builtin where
  | add | sub | mul | div | pow | sqrt | cbrt | abs | inv | neg
  | fn (k n : Nat) | safeFn (k n : Nat) | cmp (k : Nat)
  deriving DecidableEq, Repr

/-- Number of arguments of each operator. -/
def Builtin.arity : Builtin → Nat
  | .add | .sub | .mul | .div | .pow | .cmp _ => 2
  | .sqrt | .cbrt | .abs | .inv | .neg => 1
  | .fn _ n | .safeFn _ n => n

/-- Arbitrary scalar semantics of every operator on stripped `Float64` values. -/
abbrev Scalars := Builtin → List JF → JF

section WOps
variable (sc : Scalars)

/-- `*` and `/` on `WildcardQuantity` (`src/DimensionalAnalysis.jl:64-70`). -/
def wMulDiv (b : Builtin) (dop : Dim → Dim → Dim) (l r : WQ) : WQ :=
  if l.violates then l else if r.violates then r
  else ⟨sc b [l.val, r.val], dop l.dim r.dim, l.wildcard || r.wildcard, false⟩

/-- `+` and `-` on `WildcardQuantity` (`src/DimensionalAnalysis.jl:71-91`). In the
one-wildcard branches the wildcard operand is re-dimensioned to the other's dimensions, so
the result carries the other operand's dimensions. -/
def wAddSub (b : Builtin) (l r : WQ) : WQ :=
  if l.violates then l else if r.violates then r
  else if l.dim = r.dim then ⟨sc b [l.val, r.val], l.dim, l.wildcard && r.wildcard, false⟩
  else if l.wildcard && r.wildcard then ⟨sc b [l.val, r.val], Dim.one, true, false⟩
  else if l.wildcard then ⟨sc b [l.val, r.val], r.dim, false, false⟩
  else if r.wildcard then ⟨sc b [l.val, r.val], l.dim, false, false⟩
  else WQ.bad

/-- `^` on `WildcardQuantity` (`src/DimensionalAnalysis.jl:92-103`): base and power must be
dimensionless or wildcards; the value is `safe_pow(x, y) * one(Q)`, and multiplying by the
dimensionless unit quantity leaves the value unchanged. -/
def wPow (l r : WQ) : WQ :=
  if l.violates then l else if r.violates then r
  else if (decide (l.dim = Dim.one) || l.wildcard) && (decide (r.dim = Dim.one) || r.wildcard)
  then ⟨sc .pow [l.val, r.val], Dim.one, false, false⟩
  else WQ.bad

/-- `sqrt`, `cbrt`, `abs`, `inv`, `neg` on `WildcardQuantity`
(`src/DimensionalAnalysis.jl:59-71,128-139`). `sqrt` calls the Quantity `safe_sqrt` of
`src/DimensionalAnalysis.jl:34-37`, whose value agrees with the scalar `safe_sqrt` on every
finite input (NaN for negatives). -/
def wUnary (b : Builtin) (dop : Dim → Dim) (l : WQ) : WQ :=
  if l.violates then l else ⟨sc b [l.val], dop l.dim, l.wildcard, false⟩

/-- `greater`, `less`, `greater_equal`, `less_equal` on `WildcardQuantity`
(`src/DimensionalAnalysis.jl:57,67-83`, `src/Operators.jl:101-112`): equal dimensions
or either wildcard yields a dimensionless non-wildcard result; otherwise `DimensionError`. -/
def wCmp (k : Nat) (l r : WQ) : Jl WQ :=
  if l.violates || r.violates then .error (.errorException "DimensionError")
  else if decide (l.dim = r.dim) || l.wildcard || r.wildcard then
    .ok ⟨sc (.cmp k) [l.val, r.val], Dim.one, false, false⟩
  else .error (.errorException "DimensionError")

end WOps

/-! ## Operators as Julia functions -/

/-- An argument of an operator call inside `degn_eval`: a `WildcardQuantity` or a
stripped scalar `T`. -/
inductive Arg where
  | w (x : WQ)
  | t (v : JF)
  deriving DecidableEq, Repr

/-- A Julia operator as seen by `degn_eval`: `hasmethod(op, Tuple{...})` for an argument
pattern (`true` = scalar `T`, `false` = `W`), and the call itself. A `MethodError` is
`JlError.methodError`. -/
structure Op where
  hasMethod : List Bool → Bool
  call : List Arg → Jl Arg

/-- `DimensionError`, caught by `@maybe_return_call` (`src/DimensionalAnalysis.jl:28`). -/
def dimensionError : JlError := .errorException "DimensionError"

/-- The `::D` / `::T` type assertions of `src/Utils.jl:237,242` and
`src/DimensionalAnalysis.jl:175`. -/
def typeError : JlError := .errorException "TypeError"

/-- The `WildcardQuantity` overloads reached by an all-`W` call of a built-in operator
(`src/DimensionalAnalysis.jl:56-139`); `none` where no such method exists. -/
def wop (sc : Scalars) : Builtin → List WQ → Option WQ
  | .add, [l, r] => some (wAddSub sc .add l r)
  | .sub, [l, r] => some (wAddSub sc .sub l r)
  | .mul, [l, r] => some (wMulDiv sc .mul Dim.mul l r)
  | .div, [l, r] => some (wMulDiv sc .div Dim.div l r)
  | .pow, [l, r] => some (wPow sc l r)
  | .sqrt, [l] => some (wUnary sc .sqrt (Dim.root 2) l)
  | .cbrt, [l] => some (wUnary sc .cbrt (Dim.root 3) l)
  | .abs, [l] => some (wUnary sc .abs id l)
  | .inv, [l] => some (wUnary sc .inv Dim.inv l)
  | .neg, [l] => some (wUnary sc .neg id l)
  | _, _ => none

/-- The scalar of an argument, if it is one. -/
def Arg.toT : Arg → Option JF
  | .t v => some v
  | .w _ => none

/-- The quantity of an argument, if it is one. -/
def Arg.toW : Arg → Option WQ
  | .w x => some x
  | .t _ => none

/-- Methods of the built-in operators. `+`, `-`, `*`, `/` have the `(W, W)` overloads and
`Number` methods only; `cos`-like functions have `Number` methods only; every other
operator has a generic method for any argument types (`safe_pow`, `safe_sqrt`, `neg`,
`relu`, `safe_log`, `greater`, ...) or overloads for both `W` and `Number` (`cbrt`, `abs`,
`inv`). Calls with only scalars compute the scalar function; all-`W` calls reaching a `W`
overload or comparison compute it (throwing `DimensionError` for mismatched non-wildcard
comparisons); every other call throws `MethodError`. -/
def Builtin.toOp (sc : Scalars) (b : Builtin) : Op where
  hasMethod p := p.length == b.arity && (match b with
    | .add | .sub | .mul | .div => p.all id || p.all (! ·)
    | .fn _ _ => p.all id
    | _ => true)
  call args :=
    match args.mapM Arg.toT with
    | some vs => .ok (.t (sc b vs))
    | none => match args.mapM Arg.toW with
      | some ws => match b, ws with
        | .cmp k, [l, r] => (wCmp sc k l r).map Arg.w
        | _, _ => match wop sc b ws with
          | some r => .ok (.w r)
          | none => .error (.methodError "no method matching")
      | none => .error (.methodError "no method matching")

/-! ## degn_eval, src/DimensionalAnalysis.jl:156-221 -/

/-- `compute_lattice(Val(N), Val(i+1), Val(j+1)) == 1` (`src/DimensionalAnalysis.jl:219-221`)
for the zero-based lattice index `i`: argument `j` is passed stripped. -/
def pattern (n i : Nat) : List Bool :=
  (List.range n).map fun j => i / 2 ^ (n - 1 - j) % 2 == 1

/-- The arguments of one lattice point: `lattice_j == 0 ? arg_j : ustrip(arg_j)`. -/
def argsFor (p : List Bool) (ws : List WQ) : List Arg :=
  (p.zip ws).map fun (b, w) => if b then .t w.val else .w w

/-- `@nall(N, j -> lattice_j == 0 ? true : (arg_j.wildcard || has_no_dims(arg_j.val)))`. -/
def allowed (p : List Bool) (ws : List WQ) : Bool :=
  (p.zip ws).all fun (b, w) => !b || w.wildcard || decide (w.dim = Dim.one)

/-- `safe_call(op, inputs, one(W))` (`src/Utils.jl:234-251`): a `MethodError` gives
`(default, false)`; any other error is rethrown; a non-`W` result fails the `::D`
assertion. The per-task cache of `safe_call` is not modelled: for every built-in operator
method applicability depends on argument types only, so the cached outcome equals the
uncached one. -/
def safeCall (op : Op) (args : List Arg) : Jl (WQ × Bool) :=
  match op.call args with
  | .ok (.w r) => .ok (r, true)
  | .ok (.t _) => .error typeError
  | .error (.methodError _) => .ok (WQ.one, false)
  | .error e => .error e

/-- `@maybe_return_call(W, op, inputs)` (`src/DimensionalAnalysis.jl:20-32`): `some r`
when the call succeeds with a valid result; `DimensionError` falls through; other errors
propagate. -/
def maybeReturnCall (op : Op) (args : List Arg) : Jl (Option WQ) :=
  match safeCall op args with
  | .ok (r, ok) => .ok (if ok && r.valid then some r else none)
  | .error e => if e = dimensionError then .ok none else .error e

/-- The last lattice point (`src/DimensionalAnalysis.jl:170-175`):
`W(op(ustrip.(args)...)::T, false, false)`, a dimensionless non-wildcard quantity.
Errors are not caught. -/
def allScalar (op : Op) (ws : List WQ) : Jl WQ :=
  match op.call (ws.map fun w => .t w.val) with
  | .ok (.t v) => .ok ⟨v, Dim.one, false, false⟩
  | .ok (.w _) => .error typeError
  | .error e => .error e

/-- The unrolled `@nexprs(2^N, i -> ...)` loop (`src/DimensionalAnalysis.jl:157-185`)
over the zero-based lattice indices `is`, then `W(one(Q), false, true)`
(`src/DimensionalAnalysis.jl:193`). -/
def lattice (op : Op) (ws : List WQ) : List Nat → Jl WQ
  | [] => .ok WQ.bad
  | i :: is =>
    let p := pattern ws.length i
    if op.hasMethod p && allowed p ws then
      if i + 1 = 2 ^ ws.length then allScalar op ws
      else match maybeReturnCall op (argsFor p ws) with
        | .ok (some r) => .ok r
        | .ok none => lattice op ws is
        | .error e => .error e
    else lattice op ws is

/-- `degn_eval(op, args...)` (`src/DimensionalAnalysis.jl:133-195`): the first violating
argument is returned; a nonfinite argument (`isfinite(w.val)`) is a violation; then the
lattice of `W`/`T` method patterns is tried in order. -/
def degnEval (op : Op) (ws : List WQ) : Jl WQ :=
  match ws.find? (·.violates) with
  | some w => .ok w
  | none =>
    if ws.any (fun w => !w.val.valid) then .ok WQ.bad
    else lattice op ws (List.range (2 ^ ws.length))

/-! ## Leaves and the tree reduction -/

/-- `deg0_eval` (`src/DimensionalAnalysis.jl:119-132`): a constant is a dimensionless
quantity, a wildcard exactly when wildcards are allowed; a feature is
`x[t.feature] * x_units[t.feature]` (unchecked indexing). -/
def deg0Eval (row : List JF) (xu : List Q) (allow : Bool) : Tree JF → Jl WQ
  | .const v => .ok ⟨v, Dim.one, allow, false⟩
  | .feature i => do
    let x ← SymReg.Complexity.idx1 row i
    let u ← SymReg.Complexity.idx1 xu i
    .ok ⟨x * u.val, u.dim, false, false⟩
  | .branch _ _ => .error (.undefinedBehavior "childless branch")

/-- `@inbounds operators.ops[branch.degree][branch.op]` (`src/DimensionalAnalysis.jl:210`). -/
def opAt (ops : List (List Op)) (t : Tree JF) : Jl Op := do
  let l ← SymReg.Complexity.idx1 ops t.degree
  SymReg.Complexity.idx1 l (opOf t)

/-- `violates_dimensional_constraints_dispatch` (`src/DimensionalAnalysis.jl:200-216`):
`tree_mapreduce` with `break_sharing=Val(true)` on a plain `Node` (DE's `tmrT`). `D` is the
maximum degree of the node type. -/
def dispatch (D : Nat) (ops : List (List Op)) (xu : List Q) (row : List JF) (allow : Bool)
    (t : Tree JF) : Jl WQ :=
  tmrT (m := Jl) D (deg0Eval row xu allow) pure
    (fun branch ws => opAt ops branch >>= fun op => degnEval op ws) t

/-- `violates_dimensional_constraints(tree, X_units, y_units, x, options)`
(`src/DimensionalAnalysis.jl:236-257`), with `allow = !options.dimensionless_constants_only`.
A present `y_units` adds a violation when the root is not a wildcard and its dimensions
differ. -/
def violatesUnits (D : Nat) (ops : List (List Op)) (xu : List Q) (yu : Option Q)
    (row : List JF) (allow : Bool) (t : Tree JF) : Jl Bool := do
  let w ← dispatch D ops xu row allow t
  match yu with
  | none => pure w.violates
  | some y => pure (w.violates || (!w.wildcard && decide (w.dim ≠ y.dim)))

/-- The four methods of `violates_dimensional_constraints` on a node
(`src/DimensionalAnalysis.jl:223-275`), dispatching on the presence of `X_units` and
`y_units`, and reading the view `X[:, 1]` (first column of the column list) first. -/
def violatesDataset (D : Nat) (ops : List (List Op)) (columns : List (List JF))
    (xu : Option (List Q)) (yu : Option Q) (allow : Bool) (t : Tree JF) : Jl Bool := do
  let row ← SymReg.Loss.at1 columns 1
  match xu, yu with
  | some xu, yu => violatesUnits D ops xu yu row allow t
  | none, some _ => .error (.errorException "This should never happen. Please submit a bug report.")
  | none, none => .ok false

/-- Expression wrappers (`src/DimensionalAnalysis.jl:231-235`) forward `get_tree(tree)`. -/
def violatesExpr {E : Type} (getTree : E → Tree JF) (D : Nat) (ops : List (List Op))
    (columns : List (List JF)) (xu : Option (List Q)) (yu : Option Q) (allow : Bool)
    (e : E) : Jl Bool :=
  violatesDataset D ops columns xu yu allow (getTree e)

/-! ## Specification: consistent dimension assignments -/

/-- The physical dimension rule of each operator: `+`, `-` and comparisons need equal
dimensions; `^` needs a dimensionless base and power (the documented rule of
`src/DimensionalAnalysis.jl:96`); `sqrt`/`cbrt` take exact rational roots; `cos`-like and
`log`-like functions need dimensionless arguments; `neg` preserves dimensions. -/
def specRule : Builtin → List Dim → Option Dim
  | .add, [a, b] | .sub, [a, b] => if a = b then some a else none
  | .mul, [a, b] => some (a.mul b)
  | .div, [a, b] => some (a.div b)
  | .pow, [a, b] => if a = Dim.one ∧ b = Dim.one then some Dim.one else none
  | .sqrt, [a] => some (a.scale (1 / 2))
  | .cbrt, [a] => some (a.scale (1 / 3))
  | .abs, [a] => some a
  | .inv, [a] => some a.inv
  | .neg, [a] => some a
  | .fn _ n, ds | .safeFn _ n, ds =>
    if ds.length = n ∧ ds.all (· = Dim.one) then some Dim.one else none
  | .cmp _, [a, b] => if a = b then some Dim.one else none
  | _, _ => none

/-- The built-in operator at degree `n`, index `o` of a table. -/
def kindAt (table : List (List Builtin)) (n o : Nat) : Option Builtin :=
  if 1 ≤ n ∧ 1 ≤ o then (table[n - 1]?).bind (·[o - 1]?) else none

mutual
/-- `t` has dimensions `d` for some choice of dimensions of its constants, every constant
choosing independently (any dimensions when wildcards are allowed, dimensionless otherwise),
features carrying their units. -/
def Typed (table : List (List Builtin)) (xu : List Dim) (allow : Bool) : Tree JF → Dim → Prop
  | .const _, d => allow = true ∨ d = Dim.one
  | .feature i, d => 1 ≤ i ∧ xu[i - 1]? = some d
  | .branch o cs, d => ∃ b ds, kindAt table cs.length o = some b ∧
      TypedL table xu allow cs ds ∧ specRule b ds = some d
/-- Children typed pointwise. -/
def TypedL (table : List (List Builtin)) (xu : List Dim) (allow : Bool) :
    List (Tree JF) → List Dim → Prop
  | [], [] => True
  | c :: cs, d :: ds => Typed table xu allow c d ∧ TypedL table xu allow cs ds
  | _, _ => False
end

/-- The operator table seen by Julia. -/
def opsOf (sc : Scalars) (table : List (List Builtin)) : List (List Op) :=
  table.map (·.map (Builtin.toOp sc))

mutual
/-- Scalar evaluation of `t` on the first row with unit-scaled features, the values the
check computes. -/
def sval (sc : Scalars) (table : List (List Builtin)) (row : List JF) (xu : List Q) :
    Tree JF → JF
  | .const v => v
  | .feature i => (row[i - 1]?.getD (.fin 0)) * ((xu[i - 1]?.map Q.val).getD (.fin 0))
  | .branch o cs => match kindAt table cs.length o with
    | some b => sc b (svalL sc table row xu cs)
    | none => .fin 0
/-- `sval` of each child. -/
def svalL (sc : Scalars) (table : List (List Builtin)) (row : List JF) (xu : List Q) :
    List (Tree JF) → List JF
  | [] => []
  | c :: cs => sval sc table row xu c :: svalL sc table row xu cs
end

mutual
/-- Every proper subexpression has a finite scalar value. -/
def SubFinite (sc : Scalars) (table : List (List Builtin)) (row : List JF) (xu : List Q) :
    Tree JF → Prop
  | .const _ | .feature _ => True
  | .branch _ cs => SubFiniteL sc table row xu cs
/-- Each child is finite and has finite subexpressions. -/
def SubFiniteL (sc : Scalars) (table : List (List Builtin)) (row : List JF) (xu : List Q) :
    List (Tree JF) → Prop
  | [] => True
  | c :: cs => (sval sc table row xu c).valid = true ∧ SubFinite sc table row xu c ∧
      SubFiniteL sc table row xu cs
end

mutual
/-- No `sqrt`/`cbrt` truncates the exponents of a non-wildcard argument. -/
def RootsExact (ev : Tree JF → Jl WQ) (table : List (List Builtin)) : Tree JF → Prop
  | .const _ | .feature _ => True
  | .branch o cs => (∀ c w, cs = [c] → ev c = .ok w → w.violates = false →
        w.wildcard = false →
        (kindAt table 1 o = some .sqrt → w.dim.RootExact 2) ∧
        (kindAt table 1 o = some .cbrt → w.dim.RootExact 3)) ∧
      RootsExactL ev table cs
/-- `RootsExact` for each child. -/
def RootsExactL (ev : Tree JF → Jl WQ) (table : List (List Builtin)) : List (Tree JF) → Prop
  | [] => True
  | c :: cs => RootsExact ev table c ∧ RootsExactL ev table cs
end

/-- Operators of the arithmetic fragment. -/
def Builtin.arith : Builtin → Bool
  | .add | .sub | .mul | .div | .pow | .sqrt | .cbrt | .abs | .inv => true
  | _ => false

end SymReg.Units
