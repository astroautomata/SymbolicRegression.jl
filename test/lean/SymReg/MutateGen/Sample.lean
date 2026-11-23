import DynExpr.Expressions.Sampling
import SymReg.MutateGen.Weights
import SymReg.Loss.Core

/-!
Weighted choice of a mutation: `_sample_mutation` (`src/Mutate.jl:247-262`, used by
`next_generation` and by crossover choice) and the exported `sample_mutation`
(`src/MutationWeights.jl:159-164`), which calls StatsBase 0.34.13
`sample(rng, a, wv) = a[sample(rng, wv)]` (`StatsBase/src/sampling.jl:586-609`).

Both draw one `rand()` from the task-local RNG, modelled by DE's abstract draw stream
`DynExpr.Expressions.Sampling.RNG`; the draw is taken only after the weight checks.
-/

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw greater)

attribute [local semireducible] Rat.add Rat.mul Rat.inv

open SymReg.Loss (LossPrecision)

/-- Float64 addition in the checked total and prefix loops. -/
def weightAdd (a b : JF) : JF := LossPrecision.round .float64 (a + b)

/-- Float64 threshold multiplication after the task-local draw. -/
def weightThreshold (u : Rat) (total : JF) : JF :=
  LossPrecision.round .float64 (JF.fin u * total)

/-- IEEE `x < y` (`greater` is DE's IEEE `>`). -/
def jlt (x y : JF) : Bool := greater y x

/-- IEEE `w >= 0.0`: false for NaN and negative infinity. -/
def geZero : JF → Bool
  | .fin q => decide (0 ≤ q)
  | .posInf => true
  | _ => false

/-- `isfinite`. -/
def isFinite : JF → Bool
  | .fin _ => true
  | _ => false

/-- `iszero`. -/
def isZero : JF → Bool
  | .fin q => q == 0
  | _ => false

/-- The checking loop of `_sample_mutation` (`src/Mutate.jl:248-252`): each weight in order
must satisfy `weight >= 0.0`, else `ArgumentError`; the total is accumulated with `+`. -/
def checkedTotal {α : Type} : JF → List (α × JF) → Jl JF
  | acc, [] => pure acc
  | acc, (_, w) :: ws =>
    if geZero w then checkedTotal (weightAdd acc w) ws
    else throw (.argumentError "Weights must be nonnegative.")

/-- The selection loop of `_sample_mutation` (`src/Mutate.jl:256-261`): the first
one-based index whose running sum exceeds the threshold, else `lastindex(mutations)`. -/
def selectIdx {α : Type} (threshold : JF) (n : Nat) : Nat → JF → List (α × JF) → Nat
  | _, _, [] => n
  | i, cum, (_, w) :: ws =>
    let cum' := weightAdd cum w
    if jlt threshold cum' then i else selectIdx threshold n (i + 1) cum' ws

/-- `_sample_mutation(mutations)` after its single draw `u = rand()` (`src/Mutate.jl:247-262`).
Returns the one-based index. -/
def sampleMutationCore {α : Type} (ws : List (α × JF)) (u : Rat) : Jl Nat :=
  match checkedTotal (.fin 0) ws with
  | .error e => .error e
  | .ok total =>
    if !greater total (.fin 0) then .error (.argumentError "At least one weight must be positive.")
    else
      let threshold := weightThreshold u total
      .ok (selectIdx threshold ws.length 1 (.fin 0) ws)

/-- `_sample_mutation(mutations)` with the task-local RNG (`src/Mutate.jl:247-262`): the
checks of lines 248-253 run before the draw of line 255. -/
def sampleMutationR {α : Type} (ws : List (α × JF)) (rng : RNG) : Jl Nat × RNG :=
  match checkedTotal (.fin 0) ws with
  | .error e => (.error e, rng)
  | .ok total =>
    if !greater total (.fin 0) then (.error (.argumentError "At least one weight must be positive."), rng)
    else
      let (u, rng') := draw rng
      (.ok (selectIdx (weightThreshold u total) ws.length 1 (.fin 0) ws), rng')

/-- `sum(vs)` for `StatsBase.Weights(vs)` (`StatsBase/src/weights.jl:72`), in exact arithmetic. -/
def jsum (ws : List JF) : JF := ws.foldl (· + ·) (.fin 0)

/-- The forward scan of StatsBase `sample(rng, wv)` (`StatsBase/src/sampling.jl:595-598`):
`while cw < t && i < n; i += 1; cw += wv[i]; end`, on the weights after position `i`. -/
def sbScan (t : JF) : Nat → JF → List JF → Nat × JF
  | i, cw, [] => (i, cw)
  | i, cw, w :: ws => if jlt cw t then sbScan t (i + 1) (cw + w) ws else (i, cw)

/-- The backward correction `while iszero(wv[i]); i -= 1; end`
(`StatsBase/src/sampling.jl:599-604`); stepping below index 1 is a `BoundsError`. -/
def sbBack (ws : List JF) : Nat → Nat → Jl Nat
  | 0, _ => throw .boundsError
  | fuel + 1, i =>
    match ws[i - 1]? with
    | none => throw .boundsError
    | some w => if isZero w then sbBack ws fuel (i - 1) else pure i

/-- StatsBase 0.34.13 `sample(rng, wv::AbstractWeights)` after its draw `u = rand(rng)`
(`StatsBase/src/sampling.jl:586-605`), on 1-based weights. -/
def sbSampleCore (ws : List JF) (u : Rat) : Jl Nat := do
  let wsum := jsum ws
  if !isFinite wsum then throw (.argumentError "only finite weights are supported")
  let t := JF.fin u * wsum
  match ws with
  | [] => throw .boundsError
  | w1 :: rest =>
    let (i, cw) := sbScan t 1 w1 rest
    if jlt cw t then sbBack ws (i + 1) i else pure i

/-- `sample_mutation(mutations)` (`src/MutationWeights.jl:159-164`):
`StatsBase.sample(eachindex(mutations), StatsBase.Weights(map(last, mutations)))`, then the
mutation at that index. The draw follows the finiteness check. -/
def sampleMutationExported (ms : List (Kind × JF)) (rng : RNG) : Jl Kind × RNG :=
  let ws := ms.map Prod.snd
  if !isFinite (jsum ws) then (.error (.argumentError "only finite weights are supported"), rng)
  else
    let (u, rng') := draw rng
    (do
      let i ← sbSampleCore ws u
      match ms[i - 1]? with
      | some p => pure p.1
      | none => throw .boundsError, rng')

end SymReg.MutateGen
