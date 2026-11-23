import SymReg.HofMig.Core

namespace SymReg.HofMig
open DynExpr
open DynExpr.Expressions.Sampling (RNG greater)

/-- Candidate dispatch in src/Migration.jl:28-32: either direct members or
populations flattened in population order and then member order. -/
inductive Candidates where
  | members (values : List Member)
  | populations (values : List (List Member))

/-- Candidate gathering is delayed until the sampled replacement count is nonzero,
src/Migration.jl:25-32. -/
def gatherCandidates : Candidates → List Member
  | .members ms => ms
  | .populations ps => ps.flatten

/-- Random-number and runtime services for src/Migration.jl:23-24,38-43.
Both real and range draws reuse DE's stream and cursor. `exp` and birth-order
values are external scalar/runtime primitives. -/
structure MigrationRuntime where
  exp : JF → Jl JF
  births : Nat → Int

/-- Product loop of `poisson_sample`, src/Utils.jl:146-153, called by
src/Migration.jl:24. Fuel expresses a finite run; exhausting it is explicit.
The return is k-1, including -1 if an invalid mean makes the first test false. -/
def poissonLoop (threshold : JF) : Nat → Nat → JF → RNG → Jl (Int × RNG)
  | 0, _, _, _ => throw (.undefinedBehavior "Poisson loop exceeds supplied fuel")
  | fuel + 1, k, product, rng =>
    if greater product threshold then
      let u := rng.draws rng.cursor
      poissonLoop threshold fuel (k + 1) (product * .fin u)
        { rng with cursor := rng.cursor + 1 }
    else pure ((k : Int) - 1, rng)

/- Source: src/Utils.jl:146-157
function poisson_sample(rng::AbstractRNG, λ::T) where {T}
    iszero(λ) && return 0
    k, p, L = 0, one(T), exp(-λ)
    while p > L
        k += 1
        p *= rand(rng, T)
    end
    return k - 1
end
function poisson_sample(λ::T) where {T}
    return poisson_sample(default_rng(), λ)
end
-/
def poissonSample (rt : MigrationRuntime) (mean : JF) (fuel : Nat) (rng : RNG) :
    Jl (Int × RNG) := do
  if mean = .fin 0 then return (0, rng)
  let threshold ← rt.exp (-mean)
  poissonLoop threshold fuel 0 (.fin 1) rng

def poissonDefault {W : Type} (rt : MigrationRuntime) (mean : JF) (fuel : Nat)
    (defaultRNG : W → RNG × W) (world : W) : Jl (Int × RNG) × W :=
  let (rng, world') := defaultRNG world
  (poissonSample rt mean fuel rng, world')

/-- The two upper clamps in src/Migration.jl:34-36. Negative sampled counts
are retained and subsequently rejected by the random-array dimension check. -/
def clampCount (sampled : Int) (candidates population : Nat) : Int :=
  min (min sampled (candidates : Int)) (population : Int)

/-- `rand(1:population_size, num_replace)`, src/Migration.jl:38. Each draw
uses the full range independently, so duplicate destinations are possible. -/
def drawLocations (population count : Nat) (rng : RNG) : Jl (List Nat × RNG) :=
  if count = 0 then pure ([], rng)
  else if population = 0 then throw (.argumentError "collection must be non-empty")
  else
    pure ((List.range count).map (fun i =>
      (rng.indexDraws (population - 1) (rng.cursor + i)).val),
      { rng with cursor := rng.cursor + count })

/-- `rand(migrant_candidates, num_replace)`, src/Migration.jl:39. All
location draws precede all migrant draws. Sampling is with replacement. -/
def drawMigrants (candidates : List Member) (count : Nat) (rng : RNG) :
    Jl (List Member × RNG) :=
  match candidates with
  | [] => throw (.argumentError "collection must be non-empty")
  | m :: ms =>
      if count = 0 then pure ([], rng) else
      pure ((List.range count).map (fun i =>
        ((m :: ms)[(rng.indexDraws ms.length (rng.cursor + i)).val]?).getD m),
        { rng with cursor := rng.cursor + count })

/-- A single replacement and `reset_birth!`, src/Migration.jl:41-43 and
src/PopMember.jl:181-183. Repeated destinations overwrite earlier fresh copies. -/
def applyMigration (rt : MigrationRuntime) :
    List Nat → List Member → List Member → Nat → Nat → List Member × Nat × Nat
  | i :: locations, m :: migrants, population, fresh, birthCursor =>
      let (copied, f) := copyMember m fresh
      let newborn := { copied with birth := rt.births birthCursor }
      applyMigration rt locations migrants (population.set i newborn) f (birthCursor + 1)
  | _, _, population, fresh, birthCursor => (population, fresh, birthCursor)

-- Source: src/Migration.jl:25-45. The state survives an exception.
def migrateSampledState (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (sampled : Int) (fresh birthCursor : Nat) (rng : RNG) :
    Jl Unit × (List Member × Nat × Nat × RNG) :=
  if sampled = 0 then (.ok (), population, fresh, birthCursor, rng)
  else
    let migrants := gatherCandidates candidates
    let count := clampCount sampled migrants.length population.length
    if count < 0 then (.error (.argumentError "invalid Array dimensions"), population, fresh, birthCursor, rng)
    else
      match drawLocations population.length count.toNat rng with
      | .error e => (.error e, population, fresh, birthCursor, rng)
      | .ok (locations, rng') =>
        match drawMigrants migrants count.toNat rng' with
        | .error e => (.error e, population, fresh, birthCursor, rng')
        | .ok (selected, rng'') =>
          let (out, f, b) := applyMigration rt locations selected population fresh birthCursor
          (.ok (), out, f, b, rng'')

def migrateSampled (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (sampled : Int) (fresh birthCursor : Nat) (rng : RNG) :
    Jl (List Member × Nat × Nat × RNG) :=
  let (result, state) := migrateSampledState rt candidates population sampled fresh birthCursor rng
  result.map (fun _ => state)

/-- Complete `migrate!`, src/Migration.jl:16-45, including Poisson sampling,
zero early exit, both clamps, two vector draws, copying, and reset_birth!.
Candidates and destination may initially share identities: each assignment still copies. -/
def migrate (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (frac : JF) (fuel fresh birthCursor : Nat) (rng : RNG) :
    Jl (List Member × Nat × Nat × RNG) := do
  let mean := .fin (population.length : Rat) * frac
  let (sampled, rng') ← poissonSample rt mean fuel rng
  migrateSampled rt candidates population sampled fresh birthCursor rng'

end SymReg.HofMig
