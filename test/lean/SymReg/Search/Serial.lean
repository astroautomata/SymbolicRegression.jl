import SymReg.Search.DriverProperties
import DynExpr.Registry.Types

namespace SymReg.Search
open DynExpr
open SymReg.HofMig
open DynExpr.Expressions.Sampling (RNG)

-- Source: src/SymbolicRegression.jl:741-744,828-831
-- if options.seed !== nothing
--     seed!(options.seed)
-- end
-- return nothing
-- task_order = [(j, i) for j in 1:nout for i in 1:(options.populations)]
-- shuffle!(task_order)
/-- The Julia RNG algorithm and shuffle are runtime operations. They receive the
current task's RNG explicitly here, as do the subsequent stochastic services. -/
structure SerialRuntime where
  seeded : Int → RNG
  shuffle : List (Nat × Nat) → RNG → List (Nat × Nat) × RNG
  /-- Persistent dataset state after baseline updates, with its data and baseline fields. -/
  Baseline : Type
  /-- Pre-seed dataset updates and optional tests/helper setup may throw or consume randomness. -/
  beforeSeed : RNG → Jl (Baseline × RNG)
  initializeSearch : Baseline → RNG → Jl ((List (Nat → List Member) × List Hof) × RNG)
  reply : Baseline → Nat → Nat → Nat → RNG → Reply × RNG

/-- Execute the initial serial warmup jobs in Julia's output/population order.
Each job receives the stream left by its predecessor. -/
private def serialWarmup (rt : SerialRuntime) (baseline : rt.Baseline)
    (iterations outputs populations : Nat) (rng : RNG) :
    List ((Nat × Nat) × Reply) × RNG :=
  if iterations = 0 then ([], rng)
  else (((List.range outputs).flatMap fun j => (List.range populations).map (j, ·)).foldl
    (fun (replies, r) (j, i) =>
      let (reply, next) := rt.reply baseline j i 0 r
      (replies ++ [((j, i), reply)], next)) ([], rng))

/-- RNG projection through validation, worker order creation, initialization and
warmup. The iteration callback models the combined worker dispatch and optimization,
including the random calls inside each. Serial execution does not give each job an
independent copy of the task RNG. -/
def prepareSerial (rt : SerialRuntime) (seed : Option Int) (cfg : SearchConfig)
    (outputs : Nat) (baseline : rt.Baseline) (incoming : RNG) :
    Jl (List (Nat × Nat) × (List (Nat → List Member) × List Hof) × List ((Nat × Nat) × Reply) × RNG) := do
  let rng := match seed with | some s => rt.seeded s | none => incoming
  let (storage, rng) := (createWorkers (m := StateM RNG) outputs cfg.populations cfg.iterations
    .serial (pure ([], false)) (fun _ => pure ()) (fun keys => rt.shuffle keys)).run rng
  let order := storage.1.taskOrder
  let (init, rng) ← rt.initializeSearch baseline rng
  if init.2.length ≠ outputs then throw (.errorException "DimensionMismatch")
  let (replies, rng) := serialWarmup rt baseline cfg.iterations outputs cfg.populations rng
  return (order, init, replies, rng)


/-- Serial head visits share the task RNG. A relaunch advances it exactly when
the selected population supplied a result and its output has another cycle. -/
def serialHeadLoop (rt : SerialRuntime) (baseline : rt.Baseline) (cfg : SearchConfig) (order : List (Nat × Nat))
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool) :
    List Observation → Nat → HeadState → RNG → Jl (HeadState × RNG)
  | observations, step, state, rng => do
    if state.stopped || decide ((state.outputs.map OutputState.remaining).sum = 0) then
      return (state, rng)
    match observations with
    | [] => throw (.undefinedBehavior "insufficient scheduler observations")
    | observation :: rest =>
      let (j, i) ← taskAt order step
      let out ← SymReg.Loss.at1 state.outputs (j + 1)
      let observation := { observation with ready := true }
      let next ← headStep cfg state (j, i) observation
        (fun j i g => (rt.reply baseline j i g rng).1) compute check
      let rng := if (out.cells i).running && decide (out.remaining > 1) && !observation.externalBeforeRelaunch
        then (rt.reply baseline j i ((out.cells i).collected + 1) rng).2 else rng
      serialHeadLoop rt baseline cfg order compute check rest (step + 1) next rng

/-- Search result over the model's task RNG. Clock, IO, external stop and plugin
effects must be provided identically to both runs; the seed cannot reset those. -/
def seededSerialSearch (rt : SerialRuntime) (seed : Int) (cfg : SearchConfig)
    (outputs : Nat) (incoming : RNG) (observations : List Observation)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool) : Jl SearchOutput := do
  validateOptions outputs cfg.dimOut cfg.populations cfg.progress cfg.verbosity
  let (baseline, afterBaseline) ← rt.beforeSeed incoming
  let (order, (initial, halls), replies, rng) ← prepareSerial rt (some seed) cfg outputs baseline afterBaseline
  let states := initial.zipIdx.map fun (pops, j) =>
    startOutput cfg.iterations cfg.populations pops (fun i _ =>
      (replies.find? (fun p => p.1 == (j, i))).map Prod.snd |>.getD (unitReply i 0))
  let (final, _) ← serialHeadLoop rt baseline cfg order compute check observations 0 ⟨states, halls, false, 0⟩ rng
  let pops := final.outputs.map fun out =>
    (List.range cfg.populations).map fun i => (out.cells i).lastPopulation
  formatOutput pops final.halls cfg.dimOut cfg.returnState

def seeded_serial_result : Prop := ∀ (rt : SerialRuntime) (seed : Int) (cfg : SearchConfig)
    (outputs : Nat) (left right : RNG) (observations : List Observation)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool)
    (baseline : rt.Baseline) (leftPreSeed rightPreSeed : RNG),
  rt.beforeSeed left = .ok (baseline, leftPreSeed) →
  rt.beforeSeed right = .ok (baseline, rightPreSeed) →
  seededSerialSearch rt seed cfg outputs left observations compute check =
    seededSerialSearch rt seed cfg outputs right observations compute check

open DynExpr.Registry in
def serialEntries : List Entry := [
  { id := "search-serial-seed-replay", juliaFile := "src/SymbolicRegression.jl",
    juliaFns := ["_validate_options", "_create_workers", "_warmup_search!", "_main_search_loop!"],
    statement := "In the serial search model, two runs that successfully reach the seed reset with the same persistent baseline state give equal results with the same seed and later inputs, regardless of the starting task RNG."
    preconditions := "Same external observations and service functions; baseline state agrees after the pre-seed effects."
    status := .todo, prop := ``seeded_serial_result
    notes := "Model now passes baseline state into stochastic services. Re-proof requires dispatch effects in source order, including migration before relaunch." }
]
end SymReg.Search
