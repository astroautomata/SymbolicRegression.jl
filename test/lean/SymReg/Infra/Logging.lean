import SymReg.HofMig.Core
import SymReg.Loss.Core
import Init.Data.Rat.Lemmas

namespace SymReg.Infra
open DynExpr
open SymReg.HofMig (Member Hof)

/-- SRLogger, get_logger and constructor forwarding, src/Logging.jl:42-57.
Counter arithmetic uses mathematical Int, before Julia machine-Int overflow. -/
structure Logger where
  underlying : Nat
  interval : Int := 100
  step : Int := 0
  counter : Nat := 0
  deriving DecidableEq, Repr

-- Source: src/Logging.jl:49-51
def getLogger (logger : Logger) : Nat := logger.underlying

-- Source: src/Logging.jl:52-54
def shouldLog (logger : Logger) : Bool :=
  decide (logger.interval > 0) && decide (logger.step % logger.interval = 0)

-- Source: src/Logging.jl:55-58
def incrementLogStep (logger : Logger) : Logger := { logger with step := logger.step + 1 }

inductive LogEffect where
  | payload
  | scope (logger : Nat)
  | info (logger : Nat) (message : String) (data : Nat)
  | writeStep (counter : Nat) (value : Int)
  deriving DecidableEq

-- Source: src/Logging.jl:60-62
-- function LG.with_logger(f::Function, logger::AbstractSRLogger)
--     return LG.with_logger(f, get_logger(logger))
-- end
def withLogger {α : Type} (logger : Logger) (setup : Nat → Jl Unit)
    (f : Unit → ReaderT Nat Jl α) : Jl α := do
  let id := getLogger logger
  setup id
  (f ()).run id

-- Source: src/Logging.jl:82-90
-- is_terminal = all(iszero, state.cycles_remaining)
-- if should_log(logger) || (logger.log_interval > 0 && is_terminal)
--     data = log_payload(logger, state, datasets, options)
--     LG.with_logger(logger) do
--         @info("search", data = data)
--     end
-- end
-- increment_log_step!(logger)
-- return nothing
def loggingCallback (logger : Logger) (cycles : List Int)
    (payload : Jl Nat) (setup : Nat → Jl Unit) (info : Nat → String → Nat → Jl Unit) :
    Jl Unit × Logger × List LogEffect :=
  let terminal := cycles.all (· == 0)
  let complete := fun effects =>
    let updated := incrementLogStep logger
    (.ok (), updated, effects ++ [.writeStep updated.counter updated.step])
  if shouldLog logger || (decide (logger.interval > 0) && terminal) then
    match payload with
    | .error e => (.error e, logger, [.payload])
    | .ok data =>
      let id := getLogger logger
      let prior : List LogEffect := [.payload, .scope id]
      let callback (_ : Unit) : ReaderT Nat Jl (Jl Unit × List LogEffect) :=
        fun active => .ok (info active "search" data, [.info active "search" data])
      match withLogger logger setup callback with
      | .error e => (.error e, logger, prior)
      | .ok (result, observed) =>
        match result with
        | .error e => (.error e, logger, prior ++ observed)
        | .ok () => complete (prior ++ observed)
  else complete []

private def scopeEffects (effects : List LogEffect) : List LogEffect :=
  effects.filter (fun e => match e with | .scope .. | .info .. => true | _ => false)

def loggerInterval : Prop := ∀ logger cycles data setup info,
  cycles.all (· == 0) = false →
  scopeEffects (loggingCallback logger cycles (.ok data) setup info).2.2 =
    if 0 < logger.interval ∧ logger.interval ∣ logger.step then
      match setup logger.underlying with
      | .error _ => [.scope logger.underlying]
      | .ok () => [.scope logger.underlying,.info logger.underlying "search" data]
    else []

theorem loggerInterval_holds : loggerInterval := by
  intro logger cycles data setup info h
  by_cases hp : 0 < logger.interval <;>
    by_cases hm : logger.step % logger.interval = 0 <;>
    cases hs : setup logger.underlying <;>
    cases hi : info logger.underlying "search" data <;>
    simp [loggingCallback, withLogger, scopeEffects, shouldLog, getLogger, h, hp, hm, hs, hi,
      Int.dvd_iff_emod_eq_zero, Bind.bind, Except.bind, ReaderT.run]

def loggerPeriodicity : Prop := ∀ logger,
  0 < logger.interval →
  shouldLog { logger with step := 0 } = true ∧
  (∀ step, 0 < step → step < logger.interval →
    shouldLog { logger with step } = false) ∧
  shouldLog { logger with step := logger.step + logger.interval } = shouldLog logger

theorem loggerPeriodicity_holds : loggerPeriodicity := by
  intro logger h
  refine ⟨by simp [shouldLog,h], ?_, by simp [shouldLog]⟩
  intro step hpos hlt
  have hm : step % logger.interval = step := Int.emod_eq_of_lt (by omega) hlt
  simp [shouldLog,h,hm,show step ≠ 0 by omega]

def loggerFirstTerminal : Prop := ∀ logger cycles data setup info,
  0 < logger.interval → (logger.step = 0 ∨ cycles.all (· == 0) = true) →
  scopeEffects (loggingCallback logger cycles (.ok data) setup info).2.2 =
    match setup logger.underlying with
    | .error _ => [.scope logger.underlying]
    | .ok () => [.scope logger.underlying,.info logger.underlying "search" data]

theorem loggerFirstTerminal_holds : loggerFirstTerminal := by
  intro logger cycles data setup info hp h
  rcases h with hz | ht <;>
    cases hs : setup logger.underlying <;>
    cases he : info logger.underlying "search" data <;>
    simp [loggingCallback, withLogger, scopeEffects, shouldLog, getLogger, *, Bind.bind,
      Except.bind, ReaderT.run]

def loggerDisabled : Prop := ∀ logger cycles payload setup info,
  logger.interval ≤ 0 →
  loggingCallback logger cycles payload setup info =
    (.ok (), { logger with step := logger.step + 1 },
      [.writeStep logger.counter (logger.step + 1)])

theorem loggerDisabled_holds : loggerDisabled := by
  intro logger cycles payload setup info h
  have hn : ¬ 0 < logger.interval := by omega
  simp [loggingCallback,shouldLog,hn,incrementLogStep]

def loggerForwarding : Prop := ∀ logger setup (f : Unit → ReaderT Nat Jl Nat),
  getLogger logger = logger.underlying ∧
  (∀ e, setup logger.underlying = .error e → withLogger logger setup f = .error e) ∧
  (setup logger.underlying = .ok () → withLogger logger setup f = (f ()).run logger.underlying) ∧
  (incrementLogStep logger).step = logger.step + 1 ∧
  (incrementLogStep logger).counter = logger.counter ∧
  (incrementLogStep logger).underlying = logger.underlying

theorem loggerForwarding_holds : loggerForwarding := by
  intro logger setup f
  refine ⟨rfl,?_,?_,rfl,rfl,rfl⟩
  · intro e h
    simp [withLogger,getLogger,h,Bind.bind,Except.bind]
  · intro h
    simp [withLogger,getLogger,h,Bind.bind,Except.bind]

example : (0 : Int) < 1 ∧ (0 : Int) ≤ 0 ∧ ([1] : List Int).all (· == 0) = false := by decide

/-- Typed contents of _log_scalars, src/Logging.jl:117-162. Tree rendering,
complexity and pareto_volume are supplied services; the front itself reuses HofMig. -/
structure ScalarPayload where
  populationComplexities : List Int
  minLoss : JF
  paretoVolume : JF
  equations : Int → Option (JF × String)

/-- Dict construction in src/Logging.jl:155-159: later repeated complexity keys
overwrite earlier equation values. -/
def equationDictionary (writes : List (Int × JF × String)) : Int → Option (JF × String) :=
  writes.foldl (fun d (key,loss,equation) =>
    fun k => if k = key then some (loss,equation) else d k) (fun _ => none)

-- Source: src/Logging.jl:125-159
-- out["population"] = Dict(["complexities" => let
--     complexities = Int[]
--     for pop in pops, member in pop.members
--         push!(complexities, compute_complexity(member, options))
--     end
--     complexities
-- end])
-- dominating = calculate_pareto_frontier(hall_of_fame)
-- trees = [member.tree for member in dominating]
-- losses = L[member.loss for member in dominating]
-- complexities = Int[compute_complexity(member, options) for member in dominating]
-- out["summaries"] = Dict([
--     "min_loss" => length(dominating) > 0 ? dominating[end].loss : L(Inf),
--     "pareto_volume" => pareto_volume(
--         losses, complexities, options.maxsize, options.loss_scale == :linear
--     ),
-- ])
-- out["equations"] = let
--     equations = String[
--         string_tree(member.tree, options; variable_names=dataset.variable_names) for
--         member in dominating
--     ]
--     Dict([
--         "complexity=" * string(complexities[i_eqn]) =>
--             Dict("loss" => losses[i_eqn], "equation" => equations[i_eqn]) for
--         i_eqn in eachindex(complexities, losses, equations)
--     ])
-- end
def logScalars {S : Type} (pops : List (List Member)) (hall : Hof) (fresh : Nat)
    (complexity : Member → ExceptT JlError (StateM S) Int)
    (render : Member → Jl String) (convertLoss : JF → Jl JF)
    (volume : List JF → List Int → Jl JF) : ExceptT JlError (StateM S) ScalarPayload := do
  let popSizes ← pops.flatten.mapM complexity
  let front := (SymReg.HofMig.calculatePareto hall fresh).1
  let losses := front.map Member.loss
  let sizes ← front.mapM complexity
  let minLoss ← ExceptT.mk fun s =>
    (match front.getLast? with | none => convertLoss .posInf | some m => .ok m.loss, s)
  let area ← ExceptT.mk fun s => (volume losses sizes, s)
  let equations ← ExceptT.mk fun s => (front.mapM render, s)
  pure ⟨popSizes, minLoss, area,
    equationDictionary (sizes.zip (losses.zip equations))⟩

/-- log_payload's single-output flattening versus output<i> nesting,
src/Logging.jl:93-115. Empty datasets yield no per-output keys. num_evals is always
an outer key and is the sum of the full evaluation array. -/
structure LogPayload where
  single : Option ScalarPayload
  outputs : List (String × ScalarPayload)
  numEvals : JF

-- Source: src/Logging.jl:99-114; src/SearchUtils.jl:895
-- d = Ref(Dict{String,Any}())
-- for i in eachindex(datasets, state.halls_of_fame)
--     out = _log_scalars(;
--         pops=state.last_pops[i], hall_of_fame=state.halls_of_fame[i],
--         dataset=datasets[i], options,
--     )
--     if length(datasets) == 1
--         d[] = out
--     else
--         d[]["output$(i)"] = out
--     end
-- end
-- d[]["num_evals"] = sum(sum, state.num_evals)
-- return d[]
def logPayload (outputs : List ScalarPayload) (evaluations : List (List JF)) : LogPayload :=
  let sum64 := SymReg.Loss.pairwiseSum .float64
  ⟨if outputs.length = 1 then outputs.head? else none,
    if outputs.length = 1 then [] else (outputs.zipIdx 1).map
      (fun (v,i) => ("output" ++ toString i,v)),
    sum64 (evaluations.map sum64)⟩

def loggerPayloadShape : Prop := ∀ outputs evaluations,
  let result := logPayload outputs evaluations
  (∀ out, outputs = [out] → result.single = some out ∧ result.outputs = []) ∧
  (outputs.length ≠ 1 → result.single = none ∧
    result.outputs.length = outputs.length ∧
    ∀ i out, outputs[i]? = some out →
      result.outputs[i]? = some ("output" ++ toString (i + 1),out)) ∧
  result.numEvals = SymReg.Loss.pairwiseSum .float64
    (evaluations.map (SymReg.Loss.pairwiseSum .float64))

private def observedComplexity (size : Member → Int) (m : Member) :
    ExceptT JlError (StateM (List (Nat × Int))) Int :=
  ExceptT.mk fun writes => (.ok (size m), writes ++ [(m.objectId, size m)])

def loggerScalarContents : Prop := ∀ pops hall fresh (size : Member → Int)
    (render : Member → String) convertLoss volume,
  let front := (SymReg.HofMig.calculatePareto hall fresh).1
  let observed := ((logScalars pops hall fresh (observedComplexity size)
    (fun m => .ok (render m)) convertLoss volume).run [])
  observed.2 = (pops.flatten ++ front).map (fun m => (m.objectId,size m)) ∧
  (front = [] → ∀ e, convertLoss .posInf = .error e → observed.1 = .error e) ∧
  ∀ out, observed.1 = .ok out →
    out.populationComplexities = pops.flatten.map size ∧
    (∀ key, out.equations key =
      ((front.filter (fun m => size m == key)).getLast?).map
        (fun (m : Member) => (m.loss, render m)))

/-- Finite geometric points reuse Rat arithmetic. Nonfinite log results, finite
rounding and overflow are outside these finite-geometry claims. -/
abbrev Point := Rat × Rat

/-- isleftof's strict orientation determinant, src/Logging.jl:208-212. -/
def orientation (p start finish : Point) : Rat :=
  (finish.1-start.1)*(p.2-start.2) - (finish.2-start.2)*(p.1-start.1)

def isLeftOf (p start finish : Point) : Bool := decide (orientation p start finish > 0)

/-- Gift-wrapping inner scan, src/Logging.jl:194-199. -/
def hullEndpoint (points : List Point) (current initial : Point) : Point :=
  points.foldl (fun endpoint candidate =>
    if endpoint = current || isLeftOf candidate current endpoint then candidate else endpoint) initial

/-- An execution certificate for the while loop, src/Logging.jl:188-206.
`start` is selected by stable minimum-x sorting, supplied separately. No artificial
fuel is added to the source semantics. The certificate exists exactly for a
terminating execution that closes at start. -/
inductive HullRun (points : List Point) (first start : Point) : Point → List Point → Prop where
  | close (current : Point) (h : hullEndpoint points current first = start) :
      HullRun points first start current [current]
  | next (current endpoint : Point) (rest : List Point)
      (h : hullEndpoint points current first = endpoint) (ne : endpoint ≠ start)
      (tail : HullRun points first start endpoint rest) :
      HullRun points first start current (current :: rest)

/-- Shoelace loop with final-to-first closing edge, src/Logging.jl:215-222. -/
def edgeCross (a b : Point) : Rat := a.1*b.2-b.1*a.2

def crossSum (first : Point) : List Point → Rat
  | [] => 0
  | [last] => edgeCross last first
  | a :: b :: rest => edgeCross a b + crossSum first (b :: rest)

def hullArea (hull : List Point) : Rat :=
  match hull with
  | [] => 0
  | first :: rest => (crossSum first (first :: rest)).abs / 2

abbrev FloatPoint := JF × JF

-- Source: src/Logging.jl:167-184
-- if length(losses) == 0
--     return 0.0
-- end
-- y = use_linear_scaling ? copy(losses) : @.(log10(losses + eps(L)))
-- x = @. log10(complexities)
-- push!(y, minimum(y))
-- push!(x, log10(maxsize + 1))
-- push!(y, maximum(y))
-- push!(x, maximum(x))
-- xy = cat(x, y; dims=2)
-- hull = convex_hull(xy)
-- return Float64(convex_hull_area(hull))
def paretoVolume (losses : List JF) (complexities : List Int) (maxsize : Int)
    (linear : Bool) (p : SymReg.Loss.LossPrecision)
    (logLoss : JF → Jl JF) (logSize : Int → Jl JF) (epsilon : JF)
    (minimum maximum : List JF → JF) (geometry : List FloatPoint → Jl JF) :
    Jl JF × List (List FloatPoint) :=
  match losses with
  | [] => (.ok (.fin 0), [])
  | _ :: _ =>
    let preprocessed : Jl (List FloatPoint) := do
      let y ← if linear then pure losses else losses.mapM (fun l => logLoss (p.round (l + epsilon)))
      let x ← complexities.mapM logSize
      let y' := y ++ [minimum y]
      let largest ← logSize (maxsize + 1)
      let x' := x ++ [largest]
      let top := maximum y'
      let right := maximum x'
      if x'.length != y'.length then throw (.dimensionMismatch "incompatible cat dimensions")
      pure ((x' ++ [right]).zip (y' ++ [top]))
    match preprocessed with
    | .error e => (.error e, [])
    | .ok points =>
      ((geometry points).map (SymReg.Loss.LossPrecision.round .float64), [points])

private def geometryOrientationContract : Prop := ∀ p start finish,
  isLeftOf p start finish = decide (
    (finish.1-start.1)*(p.2-start.2) - (finish.2-start.2)*(p.1-start.1) > 0)

private theorem geometryOrientationContract_holds : geometryOrientationContract := by intro p start finish; rfl

private def geometryOrientationLaw : Prop := ∀ p start finish (dx dy : Rat),
  isLeftOf (p.1 + dx, p.2 + dy) (start.1 + dx, start.2 + dy)
    (finish.1 + dx, finish.2 + dy) = isLeftOf p start finish

private theorem geometryOrientationLaw_holds : geometryOrientationLaw := by
  intro p start finish dx dy
  have cancel (x y z : Rat) : (x + z) - (y + z) = x - y := by
    grind [Rat.sub_def, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  simp [isLeftOf, orientation, cancel]

def geometryOrientation : Prop := geometryOrientationContract ∧ geometryOrientationLaw

theorem geometryOrientation_holds : geometryOrientation := ⟨geometryOrientationContract_holds, geometryOrientationLaw_holds⟩

def hullAreaNonnegative : Prop :=
  hullArea [] = 0 ∧ ∀ (first : Point) (rest : List Point),
    let hull := first :: rest
    hullArea hull = ((hull.zip (rest ++ [first])).map
      (fun pair : Point × Point => pair.1.1 * pair.2.2 - pair.2.1 * pair.1.2)).sum.abs / 2 ∧
    0 ≤ hullArea hull

private theorem crossSum_zip (first a : Point) (rest : List Point) :
    crossSum first (a :: rest) =
      (((a :: rest).zip (rest ++ [first])).map (fun (a,b) => edgeCross a b)).sum := by
  induction rest generalizing a with
  | nil => simp [crossSum, Rat.add_zero]
  | cons b rest ih => simp [crossSum, ih b]

theorem hullAreaNonnegative_holds : hullAreaNonnegative := by
  refine ⟨rfl, ?_⟩
  intro first rest
  constructor
  · rw [hullArea, crossSum_zip]
    rfl
  · simp only [hullArea]
    rw [Rat.div_def]
    exact Rat.mul_nonneg Rat.abs_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (by decide)))

private theorem foldEndpoint_mem (points xs : List Point) (current initial : Point)
    (hi : initial ∈ points) (hx : ∀ x ∈ xs, x ∈ points) :
    xs.foldl (fun endpoint candidate =>
      if endpoint = current || isLeftOf candidate current endpoint then candidate else endpoint) initial ∈ points := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons x xs ih =>
    apply ih
    · dsimp
      split
      · exact hx x (by simp)
      · exact hi
    · intro y hy; exact hx y (by simp [hy])

private theorem hullEndpoint_mem (points : List Point) (current initial : Point)
    (h : initial ∈ points) : hullEndpoint points current initial ∈ points :=
  foldEndpoint_mem points points current initial h (fun _ hx => hx)

def hullVerticesInput : Prop := ∀ points first start current hull,
  first ∈ points → current ∈ points → HullRun points first start current hull →
  ∀ vertex ∈ hull, vertex ∈ points

theorem hullVerticesInput_holds : hullVerticesInput := by
  intro points first start current hull hf hc run
  induction run with
  | close c h => simpa using hc
  | next c endpoint rest h ne tail ih =>
    have he : endpoint ∈ points := h ▸ hullEndpoint_mem points c first hf
    intro vertex hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hc
    · exact ih he vertex hv
example : ((0,0) : Point) ∈ ([(0,0)] : List Point) ∧
    HullRun [(0,0)] (0,0) (0,0) (0,0) [(0,0)] := by
  exact ⟨by simp, .close _ (by decide)⟩

def volumeEmptyAndShape : Prop :=
  (∀ sizes maxsize linear p logLoss logSize eps minimum maximum geometry,
    paretoVolume [] sizes maxsize linear p logLoss logSize eps minimum maximum geometry =
      (.ok (.fin 0), [])) ∧
  ∀ losses sizes maxsize linear p logLoss logSize eps minimum maximum geometry x y largest,
    losses ≠ [] → losses.length = sizes.length →
    (if linear then .ok losses else losses.mapM (fun l => logLoss (p.round (l + eps)))) = .ok y →
    sizes.mapM logSize = .ok x → logSize (maxsize + 1) = .ok largest →
    let expected := x.zip y ++
      [(largest,minimum y), (maximum (x ++ [largest]),maximum (y ++ [minimum y]))]
    (paretoVolume losses sizes maxsize linear p logLoss logSize eps minimum maximum geometry).2 =
      [expected]

end SymReg.Infra
