import SymReg.Search.Utilities

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

-- Source: src/SymbolicRegression.jl:719-727
-- example_dataset = first(datasets)
-- nout = length(datasets)
-- @assert nout >= 1
-- @assert (nout == 1 || ropt.dim_out == 2)
-- @assert options.populations >= 1
-- if ropt.progress
--     @assert(nout == 1, "You cannot display a progress bar for multi-output searches.")
--     @assert(ropt.verbosity > 0, "You cannot display a progress bar with `verbosity=0`.")
-- end
def validateOptions (outputs dimOut : Nat) (populations : Int) (progress : Bool)
    (verbosity : Int) : Jl Unit :=
  if outputs = 0 then .error .boundsError
  else if ¬ (outputs = 1 ∨ dimOut = 2) then .error (.assertionError "dim_out")
  else if populations < 1 then .error (.assertionError "populations")
  else if progress && decide (outputs ≠ 1) then
    .error (.assertionError "You cannot display a progress bar for multi-output searches.")
  else if progress && decide (verbosity ≤ 0) then
    .error (.assertionError "You cannot display a progress bar with `verbosity=0`.")
  else .ok ()

-- Source: src/SymbolicRegression.jl:719-744.
-- if options.node_type <: GraphNode && ropt.verbosity > 0
--     @warn "The `GraphNode` interface and mutation operators are experimental and will change in future versions."
-- end
-- if ropt.runtests
--     test_option_configuration(ropt.parallelism, datasets, options, ropt.verbosity)
--     test_dataset_configuration(example_dataset, options, ropt.verbosity)
-- end
-- for dataset in datasets
--     update_baseline_loss!(dataset, options)
-- end
-- if options.define_helper_functions
--     set_default_variable_names!(first(datasets).variable_names)
-- end
-- if options.seed !== nothing
--     seed!(options.seed)
-- end
-- return nothing
def validateSearchWith {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {D : Type}
    (datasets : List D) (dimOut : Nat) (populations : Int) (progress graphNode runtests helpers : Bool)
    (verbosity : Int) (seed : Option Int)
    (warn : m Unit) (checkOptions : List D → m Unit)
    (checkDataset updateBaseline setNames : D → m Unit) (seedRNG : Int → m Unit) : m Unit := do
  let first ← match datasets with
    | [] => throw .boundsError
    | d :: _ => pure d
  match validateOptions datasets.length dimOut populations progress verbosity with
  | .error e => throw e
  | .ok () => pure ()
  if graphNode && decide (0 < verbosity) then warn
  if runtests then
    checkOptions datasets
    checkDataset first
  datasets.forM updateBaseline
  if helpers then setNames first
  if let some value := seed then seedRNG value

/-- Each Julia channel is separately allocated, even if both start empty. The
allocation site and its coordinates identify it within one search state. -/
structure WorkerChannel where
  address : Nat × Nat
  capacity : Nat
  queue : List Reply
  deriving DecidableEq, Repr

structure WorkerStorage where
  channels : List (List WorkerChannel)
  taskOrder : List (Nat × Nat)
  evaluations : List (List JF)
  cyclesRemaining : List Nat
  procs : List Nat
  createdProcs : Bool
  deriving DecidableEq, Repr

-- Source: src/SymbolicRegression.jl:801-825.
-- (procs, we_created_procs) = if ropt.parallelism == :multiprocessing
--     configure_workers(...)
-- else
--     Int[], false
-- end
-- worker_inputs = if ropt.parallelism == :multiprocessing
--     store_on_workers((datasets, options), procs)
-- else
--     nothing
-- end
def prepareWorkerInputs {m : Type → Type} [Monad m] {α : Type}
    (mode : Parallelism) (configure : m (List Nat × Bool))
    (storeInputs : List Nat → m α) : m (List Nat × Bool × Option α) := do
  let (procs, owned) ← if mode = .multiprocessing then configure else pure ([], false)
  let inputs ← if mode = .multiprocessing then some <$> storeInputs procs else pure none
  pure (procs, owned, inputs)

-- Source: src/SymbolicRegression.jl:795-845.
-- channels = [[Channel(1) for i in 1:(options.populations)] for j in 1:nout]
-- task_order = [(j, i) for j in 1:nout for i in 1:(options.populations)]
-- shuffle!(task_order)
-- num_evals = [[0.0 for i in 1:(options.populations)] for j in 1:nout]
-- total_cycles = ropt.niterations * options.populations
-- cycles_remaining = [total_cycles for j in 1:nout]
def createWorkers {m : Type → Type} [Monad m] {A : Type}
    (outputs populations iterations : Nat) (mode : Parallelism)
    (configure : m (List Nat × Bool)) (store : List Nat → m A)
    (shuffle : List (Nat × Nat) → m (List (Nat × Nat))) :
    m (WorkerStorage × Option A) := do
  let channels := (List.range outputs).map fun j =>
    (List.range populations).map fun i => (⟨(j, i), 1, []⟩ : WorkerChannel)
  let (procs, owned, inputs) ← prepareWorkerInputs mode configure store
  let order ← shuffle ((List.range outputs).flatMap fun j => (List.range populations).map (j, ·))
  return (⟨channels, order, List.replicate outputs (List.replicate populations (.fin 0)),
    List.replicate outputs (iterations * populations), procs, owned⟩, inputs)

structure PopulationMatrix where
  outputs : Nat
  populations : Nat
  columns : List (List Member)
  size_eq : columns.length = outputs * populations
  deriving DecidableEq, Repr

inductive PopulationStorage where
  | vectors (pops : List (List (List Member)))
  | matrix (values : PopulationMatrix)
  deriving DecidableEq, Repr

-- Source: src/SearchUtils.jl:832-839.
-- function get_population(
--     pops::Vector{Vector{P}}; out::Int, pop::Int
-- )::P where {P<:Population}
--     return pops[out][pop]
-- end
-- function get_population(pops::Matrix{P}; out::Int, pop::Int)::P where {P<:Population}
--     return pops[out, pop]
-- end
def getPopulation (storage : PopulationStorage) (out pop : Nat) : Jl (List Member) := do
  match storage with
  | .vectors rows =>
    let row ← SymReg.Loss.at1 rows (out + 1)
    SymReg.Loss.at1 row (pop + 1)
  | .matrix matrix =>
    if out < matrix.outputs ∧ pop < matrix.populations then
      SymReg.Loss.at1 matrix.columns (out + matrix.outputs * pop + 1)
    else .error .boundsError

inductive HallOutput where
  | scalar (hall : Hof)
  | vector (halls : List Hof)
  deriving DecidableEq, Repr

structure SavedState where
  populations : PopulationStorage
  halls : HallOutput
  deriving DecidableEq, Repr

/-- `_format_output`, `src/SymbolicRegression.jl:1386-1396`.
`embed` has already been applied to each population/hall by its expression implementation. -/
inductive SearchOutput where
  | halls (output : HallOutput)
  | state (saved : SavedState)
  deriving DecidableEq, Repr

def formatOutput (pops : List (List (List Member))) (halls : List Hof)
    (dimOut : Nat) (returnState : Bool) : Jl SearchOutput := do
  let output ← if dimOut = 1 then
    match halls with
    | [hall] => .ok (HallOutput.scalar hall)
    | _ => .error (.argumentError "only")
  else .ok (HallOutput.vector halls)
  pure (if returnState then .state ⟨.vectors pops, output⟩ else .halls output)

-- Source: src/HallOfFame.jl:111-115; src/SearchUtils.jl:821-830.
-- function Base.copy(hof::HallOfFame)
--     return HallOfFame(
--         [copy(member) for member in hof.members], [exists for exists in hof.exists]
--     )
-- end
-- function load_saved_hall_of_fame(saved_state)
--     hall_of_fame = saved_state[2]
--     hall_of_fame = if isa(hall_of_fame, HallOfFame)
--         [hall_of_fame]
--     else
--         hall_of_fame
--     end
--     return [copy(hof) for hof in hall_of_fame]
-- end
-- load_saved_hall_of_fame(::Nothing)::Nothing = nothing
structure HallCopy where
  /-- HallOfFame is immutable and is identified by these two vector references. -/
  membersId : Nat
  occupancyId : Nat
  hall : Hof
  deriving DecidableEq, Repr

def copyHalls : List Hof → Nat → List HallCopy × Nat
  | [], fresh => ([], fresh)
  | h :: hs, fresh =>
    let copied := copyHof h (fresh + 2)
    let rest := copyHalls hs copied.2
    (⟨fresh, fresh + 1, copied.1⟩ :: rest.1, rest.2)

def HallOutput.asList : HallOutput → List Hof
  | .scalar hall => [hall]
  | .vector halls => halls

def loadHalls (saved : Option SavedState) (fresh : Nat) : Option (List HallCopy × Nat) :=
  saved.map fun s => copyHalls s.halls.asList fresh

-- Source: src/Population.jl:147-153.
-- function Base.copy(pop::P)::P where {T,L,N,PM,P<:Population{T,L,N,PM}}
--     copied_members = Vector{PM}(undef, pop.n)
--     for i in 1:(pop.n)
--         copied_members[i] = copy(pop.members[i])
--     end
--     return Population(copied_members)
-- end
structure PopulationCopy where
  vectorId : Nat
  members : List Member
  next : Nat
  deriving DecidableEq, Repr

def copyPopulation (members : List Member) (next : Nat) : PopulationCopy :=
  let (members', next') := copyMembers members (next + 1)
  ⟨next, members', next'⟩

-- Source: src/SearchUtils.jl:840-844.
-- function load_saved_population(saved_state; out::Int, pop::Int)
--     saved_pop = get_population(saved_state[1]; out=out, pop=pop)
--     return copy(saved_pop)
-- end
-- load_saved_population(::Nothing; kws...) = nothing
def loadPopulation (saved : Option SavedState) (out pop fresh : Nat) : Jl (Option PopulationCopy) :=
  match saved with
  | none => .ok none
  | some s => (getPopulation s.populations out pop).map (fun ms => some (copyPopulation ms fresh))

-- Source: src/SymbolicRegression.jl:894-910.
-- init_hall_of_fame = load_saved_hall_of_fame(saved_state)
-- if init_hall_of_fame === nothing
--     for j in 1:nout
--         state.halls_of_fame[j] = HallOfFame(options, datasets[j])
--     end
-- else
--     # Recompute losses for the hall of fame, in
--     # case the dataset changed:
--     for j in eachindex(init_hall_of_fame, datasets, state.halls_of_fame)
--         hof = strip_metadata(init_hall_of_fame[j], options, datasets[j])
--         for member in hof.members[hof.exists]
--             cost, result_loss = eval_cost(datasets[j], member, options)
--             member.cost = cost
--             member.loss = result_loss
--         end
--         state.halls_of_fame[j] = hof
--     end
-- end
def initializeHalls {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {D O : Type}
    (saved : Option (List Hof)) (datasets : List D) (options : O)
    (newHall : O → D → m Hof) (strip : Hof → O → D → m Hof)
    (score : D → Member → O → m (JF × JF)) : m (List Hof) := do
  match saved with
  | none => datasets.mapM (newHall options)
  | some hs =>
    if hs.length ≠ datasets.length then throw (.errorException "DimensionMismatch")
    else (hs.zip datasets).mapM fun (h, dataset) => do
      let hof ← strip h options dataset
      let slots ← hof.slots.mapM fun slot => do
        if slot.exists then
          let (cost, loss) ← score dataset slot.member options
          pure { slot with member := { slot.member with cost := cost, loss := loss } }
        else pure slot
      pure { hof with slots }

/-- Stock `Options` has an immutable `Int` field. Only a documented custom
`AbstractOptions` implementation dispatches to an accessor (src/OptionsStruct.jl:126-177,227). -/
inductive PopulationSize (m : Type → Type) where
  | stock (value : Int)
  | custom (getProperty : m Int)

def PopulationSize.read {m : Type → Type} [Monad m] : PopulationSize m → m Int
  | .stock value => pure value
  | .custom getProperty => getProperty

-- Source: src/SymbolicRegression.jl:932-976 (project the worker reply to population and evaluations).
-- if saved_pop !== nothing && length(saved_pop.members) == options.population_size
--     _saved_pop = strip_metadata(saved_pop, options, _dataset)
--     ## Update losses:
--     for member in _saved_pop.members
--         cost, result_loss = eval_cost(_dataset, member, options)
--         member.cost = cost
--         member.loss = result_loss
--     end
--     copy_pop = copy(_saved_pop)
--     (datasets, options) -> (
--         copy_pop,
--         HallOfFame(options, datasets[j]),
--         new_trace(options),
--         0.0,
--         _worker_plugin_states,
--     )
-- else
--     if saved_pop !== nothing && ropt.verbosity > 0
--         @warn "Recreating population (output=$(j), population=$(i)), as the saved one doesn't have the correct number of members."
--     end
--     (datasets, options) -> (
--         Population(
--             datasets[j];
--             population_size=options.population_size,
--             nlength=3,
--             options=options,
--             nfeatures=max_features(datasets[j], options),
--             plugin_states=_plugin_states,
--         ),
--         HallOfFame(options, datasets[j]),
--         new_trace(options),
--         Float64(options.population_size),
--         _worker_plugin_states,
--     )
-- end
def initializePopulation {m : Type → Type} [Monad m] {D O S : Type}
    (saved : Option PopulationCopy) (headSize workerSize : PopulationSize m) (verbosity : Int)
    (dataset workerDataset : D) (options workerOptions : O) (plugins : S)
    (warn : m Unit) (maxFeatures : D → O → m Int)
    (generate : D → Int → Nat → O → Int → S → m PopulationCopy)
    (newHall : O → D → m Hof) (newTrace : O → m (Option Nat))
    (strip : PopulationCopy → O → D → m PopulationCopy)
    (score : D → Member → O → m (JF × JF)) : m (PopulationCopy × JF) := do
  if let some pop := saved then
    let expected ← headSize.read
    if (pop.members.length : Int) = expected then
      let stripped ← strip pop options dataset
      let ms ← stripped.members.mapM fun member => do
        let (cost, loss) ← score dataset member options
        pure { member with cost := cost, loss := loss }
      let copied := copyPopulation ms stripped.next
      let _ ← newHall workerOptions workerDataset
      let _ ← newTrace workerOptions
      return (copied, .fin 0)
    if verbosity > 0 then warn
  let size ← workerSize.read
  let features ← maxFeatures workerDataset workerOptions
  let pop ← generate workerDataset size 3 workerOptions features plugins
  let _ ← newHall workerOptions workerDataset
  let _ ← newTrace workerOptions
  let reported ← workerSize.read
  return (pop, SymReg.Loss.LossPrecision.round .float64 (.fin (reported : Rat)))

/-- `_preserve_loaded_state!`, `_warmup_search!`, `src/SymbolicRegression.jl:986-1018`.
Warmup extracts initialization reports without adding their evaluation field. -/
def preserveLoaded (initialized : List (List Reply)) : List (List (List Member)) :=
  initialized.map (List.map Reply.population)

def warmupZero (initialized : List (List Reply)) :
    List (List (List Member)) × List (List JF) :=
  (preserveLoaded initialized, initialized.map (fun row => row.map (fun _ => .fin 0)))

/-- Per-output merge in `src/SymbolicRegression.jl:1156-1162`. Other output halls are
untouched; all constraint/cache/NaN/tie semantics come from the existing hall model. -/
def mergeResult (h : Hof) (reply : Reply) (maxsize fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool) :
    Jl (Hof × List Member × Nat) := do
  let (afterPop, _, supply) ← updateManyChecked h reply.population maxsize fresh compute check
  updateManyChecked afterPop ((reply.bestSeen.slots.filter Slot.exists).map Slot.member)
    maxsize supply compute check

/-- `construct_datasets`, `src/SearchUtils.jl:1031-1073` extends the existing loss dataset
projection with names, units and extra information. X columns are shared across outputs. -/
structure SearchDataset where
  data : SymReg.Loss.Basic
  index : Nat
  variableNames : Option (List String)
  displayNames : Option (List String)
  targetName : String
  xUnits : Option (List String)
  yUnits : Option String
  extra : Nat

inductive TargetNames where
  | automatic | scalar (name : String) | vector (names : List String)
  deriving DecidableEq, Repr

inductive TargetUnits where
  | scalar (unit : Option String) | vector (units : List (Option String))
  deriving DecidableEq, Repr

/-- Digit conversion used by `subscriptify`, `src/Utils.jl:42-45`. -/
def subscript (n : Nat) : String :=
  String.ofList (n.repr.toList.map fun c => match c with
    | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
    | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉' | c => c)

def targetName (names : TargetNames) (variables : Option (List String))
    (outputs j : Nat) : Jl String :=
  match names with
  | .scalar s => .ok s
  | .vector ss => SymReg.Loss.at1 ss (j + 1)
  | .automatic => .ok (if outputs > 1 then "y" ++ subscript (j + 1)
      else if (variables.getD []).contains "y" then "target" else "y")

def targetUnit (units : TargetUnits) (j : Nat) : Jl (Option String) :=
  match units with
  | .scalar u => .ok u
  | .vector us => SymReg.Loss.at1 us (j + 1)

def constructDatasets (columns targets : List (List JF))
    (weights : Option (List (List JF))) (variables display : Option (List String))
    (names : TargetNames) (xUnits : Option (List String)) (units : TargetUnits)
    (extra : Nat) : Jl (List SearchDataset) :=
  targets.zipIdx.mapM fun (y, j) => do
    let w ← match weights with
      | none => .ok none
      | some ws => (SymReg.Loss.at1 ws (j + 1)).map some
    let name ← targetName names variables targets.length j
    let unit ← targetUnit units j
    pure {
      data := {
        columns := columns
        y := some y
        weights := w
        xUnits := xUnits.isSome
        yUnits := unit.isSome }
      index := j + 1
      variableNames := variables
      displayNames := display
      targetName := name
      xUnits := xUnits
      yUnits := unit
      extra := extra }

/-- Matrix-interface weight length assertion and column-major reshape,
`src/SymbolicRegression.jl:623-626`. Each target is one output row. -/
def reshapeWeights (outputs samples : Nat) (flat : List JF) : Jl (List (List JF)) :=
  if flat.length ≠ outputs * samples then .error (.assertionError "weights length")
  else (List.range outputs).mapM fun j =>
    (List.range samples).mapM fun k => SymReg.Loss.at1 flat (j + k * outputs + 1)

/-- Final save precedes the verbosity return, `src/SymbolicRegression.jl:1448-1458`. -/
def infoDump (outputs : Nat) (save : Bool) (verbosity : Int) : List Nat × Bool :=
  (if save then List.range outputs else [], decide (verbosity > 0))

/-- File naming and two writes, `src/SearchUtils.jl:914-960`.
Rendering expressions and filesystem effects are arbitrary supplied services. -/
def saveFileNames (outputs j : Nat) : List String :=
  let name := if outputs > 1 then "hall_of_fame_output" ++ (j + 1).repr ++ ".csv"
    else "hall_of_fame.csv"
  [name, name ++ ".bak"]

structure FrontierCache where
  entries : List (Nat × JF × JF × Int)
  saved : Bool
  deriving DecidableEq, Repr

/-- Each entry records the hall's object identity, cost, loss and complexity;
`src/SearchUtils.jl:963-1007`. JF structural equality models `isequal` (including NaN). -/
def saveFrontier (cache : FrontierCache) (entries : List (Nat × JF × JF × Int)) :
    Bool × FrontierCache :=
  if !cache.saved || cache.entries != entries then (true, ⟨entries, true⟩) else (false, cache)

/-- Guess shape rules, `src/SearchUtils.jl:1177-1192`. -/
inductive Guesses (α : Type) where
  | flat (values : List α) | nested (values : List (List α))

def normalizeGuesses {α : Type} (g : Guesses α) (outputs : Nat) : Jl (List (List α)) :=
  match g with
  | .flat gs => if outputs = 1 then .ok [gs]
      else .error (.argumentError "guesses must be a vector of vectors")
  | .nested gs => if gs.length = outputs then .ok gs else .error (.assertionError "guesses")

/-- `_parse_guess_expression`, `parse_guesses`, `_parse_guesses_impl`,
`src/SearchUtils.jl:1075-1175`. Expression parsing, type inference, metadata stripping and
constant optimization are supplied services; oversized seeds are warned about and retained. -/
def parseGuessLists {α : Type} (guesses : Guesses α) (outputs maxsize : Nat)
    (parse : Nat → α → Jl Member) (optimize strip : Member → Member)
    (shouldOptimize : Bool) : Jl (List (List (Member × Bool))) := do
  let lists ← normalizeGuesses guesses outputs
  lists.zipIdx.mapM fun (gs, j) => gs.mapM fun g => do
    let member ← parse j g
    let member := strip (if shouldOptimize then optimize member else member)
    pure (member, decide (member.complexity > maxsize))

/-- Template-guess guard, `src/SearchUtils.jl:1085-1099`.
Regex word matching and active function-key membership are supplied Bool inputs. -/
def templateGuessAllowed (activeNameMatches : List Bool) : Jl Unit :=
  if activeNameMatches.any id then .error (.argumentError "use placeholders") else .ok ()

/-- Transport projection of `src/SearchUtils.jl:306-362,385-410`.
Byte serialization details and scheduling are external; the payload and thrown result are exact. -/
structure Encoded (α : Type) where
  value : α

def serializeBytes {α : Type} (a : α) : Encoded α := ⟨a⟩
def deserializeBytes {α : Type} (a : Encoded α) : α := a.value

def runEncoded {α : Type} (f : Encoded (Unit → α)) : Encoded α :=
  serializeBytes (deserializeBytes f ())

def spawnEncoded {α : Type} (f : Unit → α) (_worker latency : Nat) : Nat × α :=
  (latency, deserializeBytes (runEncoded (serializeBytes f)))

def spawnJob {α β : Type} (mode : Parallelism) (f : α → β) (inputs : Encoded α)
    (worker latency : Nat) : Nat × β :=
  if mode = .serial then (0, f (deserializeBytes inputs))
  else spawnEncoded (fun _ => f (deserializeBytes inputs)) worker latency

structure WorkerStore (α : Type) where
  next : Nat
  copies : Nat → Nat → Option α

/-- Atomic key allocation and ordered put/delete, `src/SearchUtils.jl:326-362`.
The counter is natural while UInt64 has not wrapped. -/
def storeOnWorkers {α : Type} (s : WorkerStore α) (value : α) (workers : List Nat) :
    Nat × WorkerStore α :=
  (s.next, {
    next := s.next + 1
    copies := fun w k => if w ∈ workers ∧ k = s.next then some value else s.copies w k })

def deleteOnWorkers {α : Type} (s : WorkerStore α) (key : Nat) (workers : List Nat) : WorkerStore α :=
  { s with copies := fun w k => if w ∈ workers ∧ k = key then none else s.copies w k }

/-- Runtime option normalization, `src/SearchUtils.jl:142-267`.
The environment's parsed timeout, available memory and generated run id are inputs. -/
structure RuntimeInput where
  mode : String := "multithreading"
  iterations : Int := 10
  outputs : Nat := 1
  numprocs : Option Nat := none
  procs : Option (List Nat) := none
  returnState : Option Bool := none
  valReturnState : Option Bool := none
  optionReturnState : Option Bool := none
  verbosity : Option Int := none
  optionVerbosity : Option Int := none
  progress : Option Bool := none
  optionProgress : Option Bool := none
  dimOut : Option Nat := none
  workerTimeout : Option Nat := none
  environmentTimeout : Option Nat := none
  runId : Option String := none

structure Runtime where
  mode : Parallelism
  iterations : Int
  numprocs : Nat
  returnState : Bool
  verbosity : Int
  progress : Bool
  dimOut : Nat
  workerTimeout : Nat
  runId : String
  deriving DecidableEq, Repr

def parseParallelism (name : String) : Jl Parallelism :=
  if name = "serial" then .ok .serial
  else if name = "multithreading" then .ok .multithreading
  else if name = "multiprocessing" then .ok .multiprocessing
  else .error (.errorException "Invalid parallelism mode")

def runtimeOptions (input : RuntimeInput) (generatedRunId : String) : Jl Runtime := do
  let mode ← parseParallelism input.mode
  if mode ≠ .multiprocessing ∧ (input.numprocs.isSome ∨ input.procs.isSome) then
    throw (.errorException "process options require multiprocessing")
  if input.verbosity.isSome ∧ input.optionVerbosity.isSome then
    throw (.errorException "duplicate verbosity")
  if input.progress.isSome ∧ input.optionProgress.isSome then
    throw (.errorException "duplicate progress")
  if input.optionReturnState.isSome ∧
      (input.returnState.isSome ∨ input.valReturnState.isSome) then
    throw (.errorException "duplicate return_state")
  let n := input.numprocs.getD ((input.procs.map List.length).getD 4)
  if input.numprocs.isSome ∧ input.procs.isSome ∧
      (input.procs.getD []).length ≠ n then throw (.assertionError "numprocs")
  let verbosity := (input.verbosity.or input.optionVerbosity).getD 1
  pure { mode := mode, iterations := input.iterations, numprocs := n
         returnState := (input.valReturnState.or
           (input.optionReturnState.or input.returnState)).getD false
         verbosity := verbosity
         progress := (input.progress.or input.optionProgress).getD
           (decide (verbosity > 0) && decide (input.outputs = 1))
         dimOut := input.dimOut.getD (if input.outputs > 1 then 2 else 1)
         workerTimeout := (input.workerTimeout.or input.environmentTimeout).getD (max 60 (n*n))
         runId := input.runId.getD generatedRunId }

end SymReg.Search
