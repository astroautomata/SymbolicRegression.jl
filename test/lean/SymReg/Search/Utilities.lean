import SymReg.Search.Scheduler

namespace SymReg.Search
open DynExpr
open SymReg.HofMig
open DynExpr.Expressions.Sampling (greater)

/-- Numeric `early_stop_condition`, `src/Options.jl:1034-1039`, is strict `<`.
Function-valued conditions are supplied unchanged. -/
inductive EarlyStop where
  | disabled
  | threshold (loss : JF)
  | predicate (f : JF → Int → Bool)

def earlyPredicate : EarlyStop → JF → Int → Bool
  | .disabled, _, _ => false
  | .threshold t, loss, _ => less loss t
  | .predicate f, loss, complexity => f loss complexity

-- Source: src/SearchUtils.jl:533-545.
-- return _check_for_loss_threshold(halls_of_fame, options.early_stop_condition, options)
-- _check_for_loss_threshold(_, ::Nothing, ::AbstractOptions) returns false.
-- return all(halls_of_fame) do hof
--     any(hof.members[hof.exists]) do member
--         return f(member.loss, compute_complexity(member, options))::Bool
--     end
-- end
def checkLossWith {m : Type → Type} [Monad m] (halls : List Hof)
    (condition : Option (JF → Int → m Bool)) (compute : Member → m Int) : m Bool :=
  match condition with
  | none => pure false
  | some f => halls.allM fun hof =>
      (hof.slots.filter Slot.exists).anyM fun s => do
        let complexity ← compute s.member
        f s.member.loss complexity

def checkLoss (halls : List Hof) (condition : EarlyStop)
    (compute : Member → Int) : Bool :=
  checkLossWith (m := Id) halls
    (match condition with
     | .disabled => none
     | other => some (earlyPredicate other))
    compute

-- Source: src/SearchUtils.jl:548-551
-- function check_for_timeout(start_time::Float64, options::AbstractOptions)::Bool
--     return options.timeout_in_seconds !== nothing &&
--            time() - start_time > options.timeout_in_seconds::Float64
-- end
def checkTimeoutWith {m : Type → Type} [Monad m] (start : JF)
    (present : m Bool) (clock readFloat64 : m JF) : m Bool := do
  if !(← present) then return false
  let now ← clock
  let elapsed := SymReg.Loss.LossPrecision.round .float64 (now - start)
  let seconds ← readFloat64
  pure (greater elapsed seconds)

-- Stock Options has the same property value on both reads.
def checkTimeout (start : JF) (clock : Unit → JF) (limit : Option JF) : Bool × Nat :=
  (checkTimeoutWith (m := StateM Nat) start (pure limit.isSome)
    (do modify (· + 1); pure (clock ())) (pure (limit.getD (.fin 0)))).run 0

def evaluationTotal (reports : List (List JF)) : JF :=
  let juliaSum := SymReg.Loss.pairwiseSum .float64
  juliaSum (reports.map juliaSum)

-- Source: src/SearchUtils.jl:553-555.
-- function check_max_evals(num_evals, options::AbstractOptions)::Bool
--     return options.max_evals !== nothing && options.max_evals::Int <= sum(sum, num_evals)
-- end
def checkMaxEvalsWith {m : Type → Type} [Monad m] (set : m Bool)
    (readLimit : m Int) (readCounters : m (List (List JF))) : m Bool := do
  if !(← set) then return false
  let limit ← readLimit
  let counters ← readCounters
  return greaterEqual (evaluationTotal counters) (.fin (limit : Rat))

def checkMaxEvals (reports : List (List JF)) (limit : Option Int) : Bool :=
  checkMaxEvalsWith (m := Id) limit.isSome (limit.getD 0) reports

/-- The global break after collection and relaunch, `src/SymbolicRegression.jl:1333-1342`.
The Bool applies to the whole loop, never to a single output. -/
def stopSearch (loss quit timeout maxEvals external : Bool) : Bool :=
  [loss, quit, timeout, maxEvals, external].any id

-- Source: src/SymbolicRegression.jl:1334-1342.
-- if any((
--     check_for_loss_threshold(state.halls_of_fame, options),
--     check_for_user_quit(state.stdin_reader),
--     check_for_timeout(start_time, options),
--     check_max_evals(state.num_evals, options),
--     check_external_stop(ropt),
-- ))
--     break
-- end
def runStopChecks {m : Type → Type} [Monad m]
    (loss quit timeout maxEvals external : m Bool) : m Bool := do
  let l ← loss
  let q ← quit
  let t ← timeout
  let n ← maxEvals
  let e ← external
  pure (stopSearch l q t n e)

/-- `src/SearchUtils.jl:275-302`; a finite map has one value per population key. -/
abbrev Assignments := List ((Nat × Nat) × Nat)

def assigned (a : Assignments) (key : Nat × Nat) : Option Nat :=
  (a.find? (fun x => x.1 == key)).map Prod.snd

def jobCount (a : Assignments) (worker : Nat) : Nat :=
  (a.filter (fun x => x.2 == worker)).length

/-- Leftmost minimum under `<=` ties, `src/SearchUtils.jl:278-288`. -/
def nextWorker (a : Assignments) (workers : List Nat) : Jl Nat :=
  if a.any (fun x => !(workers.contains x.2)) then .error (.assertionError "worker")
  else match workers with
    | [] => .error (.argumentError "empty worker reduction")
    | w :: ws => .ok (ws.foldl (fun best w =>
        if jobCount a best ≤ jobCount a w then best else w) w)

def assignWorker (a : Assignments) (key : Nat × Nat) (mode : Parallelism)
    (workers : List Nat) : Jl (Nat × Assignments) :=
  if mode = .multiprocessing then
    match assigned a key with
    | some worker => .ok (worker, a)
    | none => (nextWorker a workers).map (fun w => (w, (key, w) :: a))
  else .ok (0, a)

/-- `src/SearchUtils.jl:461-480`: the remembered q survives CR/LF-free read boundaries. -/
def parseQuit : List UInt8 → Bool → Bool × Bool
  | [], saw => (false, saw)
  | c :: rest, saw =>
    if c = 3 then (true, false)
    else if c = 113 then parseQuit rest true
    else if c = 13 ∨ c = 10 then
      if saw then (true, false) else parseQuit rest saw
    else parseQuit rest false

/-- The IO operations in `src/SearchUtils.jl:436-459,483-530` are supplied read outcomes.
MethodError disables watching; EOF and IOError become an empty read. -/
inductive ReadResult where
  | bytes (data : List UInt8)
  | eof | ioError | methodError | failure (message : String)

structure Reader where
  readable : Bool
  sawQuit : Bool := false
  deriving DecidableEq, Repr

def readAvailable : ReadResult → Jl (List UInt8)
  | .bytes bs => .ok bs
  | .eof | .ioError => .ok []
  | .methodError => .error (.errorException "MethodError")
  | .failure msg => .error (.errorException msg)

def watchStream (readable : Bool) (firstRead : ReadResult) : Jl Reader :=
  if !readable then .ok ⟨false, false⟩
  else match firstRead with
    | .methodError => .ok ⟨false, false⟩
    | other => (readAvailable other).map (fun _ => ⟨true, false⟩)

-- Source: src/SearchUtils.jl:524-530.
-- if reader.can_read_user_input
--     data = read_available_nonblocking(reader.stream)
--     quit, reader.saw_quit_char = parse_quit_signal(data, reader.saw_quit_char)
--     return quit
-- end
-- return false
def userQuitWith {m : Type → Type} [Monad m] (reader : Reader)
    (read : m (List UInt8)) : m (Bool × Reader) := do
  if !reader.readable then return (false, reader)
  let (quit, saw) := parseQuit (← read) reader.sawQuit
  pure (quit, { reader with sawQuit := saw })

def userQuit (reader : Reader) (read : ReadResult) : Jl (Bool × Reader) :=
  userQuitWith reader (readAvailable read)

-- Source: src/SearchUtils.jl:501-520.
-- if reader.can_read_user_input
--     stop_reading_if_unshared(reader.stream)
-- end
-- stop_reading_if_unshared(stream::IO) = Base.stop_reading(stream)
-- Base.iolock_begin()
-- try
--     Base.@lock stream.cond isempty(stream.cond) && Base.stop_reading(stream)
-- finally
--     Base.iolock_end()
-- end
-- The bracket services run the body under the corresponding lock and unlock on exceptions.
def closeReaderWith {m : Type → Type} [Monad m] (reader : Reader) (libuv : Bool)
    (withIOlock withConditionLock : m Unit → m Unit)
    (emptyWaitQueue : m Bool) (stop : m Unit) : m Unit := do
  if reader.readable then
    if libuv then
      withIOlock (withConditionLock (do if ← emptyWaitQueue then stop))
    else stop

def closeReader (reader : Reader) (libuv sharedWaiters : Bool) : Bool :=
  ((closeReaderWith (m := StateM Bool) reader libuv id id (pure (!sharedWaiters))
    (set true)).run false).2

inductive Failure where
  | processExit
  | task (oldest : Failure) (later : List Failure)
  | other (message : String)

-- Source: src/SearchUtils.jl:72-78
-- function is_process_exit(ex)
--     if ex isa TaskFailedException
--         return is_process_exit(first(current_exceptions(ex.task)).exception)
--     else
--         return ex isa Distributed.ProcessExitedException
--     end
-- end
def isProcessExit : Failure → Bool
  | .processExit => true
  | .task oldest _ => isProcessExit oldest
  | .other _ => false

-- Source: src/SearchUtils.jl:58-70
-- macro filtered_async(expr)
--     return esc(quote
--         $(Base).errormonitor(@async begin
--             try
--                 $expr
--             catch ex
--                 if !$(is_process_exit)(ex)
--                     rethrow(ex)
--                 end
--             end
--         end)
--     end)
-- end
def filteredAsync {α : Type} : Except Failure α → Except Failure (Option α)
  | .ok value => .ok (some value)
  | .error failure => if isProcessExit failure then .ok none else .error failure

structure ExternalStop where
  requested : Bool := false
  fd : Int := -1
  trigger : UInt8 := 0
  lastPoll : UInt64 := 0
  deriving DecidableEq, Repr

inductive PollRead where
  | noPollResult | noReadResult | success
  deriving DecidableEq, Repr

-- Source: src/SearchUtils.jl:614-629.
-- stop.fd < 0 && return false
-- fd = StopFD(stop.fd)
-- requested = false
-- while true
--     stop.poll_fd[] = PollFD(fd, STOP_POLL_READ, Cshort(0))
--     poll_stop_fd(stop.poll_fd) == 1 || break
--     read_stop_byte(fd, stop.read_buf) == 1 || break
--     if stop.trigger == 0x00 || stop.read_buf[] == stop.trigger
--         requested = true
--     end
-- end
-- return requested
def drainDescriptor (trigger : UInt8) : List PollRead → List UInt8 → Bool × List UInt8
  | .success :: more, byte :: bytes =>
    let (found, remaining) := drainDescriptor trigger more bytes
    (trigger == 0 || byte == trigger || found, remaining)
  | _, bytes => (false, bytes)

def checkStopFD (s : ExternalStop) (events : List PollRead) (queued : List UInt8) :
    Bool × List UInt8 :=
  if s.fd < 0 then (false, queued) else drainDescriptor s.trigger events queued

-- Source: src/SearchUtils.jl:649-662,668-674,687-690.
-- stop.last_poll_ns[] = time_ns()
-- if check_stop_fd(stop)
--     stop.requested[] = true
-- end
-- return stop.requested[]
def latchStop (s : ExternalStop) (now : UInt64) (events : List PollRead)
    (queued : List UInt8) : ExternalStop × List UInt8 :=
  let (triggered, rest) := checkStopFD s events queued
  ({ s with requested := s.requested || triggered, lastPoll := now }, rest)

-- if stop.fd >= 0
--     now = time_ns()
--     if now - stop.last_poll_ns[] >= STOP_POLL_INTERVAL_NS
--         stop.last_poll_ns[] = now
--         if check_stop_fd(stop)
--             stop.requested[] = true
--         end
--     end
-- end
-- return stop.requested[]
def checkExternal (s : ExternalStop) (now : UInt64) (events : List PollRead)
    (queued : List UInt8) : ExternalStop × List UInt8 :=
  if s.fd ≥ 0 ∧ now - s.lastPoll ≥ 20000000 then latchStop s now events queued else (s, queued)

-- check_stop_fd(stop)
-- return nothing
def drainStop (s : ExternalStop) (events : List PollRead)
    (queued : List UInt8) : ExternalStop × List UInt8 :=
  (s, (checkStopFD s events queued).2)

/-- `src/SearchUtils.jl:699-719`. Histories retain the newest maxRecordings checks. -/
structure Monitor where
  history : List Bool
  maxRecordings : Nat
  startReporting : Nat
  window : Nat
  deriving DecidableEq, Repr

def recordChannel (m : Monitor) (ready : Bool) : Monitor :=
  let history := m.history ++ [ready]
  { m with history := if history.length > m.maxRecordings then history.tail else history }

-- Source: src/SearchUtils.jl:714-719.
-- function estimate_work_fraction(monitor::ResourceMonitor)::Float64
--     if length(monitor.population_ready) <= monitor.start_reporting_at
--         return 0.0
--     end
--     return mean(monitor.population_ready[(end - (monitor.window_size - 1)):end])
-- end
def estimateWork (m : Monitor) : Jl JF :=
  if m.history.length ≤ m.startReporting then .ok (.fin 0)
  else if m.window > m.history.length then .error .boundsError
  else
    let recent := m.history.drop (m.history.length - m.window)
    let f64 := SymReg.Loss.LossPrecision.round .float64
    .ok (f64 (f64 (.fin ((recent.filter id).length : Rat)) / f64 (.fin (recent.length : Rat))))

/-- `src/SearchUtils.jl:721-738` returns an empty load string on every branch. -/
def loadString (_occupation : JF) (_mode : Parallelism) : String := ""

/-- `src/SearchUtils.jl:740-772,775-802` and `src/SymbolicRegression.jl:1267-1271`.
Terminal rendering is an arbitrary callback; these are the supplied arithmetic values. -/
def progressIterations (totalCycles outputs populations : Nat) (remaining : List Nat) : Nat :=
  (totalCycles * outputs - remaining.sum) / populations

def progressPercent (totalCycles outputs : Nat) (remaining : List Nat) : JF :=
  .fin 100 * .fin ((totalCycles * outputs - remaining.sum : Nat) : Rat) /
    .fin ((totalCycles * outputs : Nat) : Rat)

def averageSpeed (speeds : List JF) : JF :=
  SymReg.Loss.sumF speeds / .fin (speeds.length : Rat)

-- Source: src/SearchUtils.jl:1015-1029.
-- cycles_elapsed = total_cycles - cycles_remaining
-- fraction_elapsed = 1.0f0 * cycles_elapsed / total_cycles
-- in_warmup_period = fraction_elapsed <= options.warmup_maxsize_by
-- if options.warmup_maxsize_by > 0 && in_warmup_period
--     return 3 + floor(
--         Int, (options.maxsize - 3) * fraction_elapsed / options.warmup_maxsize_by
--     )
-- else
--     return options.maxsize
-- end
def cycleFraction (total remaining : Int64) : JF :=
  let f32 := SymReg.Loss.LossPrecision.round .float32
  f32 ((f32 (.fin ((total - remaining).toInt : Rat))) /
    (f32 (.fin (total.toInt : Rat))))

def currentMaxsize (maxsize : Int) (warmup fraction : JF) : Jl Int :=
  let inWarmup := greaterEqual warmup fraction
  if greater warmup (.fin 0) && inWarmup then
    let f32 := SymReg.Loss.LossPrecision.round .float32
    let f64 := SymReg.Loss.LossPrecision.round .float64
    let range := (Int64.ofInt maxsize - 3).toInt
    match f64 (f32 (f32 (.fin (range : Rat)) * fraction) / warmup) with
    | .fin value =>
      let n := value.floor
      if n < -9223372036854775808 ∨ 9223372036854775808 ≤ n then .error .inexactError
      else .ok (3 + Int64.ofInt n).toInt
    | _ => .error .inexactError
  else .ok maxsize

def getCurMaxsize (maxsize : Int64) (warmup : JF) (total remaining : Int64) : Jl Int :=
  currentMaxsize maxsize.toInt warmup (cycleFraction total remaining)

/-- `_dispatch_s_r_cycle`, `src/SymbolicRegression.jl:1412-1438`.
Evolution and optimization results are arbitrary inputs; batching rechecks existing slots. -/
def dispatchEvaluations (evolution optimize : JF) (batching : Bool) (best : Hof)
    (maxsize : Nat) : JF :=
  let base := (.fin 0 + evolution) + optimize
  if batching then
    (best.slots.take maxsize).foldl (fun n slot => if slot.exists then n + .fin 1 else n) base
  else base

end SymReg.Search
