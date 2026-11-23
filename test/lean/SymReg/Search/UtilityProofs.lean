import SymReg.Search.Lifecycle

namespace SymReg.Search
open DynExpr
open SymReg.HofMig
open DynExpr.Expressions.Sampling (greater)

 def stop_disabled : Prop := ∀ (halls : List Hof) (compute : Member → Int),
  checkLoss halls .disabled compute = false
 theorem stop_disabled_holds : stop_disabled := by intro halls compute; rfl

theorem disabledLoss_skips_occupied (loss : JF) :
    checkLossWith (m := Jl) [⟨[⟨specimen loss loss, true⟩]⟩]
      none (fun _ => .error (.errorException "unexpected complexity call")) = .ok false := rfl

private theorem checkLoss_projection (halls : List Hof) (f : JF → Int → Bool)
    (compute : Member → Int) :
    checkLossWith (m := Id) halls (some f) compute =
      halls.all (fun h => h.slots.any (fun s => s.exists && f s.member.loss (compute s.member))) := by
  change (halls.allM (m := Id) fun h =>
    (h.slots.filter Slot.exists).anyM (fun s => pure (f s.member.loss (compute s.member)))) = _
  simp only [List.anyM_pure, List.any_filter, List.allM_pure]
  rfl

theorem lossThreshold_member_call (m : Member)
    (compute : Member → Jl Int) (test : JF → Int → Jl Bool) :
    checkLossWith [⟨[⟨m, true⟩]⟩] (some test) compute =
      (compute m >>= fun size => test m.loss size) := by
  cases h : compute m with
  | error e => simp [checkLossWith, List.allM, List.anyM, h, Bind.bind, Except.bind]
  | ok size =>
    cases ht : test m.loss size with
    | error e => simp [checkLossWith, List.allM, List.anyM, h, ht, Bind.bind, Except.bind]
    | ok result =>
      cases result <;> simp [checkLossWith, List.allM, List.anyM, h, ht, Bind.bind,
        Except.bind, Pure.pure, Except.pure]

 def stop_outputs : Prop := ∀ (halls : List Hof) (f : JF → Int → Bool)
    (compute : Member → Int),
  checkLoss halls (.predicate f) compute = true ↔
    ∀ h ∈ halls, ∃ slot ∈ h.slots, slot.exists = true ∧
      f slot.member.loss (compute slot.member) = true
 theorem stop_outputs_holds : stop_outputs := by
  intro halls f compute
  have h := checkLoss_projection halls f compute
  change checkLoss halls (.predicate f) compute = _ at h
  rw [h]
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]

 def stop_float : Prop := ∀ (halls : List Hof) (threshold : JF) (compute : Member → Int),
  checkLoss halls (.threshold threshold) compute =
    checkLoss halls (.predicate (fun loss _ => less loss threshold)) compute
 theorem stop_float_holds : stop_float := by intro halls threshold compute; rfl

 def timeout_exact : Prop := ∀ (start : JF) (clock : Unit → JF),
  checkTimeout start clock none = (false, 0) ∧
    (∀ limit : JF, (checkTimeout start clock (some limit)).2 = 1) ∧
    checkTimeout start clock
      (some (SymReg.Loss.LossPrecision.round .float64 (clock () - start))) = (false, 1) ∧
    (∀ (elapsed threshold : Rat),
      SymReg.Loss.LossPrecision.round .float64 (clock () - start) = .fin elapsed →
      ((checkTimeout start clock (some (.fin threshold))).1 = true ↔ threshold < elapsed))
 theorem timeout_exact_holds : timeout_exact := by
  intro start clock
  refine ⟨rfl, fun _ => rfl, ?_, ?_⟩
  · let elapsed := SymReg.Loss.LossPrecision.round .float64 (clock () - start)
    change (greater elapsed elapsed, 1) = (false, 1)
    cases elapsed <;> simp [greater]
  · intro elapsed threshold hd
    change greater (SymReg.Loss.LossPrecision.round .float64 (clock () - start))
      (.fin threshold) = true ↔ threshold < elapsed
    simp [hd, greater]

private inductive TimeoutRead
  | guard | clock | limit
  deriving DecidableEq

private def timeoutObserve {α : Type} (read : TimeoutRead) (answer : Jl α) :
    ExceptT JlError (StateM (List TimeoutRead)) α :=
  ExceptT.mk (fun seen => (answer, seen ++ [read]))

theorem checkTimeout_call_order (start : JF) (guard : Jl Bool) (clock limit : Jl JF) :
    ((checkTimeoutWith start (timeoutObserve .guard guard)
      (timeoutObserve .clock clock) (timeoutObserve .limit limit)).run []) =
    match guard with
    | .error e => (.error e, [.guard])
    | .ok false => (.ok false, [.guard])
    | .ok true =>
      match clock with
      | .error e => (.error e, [.guard, .clock])
      | .ok now =>
        (limit.map (greater (SymReg.Loss.LossPrecision.round .float64 (now - start))),
          [.guard, .clock, .limit]) := by
  cases guard with
  | error e => rfl
  | ok g => cases g <;> cases clock <;> cases limit <;> rfl

private def evaluationRead {α : Type} (tag : Nat) (result : Jl α) :
    ExceptT JlError (StateM (List Nat)) α :=
  ExceptT.mk fun log => (result, log ++ [tag])

def max_evals_exact : Prop :=
  (∀ (reports : List (List JF)) (limit : Option Int),
    checkMaxEvals reports limit = true ↔ ∃ count, limit = some count ∧
      greaterEqual (evaluationTotal reports) (.fin (count : Rat)) = true) ∧
  (∀ (set : Jl Bool) (limit : Jl Int) (reports : Jl (List (List JF))),
    ((checkMaxEvalsWith (evaluationRead 1 set) (evaluationRead 2 limit)
      (evaluationRead 3 reports)).run []) =
    match set, limit, reports with
    | .error e, _, _ => (.error e, [1])
    | .ok false, _, _ => (.ok false, [1])
    | .ok true, .error e, _ => (.error e, [1, 2])
    | .ok true, .ok _, .error e => (.error e, [1, 2, 3])
    | .ok true, .ok l, .ok rs => (.ok (checkMaxEvals rs (some l)), [1, 2, 3])) ∧
  let big := JF.fin 9007199254740992
  let one := JF.fin 1
  checkMaxEvals [[big, one], [one]] (some 9007199254740993) = false ∧
  checkMaxEvals [[big], [one, one]] (some 9007199254740993) = true

theorem max_evals_exact_holds : max_evals_exact := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · intro reports limit
    cases limit with
    | none =>
      change false = true ↔ _
      simp
    | some count =>
      change greaterEqual (evaluationTotal reports) (.fin (count : Rat)) = true ↔ _
      simp
  · intro set limit reports
    cases set with
    | error e => rfl
    | ok flag => cases flag <;> cases limit <;> cases reports <;> rfl

 def stop_disjunction : Prop := ∀ (loss quit timeout maxEvals external : Bool),
  stopSearch loss quit timeout maxEvals external = true ↔
    loss = true ∨ quit = true ∨ timeout = true ∨ maxEvals = true ∨ external = true
 theorem stop_disjunction_holds : stop_disjunction := by
  intro loss quit timeout maxEvals external
  simp [stopSearch]

 def worker_sticky : Prop := ∀ (a : Assignments) (key : Nat × Nat)
    (worker : Nat) (workers : List Nat), assigned a key = some worker →
  assignWorker a key .multiprocessing workers = .ok (worker, a)
 theorem worker_sticky_holds : worker_sticky := by
  intro a key worker workers ha
  simp [assignWorker, ha]
example : assigned [((0, 0), 7)] (0, 0) = some 7 := by decide

 def local_assignment : Prop := ∀ (a : Assignments) (key : Nat × Nat)
    (workers : List Nat) (mode : Parallelism), mode ≠ .multiprocessing →
  assignWorker a key mode workers = .ok (0, a)
 theorem local_assignment_holds : local_assignment := by
  intro a key workers mode hm
  simp [assignWorker, hm]
example : Parallelism.serial ≠ .multiprocessing := by decide

 theorem minimum_fold (a : Assignments) (ws : List Nat) (best : Nat) :
    let chosen := ws.foldl (fun best w => if jobCount a best ≤ jobCount a w then best else w) best
    (chosen = best ∨ chosen ∈ ws) ∧ jobCount a chosen ≤ jobCount a best ∧
      ∀ w ∈ ws, jobCount a chosen ≤ jobCount a w := by
  induction ws generalizing best with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons]
    by_cases h : jobCount a best ≤ jobCount a w
    · simp only [if_pos h]
      obtain ⟨hm, hb, hw⟩ := ih best
      refine ⟨?_, hb, ?_⟩
      · rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (by simp [hm])
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact hw x hx
    · simp only [if_neg h]
      obtain ⟨hm, hb, hw⟩ := ih w
      refine ⟨?_, by omega, ?_⟩
      · exact Or.inr (List.mem_cons.mpr hm)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hb
        · exact hw x hx

 def least_busy_worker : Prop := ∀ (a : Assignments) (workers : List Nat) (chosen : Nat),
  nextWorker a workers = .ok chosen → chosen ∈ workers ∧
    ∀ w ∈ workers, jobCount a chosen ≤ jobCount a w
 theorem least_busy_worker_holds : least_busy_worker := by
  intro a workers chosen hs
  unfold nextWorker at hs
  split at hs
  · contradiction
  · cases workers with
    | nil => contradiction
    | cons w ws =>
      simp only [Except.ok.injEq] at hs
      subst chosen
      obtain ⟨hm, hb, hw⟩ := minimum_fold a ws w
      constructor
      · exact List.mem_cons.mpr hm
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hb
        · exact hw x hx
example : nextWorker [] [0, 1] = .ok 0 := by decide

def worker_selection : Prop := least_busy_worker ∧
  (∀ (a : Assignments) (workers : List Nat),
    (∀ entry ∈ a, entry.2 ∈ workers) → workers ≠ [] →
      ∃ chosen, nextWorker a workers = .ok chosen) ∧
  (∀ (a : Assignments) (workers : List Nat) (entry : (Nat × Nat) × Nat),
    entry ∈ a → entry.2 ∉ workers → nextWorker a workers = .error (.assertionError "worker")) ∧
  nextWorker [] [] = .error (.argumentError "empty worker reduction") ∧
  (∀ (a : Assignments) (w : Nat) (ws : List Nat),
    (∀ entry ∈ a, entry.2 ∈ w :: ws) →
    (∀ v ∈ ws, jobCount a w ≤ jobCount a v) → nextWorker a (w :: ws) = .ok w)

private theorem workers_valid (a : Assignments) (workers : List Nat)
    (h : ∀ entry ∈ a, entry.2 ∈ workers) :
    (a.any fun entry => !workers.contains entry.2) = false := by
  rw [Bool.eq_false_iff]
  intro hb
  obtain ⟨entry, he, hb⟩ := List.any_eq_true.mp hb
  simpa [h entry he] using hb

private theorem stable_worker (a : Assignments) (w : Nat) (ws : List Nat)
    (h : ∀ v ∈ ws, jobCount a w ≤ jobCount a v) :
    ws.foldl (fun best v => if jobCount a best ≤ jobCount a v then best else v) w = w := by
  induction ws with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.foldl_cons, if_pos (h v (by simp))]
    exact ih (fun v hv => h v (by simp [hv]))

theorem worker_selection_holds : worker_selection := by
  refine ⟨least_busy_worker_holds, ?_, ?_, rfl, ?_⟩
  · intro a workers hv hn
    cases workers with
    | nil => contradiction
    | cons w ws =>
      unfold nextWorker
      rw [workers_valid a (w :: ws) hv]
      exact ⟨_, rfl⟩
  · intro a workers entry he hm
    have hb : (a.any fun e => !workers.contains e.2) = true :=
      List.any_eq_true.mpr ⟨entry, he, by simpa using hm⟩
    unfold nextWorker
    rw [hb]
    rfl
  · intro a w ws hv hm
    unfold nextWorker
    rw [workers_valid a (w :: ws) hv]
    change .ok (ws.foldl _ w) = Except.ok w
    rw [stable_worker a w ws hm]


private theorem first_minimum_fold (a : Assignments) (before after : List Nat) (w best : Nat)
    (hb : jobCount a w < jobCount a best)
    (hp : ∀ v ∈ before, jobCount a w < jobCount a v)
    (hs : ∀ v ∈ after, jobCount a w ≤ jobCount a v) :
    (before ++ w :: after).foldl
      (fun best v => if jobCount a best ≤ jobCount a v then best else v) best = w := by
  induction before generalizing best with
  | nil =>
    simp only [List.nil_append, List.foldl_cons, if_neg (show ¬jobCount a best ≤ jobCount a w by omega)]
    exact stable_worker a w after hs
  | cons p ps ih =>
    have htail : ∀ v ∈ ps, jobCount a w < jobCount a v := fun v hv =>
      hp v (List.mem_cons_of_mem _ hv)
    simp only [List.cons_append, List.foldl_cons]
    split
    · exact ih best hb htail
    · exact ih p (hp p (by simp)) htail

theorem nextWorker_first_minimum (a : Assignments) (before after : List Nat) (w : Nat)
    (valid : ∀ e ∈ a, e.2 ∈ before ++ w :: after)
    (hp : ∀ v ∈ before, jobCount a w < jobCount a v)
    (hs : ∀ v ∈ after, jobCount a w ≤ jobCount a v) :
    nextWorker a (before ++ w :: after) = .ok w := by
  unfold nextWorker
  rw [workers_valid _ _ valid]
  cases before with
  | nil =>
    change Except.ok (after.foldl _ w) = _
    rw [stable_worker a w after hs]
  | cons p ps =>
    change Except.ok ((ps ++ w :: after).foldl _ p) = _
    rw [first_minimum_fold a ps after w p (hp p (by simp))
      (fun v hv => hp v (List.mem_cons_of_mem _ hv)) hs]
 def quit_chunking : Prop := ∀ (left right : List UInt8) (saw remembered : Bool),
  parseQuit left saw = (false, remembered) →
  parseQuit (left ++ right) saw = parseQuit right remembered
 theorem quit_chunking_holds : quit_chunking := by
  intro left
  induction left with
  | nil => intro right saw remembered h; simp_all [parseQuit]
  | cons c cs ih =>
    intro right saw remembered h
    by_cases hc : c = 3
    · simp [parseQuit, hc] at h
    · by_cases hq : c = 113
      · simpa [parseQuit, hc, hq] using
          ih right true remembered (by simpa [parseQuit, hc, hq] using h)
      · by_cases hn : c = 13 ∨ c = 10
        · cases saw
          · simpa [parseQuit, hc, hq, hn] using
              ih right false remembered (by simpa [parseQuit, hc, hq, hn] using h)
          · simp [parseQuit, hc, hq, hn] at h
        · simpa [parseQuit, hc, hq, hn] using
            ih right false remembered (by simpa [parseQuit, hc, hq, hn] using h)
def quit_commands : Prop :=
  parseQuit [113] false = (false, true) ∧
  parseQuit [113, 10] false = (true, false) ∧
  parseQuit [113, 13] false = (true, false) ∧
  parseQuit [113, 120, 10] false = (false, false) ∧
  parseQuit [3, 113] false = (true, false)

theorem quit_commands_holds : quit_commands := by unfold quit_commands; decide

def quit_chunks_and_commands : Prop := quit_chunking ∧ quit_commands

theorem quit_chunks_and_commands_holds : quit_chunks_and_commands :=
  ⟨quit_chunking_holds, quit_commands_holds⟩

 def reader_safety : Prop := ∀ (reader : Reader) (result : ReadResult),
  reader.readable = false → userQuit reader result = .ok (false, reader)
 theorem reader_safety_holds : reader_safety := by
  intro reader result hr
  simp [userQuit, userQuitWith, hr, pure, Except.pure]
example : (⟨false, false⟩ : Reader).readable = false := rfl

 def shared_stream : Prop := ∀ (reader : Reader), closeReader reader true true = false
 theorem shared_stream_holds : shared_stream := by
  intro reader
  cases reader with
  | mk readable saw => cases readable <;> rfl

private def readerMark (name : String) : StateM (List String) Unit :=
  modify (· ++ [name])

private def readerBracket (name : String) (body : StateM (List String) Unit) :
    StateM (List String) Unit := do
  readerMark (name ++ " lock")
  body
  readerMark (name ++ " unlock")

theorem unreadableReader_skips_read (read : StateM (List String) (List UInt8))
    (sawQuit : Bool) (prior : List String) :
    (userQuitWith ⟨false, sawQuit⟩ read).run prior = ((false, ⟨false, sawQuit⟩), prior) := rfl

theorem libuvReader_checks_waiters_under_locks (sawQuit : Bool) (empty : Bool) :
    (closeReaderWith (m := StateM (List String)) ⟨true, sawQuit⟩ true
      (readerBracket "io") (readerBracket "condition")
      (do readerMark "waiters"; pure empty) (readerMark "stop")).run [] =
      ((), ["io lock", "condition lock", "waiters"] ++ (if empty then ["stop"] else []) ++
        ["condition unlock", "io unlock"]) := by cases empty <;> rfl

inductive OldestCause : Failure → Failure → Prop where
  | exited : OldestCause .processExit .processExit
  | other (msg : String) : OldestCause (.other msg) (.other msg)
  | nested {first terminal : Failure} (later : List Failure) :
      OldestCause first terminal → OldestCause (.task first later) terminal

def process_exit_filter : Prop := ∀ (failure : Failure),
  (OldestCause failure .processExit →
    filteredAsync (.error failure : Except Failure Nat) = .ok none) ∧
  (∀ msg, OldestCause failure (.other msg) →
    filteredAsync (.error failure : Except Failure Nat) = .error failure) ∧
  filteredAsync (.error (.task .processExit [.other "cleanup failed"]) :
    Except Failure Nat) = .ok none

private theorem classify_oldest {first terminal : Failure} (h : OldestCause first terminal) :
    isProcessExit first = isProcessExit terminal := by
  induction h with
  | exited => rfl
  | other => rfl
  | nested _ _ ih => exact ih

theorem process_exit_filter_holds : process_exit_filter := by
  intro failure
  refine ⟨?_, ?_, rfl⟩
  · intro h
    simp [filteredAsync, classify_oldest h, isProcessExit]
  · intro msg h
    simp [filteredAsync, classify_oldest h, isProcessExit]

def external_latched : Prop := ∀ (s : ExternalStop) (now : UInt64)
    (events : List PollRead) (queued : List UInt8),
  (s.requested = true → (checkExternal s now events queued).1.requested = true) ∧
  (s.fd < 0 ∨ now - s.lastPoll < 20000000 →
    checkExternal s now events queued = (s, queued)) ∧
  (drainStop s events queued).1 = s

theorem external_latched_holds : external_latched := by
  intro s now events queued
  refine ⟨?_, ?_, rfl⟩
  · intro hs
    unfold checkExternal
    split
    · unfold latchStop
      cases checkStopFD s events queued
      simp [hs]
    · exact hs
  · intro h
    unfold checkExternal
    split
    · rename_i hgate
      rcases h with hn | ht
      · exact False.elim (Int.not_lt_of_ge hgate.1 hn)
      · exact False.elim ((UInt64.not_lt.mpr hgate.2) ht)
    · rfl

private theorem drain_consumed (trigger : UInt8) (seen rest : List UInt8)
    (stop : PollRead) (tail : List PollRead) (hstop : stop ≠ .success) :
    drainDescriptor trigger (List.replicate seen.length .success ++ stop :: tail) (seen ++ rest) =
      (seen.any (fun byte => trigger == 0 || byte == trigger), rest) := by
  induction seen with
  | nil => cases stop <;> simp_all [drainDescriptor]
  | cons b bs ih =>
    simp [List.replicate_succ, drainDescriptor, ih]

def external_trigger : Prop := ∀ (s : ExternalStop) (now : UInt64) (seen rest : List UInt8)
    (stop : PollRead) (tail : List PollRead),
  s.fd ≥ 0 → now - s.lastPoll ≥ 20000000 → stop ≠ .success →
  let events := List.replicate seen.length PollRead.success ++ stop :: tail
  let (after, remaining) := checkExternal s now events (seen ++ rest)
  remaining = rest ∧ after.lastPoll = now ∧
    (after.requested = true ↔ s.requested = true ∨
      ∃ byte ∈ seen, s.trigger = 0 ∨ byte = s.trigger) ∧
  drainStop s events (seen ++ rest) = (s, rest)

theorem external_trigger_holds : external_trigger := by
  intro s now seen rest stop tail hfd htime hstop
  have hn : ¬ s.fd < 0 := Int.not_lt_of_ge hfd
  simp [checkExternal, latchStop, drainStop, checkStopFD, hfd, htime, hn,
    drain_consumed _ _ _ _ _ hstop, List.any_eq_true, Bool.or_eq_true]

example : (⟨true, -1, 0, 0⟩ : ExternalStop).requested = true := rfl
example : 0 ≤ (3 : Int) ∧ (20000000 : UInt64) - 0 ≥ 20000000 ∧
    PollRead.noPollResult ≠ .success := by decide

 def monitor_capacity : Prop := ∀ (m : Monitor) (ready : Bool),
  m.history.length ≤ m.maxRecordings →
  (recordChannel m ready).history =
    (m.history ++ [ready]).drop (m.history.length + 1 - m.maxRecordings)
 theorem monitor_capacity_holds : monitor_capacity := by
  intro m ready hh
  unfold recordChannel
  dsimp only
  split
  · rename_i hover
    have hd : m.history.length + 1 - m.maxRecordings = 1 := by simp at hover; omega
    rw [hd]
    cases m.history <;> rfl
  · rename_i hfit
    have hd : m.history.length + 1 - m.maxRecordings = 0 := by simp at hfit; omega
    simp [hd]
example : (⟨[], 1, 0, 1⟩ : Monitor).history.length ≤ 1 := by decide

def monitor_window : Prop := ∀ (m : Monitor) (past recent : List Bool),
  m.history.length > m.startReporting → m.history = past ++ recent →
  recent.length = m.window →
  let f64 := SymReg.Loss.LossPrecision.round .float64
  estimateWork m = .ok (f64 (f64 (.fin (recent.countP id : Rat)) / f64 (.fin (m.window : Rat))))

theorem monitor_window_holds : monitor_window := by
  intro m past recent hs hh hw
  have hlength : m.history.length = past.length + m.window := by rw [hh, List.length_append, hw]
  have hstart : ¬ m.history.length ≤ m.startReporting := by omega
  have hwindow : ¬ m.window > m.history.length := by omega
  have hdrop : m.history.length - m.window = past.length := by omega
  rw [estimateWork, ite_eq_right hstart, ite_eq_right hwindow, hdrop, hh, List.drop_append_length]
  simp only [List.countP_eq_length_filter, hw]

def monitor_startup : Prop :=
  (∀ (m : Monitor), m.history.length ≤ m.startReporting → estimateWork m = .ok (.fin 0)) ∧
  (∀ (past : List Bool) (capacity : Nat),
    estimateWork ⟨past ++ [true], capacity, past.length, 1⟩ = .ok (.fin 1))

theorem monitor_startup_holds : monitor_startup := by
  constructor
  · intro m hh
    simp [estimateWork, hh]
  · intro past capacity
    have he := monitor_window_holds ⟨past ++ [true], capacity, past.length, 1⟩ past [true]
      (by simp) rfl rfl
    refine he.trans ?_
    change (Except.ok (SymReg.Loss.LossPrecision.round .float64
      (SymReg.Loss.LossPrecision.round .float64 (.fin 1) /
        SymReg.Loss.LossPrecision.round .float64 (.fin 1))) : Jl JF) = .ok (.fin 1)
    decide +kernel

example : (⟨[], 1, 0, 1⟩ : Monitor).history.length ≤ 0 := by decide
example : let m : Monitor := ⟨[true, false], 2, 0, 2⟩
  m.history.length > m.startReporting ∧ m.history = [] ++ [true, false] ∧
    ([true, false] : List Bool).length = m.window := by decide

 def progress_complete : Prop := ∀ (n p outputs : Nat), p > 0 →
  progressIterations (n * p) outputs p (List.replicate outputs 0) = n * outputs
 theorem progress_complete_holds : progress_complete := by
  intro n p outputs hp
  have hz : (List.replicate outputs (0 : Nat)).sum = 0 := by
    induction outputs <;> simp_all [List.replicate_succ]
  simp only [progressIterations, hz, Nat.sub_zero]
  rw [Nat.mul_right_comm, Nat.mul_div_cancel _ hp]
example : (1 : Nat) > 0 := by decide

 def maxsize_disabled : Prop := ∀ (maxsize : Int) (fraction : JF),
  currentMaxsize maxsize (.fin 0) fraction = .ok maxsize
 theorem maxsize_disabled_holds : maxsize_disabled := by
  intro maxsize fraction
  simp [currentMaxsize, greater]

theorem getCurMaxsize_disabled (maxsize total remaining : Int64) :
    getCurMaxsize maxsize (.fin 0) total remaining = .ok maxsize.toInt :=
  maxsize_disabled_holds maxsize.toInt (cycleFraction total remaining)

 def dispatch_unbatched : Prop := ∀ (evolution optimize : JF) (best : Hof) (maxsize : Nat),
  dispatchEvaluations evolution optimize false best maxsize = (.fin 0 + evolution) + optimize
 theorem dispatch_unbatched_holds : dispatch_unbatched := by intro evolution optimize best maxsize; rfl

 def transport_payload : Prop := ∀ (α β : Type) (mode : Parallelism) (f : α → β)
    (inputs : α) (worker latency : Nat),
  (spawnJob mode f (serializeBytes inputs) worker latency).2 = f inputs
 theorem transport_payload_holds : transport_payload := by
  intro α β mode f inputs worker latency
  unfold spawnJob
  split <;> rfl

 def worker_storage : Prop := ∀ (α : Type) (s : WorkerStore α) (value : α)
    (workers : List Nat) (worker : Nat), worker ∈ workers →
  let stored := storeOnWorkers s value workers
  stored.2.copies worker stored.1 = some value ∧ stored.2.next = s.next + 1 ∧
    (deleteOnWorkers stored.2 stored.1 workers).copies worker stored.1 = none
 theorem worker_storage_holds : worker_storage := by
  intro α s value workers worker hw
  simp [storeOnWorkers, deleteOnWorkers, hw]
example : (0 : Nat) ∈ [0] := by simp

end SymReg.Search
