import SymReg.Search.UtilityProofs
import SymReg.ConstraintsProofs
import SymReg.HofMig.Frontier

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

 def validate_exact : Prop := ∀ (outputs dimOut : Nat) (populations : Int) (progress : Bool) (verbosity : Int),
  validateOptions outputs dimOut populations progress verbosity = .ok () ↔
    outputs > 0 ∧ (outputs = 1 ∨ dimOut = 2) ∧ populations > 0 ∧
      (progress = true → outputs = 1 ∧ verbosity > 0)

theorem validate_exact_holds : validate_exact := by
  intro outputs dimOut populations progress verbosity
  unfold validateOptions
  split <;> (repeat' split)
  all_goals simp_all [Bool.and_eq_true, decide_eq_true_eq] <;> omega

private def configEvent (name : String) (result : Jl Unit) :
    ExceptT JlError (StateM (List String)) Unit :=
  ExceptT.mk (fun seen => (result, seen ++ [name]))

theorem validation_precedes_baselines_and_seed (configuration datasetCheck baseline : Jl Unit) :
    ((validateSearchWith [0] 1 1 false false true true 1 (some 7) (pure ())
      (fun _ => configEvent "options" configuration)
      (fun _ => configEvent "dataset" datasetCheck)
      (fun _ => configEvent "baseline" baseline)
      (fun _ => configEvent "names" (.ok ()))
      (fun _ => configEvent "seed" (.ok ()))).run []) =
      match configuration, datasetCheck, baseline with
      | .error e, _, _ => (.error e, ["options"])
      | .ok _, .error e, _ => (.error e, ["options", "dataset"])
      | .ok _, .ok _, .error e => (.error e, ["options", "dataset", "baseline"])
      | .ok _, .ok _, .ok _ => (.ok (), ["options", "dataset", "baseline", "names", "seed"]) := by
  cases configuration <;> cases datasetCheck <;> cases baseline <;> rfl

def initial_dimensions : Prop := ∀ (outputs populations iterations : Nat)
    (mode : Parallelism) (configured : List Nat × Bool)
    (shuffle : List (Nat × Nat) → List (Nat × Nat)),
  (∀ keys, (shuffle keys).Perm keys) →
  let s := (createWorkers (m := Id) outputs populations iterations mode configured (fun _ => ()) shuffle).1
  s.channels.length = outputs ∧ s.taskOrder.length = outputs * populations ∧
    s.taskOrder = shuffle ((List.range outputs).flatMap fun j =>
      (List.range populations).map (j, ·)) ∧
    (∀ j i, (j, i) ∈ s.taskOrder ↔ j < outputs ∧ i < populations) ∧
    (∀ j i, j < outputs → i < populations →
      (s.channels[j]?.bind fun row => row[i]?) = some ⟨(j, i), 1, []⟩) ∧
    s.cyclesRemaining = List.replicate outputs (iterations * populations) ∧
    s.evaluations = List.replicate outputs (List.replicate populations (.fin 0)) ∧
    ∀ row ∈ s.channels, row.length = populations

theorem initial_dimensions_holds : initial_dimensions := by
  intro outputs populations iterations mode configured shuffle hshuffle
  let keys := (List.range outputs).flatMap fun j => (List.range populations).map (j, ·)
  have hl : ((List.range outputs).map (fun _ => populations)).sum = outputs * populations := by
    induction outputs <;> simp_all [List.range_succ, Nat.succ_mul]
  have hk : keys.length = outputs * populations := by simp [keys, List.length_flatMap, hl]
  have hp : (shuffle keys).Perm keys := hshuffle _
  let channels := (List.range outputs).map fun j => (List.range populations).map fun i =>
    (⟨(j, i), 1, []⟩ : WorkerChannel)
  let s := (createWorkers (m := Id) outputs populations iterations mode configured (fun _ => ()) shuffle).1
  have ho : s.taskOrder = shuffle keys := by cases mode <;> rfl
  have hc : s.channels = channels := by cases mode <;> rfl
  have he : s.evaluations = List.replicate outputs (List.replicate populations (.fin 0)) := by
    cases mode <;> rfl
  have hr : s.cyclesRemaining = List.replicate outputs (iterations * populations) := by
    cases mode <;> rfl
  change s.channels.length = outputs ∧ _
  rw [ho, hc]
  refine ⟨by simp [channels], hp.length_eq.trans hk, rfl, ?_, ?_, hr, he, ?_⟩
  · intro j i
    rw [hp.mem_iff]
    simp [keys, List.mem_flatMap, List.mem_map, List.mem_range]
  · intro j i hj hi
    simp [channels, List.getElem?_map, List.getElem?_range hj, List.getElem?_range hi]
  · intro row hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp

example : ∀ keys : List (Nat × Nat), keys.reverse.Perm keys := List.reverse_perm

def serial_workers : Prop := ∀ (outputs populations iterations : Nat) (mode : Parallelism)
    (configure : StateM Nat (List Nat × Bool)) (store : List Nat → StateM Nat Nat)
    (shuffle : List (Nat × Nat) → StateM Nat (List (Nat × Nat))) (before : Nat),
  mode ≠ .multiprocessing →
  let ((s, input), after) := (createWorkers outputs populations iterations mode configure store shuffle).run before
  let keys := (List.range outputs).flatMap fun j => (List.range populations).map (j, ·)
  s.procs = [] ∧ s.createdProcs = false ∧ input = none ∧
    (s.taskOrder, after) = (shuffle keys).run before

theorem serial_workers_holds : serial_workers := by
  intro outputs populations iterations mode configure store shuffle before hm
  let keys := (List.range outputs).flatMap fun j => (List.range populations).map (j, ·)
  let channels := (List.range outputs).map fun j => (List.range populations).map fun i =>
    (⟨(j, i), 1, []⟩ : WorkerChannel)
  have hcreate : (createWorkers outputs populations iterations mode configure store shuffle).run before =
      (let (order, after) := (shuffle keys).run before
       ((⟨channels, order, List.replicate outputs (List.replicate populations (.fin 0)),
          List.replicate outputs (iterations * populations), [], false⟩, none), after)) := by
    cases mode with
    | serial | multithreading => rfl
    | multiprocessing => exact False.elim (hm rfl)
  rw [hcreate]
  change (let (order, last) := (shuffle keys).run before
    [] = ([] : List Nat) ∧ false = false ∧ (none : Option Nat) = none ∧
      (order, last) = (shuffle keys).run before)
  cases (shuffle keys).run before
  exact ⟨rfl, rfl, rfl, rfl⟩
example : Parallelism.multithreading ≠ .multiprocessing := by decide

theorem localWorkerInputs_skip_remote {α : Type} (mode : Parallelism)
    (configure : Jl (List Nat × Bool)) (store : List Nat → Jl α)
    (localMode : mode ≠ .multiprocessing) :
    prepareWorkerInputs mode configure store = .ok ([], false, none) := by
  simp [prepareWorkerInputs, localMode, Bind.bind, Except.bind, Pure.pure, Except.pure]

example (e : JlError) :
    prepareWorkerInputs (m := Jl) (α := Nat) .multithreading (.error e) (fun _ => .error e) =
      .ok ([], false, none) := rfl

 def result_type_paths : Prop := ∀ (reply : Reply) (latency : Nat),
  extractWorker .serial reply = reply ∧
  extractWorker .multithreading (latency, reply) = reply ∧
  extractWorker .multiprocessing (latency, reply) = reply
 theorem result_type_paths_holds : result_type_paths := by intro reply latency; exact ⟨rfl, rfl, rfl⟩

 def state_format : Prop := ∀ (pops : List (List (List Member))) (h : Hof),
  formatOutput pops [h] 1 true = .ok (.state ⟨.vectors pops, .scalar h⟩) ∧
    formatOutput pops [h] 1 false = .ok (.halls (.scalar h))
 theorem state_format_holds : state_format := by intro pops h; exact ⟨rfl, rfl⟩

 def vector_format : Prop := ∀ (pops : List (List (List Member))) (halls : List Hof),
  formatOutput pops halls 2 false = .ok (.halls (.vector halls)) ∧
  formatOutput pops halls 2 true = .ok (.state ⟨.vectors pops, .vector halls⟩)
 theorem vector_format_holds : vector_format := by
  intro pops halls
  exact ⟨rfl, rfl⟩
example : (2 : Nat) ≠ 1 := by decide

private theorem copiedMemberIds_distinct (members : List Member) (fresh : Nat) :
    ((copyMembers members fresh).1.map Member.objectId).Nodup ∧
      ((copyMembers members fresh).1.map Member.treeId).Nodup := by
  induction members generalizing fresh with
  | nil => simp [copyMembers]
  | cons member members ih =>
    obtain ⟨hobjects, htrees⟩ := ih (fresh + 2)
    simp only [copyMembers, copyMember, List.map_cons, List.nodup_cons]
    refine ⟨⟨?_, hobjects⟩, ⟨?_, htrees⟩⟩
    · intro hm
      obtain ⟨m, hp, h⟩ := List.mem_map.mp hm
      have hf := (copyMembers_fresh members (fresh + 2) m hp).1
      omega
    · intro hm
      obtain ⟨m, hp, h⟩ := List.mem_map.mp hm
      have hf := (copyMembers_fresh members (fresh + 2) m hp).2
      omega

def copiedPopulation (source : List Member) (fresh : Nat) (loaded : PopulationCopy) : Prop :=
  fresh ≤ loaded.vectorId ∧ loaded.members.map payload = source.map payload ∧
    (loaded.members.map Member.objectId).Nodup ∧ (loaded.members.map Member.treeId).Nodup ∧
    ∀ member ∈ loaded.members, loaded.vectorId < member.objectId ∧ loaded.vectorId < member.treeId

theorem copiedPopulation_holds (source : List Member) (fresh : Nat) :
    copiedPopulation source fresh (copyPopulation source fresh) := by
  obtain ⟨hobjects, htrees⟩ := copiedMemberIds_distinct source (fresh + 1)
  refine ⟨Nat.le_refl _, copyMembers_payload _ _, hobjects, htrees, ?_⟩
  intro m hm
  have h := copyMembers_fresh source (fresh + 1) m hm
  exact ⟨Nat.lt_of_succ_le h.1, Nat.lt_trans (Nat.lt_succ_self _) h.2⟩

def state_population_roundtrip : Prop := ∀ (pops : List (List (List Member)))
    (halls : HallOutput) (out pop fresh : Nat) (row : List (List Member)) (members : List Member),
  pops[out]? = some row → row[pop]? = some members →
  ∃ loaded, loadPopulation (some ⟨.vectors pops, halls⟩) out pop fresh = .ok (some loaded) ∧
    copiedPopulation members fresh loaded

theorem state_population_roundtrip_holds : state_population_roundtrip := by
  intro pops halls out pop fresh row members hout hpop
  refine ⟨_, ?_, copiedPopulation_holds members fresh⟩
  simp [loadPopulation, getPopulation, SymReg.Loss.at1, hout, hpop, bind, Except.bind, Except.map]
example : getPopulation (.vectors [[[specimen (.fin 0) (.fin 1)]]]) 0 0 =
    .ok [specimen (.fin 0) (.fin 1)] := by decide

def legacy_population_shape : Prop := ∀ (matrix : PopulationMatrix)
    (halls : HallOutput) (out pop fresh : Nat) (members : List Member),
  out < matrix.outputs → pop < matrix.populations →
  matrix.columns[matrix.outputs * pop + out]? = some members →
  ∃ loaded, loadPopulation (some ⟨.matrix matrix, halls⟩) out pop fresh = .ok (some loaded) ∧
    copiedPopulation members fresh loaded

theorem legacy_population_shape_holds : legacy_population_shape := by
  intro matrix halls out pop fresh members hout hpop hdata
  refine ⟨_, ?_, copiedPopulation_holds members fresh⟩
  simp [loadPopulation, getPopulation, hout, hpop, SymReg.Loss.at1, Nat.add_comm out, hdata, Except.map]

def saved_population_bounds : Prop :=
  (∀ (rows : List (List (List Member))) (halls : HallOutput) (out pop fresh : Nat),
    (rows[out]?.bind fun r => r[pop]?) = none →
    loadPopulation (some ⟨.vectors rows, halls⟩) out pop fresh = .error .boundsError) ∧
  (∀ (matrix : PopulationMatrix) (halls : HallOutput) (out pop fresh : Nat),
    (matrix.outputs ≤ out ∨ matrix.populations ≤ pop) →
    loadPopulation (some ⟨.matrix matrix, halls⟩) out pop fresh = .error .boundsError)

theorem saved_population_bounds_holds : saved_population_bounds := by
  constructor
  · intro rows halls out pop fresh h
    cases hout : rows[out]? with
    | none => simp [loadPopulation, getPopulation, SymReg.Loss.at1, hout, bind, Except.bind, Except.map]
    | some row =>
      have hpop : row[pop]? = none := by simpa [hout] using h
      simp [loadPopulation, getPopulation, SymReg.Loss.at1, hout, hpop, bind, Except.bind, Except.map]
  · intro matrix halls out pop fresh h
    have hb : ¬ (out < matrix.outputs ∧ pop < matrix.populations) := by omega
    simp [loadPopulation, getPopulation, hb, Except.map]

def saved_hall_shape : Prop := ∀ (hs : List Hof) (datasets : List Nat) (options : Nat)
    (newHall : Nat → Nat → Jl Hof) (strip : Hof → Nat → Nat → Jl Hof)
    (score : Nat → Member → Nat → Jl (JF × JF)),
  hs.length ≠ datasets.length → initializeHalls (some hs) datasets options newHall strip score =
    .error (.errorException "DimensionMismatch")
theorem saved_hall_shape_holds : saved_hall_shape := by
  intro hs datasets options newHall strip score hn
  simp only [initializeHalls]
  split
  · rfl
  · contradiction
example : ([] : List Hof).length ≠ 1 := by decide

private inductive PopInitCall where
  | warning
  | size (options : Nat)
  | features (dataset options : Nat)
  | generate (dataset : Nat) (size : Int) (length options : Nat) (features : Int) (plugins : Nat)
  | hall (options dataset : Nat)
  | trace (options : Nat)
  | strip (copy : PopulationCopy) (options dataset : Nat)
  | score (dataset : Nat) (member : Member) (options : Nat)

private abbrev PopInitM := ExceptT JlError (StateM (List PopInitCall))

private def popInitCall {A : Type} (call : PopInitCall) (result : Jl A) : PopInitM A :=
  ExceptT.mk fun calls => (result, calls ++ [call])

private theorem runInitBind {A B : Type} (x : PopInitM A) (f : A → PopInitM B)
    (trace : List PopInitCall) :
    ((x >>= f).run trace) = match x.run trace with
    | (.error e, next) => (.error e, next)
    | (.ok a, next) => (f a).run next := by
  change (match x.run trace with
    | (result, next) => (ExceptT.bindCont f result : StateM (List PopInitCall) (Jl B)) next) = _
  cases x.run trace with
  | mk value next => cases value <;> rfl

private theorem runInitPure {A : Type} (value : A) (trace : List PopInitCall) :
    ((pure value : PopInitM A).run trace) = (.ok value, trace) := rfl

private theorem runInitCall {A : Type} (call : PopInitCall) (result : Jl A) (trace : List PopInitCall) :
    ((popInitCall call result).run trace) = (result, trace ++ [call]) := rfl

private theorem runInitMap {A B : Type} (x : PopInitM A) (f : A → B)
    (trace : List PopInitCall) :
    ((f <$> x).run trace) = ((x.run trace).1.map f, (x.run trace).2) := by
  rw [map_eq_pure_bind, runInitBind]
  cases x.run trace with
  | mk value next => cases value <;> rfl

private theorem runInitMapM {A B : Type} (f : A → PopInitM B) (g : A → B)
    (observe : A → PopInitCall) (call : ∀ a trace, ((f a).run trace) = (.ok (g a), trace ++ [observe a]))
    (xs : List A) (trace : List PopInitCall) :
    ((xs.mapM f).run trace) = (.ok (xs.map g), trace ++ xs.map observe) := by
  induction xs generalizing trace with
  | nil => simp [List.mapM_nil, runInitPure]
  | cons a xs ih =>
    simp [List.mapM_cons, runInitBind, runInitMap, call, ih, Except.map, List.append_assoc]

private def stockSizeRecreation : Prop :=
  ∀ (saved : PopulationCopy) (headSize workerSize verbosity : Int)
    (headDataset workerDataset headOptions workerOptions plugins : Nat)
    (warning : Jl Unit) (features : Jl Int) (make : Jl PopulationCopy)
    (hall : Jl Hof) (trace : Option Nat) (unexpected : JlError),
    (saved.members.length : Int) ≠ headSize →
    ((initializePopulation (m := PopInitM) (some saved) (.stock headSize) (.stock workerSize)
      verbosity headDataset workerDataset headOptions workerOptions plugins
      (popInitCall .warning warning)
      (fun d o => popInitCall (.features d o) features)
      (fun d n len o f p => popInitCall (.generate d n len o f p) make)
      (fun o d => popInitCall (.hall o d) hall)
      (fun o => popInitCall (.trace o) (.ok trace))
      (fun p o d => popInitCall (.strip p o d) (.error unexpected))
      (fun d p o => popInitCall (.score d p o) (.error unexpected))).run []) =
    match if 0 < verbosity then warning else .ok () with
    | .error e => (.error e, [.warning])
    | .ok () =>
      let calls := (if 0 < verbosity then [PopInitCall.warning] else []) ++
        [.features workerDataset workerOptions]
      match features with
      | .error e => (.error e, calls)
      | .ok nf =>
        let calls := calls ++ [.generate workerDataset workerSize 3 workerOptions nf plugins]
        match make with
        | .error e => (.error e, calls)
        | .ok pop =>
          let calls := calls ++ [.hall workerOptions workerDataset]
          match hall with
          | .error e => (.error e, calls)
          | .ok _ =>
            (.ok (pop, SymReg.Loss.LossPrecision.round .float64 (.fin (workerSize : Rat))),
              calls ++ [.trace workerOptions])

private theorem stockSizeRecreation_holds : stockSizeRecreation := by
  intro saved headSize workerSize verbosity d wd o wo plugins warn features make hall trace unexpected hsize
  by_cases hv : 0 < verbosity <;> cases warn <;> cases features <;> cases make <;>
    cases hall <;>
    simp only [initializePopulation, PopulationSize.read, runInitBind, runInitPure, runInitCall,
      hsize, hv, ite_true, ite_false, List.nil_append] <;> rfl

private def workerSizeAccessor (options : Nat) (before after : Jl Int) : PopInitM Int :=
  ExceptT.mk fun calls =>
    (if calls.any (fun | .trace _ => true | _ => false) then after else before,
      calls ++ [.size options])

private def customSizeRecreation : Prop :=
  ∀ (saved pop : PopulationCopy) (headSize first last : Jl Int)
    (trace : Jl (Option Nat))
    (headDataset workerDataset headOptions workerOptions plugins : Nat) (features : Int),
    (∀ size, headSize = .ok size → (saved.members.length : Int) ≠ size) →
    ((initializePopulation (m := PopInitM) (some saved)
      (.custom (popInitCall (.size headOptions) headSize))
      (.custom (workerSizeAccessor workerOptions first last))
      1 headDataset workerDataset headOptions workerOptions plugins
      (popInitCall .warning (.ok ()))
      (fun d o => popInitCall (.features d o) (.ok features))
      (fun d n len o f p => popInitCall (.generate d n len o f p) (.ok pop))
      (fun o d => popInitCall (.hall o d) (.ok ⟨[]⟩))
      (fun o => popInitCall (.trace o) trace)
      (fun p o d => popInitCall (.strip p o d) (.ok p))
      (fun d p o => popInitCall (.score d p o) (.ok (p.cost, p.loss)))).run []) =
    match headSize with
    | .error e => (.error e, [.size headOptions])
    | .ok _ =>
      let calls := [PopInitCall.size headOptions, .warning, .size workerOptions]
      match first with
      | .error e => (.error e, calls)
      | .ok n =>
        let calls := calls ++ [.features workerDataset workerOptions,
          .generate workerDataset n 3 workerOptions features plugins,
          .hall workerOptions workerDataset, .trace workerOptions]
        match trace with
        | .error e => (.error e, calls)
        | .ok _ =>
          (last.map (fun count => (pop, SymReg.Loss.LossPrecision.round .float64 (.fin (count : Rat)))),
            calls ++ [.size workerOptions])

private theorem customSizeRecreation_holds : customSizeRecreation := by
  intro saved pop headSize first last trace d wd o wo plugins features hsize
  cases headSize with
  | error e => rfl
  | ok n =>
    have hn := hsize n rfl
    cases first <;> cases trace <;> cases last <;>
      simp only [initializePopulation, PopulationSize.read, runInitBind, runInitCall,
        workerSizeAccessor, hn, ite_false] <;> rfl

def population_size_recreation : Prop := stockSizeRecreation ∧ customSizeRecreation

theorem population_size_recreation_holds : population_size_recreation :=
  ⟨stockSizeRecreation_holds, customSizeRecreation_holds⟩

example : ((⟨7, [], 8⟩ : PopulationCopy).members.length : Int) ≠ 1 := by decide

private def scored (costLoss : Member → JF × JF) (m : Member) : Member :=
  { m with cost := (costLoss m).1, loss := (costLoss m).2 }

private theorem map_score_calls (members : List Member) (d o : Nat)
    (costLoss : Member → JF × JF) (trace : List PopInitCall) :
    ((members.mapM (m := PopInitM) fun m => do
      let (cost, loss) ← popInitCall (.score d m o) (.ok (costLoss m))
      pure { m with cost := cost, loss := loss }).run trace) =
      (.ok (members.map (scored costLoss)), trace ++ members.map (fun m => .score d m o)) := by
  apply runInitMapM
  intro member calls
  cases h : costLoss member
  unfold scored
  rw [h]
  rfl

def restored_population_rescored : Prop :=
  ∀ (saved stripped : PopulationCopy) (size verbosity : Int)
    (dataset workerDataset options workerOptions plugins : Nat)
    (costLoss : Member → JF × JF) (unexpected : JlError),
    (saved.members.length : Int) = size → saved.vectorId < stripped.next →
    let (result, calls) := ((initializePopulation (m := PopInitM) (some saved) (.stock size) (.stock size) verbosity
      dataset workerDataset options workerOptions plugins
      (popInitCall .warning (.error unexpected))
      (fun d o => popInitCall (.features d o) (.error unexpected))
      (fun d n len o f p => popInitCall (.generate d n len o f p) (.error unexpected))
      (fun _ _ => pure ⟨[]⟩)
      (fun _ => pure none)
      (fun p o d => popInitCall (.strip p o d) (.ok stripped))
      (fun d m o => popInitCall (.score d m o) (.ok (costLoss m)))).run [])
    (∃ pop, result = .ok (pop, .fin 0) ∧ saved.vectorId < pop.vectorId ∧
      pop.members.map payload = (stripped.members.map (scored costLoss)).map payload ∧
      ∀ member ∈ pop.members, pop.vectorId < member.objectId) ∧
    calls = .strip saved options dataset :: stripped.members.map (fun m => .score dataset m options)

theorem restored_population_rescored_holds : restored_population_rescored := by
  intro saved stripped size verbosity dataset workerDataset options workerOptions plugins costLoss
    unexpected hsize hnext
  simp only [initializePopulation, PopulationSize.read, hsize, ite_true, runInitBind, runInitCall, List.nil_append,
    map_score_calls, runInitPure, List.cons_append]
  refine ⟨⟨_, rfl, hnext, copyMembers_payload _ _, ?_⟩, trivial⟩
  intro member hm
  have hf := (copyMembers_fresh _ _ member hm).1
  exact Nat.lt_of_succ_le hf

example : (⟨7, [], 8⟩ : PopulationCopy).members.length = 0 ∧ 7 < 8 := by decide

 def zero_warmup_preserves : Prop := ∀ (initialized : List (List Reply)),
  (warmupZero initialized).1 = initialized.map (List.map Reply.population) ∧
    ∀ row ∈ (warmupZero initialized).2, ∀ count ∈ row, count = .fin 0
 theorem zero_warmup_preserves_holds : zero_warmup_preserves := by
  intro initialized
  simp [warmupZero, preserveLoaded]

 def initialization_evaluations_counted : Prop := ∀ (initialized : List (List Reply)),
  evaluationTotal (warmupZero initialized).2 =
    evaluationTotal (initialized.map (List.map Reply.evaluations))
 theorem initialization_evaluations_counted_refuted : ¬ initialization_evaluations_counted := by
  intro h
  have hh := h [[unitReply 0 0]]
  exact (by decide +kernel : evaluationTotal (warmupZero [[unitReply 0 0]]).2 ≠
    evaluationTotal ([[unitReply 0 0]].map (List.map Reply.evaluations))) hh

 def merge_stream : Prop := ∀ (h : Hof) (reply : Reply) (maxsize fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  (mergeResult h reply maxsize fresh compute check).map (fun r => (r.1, r.2.2)) =
    (updateManyChecked h (reply.population ++
      (reply.bestSeen.slots.filter Slot.exists).map Slot.member) maxsize fresh compute check).map
      (fun r => (r.1, r.2.2))
 theorem merge_stream_holds : merge_stream := by
  intro h reply maxsize fresh compute check
  rw [checked_many_append_holds]
  unfold mergeResult
  cases hp : updateManyChecked h reply.population maxsize fresh compute check with
  | error e => simp [bind, Except.bind, Except.map]
  | ok triple =>
    rcases triple with ⟨h', ms, f⟩
    cases hs : updateManyChecked h' ((reply.bestSeen.slots.filter Slot.exists).map Slot.member)
      maxsize f compute check <;> simp [hs, bind, Except.bind, pure, Except.pure, Except.map]

private theorem except_map_comp {α β γ : Type} (result : Jl α) (f : α → β) (g : β → γ) :
    (result.map f).map g = result.map (fun value => g (f value)) := by
  cases result <;> rfl

 def merge_best_per_complexity : Prop := ∀ (h : Hof) (reply : Reply) (maxsize fresh k : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  k < h.slots.length →
  (mergeResult h reply maxsize fresh compute check).map (fun result => slotPayload result.1 k) =
    bestChecked k maxsize compute check (slotPayload h k)
      (reply.population ++ (reply.bestSeen.slots.filter Slot.exists).map Slot.member)
 theorem merge_best_per_complexity_holds : merge_best_per_complexity := by
  intro h reply maxsize fresh k compute check hk
  have hs := merge_stream_holds h reply maxsize fresh compute check
  have hm := congrArg (fun r : Jl (Hof × Nat) => r.map (fun x => slotPayload x.1 k)) hs
  rw [except_map_comp, except_map_comp] at hm
  exact hm.trans (checked_all_slots_best_seen_holds h _ maxsize fresh k compute check hk)
example : 0 < (⟨[⟨specimen (.fin 0) (.fin 1), false⟩]⟩ : Hof).slots.length := by decide

 def dataset_single : Prop := ∀ (columns y : List (List JF)) (extra : Nat),
  constructDatasets columns y none none none (.scalar "z") none (.scalar none) extra =
    .ok (y.zipIdx.map fun (target, j) =>
      { data := { columns := columns, y := some target, weights := none }
        index := j + 1, variableNames := none, displayNames := none, targetName := "z",
        xUnits := none, yUnits := none, extra := extra })
 theorem dataset_single_holds : dataset_single := by
  intro columns y extra
  unfold constructDatasets
  apply SymReg.Constraints.mapM_ok
  rintro ⟨target, j⟩ hj
  simp [targetName, targetUnit, bind, Except.bind, pure, Except.pure]

 def dataset_names : Prop := ∀ (variables : Option (List String)) (name : String)
    (names : List String) (j : Nat),
  targetName .automatic variables 1 j =
    .ok (if (variables.getD []).contains "y" then "target" else "y") ∧
  targetName (.scalar name) variables 2 j = .ok name ∧
  targetName (.vector names) variables 2 j = SymReg.Loss.at1 names (j + 1)
 theorem dataset_names_holds : dataset_names := by intro variables name names j; exact ⟨rfl, rfl, rfl⟩

 def dataset_multi_names : Prop := ∀ (outputs j : Nat) (variables : Option (List String)),
  outputs > 1 → targetName .automatic variables outputs j = .ok ("y" ++ subscript (j + 1))
 theorem dataset_multi_names_holds : dataset_multi_names := by
  intro outputs j variables ho
  simp [targetName, ho]
example : (2 : Nat) > 1 := by decide

 def weight_length_check : Prop := ∀ (outputs samples : Nat) (weights : List JF),
  weights.length ≠ outputs * samples → reshapeWeights outputs samples weights =
    .error (.assertionError "weights length")
 theorem weight_length_check_holds : weight_length_check := by
  intro outputs samples weights hn
  simp [reshapeWeights, hn]
example : ([] : List JF).length ≠ 1 * 1 := by decide

 def final_saves : Prop := ∀ (outputs : Nat) (verbosity : Int),
  (infoDump outputs true verbosity).1 = List.range outputs
 theorem final_saves_holds : final_saves := by intro outputs verbosity; rfl

 def frontier_no_repeat : Prop := ∀ (cache : FrontierCache) (entries : List (Nat × JF × JF × Int)),
  (saveFrontier (saveFrontier cache entries).2 entries).1 = false
 theorem frontier_no_repeat_holds : frontier_no_repeat := by
  intro cache entries
  unfold saveFrontier
  split <;> simp_all

 def guess_shape : Prop := ∀ (α : Type) (guesses : List α) (outputs : Nat),
  outputs ≠ 1 → normalizeGuesses (.flat guesses) outputs =
    .error (.argumentError "guesses must be a vector of vectors")
 theorem guess_shape_holds : guess_shape := by
  intro α guesses outputs hn
  simp [normalizeGuesses, hn]
example : (2 : Nat) ≠ 1 := by decide

 def guess_oversize_retained : Prop := ∀ (α : Type) (gs : List α) (maxsize : Nat)
    (parse : α → Member),
  parseGuessLists (.flat gs) 1 maxsize (fun _ g => .ok (parse g)) id id false =
    .ok [gs.map (fun g => (parse g, decide ((parse g).complexity > maxsize)))]
 theorem guess_oversize_retained_holds : guess_oversize_retained := by
  intro α gs maxsize parse
  have hm := SymReg.Constraints.mapM_ok
    (fun g => (.ok (parse g, decide ((parse g).complexity > maxsize)) : Jl (Member × Bool)))
    (fun g => (parse g, decide ((parse g).complexity > maxsize))) gs (by intros; rfl)
  simp [parseGuessLists, normalizeGuesses, hm, bind, Except.bind, pure, Except.pure]

 def runtime_defaults : Prop := ∀ (runId : String), runtimeOptions {} runId =
  .ok { mode := .multithreading, iterations := 10, numprocs := 4, returnState := false,
        verbosity := 1, progress := true, dimOut := 1, workerTimeout := 60, runId := runId }
 theorem runtime_defaults_holds : runtime_defaults := by intro runId; rfl

end SymReg.Search
