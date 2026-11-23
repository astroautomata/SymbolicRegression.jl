import SymReg.HofMig.Core

namespace SymReg.Infra
open DynExpr
open SymReg.HofMig (Member payload copyMember)

/-- Per-attempt trace keys, src/Tracing.jl:28-46. General result/reason values
remain runtime identity tokens; the standard handlers use strings. -/
structure StepTrace where
  type : Option String := none
  result : Option String := none
  reason : Option String := none
  id : Nat := 0
  deriving DecidableEq, Repr

-- Source: src/Tracing.jl:10-14
-- @inline new_trace(options::AbstractOptions) = new_trace(options.use_tracing)
-- @inline new_trace(::Val{enabled}) where {enabled} = enabled ? TraceType() : nothing
-- @inline new_trace(trace::MaybeTrace) = isnothing(trace) ? nothing : TraceType()
-- @inline new_step_trace(steps) = isnothing(steps) ? nothing : TraceType()
def newTrace (enabled : Bool) (fresh : Nat) : Option StepTrace × Nat :=
  if enabled then (some { id := fresh },fresh + 1) else (none,fresh)

structure TracedSteps (α : Type) where
  id : Nat
  items : List α

def newStepTrace {α : Type} (steps : Option (TracedSteps α)) (fresh : Nat) :
    Option StepTrace × Nat := newTrace steps.isSome fresh

def traceType (trace : Option StepTrace) (type : String) : Option StepTrace :=
  trace.map (fun t => { t with type := some type })

def traceResult (trace : Option StepTrace) (result reason : String) : Option StepTrace :=
  trace.map (fun t => { t with result := some result, reason := some reason })

def traceIdentity (trace : Option StepTrace) : Option StepTrace :=
  trace.map (fun t => { t with
    type := some "identity"
    result := some "accept"
    reason := some "identity" })

-- Source: src/Tracing.jl:16-18,26
-- @inline function new_traced_steps(trace::MaybeTrace, ::Type{P}) where {P}
--     return isnothing(trace) ? nothing : Tuple{P,P,TraceType}[]
-- end
-- @inline reset_traced_steps!(steps) = isnothing(steps) ? nothing : empty!(steps)
abbrev TraceAttempt := Member × Member × StepTrace

def newTracedSteps (trace : Option StepTrace) (fresh : Nat) :
    Option (TracedSteps TraceAttempt) × Nat :=
  match trace with | none => (none,fresh) | some _ => (some ⟨fresh,[]⟩,fresh+1)

def resetTracedSteps {α : Type} (steps : Option (TracedSteps α)) :
    Option (TracedSteps α) := steps.map (fun v => { v with items := [] })

-- Source: src/Tracing.jl:20-24
-- @inline function trace_mutation_step!(steps, parent, member, trace::MaybeTrace)
--     isnothing(trace) && return nothing
--     push!(steps, (copy(parent), copy(member), trace))
--     return nothing
-- end
def traceMutationStep (steps : TracedSteps TraceAttempt)
    (parent child : Member) (trace : Option StepTrace) (fresh : Nat) :
    TracedSteps TraceAttempt × Nat :=
  match trace with
  | none => (steps,fresh)
  | some t =>
    let (p,f) := copyMember parent fresh
    let (c,g) := copyMember child f
    ({steps with items := steps.items ++ [(p,c,t)]},g)

def traceEnabled : Prop := ∀ (live : List Nat) (fresh : Nat) t type result reason (steps : TracedSteps Nat),
  (∀ id ∈ live, id < fresh) →
  newTrace false fresh = (none,fresh) ∧
  newTrace true fresh = (some ⟨none,none,none,fresh⟩,fresh+1) ∧
  fresh ∉ live ∧
  (newTrace true (fresh+1)).1 = some ⟨none,none,none,fresh+1⟩ ∧
  traceType none type = none ∧ traceResult none result reason = none ∧
  traceIdentity none = none ∧
  traceIdentity (some t) = some ⟨some "identity",some "accept",some "identity",t.id⟩ ∧
  newTracedSteps none fresh = (none,fresh) ∧
  newTracedSteps (some t) fresh = (some ⟨fresh,[]⟩,fresh+1) ∧
  resetTracedSteps (none : Option (TracedSteps Nat)) = none ∧
  resetTracedSteps (some steps) = some ⟨steps.id,[]⟩ ∧
  newStepTrace (none : Option (TracedSteps Nat)) fresh = (none,fresh) ∧
  newStepTrace (some steps) fresh = (some ⟨none,none,none,fresh⟩,fresh+1)

theorem traceEnabled_holds : traceEnabled := by
  intro live fresh t type result reason steps h
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  intro hm
  exact (Nat.lt_irrefl fresh) (h fresh hm)
example : ∀ id ∈ ([0] : List Nat), id < 1 := by simp

private def memberIds (m : Member) := [m.objectId,m.treeId]

def traceStepCopies : Prop := ∀ steps parent child trace fresh otherLive,
  let live := memberIds parent ++ memberIds child ++ [trace.id, steps.id] ++
    steps.items.flatMap (fun (p,c,t) => memberIds p ++ memberIds c ++ [t.id]) ++ otherLive
  (∀ id ∈ live, id < fresh) →
  (∃ p c,
    traceMutationStep steps parent child (some trace) fresh =
      (⟨steps.id,steps.items ++ [(p,c,trace)]⟩,fresh+4) ∧
    payload p = payload parent ∧ payload c = payload child ∧
    p.lossNegativeZero = parent.lossNegativeZero ∧ c.lossNegativeZero = child.lossNegativeZero ∧
    (memberIds p ++ memberIds c).Nodup ∧
    ∀ id ∈ memberIds p ++ memberIds c, id ∉ live) ∧
  traceMutationStep steps parent child none fresh = (steps,fresh)

theorem traceStepCopies_holds : traceStepCopies := by
  unfold traceStepCopies
  intro steps parent child trace fresh otherLive live h
  refine ⟨?_,rfl⟩
  refine ⟨(copyMember parent fresh).1,(copyMember child (fresh+2)).1,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [traceMutationStep,copyMember] <;> omega
  · simp [memberIds,copyMember] <;> omega
  · intro id hm hl
    have lt := h id hl
    simp [memberIds,copyMember] at hm
    omega
example : ∀ id ∈ ([0,1,2,3,4,5] : List Nat), id < 6 := by simp

/-- Population snapshots record all seven source fields, src/Tracing.jl:83-95.
Tree rendering and complexity resolution are arbitrary external services. -/
structure MemberSnapshot where
  tree : String
  loss : JF
  cost : JF
  complexity : Int
  birth : Int
  reference : Int
  parent : Int
  deriving DecidableEq, Repr

def tracePopulation (members : List Member) (render : Member → String)
    (complexity : Member → Int) : List MemberSnapshot :=
  members.map fun m => ⟨render m,m.loss,m.cost,complexity m,m.birth,m.reference,m.parent⟩

/-- Source event schemas, src/Tracing.jl:124-136,159-170,201-215.
Time is supplied explicitly. details retain the mutation record id. -/
inductive TraceEvent where
  | mutate (time : Nat) (child : Int) (selected : Bool) (details : Nat)
  | tuning (time : Nat) (child : Int) (mutationType : String)
  | crossover (time : Nat) (parent1 parent2 child1 child2 : Int) (details : Nat)
  | death (time : Nat)
  deriving DecidableEq, Repr

structure MutationEntry where
  tree : String
  cost : JF
  loss : JF
  parent : Int
  events : List TraceEvent := []
  snapshot : Option MemberSnapshot := none
  deriving DecidableEq, Repr

abbrev MutationDictionary := Int → Option MutationEntry

def putMutation (d : MutationDictionary) (key : Int) (v : MutationEntry) : MutationDictionary :=
  fun k => if k = key then some v else d k

/-- _trace_member! creates once by string(member.ref), src/Tracing.jl:97-109.
Integer keys are lossless: decimal string conversion is injective on Julia Int.
Repeated refs preserve the first snapshot, even if later fields have changed. -/
def traceMember (d : MutationDictionary) (m : Member) (render : Member → String) :
    MutationDictionary :=
  match d m.reference with
  | some _ => d
  | none => putMutation d m.reference ⟨render m,m.cost,m.loss,m.parent,[],none⟩

def appendEvents (d : MutationDictionary) (key : Int) (events : List TraceEvent) :
    MutationDictionary :=
  match d key with
  | none => d
  | some entry => putMutation d key { entry with events := entry.events ++ events }

/-- Parent-keyed mutation event schema, src/Tracing.jl:158-166. -/
def mutationEvent (parent child : Member) (index selected time details : Nat) :
    Int × TraceEvent :=
  (parent.reference,.mutate time child.reference (index == selected) details)

/-- Shared event attached to both crossover parents, src/Tracing.jl:201-213. -/
def crossoverEvent (p1 p2 c1 c2 : Member) (time details : Nat) : TraceEvent :=
  .crossover time p1.reference p2.reference c1.reference c2.reference details

/-- Mutation attempts, src/Tracing.jl:140-173. All members are inserted before
any event, selected_attempt_idx is one-based, and death is conditional on replacement. -/
def traceAttempts (d : MutationDictionary) (steps : List (Member × Member × Nat))
    (oldest : Member) (replace : Bool) (selected : Nat) (time : Nat → Nat)
    (render : Member → String) : MutationDictionary :=
  let members := (if replace then [oldest] else []) ++ steps.flatMap (fun (p,c,_) => [p,c])
  let d := members.foldl (fun d m => traceMember d m render) d
  let d := (steps.zipIdx 1).foldl (fun d ((p,c,t),i) =>
    let event := mutationEvent p c i selected (time i) t
    appendEvents d event.1 [event.2]) d
  if replace then appendEvents d oldest.reference [.death (time (steps.length+1))] else d

/-- Crossover records the same four-reference event on BOTH parents and one
death per replaced slot, including repeated references, src/Tracing.jl:175-217. -/
def traceCrossover (d : MutationDictionary) (p1 p2 c1 c2 old1 old2 : Member)
    (details time death1 death2 : Nat) (render : Member → String) : MutationDictionary :=
  let d := [p1,p2,c1,c2,old1,old2].foldl (fun d m => traceMember d m render) d
  let event := crossoverEvent p1 p2 c1 c2 time details
  let d := appendEvents d p1.reference [event]
  let d := appendEvents d p2.reference [event]
  let d := appendEvents d old1.reference [.death death1]
  appendEvents d old2.reference [.death death2]

structure OptimizationState where
  mutations : MutationDictionary
  eventVector : Int → Option Nat
  next : Nat

-- Source: src/Tracing.jl:114-137
-- isnothing(trace) && return nothing
-- @assert haskey(trace, "mutations")
-- mutations = trace["mutations"]::TraceType
-- _trace_member!(mutations, member, options)
-- mutation_type = if optimized && options.should_optimize_constants
--     "simplification_and_optimization"
-- else
--     "simplification"
-- end
-- tuning_event = TraceType(
--     "type" => "tuning",
--     "time" => time(),
--     "child" => new_ref,
--     "mutation" => TraceType("type" => mutation_type),
-- )
-- death_event = TraceType("type" => "death", "time" => time())
-- old_entry = get!(mutations, string(old_ref)) do
--     entry = copy(first(member for member in trace["members"] if member["ref"] == old_ref))
--     entry["events"] = Vector{TraceType}()
--     entry
-- end
-- push!(old_entry["events"], tuning_event, death_event)
-- return nothing
def traceOptimization (state : Option OptimizationState) (m : Member) (oldRef newRef : Int)
    (optimized shouldOptimize : Bool) (time death : Nat)
    (render : Member → Jl String) (snapshots : List MemberSnapshot) :
    Jl Unit × Option OptimizationState :=
  match state with
  | none => (.ok (),none)
  | some before =>
    let inserted : Jl OptimizationState :=
      match before.mutations m.reference with
      | some _ => .ok before
      | none => do
        let tree ← render m
        pure { mutations := putMutation before.mutations m.reference ⟨tree,m.cost,m.loss,m.parent,[],none⟩
               eventVector := fun k => if k = m.reference then some before.next else before.eventVector k
               next := before.next + 1 }
    match inserted with
    | .error e => (.error e,some before)
    | .ok after =>
      let mutationType := if optimized && shouldOptimize then
        "simplification_and_optimization" else "simplification"
      let events := [.tuning time newRef mutationType,.death death]
      match after.mutations oldRef with
      | some _ =>
        (.ok (),some {after with mutations := appendEvents after.mutations oldRef events})
      | none =>
        match snapshots.find? (fun s => s.reference == oldRef) with
        | none => (.error (.argumentError "collection must be non-empty"),some after)
        | some s =>
          (.ok (),some {
            mutations := putMutation after.mutations oldRef ⟨s.tree,s.cost,s.loss,s.parent,events,some s⟩
            eventVector := fun k => if k = oldRef then some after.next else after.eventVector k
            next := after.next + 1 })

structure IterationTrace where
  schemaVersion : Nat := 1
  recordType : String := "iteration"
  output : Nat
  population : Nat
  iteration : Int
  startedAt : Nat
  members : List MemberSnapshot
  mutations : MutationDictionary

/-- trace_iteration_start!, src/Tracing.jl:68-81. Mutations start empty and the
population snapshot precedes mutation, retaining the original ref/parent links. -/
def traceIterationStart (output population : Nat) (iteration : Int) (time : Nat)
    (members : List Member) (render : Member → String) (complexity : Member → Int) :
    IterationTrace :=
  ⟨1,"iteration",output,population,iteration,time,
    tracePopulation members render complexity,fun _ => none⟩

/-- next_trace_iteration, src/Tracing.jl:64-66. Outer none is disabled tracing;
an enabled trace with no iteration field throws KeyError. -/
inductive TraceIterationError where
  | keyError (key : String)

def nextTraceIteration : Option (Option Int) → Except TraceIterationError Int
  | none => .ok 0
  | some none => .error (.keyError "iteration")
  | some (some iteration) => .ok (iteration+1)

inductive HeaderValue where
  | int (n : Nat)
  | text (s : String)
  | time (t : JF)
  deriving DecidableEq

structure SearchTrace where
  id : Nat
  fields : String → Option HeaderValue

abbrev TraceWrite := Nat × String × Bool

private def populatedFields (fields : String → Option HeaderValue) (time : JF)
    (options : Option String) : String → Option HeaderValue
  | "schema_version" => some (.int 1)
  | "record_type" => some (.text "search")
  | "started_at" => some (.time time)
  | "options" => (options.map HeaderValue.text).or (fields "options")
  | k => fields k

-- Source: src/Tracing.jl:48-57
-- @inline function initialize_trace!(trace::MaybeTrace, options, filename)
--     isnothing(trace) && return nothing
--     trace["schema_version"] = TRACE_SCHEMA_VERSION
--     trace["record_type"] = "search"
--     trace["started_at"] = time()
--     trace["options"] = string(options)
--     write_trace(trace, filename; append=false)
--     empty!(trace)
--     return nothing
-- end
def initializeTrace (trace : Option SearchTrace) (time : JF) (options : Jl String) (filename : String)
    (write : SearchTrace → String → Bool → Jl Unit) :
    Jl Unit × Option SearchTrace × List TraceWrite :=
  match trace with
  | none => (.ok (),none,[])
  | some before =>
    match options with
    | .error e =>
      (.error e, some ⟨before.id,populatedFields before.fields time none⟩, [])
    | .ok text =>
      let header : SearchTrace := ⟨before.id,populatedFields before.fields time (some text)⟩
      let call := [(header.id,filename,false)]
      match write header filename false with
      | .error e => (.error e,some header,call)
      | .ok () => (.ok (),some { header with fields := fun _ => none },call)

def writeTrace (trace : Option StepTrace) (append : Bool)
    (write : StepTrace → Bool → Jl Unit) : Jl Unit :=
  match trace with | none => .ok () | some t => write t append

def traceMemberFirstWins : Prop := ∀ d m render entry,
  d m.reference = some entry → traceMember d m render = d

theorem traceMemberFirstWins_holds : traceMemberFirstWins := by
  intros d m render entry h; simp [traceMember,h]
example : (fun _ : Int => some (⟨"x",.fin 0,.fin 0,-1,[],none⟩ : MutationEntry)) 0 =
    some ⟨"x",.fin 0,.fin 0,-1,[],none⟩ := rfl

def traceMemberInserted : Prop := ∀ d m render,
  d m.reference = none →
  (traceMember d m render) m.reference =
    some ⟨render m,m.cost,m.loss,m.parent,[],none⟩

theorem traceMemberInserted_holds : traceMemberInserted := by
  intros d m render h; simp [traceMember,h,putMutation]
example : (fun _ : Int => (none : Option MutationEntry)) 0 = none := rfl

def tracePopulationLinks : Prop := ∀ members render complexity,
  (tracePopulation members render complexity).map (fun m => (m.reference,m.parent)) =
    members.map (fun m => (m.reference,m.parent))

theorem tracePopulationLinks_holds : tracePopulationLinks := by
  intro members render complexity; simp [tracePopulation,List.map_map]

def traceIterationSchema : Prop := ∀ output population iteration time members render complexity key,
  let t := traceIterationStart output population iteration time members render complexity
  t.schemaVersion = 1 ∧ t.recordType = "iteration" ∧ t.output = output ∧
  t.population = population ∧ t.iteration = iteration ∧ t.mutations key = none ∧
  nextTraceIteration (some (some t.iteration)) = .ok (iteration + 1)

theorem traceIterationSchema_holds : traceIterationSchema := by
  intro output population iteration time members render complexity key
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def traceWriteForwarding : Prop := ∀ t append write time options filename,
  writeTrace none append write = .ok () ∧
  writeTrace (some t) append write = write t append ∧
  initializeTrace none time options filename (fun _ _ _ => .error .boundsError) = (.ok (),none,[])

theorem traceWriteForwarding_holds : traceWriteForwarding := by
  intro t append write time options filename; exact ⟨rfl,rfl,rfl⟩

private def traceEventLinksContract : Prop := ∀ parent child p2 c2 index selected time details,
  mutationEvent parent child index selected time details =
    (parent.reference,.mutate time child.reference (index == selected) details) ∧
  crossoverEvent parent p2 child c2 time details =
    .crossover time parent.reference p2.reference child.reference c2.reference details

private theorem traceEventLinksContract_holds : traceEventLinksContract := by
  intro parent child p2 c2 index selected time details; exact ⟨rfl,rfl⟩

private def traceEventLinksLaw : Prop := ∀ d parent child oldest selected time details render entry,
  d parent.reference = some entry → parent.reference ≠ child.reference →
  (traceAttempts d [(parent, child, details)] oldest false selected time render parent.reference).map
    MutationEntry.events = some (entry.events ++ [.mutate (time 1) child.reference (1 == selected) details])

private theorem traceEventLinksLaw_holds : traceEventLinksLaw := by
  intro d parent child oldest selected time details render entry hp hne
  have hn : child.reference ≠ parent.reference := Ne.symm hne
  simp [traceAttempts, traceMember, appendEvents, mutationEvent, putMutation, hp, hne, hn,
    List.zipIdx]
  split <;> simp_all [putMutation, hp, hne]

private def traceDictionaryLinks : Prop :=
  (∀ d steps oldest replace selected time render key,
    let byParent := (steps.zipIdx 1).filterMap fun ((parent, child, details), index) =>
      if parent.reference = key then some (.mutate (time index) child.reference (index == selected) details) else none
    let death := if replace && oldest.reference == key then [.death (time (steps.length + 1))] else []
    let before := ((d key).map MutationEntry.events).getD []
    ((traceAttempts d steps oldest replace selected time render key).map MutationEntry.events).getD [] =
      before ++ byParent ++ death) ∧
  ∀ d p1 p2 c1 c2 old1 old2 details time death1 death2 render key,
    let event : TraceEvent := .crossover time p1.reference p2.reference c1.reference c2.reference details
    let before := ((d key).map MutationEntry.events).getD []
    ((traceCrossover d p1 p2 c1 c2 old1 old2 details time death1 death2 render key).map MutationEntry.events).getD [] =
      before ++ (if p1.reference = key then [event] else []) ++
      (if p2.reference = key then [event] else []) ++
      (if old1.reference = key then [.death death1] else []) ++
      (if old2.reference = key then [.death death2] else [])

def traceEventLinks : Prop := traceEventLinksContract ∧ traceEventLinksLaw ∧ traceDictionaryLinks

def traceOptimizationLinks : Prop := ∀ before member oldRef newRef optimized enabled time death render snapshots tree,
  render member = .ok tree →
  let (outcome, updated) := traceOptimization (some before) member oldRef newRef
    optimized enabled time death render snapshots
  let wording := if optimized = true ∧ enabled = true then
    "simplification_and_optimization" else "simplification"
  let additions := [.tuning time newRef wording,.death death]
  ∃ after, updated = some after ∧
    (∀ existing, before.mutations oldRef = some existing →
      outcome = .ok () ∧
      (after.mutations oldRef).map MutationEntry.events = some (existing.events ++ additions) ∧
      after.eventVector oldRef = before.eventVector oldRef) ∧
    (before.mutations oldRef = none → oldRef ≠ member.reference →
      match snapshots.find? (fun s => s.reference == oldRef) with
      | none => outcome = .error (.argumentError "collection must be non-empty") ∧
        (after.mutations member.reference).isSome = true
      | some snapshot => outcome = .ok () ∧
        (after.mutations oldRef).map MutationEntry.snapshot = some (some snapshot) ∧
        (after.mutations oldRef).map MutationEntry.events = some additions ∧
        after.eventVector oldRef = some (if (before.mutations member.reference).isSome
          then before.next else before.next + 1)) ∧
    (before.mutations member.reference = none →
      (after.mutations member.reference).map MutationEntry.tree = some tree)

def traceInitialization : Prop := ∀ trace time options filename write,
  let result := initializeTrace (some trace) time (.ok options) filename write
  let atWrite := fun (fields : String → Option HeaderValue) =>
    fields "schema_version" = some (.int 1) ∧
    fields "record_type" = some (.text "search") ∧
    fields "started_at" = some (.time time) ∧
    fields "options" = some (.text options) ∧
    ∀ k, k ∉ (["schema_version","record_type","started_at","options"] : List String) →
      fields k = trace.fields k
  (∃ fields, atWrite fields ∧
    result.2.2 = [(trace.id,filename,false)] ∧
    match write ⟨trace.id,fields⟩ filename false with
    | .ok () => result.1 = .ok () ∧ result.2.1 = some ⟨trace.id, fun _ => none⟩
    | .error e => result.1 = .error e ∧ result.2.1 = some ⟨trace.id,fields⟩) ∧
  (∀ e, ∃ fields,
    initializeTrace (some trace) time (.error e) filename write =
      (.error e,some ⟨trace.id,fields⟩,[]) ∧
    fields "schema_version" = some (.int 1) ∧
    fields "record_type" = some (.text "search") ∧
    fields "started_at" = some (.time time) ∧
    ∀ k, k ∉ (["schema_version","record_type","started_at"] : List String) →
      fields k = trace.fields k) ∧
  nextTraceIteration none = .ok 0 ∧
  nextTraceIteration (some none) = .error (.keyError "iteration")

theorem traceInitialization_holds : traceInitialization := by
  intro trace time options filename write
  let header := populatedFields trace.fields time (some options)
  refine ⟨⟨header,⟨rfl,rfl,rfl,rfl,?_⟩,?_,?_⟩,?_,rfl,rfl⟩
  · intro k h
    have h1 : k ≠ "schema_version" := fun eq => h (by simp [eq])
    have h2 : k ≠ "record_type" := fun eq => h (by simp [eq])
    have h3 : k ≠ "started_at" := fun eq => h (by simp [eq])
    have h4 : k ≠ "options" := fun eq => h (by simp [eq])
    unfold header populatedFields
    split <;> first | contradiction | rfl
  · unfold initializeTrace
    change (match write ⟨trace.id,header⟩ filename false with
      | .error e => ((.error e : Jl Unit),some (⟨trace.id,header⟩ : SearchTrace),[(trace.id,filename,false)])
      | .ok _ => (.ok (),some ⟨trace.id,fun _ => none⟩,[(trace.id,filename,false)])).2.2 = _
    cases write ⟨trace.id,header⟩ filename false <;> rfl
  · cases h : write ⟨trace.id,header⟩ filename false <;>
      dsimp [header] at h <;> simp [initializeTrace, h] <;> rfl
  · intro e
    refine ⟨populatedFields trace.fields time none,rfl,rfl,rfl,rfl,?_⟩
    intro k h
    have h1 : k ≠ "schema_version" := fun eq => h (by simp [eq])
    have h2 : k ≠ "record_type" := fun eq => h (by simp [eq])
    have h3 : k ≠ "started_at" := fun eq => h (by simp [eq])
    unfold populatedFields
    split <;> first | contradiction | rfl

end SymReg.Infra
