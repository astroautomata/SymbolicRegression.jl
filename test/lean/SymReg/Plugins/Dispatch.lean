import SymReg.Population.Pop
import SymReg.Population.RegEvol
import SymReg.SimpCons.Cycles
import SymReg.MutateGen.Engine

/-!
`src/Plugin.jl`, SymbolicRegression.jl daae84e5. Heterogeneous Julia tuples are
represented by lists over a sum type chosen by the caller. Mutable hook effects are
returned explicitly. The existing strict-map, member resolver, event, mutation-kind
and middleware models are reused. Pure state values represent independent snapshots;
identity-sensitive custom deepcopy methods are supplied by the caller.
-/
namespace SymReg.Plugins
open DynExpr

/-- `src/Plugin.jl:524-530`: defaults are compared only with the user tuple. -/
def mergeDefaults {P : Type} (kind : P → Nat) (users : List P)
    (defaults : List (Option P)) : List P :=
  users ++ (defaults.filterMap id).filter (fun d => !(users.any (fun p => kind p == kind d)))

/- Source: src/Plugin.jl:131-135
function init_plugin_states(options, dataset)
    return map(options.plugins) do plugin
        init_plugin_state(plugin, options, dataset)
    end
end
-/
def initStates {P S W O D : Type} (factory : P → O → D → W → Jl S × W)
    (options : O) (dataset : D) : List P → W → Jl (List S) × W
  | [], w => (.ok [], w)
  | p :: ps, w =>
    match factory p options dataset w with
    | (.error e, w') => (.error e, w')
    | (.ok s, w') =>
      let (result, w'') := initStates factory options dataset ps w'
      (result.map (List.cons s), w'')

/-- Default observer methods, `src/Plugin.jl:181-183,196-198,213-217,231-233,
285-289,435-437`; only effects are retained, since the engine ignores return values. -/
def defaultObserver {S : Type} (state : S) : S := state

/-- Default conditioners, `src/Plugin.jl:475-477`, preserve the context. -/
def defaultCondition {C : Type} (context : C) : C := context

/-- Default state factory, `src/Plugin.jl:122-124`. -/
def defaultInit {P : Type} (_plugin : P) : Option Unit := none

-- Source: src/Plugin.jl:149
def defaultMutations : List (SymReg.MutateGen.Kind × JF) := []

-- Source: src/Plugin.jl:163
def defaultCrossovers {C : Type} : List (C × JF) := []

-- Source: src/Plugin.jl:392-394
def defaultMember {R : Type} : Option R := none

-- Source: src/Plugin.jl:511-513
def defaultWrapper {R : Type} : Option R := none

-- Source: src/Plugin.jl:338-342
def defaultTournament : JF := .fin 1

-- Source: src/Plugin.jl:304-306
def defaultAcceptance : JF := .fin 1

/- Source: src/Plugin.jl:355-357
function fork_plugin_state(head_state, ::AbstractPlugin, dataset)
    return deepcopy(head_state)
end
-/
def forkState {S W : Type} (copy : S → W → Jl S × W) (head : S) (world : W) :
    Jl S × W × List S :=
  let (result, after) := copy head world
  (result, after, [head])

/- Source: src/Plugin.jl:368-372
function refresh_worker_plugin_state(
    worker_state, latest_head_state, ::AbstractPlugin, dataset
)
    return worker_state
end
-/
def refreshState {S W : Type} (worker _head : S) (world : W) : Jl S × W × List S :=
  (.ok worker, world, [])

/- Source: src/Plugin.jl:460-461; src/Mutations.jl:48-61
prepare_mutation_context(::AbstractMutation) = nothing
prepare_mutation_context(::ConstantMutation) = ConstantMutationContext()
-/
def prepareContext (mutation : SymReg.MutateGen.Kind) (heap : Array JF) :
    Option Nat × Array JF :=
  if mutation = .constant then (some heap.size, heap.push (.fin 1)) else (none, heap)

/-- Conditioner sequencing, `src/Plugin.jl:464-469`, instantiated by
`src/Mutate.jl:322-325,384-387`: the same context is threaded left to right. -/
def conditionAll {P S C : Type} (hook : P → S → C → C × S)
    (plugins : List P) (states : List S) (context : C) : Jl (C × List S) :=
  if plugins.length ≠ states.length then
    throw (.dimensionMismatch "collections must have equal lengths")
  else pure ((plugins.zip states).foldl (fun cs ps =>
    let next := hook ps.1 ps.2 cs.1
    (next.1, cs.2 ++ [next.2])) (context, []))

def merge_preserves_users : Prop := ∀ (P : Type) (kind : P → Nat) users defaults,
  ∃ suffix, mergeDefaults kind users defaults = users ++ suffix

theorem merge_preserves_users_holds : merge_preserves_users := by
  intro P kind users defaults
  exact ⟨_, rfl⟩

private inductive DefaultSuffix {P : Type} (eligible : P → Prop) :
    List (Option P) → List P → Prop where
  | nil : DefaultSuffix eligible [] []
  | absent : DefaultSuffix eligible ds out → DefaultSuffix eligible (none :: ds) out
  | skip : ¬ eligible d → DefaultSuffix eligible ds out →
      DefaultSuffix eligible (some d :: ds) out
  | keep : eligible d → DefaultSuffix eligible ds out →
      DefaultSuffix eligible (some d :: ds) (d :: out)

def merge_default_membership : Prop := ∀ (P : Type) (kind : P → Nat) users defaults,
  ∃ suffix, mergeDefaults kind users defaults = users ++ suffix ∧
    DefaultSuffix (fun d => ∀ p ∈ users, kind p ≠ kind d) defaults suffix

theorem merge_default_membership_holds : merge_default_membership := by
  intro P kind users defaults
  let eligible := fun d => !(users.any (fun p => kind p == kind d))
  refine ⟨(defaults.filterMap id).filter eligible, rfl, ?_⟩
  have he (d : P) : eligible d = true ↔ ∀ p ∈ users, kind p ≠ kind d := by
    simp [eligible, List.any_eq_false]
  induction defaults with
  | nil => exact .nil
  | cons d ds ih =>
    cases d with
    | none => exact .absent ih
    | some d =>
      by_cases h : eligible d = true
      · simpa [h] using DefaultSuffix.keep ((he d).mp h) ih
      · simpa [h] using DefaultSuffix.skip (mt (he d).mpr h) ih

/-- One transition per visited factory; the final transition may throw. -/
inductive InitSequence {P S W : Type} (call : P → W → Jl S × W) :
    List P → W → Jl (List S) → W → Prop where
  | nil : InitSequence call [] w (.ok []) w
  | failure : call p w = (.error e, w') →
      InitSequence call (p :: ps) w (.error e) w'
  | success : call p w = (.ok s, w') → InitSequence call ps w' result w'' →
      InitSequence call (p :: ps) w (result.map (List.cons s)) w''

def init_pairing : Prop := ∀ (P S W O D : Type)
    (factory : P → O → D → W → Jl S × W) plugins options dataset w,
  let (result, w') := initStates factory options dataset plugins w
  InitSequence (fun p w => factory p options dataset w) plugins w result w'

theorem init_pairing_holds : init_pairing := by
  intro P S W O D factory plugins options dataset w
  induction plugins generalizing w with
  | nil => exact .nil
  | cons p ps ih =>
    cases hp : factory p options dataset w with
    | mk result w' =>
      cases result with
      | error error =>
        simpa [initStates, hp] using
          (InitSequence.failure (call := fun p w => factory p options dataset w)
            (p := p) (ps := ps) hp)
      | ok s =>
        specialize ih w'
        cases hr : initStates factory options dataset ps w' with
        | mk result w'' =>
          rw [hr] at ih
          simpa [initStates, hp, hr] using
            InitSequence.success (call := fun p w => factory p options dataset w)
              (p := p) hp ih

def default_neutrality : Prop := ∀ (P S C R L : Type) (p : P)
    (observe : S → Jl S) (condition : C → Jl C) s c
    (useWeight : JF → R) (convertLoss : JF → L) (useLoss : L → R)
    (mutations : List (SymReg.MutateGen.Kind × JF)) (crossovers : List (R × JF))
    (members wrappers : List R),
  (observe s).map defaultObserver = observe s ∧
  (condition c).map defaultCondition = condition c ∧
  (defaultInit p).toList.length = 0 ∧
  mutations ++ defaultMutations = mutations ∧ crossovers ++ defaultCrossovers = crossovers ∧
  members ++ (defaultMember (R := R)).toList = members ∧
  wrappers ++ (defaultWrapper (R := R)).toList = wrappers ∧
  useWeight defaultAcceptance = useWeight (.fin 1) ∧
  useLoss (convertLoss defaultTournament) = useLoss (convertLoss (.fin 1))

theorem default_neutrality_holds : default_neutrality := by
  intro P S C R L p observe condition s c useWeight convertLoss useLoss mutations crossovers members wrappers
  cases observe s <;> cases condition c <;>
    simp [Except.map, defaultObserver, defaultCondition, defaultInit, defaultMutations,
      defaultCrossovers, defaultMember, defaultWrapper, defaultAcceptance, defaultTournament]

def worker_persistence : Prop := ∀ (S W : Type) (copy : S → W → Jl S × W)
    (head worker newer : S) (world : W),
  let (result, after, calls) := forkState copy head world
  let (refreshed, final, refreshCalls) := refreshState worker newer after
  calls = [head] ∧ (result, after) = copy head world ∧
  refreshed = .ok worker ∧ final = after ∧ refreshCalls = []

theorem worker_persistence_holds : worker_persistence := by
  intro S W copy head worker newer world
  cases h : copy head world
  simp [forkState, refreshState, h]

def context_dispatch : Prop := ∀ mutation heap,
  let (object, after) := prepareContext mutation heap
  (mutation = .constant → ∃ id, object = some id ∧ heap.size ≤ id ∧
    after[id]? = some (.fin 1) ∧
    (∀ i, i < heap.size → after[i]? = heap[i]?) ∧
    ∀ id', (prepareContext mutation after).1 = some id' → id ≠ id') ∧
  (mutation ≠ .constant → object = none ∧ after = heap)

theorem context_dispatch_holds : context_dispatch := by
  intro mutation heap
  by_cases h : mutation = .constant
  · subst mutation
    refine ⟨fun _ => ⟨heap.size, rfl, Nat.le_refl _, ?_, ?_, ?_⟩, by simp⟩
    · simp [prepareContext]
    · intro i hi
      simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]
    · simp [prepareContext]
  · simp [prepareContext, h]

def conditioner_order : Prop := ∀ (P S C : Type) (hook : P → S → C → C × S)
    (p q : P) (s t : S) (context : C),
  let first := hook p s context
  let second := hook q t first.1
  conditionAll hook [p, q] [s, t] context = .ok (second.1, [first.2, second.2])

theorem conditioner_order_holds : conditioner_order := by
  intro P S C hook p q s t context
  rfl

/- Source: src/Mutate.jl:275-285; src/Plugin.jl:15-17.
The caller discards the tuple map's results. Retain the effects separately from them. -/
def dispatchObserver {P S R W : Type} (hook : P → S → W → Jl R × W)
    (plugins : List P) (states : List S) (w : W) : Jl Unit × W :=
  if plugins.length ≠ states.length then
    (.error (.dimensionMismatch "collections must have equal lengths"), w)
  else
    let (results, w') := initStates (fun ps _ _ => hook ps.1 ps.2) () ()
      (plugins.zip states) w
    (results.map (fun _ => ()), w')

def hook_pairing : Prop := ∀ (P S R W : Type) (hook : P → S → W → Jl R × W) plugins states w,
  let (result, w') := dispatchObserver hook plugins states w
  (plugins.length ≠ states.length →
    result = .error (.dimensionMismatch "collections must have equal lengths") ∧ w' = w) ∧
  (plugins.length = states.length →
    ∃ returns, InitSequence (fun ps => hook ps.1 ps.2) (plugins.zip states) w returns w' ∧
      result = returns.map (fun _ => ()))

theorem hook_pairing_holds : hook_pairing := by
  intro P S R W hook plugins states w
  by_cases h : plugins.length ≠ states.length
  · have he : dispatchObserver hook plugins states w =
        (.error (.dimensionMismatch "collections must have equal lengths"), w) := by
      unfold dispatchObserver
      rw [if_pos h]
    rw [he]
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun eq => False.elim (h eq)⟩
  · let factory : P × S → Unit → Unit → W → Jl R × W := fun ps _ _ => hook ps.1 ps.2
    have run := init_pairing_holds (P × S) R W Unit Unit factory (plugins.zip states) () () w
    cases hr : initStates factory () () (plugins.zip states) w with
    | mk returns w' =>
      rw [hr] at run
      have he : dispatchObserver hook plugins states w = (returns.map (fun _ => ()), w') := by
        unfold dispatchObserver
        rw [if_neg h]
        change (let (rs, ws) := initStates factory () () (plugins.zip states) w
                (rs.map (fun _ => ()), ws)) = _
        rw [hr]
      rw [he]
      exact ⟨fun hn => False.elim (h hn), fun _ => ⟨returns, run, rfl⟩⟩

def wrapper_order : Prop := ∀ (P R : Type) (outer inner : P → (P → R) → R)
    (base : P → R) (parent : P),
  SymReg.Population.buildStep [some outer, none, some inner] base parent =
    outer parent (fun p => inner p base)

theorem wrapper_order_holds : wrapper_order := by
  intro P R outer inner base parent
  rfl

example : ([1, 2] : List Nat).length = ([3, 4] : List Nat).length := rfl
example : mergeDefaults id [1] [none, some 1, some 2, some 2] = [1, 2, 2] := by decide

end SymReg.Plugins
