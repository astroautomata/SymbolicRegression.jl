import SymReg.Loss.Core

namespace SymReg.SimpCons
open DynExpr SymReg.HeapLemmas

inductive CycleError where
  | dimensionMismatch (message : String)
  | julia (error : JlError)

/-- The world contains the mutable objects denoted by the callback arguments,
including plugin states and the hall of fame. Writes survive exceptions. -/
abbrev CycleAction (W A : Type) := ExceptT CycleError (StateM W) A

private theorem cycleBind_run {W A B : Type} (x : CycleAction W A)
    (f : A → CycleAction W B) (w : W) :
    (x >>= f).run w =
    match x.run w with
    | (.error e, w') => (.error e, w')
    | (.ok a, w') => (f a).run w' := by
  rcases h : x.run w with ⟨r, s⟩
  change x w = (r, s) at h
  cases r <;> simp [Bind.bind, ExceptT.bind, StateT.bind, h, ExceptT.bindCont] <;> rfl

private theorem cyclePure_run {W A : Type} (a : A) (w : W) :
    (pure a : CycleAction W A).run w = (.ok a, w) := rfl

private def runHooks {P S W R : Type} (f : P → S → CycleAction W R) :
    List (P × S) → CycleAction W Unit
  | [] => pure ()
  | (p, s) :: pairs => do
    let _ ← f p s
    runHooks f pairs

-- Source: src/Utils.jl:11-13
/-
@unstable @inline function strictmap(f, xs...)
    allequal(length, xs) || throw(DimensionMismatch("collections must have equal lengths"))
    return map(f, xs...)
end
-/
def hookMap {P S W R : Type} (f : P → S → CycleAction W R)
    (plugins : List P) (states : List S) : CycleAction W Unit := do
  if plugins.length ≠ states.length then
    throw (.dimensionMismatch "collections must have equal lengths")
  else runHooks f (plugins.zip states)

-- Source: src/SingleIteration.jl:69-74
/-
function _on_cycle_start!(plugin_states, cycle_idx, ncycles, options)
    strictmap(options.plugins, plugin_states) do plugin, pstate
        return on_cycle_start!(pstate, plugin, cycle_idx, ncycles, options)
    end
    return nothing
end
-/
def onCycleStart {P S W R : Type} (hook : P → S → Nat → Int → CycleAction W R)
    (plugins : List P) (states : List S) (cycle : Nat) (ncycles : Int) : CycleAction W Unit :=
  hookMap (fun p s => hook p s cycle ncycles) plugins states

-- Source: src/SingleIteration.jl:75-80
/-
function _on_cycle_end!(plugin_states, pop, dataset, best_examples_seen, options)
    strictmap(options.plugins, plugin_states) do plugin, pstate
        return on_cycle_end!(pstate, plugin, pop, dataset, best_examples_seen, options)
    end
    return nothing
end
-/
def onCycleEnd {P S Pop Data Hof W R : Type}
    (hook : P → S → Pop → Data → Hof → CycleAction W R) (plugins : List P) (states : List S)
    (pop : Pop) (dataset : Data) (hof : Hof) : CycleAction W Unit :=
  hookMap (fun p s => hook p s pop dataset hof) plugins states

structure CycleState (Pop Hof : Type) where
  population : Pop
  hallOfFame : Hof
  numEvals : JF

-- Source: src/SingleIteration.jl:47-62
/-
    for cycle_idx in 1:ncycles
        _on_cycle_start!(plugin_states, cycle_idx, ncycles, options)
        pop, tmp_num_evals = reg_evol_cycle(
            batched_dataset,
            pop,
            curmaxsize,
            options,
            trace;
            plugin_states,
            best_seen=best_examples_seen,
            eval_context,
        )
        num_evals += tmp_num_evals
        _update_hall_of_fame_unchecked!(best_examples_seen, pop.members, options)
        _on_cycle_end!(plugin_states, pop, batched_dataset, best_examples_seen, options)
    end
-/
def cycleStep {Plugin S Pop Members Data Hof Context W Start End : Type}
    (startHook : Plugin → S → Nat → Int → CycleAction W Start)
    (endHook : Plugin → S → Pop → Data → Hof → CycleAction W End)
    (evolve : Data → Context → Pop → Hof → List S → CycleAction W (Pop × JF))
    (members : Pop → Members) (updateHof : Hof → Members → CycleAction W Unit)
    (plugins : List Plugin) (states : List S)
    (dataset : Data) (context : Context) (cycle : Nat) (ncycles : Int)
    (state : CycleState Pop Hof) : CycleAction W (CycleState Pop Hof) := do
  onCycleStart startHook plugins states cycle ncycles
  let (pop, n) ← evolve dataset context state.population state.hallOfFame states
  let total := SymReg.Loss.LossPrecision.round .float64 (state.numEvals + n)
  updateHof state.hallOfFame (members pop)
  onCycleEnd endHook plugins states pop dataset state.hallOfFame
  pure ⟨pop, state.hallOfFame, total⟩

-- Source: src/SingleIteration.jl:47
def runCycles {M : Type → Type} [Monad M] {State : Type} (step : Nat → State → M State) :
    Nat → Nat → State → M State
  | 0, _, state => pure state
  | n + 1, i, state => do
    let state ← step i state
    runCycles step n (i + 1) state

-- Source: src/SingleIteration.jl:37-64
/-
    best_examples_seen = HallOfFame(options, dataset)
    num_evals = 0.0

    batched_dataset = if batching_required(options, dataset)
        batch(dataset, get_batch_size(options, dataset.n))
    else
        dataset
    end
    eval_context = create_eval_context(batched_dataset, options, curmaxsize)
-/
def srCycle {Plugin S Pop Members Data Hof Context W Start End : Type}
    (makeHof : Data → CycleAction W Hof) (batchingRequired : Bool)
    (batch : Data → CycleAction W Data) (makeContext : Data → CycleAction W Context)
    (startHook : Plugin → S → Nat → Int → CycleAction W Start)
    (endHook : Plugin → S → Pop → Data → Hof → CycleAction W End)
    (evolve : Data → Context → Pop → Hof → List S → CycleAction W (Pop × JF))
    (members : Pop → Members) (updateHof : Hof → Members → CycleAction W Unit)
    (plugins : List Plugin)
    (dataset : Data) (population : Pop) (pluginStates : List S) (ncycles : Int) :
    CycleAction W (CycleState Pop Hof) := do
  let hof ← makeHof dataset
  let dataset ← if batchingRequired then batch dataset else pure dataset
  let context ← makeContext dataset
  runCycles (cycleStep startHook endHook evolve members updateHof plugins pluginStates dataset context · ncycles)
    ncycles.toNat 1 ⟨population, hof, .fin 0⟩

def pluginLengthError : Prop :=
  ∀ (P S W R : Type) (hook : P → S → CycleAction W R) plugins states w,
    plugins.length ≠ states.length →
    (hookMap hook plugins states).run w =
      (.error (.dimensionMismatch "collections must have equal lengths"), w)

theorem pluginLengthError_holds : pluginLengthError := by
  intro P S W R hook plugins states w h
  simp only [hookMap, if_pos h]
  rfl

def pluginPairing : Prop :=
  ∀ (P S : Type) (plugins : List P) (states : List S) (initial : List (P × S)),
    plugins.length = states.length →
    (hookMap (fun p s => do
        modify fun seen : List (P × S) => seen ++ [(p, s)]
        pure p) plugins states).run initial = (.ok (), initial ++ plugins.zip states)

private theorem cycleHookForOrder {P S : Type} (pairs : List (P × S)) (initial : List (P × S)) :
    (runHooks (fun p s => do
      modify fun seen : List (P × S) => seen ++ [(p, s)]
      pure p) pairs).run initial = (.ok (), initial ++ pairs) := by
  induction pairs generalizing initial with
  | nil => simp [runHooks]; rfl
  | cons pair pairs ih =>
    obtain ⟨p, s⟩ := pair
    simp only [runHooks, cycleBind_run]
    change (runHooks _ pairs).run (initial ++ [(p, s)]) = _
    simpa [List.append_assoc] using ih (initial ++ [(p, s)])

theorem pluginPairing_holds : pluginPairing := by
  intro P S plugins states initial h
  simp only [hookMap, if_neg (not_not_intro h)]
  exact cycleHookForOrder (plugins.zip states) initial

example : ([1] : List Nat).length ≠ ([] : List Nat).length := by decide
example : ([1] : List Nat).length = ([2] : List Nat).length := rfl

example : (hookMap (fun (_ : Nat) (s : Nat) => do
    modify fun seen : List Nat => seen ++ [s]
    (throw (.julia (.userError "hook failed")) : CycleAction (List Nat) Unit)) [1, 2] [9, 8]).run [] =
    (.error (.julia (.userError "hook failed")), [9]) := rfl

/-- Splitting the cycle range preserves the final state and the first error. -/
private def cycleRecurrenceContract : Prop :=
  ∀ (S : Type) (step : Nat → S → Jl S) n i s,
    runCycles step (n + 1) i s = do
      let s ← step i s
      runCycles step n (i + 1) s

private theorem cycleRecurrenceContract_holds : cycleRecurrenceContract := by
  intro S step n i s
  rfl

private def cycleRecurrenceLaw : Prop :=
  ∀ (S : Type) (step : Nat → S → Jl S) n m i s,
    runCycles step (n + m) i s =
      (runCycles step n i s).bind (runCycles step m (i + n))

private theorem cycleRecurrenceLaw_holds : cycleRecurrenceLaw := by
  intro S step n
  induction n with
  | zero =>
    intro m i s
    simp [runCycles, Except.bind, pure, Except.pure]
  | succ n ih =>
    intro m i s
    rw [Nat.succ_add]
    have hindex : i + (n + 1) = i + 1 + n := by omega
    simp only [runCycles, hindex]
    cases h : step i s with
    | error e => simp [h, bind, Except.bind]
    | ok s' => simpa [h, bind, Except.bind] using ih m (i + 1) s'

private def cycleStartSequence : Prop := ∀ n : Int,
  let actual := srCycle (fun (_ : Unit) => pure ()) false (fun _ => pure ())
    (fun _ => pure ()) (fun _ (_ : Unit) index total => do
      modify fun seen : List (Nat × Int) => seen ++ [(index, total)])
    (fun _ _ _ _ _ => pure ()) (fun _ _ _ _ _ => pure ((), .fin 0))
    id (fun _ _ => pure ()) [()] () () [()] n
  (actual.run []).2 = (List.range n.toNat).map (fun i => (i + 1, n))

def cycleRecurrence : Prop := cycleRecurrenceContract ∧ cycleRecurrenceLaw ∧ cycleStartSequence

private theorem cycleStartSequence_holds : cycleStartSequence := by
  intro n
  let step := fun i => cycleStep (fun (_ : Unit) (_ : Unit) index total =>
      modify fun seen : List (Nat × Int) => seen ++ [(index, total)])
    (fun _ _ (_ : Unit) (_ : Unit) (_ : Unit) => pure ())
    (fun _ (_ : Unit) (_ : Unit) (_ : Unit) (_ : List Unit) => pure ((), JF.fin 0))
    id (fun _ _ => pure ()) [()] [()] () () i n
  have hstep (i : Nat) (s : CycleState Unit Unit) (w : List (Nat × Int)) :
      (step i s).run w = (.ok ⟨(), (), Loss.LossPrecision.round .float64 (s.numEvals + .fin 0)⟩,
        w ++ [(i, n)]) := by
    cases s with
    | mk p h e => cases p; cases h; rfl
  have hrun (k i : Nat) (s : CycleState Unit Unit) (w : List (Nat × Int)) :
      ((runCycles step k (i + 1) s).run w).2 =
        w ++ (List.range' i k).map (fun j => (j + 1, n)) := by
    induction k generalizing i s w with
    | zero => simp [runCycles, cyclePure_run]
    | succ k ih =>
      simp only [runCycles, cycleBind_run, hstep, List.range'_succ, List.map_cons]
      rw [ih, List.append_assoc]
      rfl
  change ((runCycles step n.toNat (0 + 1) ⟨(), (), .fin 0⟩).run []).2 = _
  simpa [List.range_eq_range'] using hrun n.toNat 0 ⟨(), (), .fin 0⟩ []

theorem cycleRecurrence_holds : cycleRecurrence :=
  ⟨cycleRecurrenceContract_holds, cycleRecurrenceLaw_holds, cycleStartSequence_holds⟩


/-- Zero and negative cycle counts run initialization, including ordinary
batch selection, with no cycle hooks or evolution. -/
def emptyCycleRange : Prop :=
  ∀ (Plugin S Pop Members Data Hof Context W Start End : Type)
    (makeHof : Data → CycleAction W Hof) batchingRequired
    (batch : Data → CycleAction W Data) (makeContext : Data → CycleAction W Context)
    (startHook : Plugin → S → Nat → Int → CycleAction W Start)
    (endHook : Plugin → S → Pop → Data → Hof → CycleAction W End)
    (evolve : Data → Context → Pop → Hof → List S → CycleAction W (Pop × JF))
    (members : Pop → Members) updateHof plugins (dataset : Data) (population : Pop)
    pluginStates (ncycles : Int) w,
    ncycles ≤ 0 →
    (srCycle makeHof batchingRequired batch makeContext startHook endHook evolve members updateHof
      plugins dataset population pluginStates ncycles).run w =
    match (makeHof dataset).run w with
    | (.error e, w') => (.error e, w')
    | (.ok hof, w') =>
      match (if batchingRequired then (batch dataset).run w' else (.ok dataset, w')) with
      | (.error e, w'') => (.error e, w'')
      | (.ok data, w'') =>
        match (makeContext data).run w'' with
        | (.error e, final) => (.error e, final)
        | (.ok _, final) => (.ok ⟨population, hof, .fin 0⟩, final)

theorem emptyCycleRange_holds : emptyCycleRange := by
  intro Plugin S Pop Members Data Hof Context W Start End makeHof required batch makeContext
    startHook endHook evolve members updateHof plugins dataset pop states ncycles w hn
  have hz : ncycles.toNat = 0 := by omega
  cases required <;>
    simp only [srCycle, hz, runCycles, Bool.false_eq_true, ite_false, ite_true,
      cycleBind_run, cyclePure_run]
  all_goals split <;> (try simp_all) <;> (try rfl)
  all_goals split <;> (try simp_all) <;> (try rfl)
  all_goals split <;> simp_all

/-- An evolution exception retains the world left by evolution and stops the
cycle loop before any hall-of-fame update or end hook. -/
def evolutionFailureStops : Prop :=
  ∀ (Plugin S Pop Members Data Hof Context W Start End : Type)
    (startHook : Plugin → S → Nat → Int → CycleAction W Start)
    (endHook : Plugin → S → Pop → Data → Hof → CycleAction W End)
    (evolve : Data → Context → Pop → Hof → List S → CycleAction W (Pop × JF))
    (members : Pop → Members) updateHof plugins states dataset context cycle ncycles remaining
    (state : CycleState Pop Hof) w started final err,
    (onCycleStart startHook plugins states cycle ncycles).run w = (.ok (), started) →
    (evolve dataset context state.population state.hallOfFame states).run started =
        (.error err, final) →
    (runCycles (cycleStep startHook endHook evolve members updateHof plugins states dataset context · ncycles)
       (remaining + 1) cycle state).run w = (.error err, final)

theorem evolutionFailureStops_holds : evolutionFailureStops := by
  intro Plugin S Pop Members Data Hof Context W Start End startHook endHook evolve members updateHof
    plugins states data context cycle ncycles remaining state w started final err hs he
  simp only [runCycles, cycleStep, cycleBind_run, hs, he]

/-- Observe the callback arguments and returned accounting for one completed
cycle; distinct old and new population values distinguish forwarding errors. -/
def cycleAccounting : Prop :=
  ∀ (old next hof plugin pstate data context : Nat) (cycle : Nat) (ncycles : Int)
    (members : Nat → Nat) (initial reported : JF),
    SymReg.Loss.LossPrecision.round .float64 initial = initial →
    SymReg.Loss.LossPrecision.round .float64 reported = reported →
    let run := cycleStep
      (fun (p s : Nat) i n => modify fun log : List (List Int) => log ++ [(0 : Int) :: [p, s, i, n]])
      (fun (p s pop d h : Nat) => modify fun log : List (List Int) => log ++ [(3 : Int) :: [p, s, pop, d, h]])
      (fun (d c pop h : Nat) (_ : List Nat) => do
        modify fun log : List (List Int) => log ++ [(1 : Int) :: [d, c, pop, h]]
        pure (next, reported))
      members (fun (h vector : Nat) => modify fun log : List (List Int) => log ++ [(2 : Int) :: [h, vector]])
      [plugin] [pstate] data context cycle ncycles ⟨old, hof, initial⟩
    run.run [] = (.ok ⟨next, hof, SymReg.Loss.LossPrecision.round .float64 (initial + reported)⟩,
      [(0 : Int) :: [plugin, pstate, cycle, ncycles], (1 : Int) :: [data, context, old, hof],
        (2 : Int) :: [hof, members next], (3 : Int) :: [plugin, pstate, next, data, hof]])

theorem cycleAccounting_holds : cycleAccounting := by
  intro old next hof plugin pstate data context cycle ncycles members initial reported _ _
  rfl

end SymReg.SimpCons
