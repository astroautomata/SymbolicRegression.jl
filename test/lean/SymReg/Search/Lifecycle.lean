import SymReg.Search.StateData

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

/-- Head-loop state, `src/SearchUtils.jl:887-897`. Outputs have independent halls and
budgets; stopping exits the single shared while loop. -/
structure HeadState where
  outputs : List OutputState
  halls : List Hof
  stopped : Bool := false
  fresh : Nat := 0

structure Observation where
  ready : Bool
  userQuit : Bool
  /-- Poll before relaunch, `src/SymbolicRegression.jl:1211`. -/
  externalBeforeRelaunch : Bool
  /-- Poll after yielding, `src/SymbolicRegression.jl:1287,1339`. -/
  externalStop : Bool
  now : JF

structure SearchConfig where
  populations : Nat
  iterations : Nat
  dimOut : Nat
  returnState : Bool
  progress : Bool := false
  verbosity : Int := 0
  maxsize : Nat
  startTime : JF
  timeout : Option JF := none
  maxEvals : Option Int := none
  earlyStop : EarlyStop := .disabled

/-- The actual visit order is a fixed shuffled list cycled by kappa,
`src/SymbolicRegression.jl:828-831,1109-1113`. -/
def taskAt (order : List (Nat × Nat)) (step : Nat) : Jl (Nat × Nat) :=
  SymReg.Loss.at1 order (step % order.length + 1)

/-- The whole-body ready branch, including relaunch before the end-of-loop checks,
`src/SymbolicRegression.jl:1107-1344`. The evolution reply includes arbitrary evaluation,
plugin and trace results; migration affects the next worker reply supplied by `work`. -/
def headStep (cfg : SearchConfig) (state : HeadState) (key : Nat × Nat)
    (observation : Observation) (work : Nat → Nat → Nat → Reply)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool) : Jl HeadState := do
  if state.stopped || decide ((state.outputs.map OutputState.remaining).sum = 0) then
    return state
  let output ← SymReg.Loss.at1 state.outputs (key.1 + 1)
  let hall ← SymReg.Loss.at1 state.halls (key.1 + 1)
  let updated := collect output key.2 observation.ready observation.externalBeforeRelaunch (work key.1)
  let (halls, fresh) ← if updated.receipts.length ≠ output.receipts.length then do
    let (newHall, _, fresh) ← mergeResult hall (output.cells key.2).pending cfg.maxsize
      state.fresh compute check
    pure (state.halls.set key.1 newHall, fresh)
  else pure (state.halls, state.fresh)
  let outputs := state.outputs.set key.1 updated
  let evaluations := outputs.map fun out =>
    (List.range cfg.populations).map (fun i => (out.cells i).evaluations)
  let stop ← runStopChecks
    (pure (checkLoss halls cfg.earlyStop (fun m => (resolveComplexity compute m).2)))
    (pure observation.userQuit)
    (pure (checkTimeout cfg.startTime (fun _ => observation.now) cfg.timeout).1)
    (pure (checkMaxEvals evaluations cfg.maxEvals))
    (pure observation.externalStop)
  return { outputs := outputs, halls := halls, stopped := stop, fresh := fresh }

/-- Head-loop replay, `src/SymbolicRegression.jl:1107-1348`.
Insufficient observations report exhausted model fuel rather than returning an unfinished search. -/
def mainSearchLoop (cfg : SearchConfig) (order : List (Nat × Nat))
    (observations : List Observation) (step : Nat) (state : HeadState)
    (work : Nat → Nat → Nat → Reply) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool) : Jl HeadState := do
  if state.stopped || decide ((state.outputs.map OutputState.remaining).sum = 0) then
    return state
  match observations with
  | [] => throw (.undefinedBehavior "insufficient scheduler observations")
  | observation :: rest =>
    let key ← taskAt order step
    let updated ← headStep cfg state key observation work compute check
    mainSearchLoop cfg order rest (step + 1) updated work compute check

/-- `equation_search` and `_equation_search`, `src/SymbolicRegression.jl:665-714`.
Initial populations and halls are the outputs of saved-state loading or constructors.
Metadata services are applied outside this bookkeeping projection. -/
def equationSearch (cfg : SearchConfig) (initial : List (Nat → List Member))
    (halls : List Hof) (order : List (Nat × Nat)) (observations : List Observation)
    (work : Nat → Nat → Nat → Reply) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool) : Jl SearchOutput := do
  validateOptions initial.length cfg.dimOut cfg.populations cfg.progress cfg.verbosity
  if halls.length ≠ initial.length then throw (.errorException "DimensionMismatch")
  let outputs := initial.zipIdx.map fun (pops, j) =>
    startOutput cfg.iterations cfg.populations pops (work j)
  let state ← mainSearchLoop cfg order observations 0 ⟨outputs, halls, false, 0⟩ work compute check
  let returnedPopulations := state.outputs.map fun output =>
    (List.range cfg.populations).map (fun i => (tearDown output).cells i |>.lastPopulation)
  formatOutput returnedPopulations state.halls cfg.dimOut cfg.returnState

 def global_stop_all : Prop := ∀ (cfg : SearchConfig) (state : HeadState)
    (key : Nat × Nat) (observation : Observation) (work : Nat → Nat → Nat → Reply)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  state.stopped = true → headStep cfg state key observation work compute check = .ok state

 theorem global_stop_all_holds : global_stop_all := by
  intro cfg state key observation work compute check hs
  simp [headStep, hs, pure, Except.pure]

example : (⟨[], [], true, 0⟩ : HeadState).stopped = true := rfl

 def global_stop_persistent : Prop := ∀ (cfg : SearchConfig) (state : HeadState)
    (order : List (Nat × Nat)) (observations : List Observation) (step : Nat)
    (work : Nat → Nat → Nat → Reply) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool),
  state.stopped = true →
  mainSearchLoop cfg order observations step state work compute check = .ok state

 theorem global_stop_persistent_holds : global_stop_persistent := by
  intro cfg state order observations step work compute check hs
  cases observations <;> simp [mainSearchLoop, hs, pure, Except.pure]

example : (⟨[], [], true, 0⟩ : HeadState).stopped = true := rfl

 def loop_returns_terminal : Prop := ∀ (cfg : SearchConfig) (state result : HeadState)
    (order : List (Nat × Nat)) (observations : List Observation) (step : Nat)
    (work : Nat → Nat → Nat → Reply) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool),
  mainSearchLoop cfg order observations step state work compute check = .ok result →
    result.stopped = true ∨ (result.outputs.map OutputState.remaining).sum = 0
 theorem loop_returns_terminal_holds : loop_returns_terminal := by
  intro cfg state result order observations step work compute check
  induction observations generalizing state step with
  | nil =>
    intro hs
    simp only [mainSearchLoop] at hs
    split at hs
    · rename_i ht
      cases hs
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using ht
    · contradiction
  | cons observation rest ih =>
    intro hs
    simp only [mainSearchLoop] at hs
    split at hs
    · rename_i ht
      cases hs
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using ht
    · cases hk : taskAt order step with
      | error err => simp [hk, bind, Except.bind] at hs
      | ok key =>
        cases hh : headStep cfg state key observation work compute check with
        | error err => simp [hk, hh, bind, Except.bind] at hs
        | ok updated =>
          exact ih updated (step + 1) (by simpa [hk, hh, bind, Except.bind] using hs)

end SymReg.Search
