import SymReg.Loss.Core

namespace SymReg.Infra
open DynExpr

inductive WorkloadType where
  | float32 | float64
  deriving DecidableEq

-- Source: src/precompile.jl:13-14
-- const PRECOMPILE_FLOAT64 = @load_preference("precompile_float64", true)
-- const PRECOMPILE_TYPES = PRECOMPILE_FLOAT64 ? (Float32, Float64) : (Float32,)
def precompileTypes (float64 : Option Bool) : List WorkloadType :=
  if float64.getD true then [.float32,.float64] else [.float32]

inductive WorkloadMacro where
  | setup | compile
  deriving DecidableEq

inductive KeywordValue where
  | integer (n : Int) | flag (enabled : Bool) | symbol (name : String)
  | identity (id : Nat) | nothing | operators (names : List String)
  | floating (x : JF) | weights (values : List (String × JF))

abbrev WorkloadKeywords := List (String × KeywordValue)

inductive WorkloadCall where
  | invokeMacro (kind : WorkloadMacro)
  | beginType (type : WorkloadType)
  | randomArray (type : WorkloadType) (shape : List Nat)
  | options (keywords : WorkloadKeywords)
  | search (x y : Nat) (keywords : WorkloadKeywords)
  | frontier (hall : Nat)
  | buffer
  | serialize (buffer value : Nat)
  | rewind (buffer : Nat)
  | deserialize (buffer : Nat)

abbrev WorkloadM := ExceptT JlError (StateM (List WorkloadCall))

private def observeWorkload {α : Type} (call : WorkloadCall) (result : Jl α) : WorkloadM α :=
  ExceptT.mk fun calls => (result,calls ++ [call])

-- Source: src/precompile.jl:20-28,35-43
-- return quote
--     if $(esc(mode)) == :compile
--         $(esc(ex))
--     elseif $(esc(mode)) == :precompile
--         $(esc(precompile_ex))
--     else
--         error("Invalid value for mode: " * show($(esc(mode))))
--     end
-- end
def workloadMode {α : Type} (kind : WorkloadMacro) (mode : String)
    (body : Unit → WorkloadM α)
    (macroCall : WorkloadMacro → (Unit → WorkloadM α) → WorkloadM α) :
    WorkloadM α := do
  if mode = "compile" then body ()
  else if mode = "precompile" then
    observeWorkload (.invokeMacro kind) (.ok ())
    macroCall kind body
  else throw (.methodError "*(::String, ::Nothing)")

-- Source: src/precompile.jl:16-29
def maybeSetupWorkload {α : Type} (mode : String) (body : Unit → WorkloadM α)
    (macroCall : WorkloadMacro → (Unit → WorkloadM α) → WorkloadM α) : WorkloadM α :=
  workloadMode .setup mode body macroCall

-- Source: src/precompile.jl:31-44
def maybeCompileWorkload {α : Type} (mode : String) (body : Unit → WorkloadM α)
    (macroCall : WorkloadMacro → (Unit → WorkloadM α) → WorkloadM α) : WorkloadM α :=
  workloadMode .compile mode body macroCall

def defaultOperatorKeywords : WorkloadKeywords :=
  [("binary_operators",.operators ["+","*","/","-","^"]),
   ("unary_operators",.operators ["sin","cos","exp","log","sqrt","abs"])]

def defaultSearchKeywords : WorkloadKeywords :=
  [("parallelism",.symbol "multithreading"),("verbosity",.integer 0)]

private def overlay (base overrides : WorkloadKeywords) : WorkloadKeywords :=
  base.filter (fun (key,_) => !overrides.any (fun (k,_) => k == key)) ++ overrides

private def compileKeywords : WorkloadKeywords :=
  [("populations",.integer 3),("population_size",.integer 50),
   ("tournament_selection_n",.integer 6),("ncycles_per_iteration",.integer 30),
   ("mutation_weights",.weights (["mutate_constant","mutate_operator","swap_operands",
     "add_node","insert_node","delete_node","simplify","randomize","do_nothing","optimize"].map
       (fun k => (k,.fin 1)))),
   ("fraction_replaced",.floating (SymReg.Loss.LossPrecision.round .float64 (.fin (1/5)))),
   ("fraction_replaced_hof",.floating (SymReg.Loss.LossPrecision.round .float64 (.fin (1/5)))),
   ("define_helper_functions",.flag false),
   ("optimizer_probability",.floating (SymReg.Loss.LossPrecision.round .float64 (.fin (1/20)))),
   ("save_to_file",.flag false)]

structure WorkloadServices where
  randn : WorkloadType → List Nat → Jl Nat
  options : WorkloadKeywords → Jl Nat
  search : Nat → Nat → WorkloadKeywords → Jl Nat
  frontier : Nat → Jl Unit
  buffer : Jl Nat
  serialize : Nat → Nat → Jl Unit
  rewind : Nat → Jl Unit
  deserialize : Nat → Jl Nat
  macroCall : WorkloadMacro → (Unit → WorkloadM Unit) → WorkloadM Unit

-- Source: src/precompile.jl:55-116
-- @maybe_setup_workload mode begin
--     for T in PRECOMPILE_TYPES, nout in (1,)
--         start = nout == 1
--         N = 30
--         X = randn(T, 3, N)
--         y = start ? randn(T, N) : randn(T, nout, N)
--         @maybe_compile_workload mode begin
--             options = SymbolicRegression.Options(;
--                 operator_kwargs...,
--                 populations=3,
--                 population_size=start ? 50 : 12,
--                 tournament_selection_n=6,
--                 ncycles_per_iteration=start ? 30 : 1,
--                 mutation_weights=(;
--                     mutate_constant=1.0,
--                     mutate_operator=1.0,
--                     swap_operands=1.0,
--                     add_node=1.0,
--                     insert_node=1.0,
--                     delete_node=1.0,
--                     simplify=1.0,
--                     randomize=1.0,
--                     do_nothing=1.0,
--                     optimize=1.0,
--                 ),
--                 fraction_replaced=0.2,
--                 fraction_replaced_hof=0.2,
--                 define_helper_functions=false,
--                 optimizer_probability=0.05,
--                 save_to_file=false,
--             )
--             state = equation_search(
--                 X,
--                 y;
--                 niterations=start ? 3 : 1,
--                 options=options,
--                 return_state=true,
--                 saved_state=nothing,
--                 search_kwargs...,
--             )
--             hof = equation_search(
--                 X,
--                 y;
--                 niterations=0,
--                 options=options,
--                 saved_state=state,
--                 return_state=false,
--                 search_kwargs...,
--             )
--             nout == 1 && calculate_pareto_frontier(hof::HallOfFame)
--             if precompile_serialization
--                 for value in (options, state)
--                     buffer = IOBuffer()
--                     Serialization.serialize(buffer, value)
--                     seekstart(buffer)
--                     Serialization.deserialize(buffer)
--                 end
--             end
--         end
--     end
-- end
-- return nothing
private def precompileForType (mode : String) (operatorKeywords searchKeywords : WorkloadKeywords)
    (serialization : Bool) (svc : WorkloadServices) (t : WorkloadType) : WorkloadM Unit := do
  observeWorkload (.beginType t) (.ok ())
  let x ← observeWorkload (.randomArray t [3,30]) (svc.randn t [3,30])
  let y ← observeWorkload (.randomArray t [30]) (svc.randn t [30])
  maybeCompileWorkload mode (fun () => do
    let keys := overlay operatorKeywords compileKeywords
    let opt ← observeWorkload (.options keys) (svc.options keys)
    let first := overlay [("niterations",.integer 3),("options",.identity opt),
      ("return_state",.flag true),("saved_state",.nothing)] searchKeywords
    let state ← observeWorkload (.search x y first) (svc.search x y first)
    let second := overlay [("niterations",.integer 0),("options",.identity opt),
      ("saved_state",.identity state),("return_state",.flag false)] searchKeywords
    let hof ← observeWorkload (.search x y second) (svc.search x y second)
    observeWorkload (.frontier hof) (svc.frontier hof)
    if serialization then
      for item in [opt,state] do
        let buf ← observeWorkload .buffer svc.buffer
        observeWorkload (.serialize buf item) (svc.serialize buf item)
        observeWorkload (.rewind buf) (svc.rewind buf)
        let _ ← observeWorkload (.deserialize buf) (svc.deserialize buf)
        pure ()) svc.macroCall

-- Source: src/precompile.jl:56,114
private def precompileForTypes (mode : String) (operatorKeywords searchKeywords : WorkloadKeywords)
    (serialization : Bool) (svc : WorkloadServices) : List WorkloadType → WorkloadM Unit
  | [] => pure ()
  | t :: ts => do
    precompileForType mode operatorKeywords searchKeywords serialization svc t
    precompileForTypes mode operatorKeywords searchKeywords serialization svc ts

-- Source: src/precompile.jl:55-61,113-116
def doPrecompilation (mode : String) (preference : Option Bool)
    (operatorKeywords searchKeywords : WorkloadKeywords) (serialization : Bool)
    (svc : WorkloadServices) : WorkloadM Unit :=
  maybeSetupWorkload mode
    (fun () => precompileForTypes mode operatorKeywords searchKeywords serialization svc
      (precompileTypes preference)) svc.macroCall

private def startedTypes (calls : List WorkloadCall) : List WorkloadType :=
  calls.filterMap fun c => match c with | .beginType t => some t | _ => none

def precompilePreference : Prop := ∀ preference svc,
  let (outcome,calls) := (doPrecompilation "compile" preference defaultOperatorKeywords
    defaultSearchKeywords false svc).run []
  outcome = .ok () →
  (preference = some false → startedTypes calls = [.float32]) ∧
  (preference ≠ some false → startedTypes calls = [.float32,.float64])

private theorem startedTypes_append (a b : List WorkloadCall) :
    startedTypes (a ++ b) = startedTypes a ++ startedTypes b := by
  simp [startedTypes, List.filterMap_append]

private theorem workload_bind_run {A B : Type} (act : WorkloadM A) (next : A → WorkloadM B)
    (before : List WorkloadCall) :
    (act >>= next).run before =
      match act.run before with
      | (.error e, after) => (.error e, after)
      | (.ok a, after) => (next a).run after := by
  change (let (r, after) := act.run before; ExceptT.bindCont next r after) = _
  cases act.run before with
  | mk result after => cases result <;> rfl

private theorem observe_run {A : Type} (call : WorkloadCall) (result : Jl A)
    (before : List WorkloadCall) :
    (observeWorkload call result).run before = (result, before ++ [call]) := rfl

private theorem workload_pure_run {A : Type} (value : A) (calls : List WorkloadCall) :
    (pure value : WorkloadM A).run calls = (.ok value, calls) := rfl

private theorem startsForType (svc : WorkloadServices) (t : WorkloadType) (before after : List WorkloadCall)
    (h : (precompileForType "compile" defaultOperatorKeywords defaultSearchKeywords false svc t).run before =
      (.ok (), after)) :
    startedTypes after = startedTypes before ++ [t] := by
  simp only [precompileForType, maybeCompileWorkload, workloadMode, String.reduceEq,
    ite_true, Bool.false_eq_true, ite_false, workload_bind_run, observe_run] at h
  repeat' (split at h <;> simp_all only [Prod.mk.injEq])
  all_goals try
    have hbad : (Except.error _ : Jl Unit) = .ok () :=
      congrArg (fun pair : Jl Unit × List WorkloadCall => pair.1) h
    cases hbad
  all_goals
    simp only [workload_pure_run] at h
    have hlast := (Prod.mk.inj h).2
    clear h
    subst after
    rename_i _ _ _ e₁ _ _ _ e₂ _ _ _ e₃ _ _ _ e₄ _ _ _ e₅ _ _ _ e₆
    rw [← e₆.2, ← e₅.2, ← e₄.2, ← e₃.2, ← e₂.2, ← e₁.2]
    simp [startedTypes, List.filterMap_append]

private theorem startsForTypes (sv : WorkloadServices) (types : List WorkloadType)
    (before after : List WorkloadCall)
    (h : (precompileForTypes "compile" defaultOperatorKeywords defaultSearchKeywords false sv types).run
      before = (.ok (), after)) :
    startedTypes after = startedTypes before ++ types := by
  induction types generalizing before after with
  | nil =>
    have he : before = after := (Prod.mk.inj h).2
    simp [he]
  | cons t ts ih =>
    simp only [precompileForTypes, workload_bind_run] at h
    split at h
    · cases h
    · rename_i u next hstep
      cases u
      have ht := startsForType sv t before next hstep
      rw [ih next after h, ht, List.append_assoc]
      rfl

theorem precompilePreference_holds : precompilePreference := by
  intro pref sv
  generalize hr : (doPrecompilation "compile" pref defaultOperatorKeywords
    defaultSearchKeywords false sv).run [] = run
  obtain ⟨result, calls⟩ := run
  intro he
  change result = .ok () at he
  subst result
  change (precompileForTypes "compile" defaultOperatorKeywords defaultSearchKeywords false sv
    (precompileTypes pref)).run [] = (.ok (), calls) at hr
  have ht := startsForTypes sv (precompileTypes pref) [] calls hr
  change startedTypes calls = precompileTypes pref at ht
  constructor
  · intro hf
    simpa [hf, precompileTypes] using ht
  · intro hf
    cases pref with
    | none => simpa [precompileTypes] using ht
    | some b => cases b <;> simp_all [precompileTypes]

def precompileModeForwarding : Prop := ∀ (body : Unit → WorkloadM Nat) macroCall before,
  (maybeSetupWorkload "compile" body macroCall).run before = (body ()).run before ∧
  (maybeCompileWorkload "compile" body macroCall).run before = (body ()).run before ∧
  (maybeSetupWorkload "precompile" body macroCall).run before =
    (macroCall .setup body).run (before ++ [.invokeMacro .setup]) ∧
  (maybeCompileWorkload "precompile" body macroCall).run before =
    (macroCall .compile body).run (before ++ [.invokeMacro .compile])

theorem precompileModeForwarding_holds : precompileModeForwarding := by
  intro body macroCall before
  exact ⟨rfl,rfl,rfl,rfl⟩

private def keyword (name : String) (keys : WorkloadKeywords) : Option KeywordValue :=
  (keys.find? (fun (key,_) => key == name)).map Prod.snd

def precompileShapes : Prop := ∀ preference operatorKeywords searchKeywords serialization svc,
  let (outcome,calls) := (doPrecompilation "compile" preference operatorKeywords
    searchKeywords serialization svc).run []
  outcome = .ok () →
  ∀ t, t ∈ startedTypes calls → ∃ x y opt state first second keys,
    svc.randn t [3,30] = .ok x ∧ svc.randn t [30] = .ok y ∧
    svc.options keys = .ok opt ∧ svc.search x y first = .ok state ∧
    keyword "population_size" keys = some (.integer 50) ∧
    keyword "ncycles_per_iteration" keys = some (.integer 30) ∧
    keyword "niterations" first = (keyword "niterations" searchKeywords).or (some (.integer 3)) ∧
    keyword "niterations" second = (keyword "niterations" searchKeywords).or (some (.integer 0)) ∧
    keyword "saved_state" second = (keyword "saved_state" searchKeywords).or (some (.identity state)) ∧
    ∃ prior suffix hall, calls = prior ++
      [.beginType t,.randomArray t [3,30],.randomArray t [30],.options keys,
       .search x y first,.search x y second,.frontier hall] ++ suffix ∧
    (serialization = true → ∃ b c rest, suffix =
      [.buffer,.serialize b opt,.rewind b,.deserialize b,
       .buffer,.serialize c state,.rewind c,.deserialize c] ++ rest)

def precompileInvalidDiagnostic : Prop := ∀ mode kind body macroCall,
  mode ≠ "compile" → mode ≠ "precompile" →
  ∃ message, (workloadMode (α := Nat) kind mode body macroCall).run [] =
    (.error (.errorException message),[])

theorem precompileInvalidDiagnostic_refuted : ¬ precompileInvalidDiagnostic := by
  intro h
  obtain ⟨_,hm⟩ := h "invalid" .setup (fun _ => pure 0) (fun _ _ => pure 0)
    (by decide) (by decide)
  change ((.error (.methodError "*(::String, ::Nothing)") : Jl Nat), []) = _ at hm
  cases hm

end SymReg.Infra
