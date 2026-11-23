import SymReg.Infra.Configure

namespace SymReg.Infra
open DynExpr

/-- src/Configure.jl:232-248. Futures have all been fetched concurrently before
this ordered scan; a successful fetched value is discarded. -/
def fetchAll : List (Jl Nat) → Jl Unit
  | [] => .ok ()
  | .ok _ :: xs => fetchAll xs
  | .error e :: _ => .error e

def workerFetchSuccess : Prop := ∀ results,
  fetchAll results = .ok () ↔ ∀ r ∈ results, ∃ v, r = .ok v

theorem workerFetchSuccess_holds : workerFetchSuccess := by
  intro results
  induction results with
  | nil => simp [fetchAll]
  | cons r rs ih => cases r <;> simp [fetchAll, ih]

def workerFirstFailure : Prop := ∀ (prior : List Nat) e suffix,
  fetchAll (prior.map Except.ok ++ .error e :: suffix) = .error e

theorem workerFirstFailure_holds : workerFirstFailure := by
  intro prior e suffix
  induction prior with
  | nil => rfl
  | cons x xs ih => simpa [fetchAll] using ih

-- Source: src/Configure.jl:201-212
-- try
--     test_function_on_workers(example_inputs, op, procs)
-- catch e
--     undefined_on_workers = isa(e.captured.ex, UndefVarError)
--     if undefined_on_workers
--         copy_definition_to_workers(op, procs, options, verbosity)
--     else
--         throw(e)
--     end
-- end
-- test_function_on_workers(example_inputs, op, procs)
def moveFunction {S : Type} (op : Nat) (args procs : List Nat) (options : Nat) (verbosity : Int)
    (probe : Nat → List Nat → List Nat → S → Jl Unit × S)
    (inspect : JlError → S → Jl Bool × S)
    (copy : Nat → List Nat → Nat → Int → S → Jl Unit × S) (s : S) : Jl Unit × S :=
  match probe op args procs s with
  | (.ok _, s') => probe op args procs s'
  | (.error first, s') =>
    match inspect first s' with
    | (.error e, s'') => (.error e, s'')
    | (.ok false, s'') => (.error first, s'')
    | (.ok true, s'') =>
      match copy op procs options verbosity s'' with
      | (.error e, s''') => (.error e, s''')
      | (.ok _, s''') => probe op args procs s'''

def workerCopyGate : Prop := ∀ (S : Type) op args procs options verbosity probe inspect copy (s : S),
  let out := moveFunction op args procs options verbosity probe inspect copy s
  (∀ post, probe op args procs s = (.ok (), post) → out = probe op args procs post) ∧
  (∀ first post e after, probe op args procs s = (.error first, post) →
    inspect first post = (.error e, after) → out = (.error e, after)) ∧
  (∀ first post after, probe op args procs s = (.error first, post) →
    inspect first post = (.ok false, after) → out = (.error first, after)) ∧
  (∀ first post after e endState, probe op args procs s = (.error first, post) →
    inspect first post = (.ok true, after) → copy op procs options verbosity after = (.error e, endState) →
    out = (.error e, endState)) ∧
  (∀ first post after endState, probe op args procs s = (.error first, post) →
    inspect first post = (.ok true, after) → copy op procs options verbosity after = (.ok (), endState) →
    out = probe op args procs endState)

theorem workerCopyGate_holds : workerCopyGate := by
  intro S op args procs options verbosity probe inspect copy s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro post h; simp [moveFunction, h]
  · intro first post e after h hi; simp [moveFunction, h, hi]
  · intro first post after h hi; simp [moveFunction, h, hi]
  · intro first post after e endState h hi hc; simp [moveFunction, h, hi, hc]
  · intro first post after endState h hi hc; simp [moveFunction, h, hi, hc]

-- Source: src/Configure.jl:220-227
-- @everywhere procs @eval function $name end
-- for m in src_ms
--     @everywhere procs @eval $m
-- end
def copyDefinition {S : Type} (declare evalMethod : Nat → List Nat → ExceptT JlError (StateM S) Unit)
    (name : Nat) (methods procs : List Nat) : ExceptT JlError (StateM S) Unit := do
  declare name procs
  methods.forM fun m => evalMethod m procs

private def recordMethod (declaration : Bool) (failure : Option Nat) (id : Nat) (procs : List Nat) :
    ExceptT JlError (StateM (List (Bool × Nat × List Nat))) Unit :=
  ExceptT.mk fun calls =>
    (if failure = some id then .error (.errorException "remote eval") else .ok (),
      calls ++ [(declaration,id,procs)])

def workerMethodsOrder : Prop := ∀ name methods procs,
  ((copyDefinition (recordMethod true none) (recordMethod false none) name methods procs).run []) =
    (.ok (), (true,name,procs) :: methods.map (fun m => (false,m,procs))) ∧
  ((copyDefinition (recordMethod true (some name)) (recordMethod false none) name methods procs).run []) =
    (.error (.errorException "remote eval"), [(true,name,procs)]) ∧
  (∀ prior failed suffix, methods = prior ++ failed :: suffix → failed ∉ prior →
    ((copyDefinition (recordMethod true none) (recordMethod false (some failed)) name methods procs).run []) =
      (.error (.errorException "remote eval"),
        (true,name,procs) :: (prior ++ [failed]).map (fun m => (false,m,procs))))

private theorem recordMethods (methods procs : List Nat) (prev : List (Bool × Nat × List Nat)) :
    ((methods.forM fun m => recordMethod false none m procs).run prev) =
      (.ok (), prev ++ methods.map (fun m => (false,m,procs))) := by
  induction methods generalizing prev with
  | nil => simp [List.forM] <;> rfl
  | cons m ms ih =>
    change ((ms.forM fun a => recordMethod false none a procs).run (prev ++ [(false,m,procs)])) = _
    rw [ih]
    simp [List.append_assoc]

private theorem recordMethodFailure (prior suffix : List Nat) (failed : Nat) (procs : List Nat)
    (prev : List (Bool × Nat × List Nat)) (hf : failed ∉ prior) :
    (((prior ++ failed :: suffix).forM fun m => recordMethod false (some failed) m procs).run prev) =
      (.error (.errorException "remote eval"), prev ++ (prior ++ [failed]).map (fun m => (false,m,procs))) := by
  induction prior generalizing prev with
  | nil =>
    simp [List.forM, recordMethod, Bind.bind, ExceptT.bind, ExceptT.bindCont,
      StateT.bind, Pure.pure] <;> rfl
  | cons m ms ih =>
    have hne : failed ≠ m := fun h => hf (by simp [h])
    have hs : failed ∉ ms := fun h => hf (by simp [h])
    change ((do
      recordMethod false (some failed) m procs
      (ms ++ failed :: suffix).forM fun a => recordMethod false (some failed) a procs :
      ExceptT JlError (StateM (List (Bool × Nat × List Nat))) Unit).run prev) = _
    have step : recordMethod false (some failed) m procs =
        ExceptT.mk (fun calls => (.ok (), calls ++ [(false,m,procs)])) := by
      simp [recordMethod, hne]
    rw [step]
    change (((ms ++ failed :: suffix).forM fun a => recordMethod false (some failed) a procs).run
      (prev ++ [(false,m,procs)])) = _
    rw [ih _ hs]
    simp [List.append_assoc]

theorem workerMethodsOrder_holds : workerMethodsOrder := by
  intro name methods procs
  refine ⟨?_, ?_, ?_⟩
  · change ((methods.forM fun m => recordMethod false none m procs).run [(true,name,procs)]) = _
    rw [recordMethods] <;> rfl
  · simp [copyDefinition, recordMethod, Bind.bind, ExceptT.bind, ExceptT.bindCont,
      StateT.bind, Pure.pure] <;> rfl
  · intro prior failed suffix h hf
    rw [h]
    change (((prior ++ failed :: suffix).forM fun m => recordMethod false (some failed) m procs).run
      [(true,name,procs)]) = _
    rw [recordMethodFailure _ _ _ _ _ hf] <;> rfl

inductive ExampleValue where
  | initialT | zeroL | integerZero | node | dataset | options | expression
  deriving DecidableEq, Repr

/-- Options observations for src/Configure.jl:132-200. Expression make_example_inputs
is an arbitrary service result. Function ids and value tokens retain identity. -/
structure FunctionTransfer where
  unary : List Nat
  binary : List Nat
  elementwise : Nat
  supervised : Bool
  weighted : Bool
  earlyStop : Option Nat
  expressionExamples : List (Nat × List ExampleValue)
  loss : Option Nat
  expressionLoss : Option Nat
  complexity : Option Nat

private def oneTransfer (op : Option Nat) (args : List ExampleValue) :
    List (Nat × List ExampleValue) := op.toList.map (fun f => (f,args))

/-- Exact set order and example-argument order, src/Configure.jl:128-215. -/
def functionTransferPlan (o : FunctionTransfer) : List (Nat × List ExampleValue) :=
  o.unary.map (fun f => (f,[.initialT])) ++
  o.binary.map (fun f => (f,[.initialT,.initialT])) ++
  (if o.supervised then [] else [(o.elementwise,
    if o.weighted then [.initialT,.initialT,.initialT] else [.initialT,.initialT])]) ++
  oneTransfer o.earlyStop [.zeroL,.integerZero] ++
  o.expressionExamples ++
  oneTransfer o.loss [.node,.dataset,.options] ++
  oneTransfer o.expressionLoss [.expression,.dataset,.options] ++
  oneTransfer o.complexity [.expression]

def workerFunctionArguments : Prop := ∀ (o : FunctionTransfer),
  ∃ operators custom early losses,
    functionTransferPlan o = operators ++ custom ++ early ++ o.expressionExamples ++ losses ∧
    operators =
      o.unary.map (fun f => (f,[.initialT])) ++
      o.binary.map (fun f => (f,[.initialT,.initialT])) ∧
    custom = (if o.supervised then [] else [(o.elementwise,
      if o.weighted then [.initialT,.initialT,.initialT] else [.initialT,.initialT])]) ∧
    early = o.earlyStop.toList.map (fun f => (f,[.zeroL,.integerZero])) ∧
    losses = o.loss.toList.map (fun f => (f,[.node,.dataset,.options])) ++
      o.expressionLoss.toList.map (fun f => (f,[.expression,.dataset,.options])) ++
      o.complexity.toList.map (fun f => (f,[.expression]))

theorem workerFunctionArguments_holds : workerFunctionArguments := by
  intro o
  refine ⟨_, _, _, _, ?_, rfl, rfl, rfl, rfl⟩
  simp only [functionTransferPlan, oneTransfer, List.append_assoc]

/-- Worker import choice, src/Configure.jl:270-321. The extension scan keeps
source-table order and appends explicit imports without deduplicating them. -/
def relevantExtensions : List String :=
  ["Bumper", "CUDA", "ClusterManagers", "Enzyme", "LoopVectorization", "Mooncake",
   "SymbolicUtils", "TensorBoardLogger", "Zygote"]

structure ImportPlan where
  localFile : Option String
  imports : List String
  deriving DecidableEq, Repr

def importModulePlan (loaded : List String) (filename : String)
    (requested : Option (List String)) : ImportPlan :=
  ⟨if loaded.contains "SymbolicRegression" then none else some filename,
    relevantExtensions.filter loaded.contains ++ requested.getD []⟩

inductive WorkerImport where
  | includeFile (path : String)
  | useLocal
  | usePackage
  | useExtension (name : String)
  deriving DecidableEq

-- Source: src/Configure.jl:279-287,308-312. Each worker executes its own quote.
-- include($filename)
-- using .SymbolicRegression
-- using SymbolicRegression
-- using $ext: $ext
def evaluateImportQuote {m : Type → Type} [Monad m]
    (eval : WorkerImport → m Unit) (plan : ImportPlan) : m Unit := do
  match plan.localFile with
  | some filename =>
    eval (.includeFile filename)
    eval .useLocal
  | none => eval .usePackage
  plan.imports.forM fun name => eval (.useExtension name)
-- Source: src/Configure.jl:308-321.
-- for ext in all_extensions
--     push!(expr.args, quote
--         using $ext: $ext
--     end)
-- end
-- verbosity > 0 && if isempty(relevant_extensions)
--     @info "Importing SymbolicRegression on workers."
-- else
--     @info "Importing SymbolicRegression on workers as well as extensions $(join(relevant_extensions, ',' * ' '))."
-- end
-- @everywhere procs Core.eval(Core.Main, $expr)
-- verbosity > 0 && @info "Finished!"
-- return nothing
def importModuleOnWorkers {m : Type → Type} [Monad m]
    (loaded : List String) (filename : String) (requested : Option (List String))
    (procs : List Nat) (verbosity : Int) (info : String → m Unit)
    (eval : Nat → WorkerImport → m Unit)
    (everywhereEval : List Nat → (Nat → m Unit) → m Unit) : m Unit := do
  let plan := importModulePlan loaded filename requested
  if verbosity > 0 then
    let extensions := relevantExtensions.filter loaded.contains
    if extensions.isEmpty then info "Importing SymbolicRegression on workers."
    else info ("Importing SymbolicRegression on workers as well as extensions " ++
      String.intercalate ", " extensions ++ ".")
  everywhereEval procs (fun p => evaluateImportQuote (eval p) plan)
  if verbosity > 0 then info "Finished!"


theorem workerImportQuote_order (plan : ImportPlan) :
    ((evaluateImportQuote (m := StateM (List WorkerImport))
      (fun part => modify (· ++ [part])) plan).run []).2 =
      (match plan.localFile with
       | some path => [.includeFile path, .useLocal]
       | none => [.usePackage]) ++ plan.imports.map WorkerImport.useExtension := by
  have extensionOrder (prior : List WorkerImport) (exts : List String) :
      ((exts.forM (m := StateM (List WorkerImport)) (fun name => modify (· ++ [.useExtension name]))).run prior).2 =
        prior ++ exts.map WorkerImport.useExtension := by
    induction exts generalizing prior with
    | nil => simp [List.forM]; rfl
    | cons e es ih =>
      change ((es.forM (m := StateM (List WorkerImport))
        (fun name => modify (· ++ [.useExtension name]))).run (prior ++ [.useExtension e])).2 = _
      rw [ih]
      simp [List.append_assoc]
  cases h : plan.localFile with
  | none =>
    unfold evaluateImportQuote
    rw [h]
    exact extensionOrder [.usePackage] plan.imports
  | some path =>
    unfold evaluateImportQuote
    rw [h]
    exact extensionOrder [.includeFile path, .useLocal] plan.imports

theorem quietWorkerImport_propagates (loaded : List String) (filename : String)
    (requested : Option (List String)) (procs : List Nat) (verbosity : Int)
    (info : String → Jl Unit) (eval : Nat → WorkerImport → Jl Unit)
    (everywhereEval : List Nat → (Nat → Jl Unit) → Jl Unit)
    (quiet : verbosity ≤ 0) :
    importModuleOnWorkers loaded filename requested procs verbosity info eval everywhereEval =
      everywhereEval procs (fun p => evaluateImportQuote (eval p) (importModulePlan loaded filename requested)) := by
  have h : ¬ verbosity > 0 := by omega
  cases he : everywhereEval procs (fun p => evaluateImportQuote (eval p) (importModulePlan loaded filename requested)) with
  | error e => simp [importModuleOnWorkers, h, he, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | ok result => cases result; simp [importModuleOnWorkers, h, he, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `activate_env_on_workers`, src/Configure.jl:258-268. -/
def activateEnvironmentPlan (procs : List Nat) (project : String) : List (Nat × String) :=
  procs.map (fun p => (p,project))

def workerImportOrder : Prop := ∀ loaded filename requested,
  let plan := importModulePlan loaded filename requested
  plan.localFile = (if "SymbolicRegression" ∈ loaded then none else some filename) ∧
  plan.imports = (["Bumper", "CUDA", "ClusterManagers", "Enzyme", "LoopVectorization",
    "Mooncake", "SymbolicUtils", "TensorBoardLogger", "Zygote"].filter loaded.contains) ++
    requested.getD []

theorem workerImportOrder_holds : workerImportOrder := by
  intro loaded filename requested; simp [importModulePlan, relevantExtensions]

/-- Per-worker test_module_on_workers arguments, src/Configure.jl:324-336.
TEST_TYPE is Float32, represented by its name rather than a second scalar model. -/
def moduleTestPlan (procs : List Nat) : List (Nat × Nat × Nat × String) :=
  procs.map (fun p => (p,3,5,"Float32"))

/-- Per-worker test_entire_pipeline arguments, src/Configure.jl:338-380.
Population creation uses head states; evolution uses worker states; final
optimization receives no trace. Services themselves remain arbitrary. -/
structure PipelineTest where
  populationSize : Nat := 20
  initialLength : Nat := 3
  cycleSize : Nat := 5
  maximumSize : Nat := 5
  headStates : List Nat
  workerStates : List Nat
  finalMaximumSize : Nat
  finalTrace : Option Nat := none
  deriving DecidableEq, Repr

def pipelineTest (head worker : List Nat) (maxsize : Nat) : PipelineTest :=
  { headStates := head, workerStates := worker, finalMaximumSize := maxsize }

def workerPipelineArguments : Prop := ∀ head worker maxsize procs project,
  pipelineTest head worker maxsize = ⟨20,3,5,5,head,worker,maxsize,none⟩ ∧
  (moduleTestPlan procs).length = procs.length ∧
  (∀ proc ∈ procs, (proc,3,5,"Float32") ∈ moduleTestPlan procs) ∧
  activateEnvironmentPlan procs project = procs.map (fun p => (p,project))

theorem workerPipelineArguments_holds : workerPipelineArguments := by
  intro head worker maxsize procs project
  simp [pipelineTest, moduleTestPlan, activateEnvironmentPlan]

/-- configure_workers stages, src/Configure.jl:382-425. The process-creation
service receives lazy=false, timeout and exeflags. project_path is unused by this
function: activation is an independent helper and is absent from this plan. -/
structure WorkerSetup where
  processes : List Nat
  created : Bool
  stages : List String
  deriving DecidableEq, Repr

def configureWorkersPlan (supplied : Option (List Nat)) (created : List Nat)
    (runtests : Bool) : WorkerSetup :=
  let fresh := supplied.isNone
  ⟨supplied.getD created, fresh,
    (if fresh then ["addprocs(lazy=false)", "import"] else []) ++ ["move-functions"] ++
    (if runtests then ["test-module", "test-pipeline"] else [])⟩

def workerSetupReuse : Prop := ∀ procs created tests,
  (configureWorkersPlan (some procs) created tests).processes = procs ∧
  (configureWorkersPlan (some procs) created tests).created = false ∧
  (configureWorkersPlan (some procs) created tests).stages =
    ["move-functions"] ++ (if tests then ["test-module", "test-pipeline"] else [])

theorem workerSetupReuse_holds : workerSetupReuse := by
  intro procs created tests; exact ⟨rfl,rfl,rfl⟩


-- Source: src/Configure.jl:398-424 (procs === nothing).
-- withenv("JULIA_WORKER_TIMEOUT" => string(worker_timeout)) do
--     return (addprocs_function(numprocs; lazy=false, exeflags), true)
-- end
-- import_module_on_workers(procs, file, worker_imports, verbosity)
-- move_functions_to_workers(procs, options, example_dataset, verbosity)
-- if runtests
--     test_module_on_workers(procs, options, verbosity)
--     test_entire_pipeline(
--         procs,
--         example_dataset,
--         options,
--         verbosity,
--         test_head_plugin_states,
--         test_worker_plugin_states,
--     )
-- end
-- return (procs, we_created_procs)
private def runCreatedWorkers {m : Type → Type} [Monad m]
    (add : Int → Bool → String → String → m (List Nat))
    (step : String → List Nat → m Unit) (numprocs : Int) (timeout flags : String)
    (tests : Bool) : m (List Nat × Bool) := do
  let ps ← add numprocs false timeout flags
  step "import" ps
  step "move-functions" ps
  if tests then
    step "test-module" ps
    step "test-pipeline" ps
  pure (ps, true)

def workerSetupCreate : Prop :=
  (∀ add step n timeout flags tests,
    (∀ e, add n false timeout flags = (Except.error e : Jl (List Nat)) →
      runCreatedWorkers add step n timeout flags tests = .error e) ∧
    (∀ ps, add n false timeout flags = .ok ps →
      runCreatedWorkers add step n timeout flags tests =
        ((["import", "move-functions"] ++ (if tests then ["test-module", "test-pipeline"] else [])).mapM
          (fun stage => step stage ps)).map (fun _ => (ps, true)))) ∧
  ∀ procs tests,
  configureWorkersPlan none procs tests =
    ⟨procs,true,["addprocs(lazy=false)","import","move-functions"] ++
      (if tests then ["test-module","test-pipeline"] else [])⟩

theorem workerSetupCreate_holds : workerSetupCreate := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro add step n timeout flags tests
  refine ⟨?_, ?_⟩
  · intro e h
    simp [runCreatedWorkers, h, Bind.bind, Except.bind]
  · intro ps h
    cases tests <;> cases hi : step "import" ps <;> cases hm : step "move-functions" ps <;>
      cases ht : step "test-module" ps <;> cases hp : step "test-pipeline" ps <;>
      simp [runCreatedWorkers, h, hi, hm, ht, hp, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.map]

private inductive ConfigureEvent where
  | add (n : Int) (lazy : Bool) (timeout flags : String)
  | step (name : String) (procs : List Nat)

private def configureLogged {α : Type} (event : ConfigureEvent) (outcome : Jl α) :
    ExceptT JlError (StateM (List ConfigureEvent)) α :=
  ExceptT.mk (fun events => (outcome, events ++ [event]))

theorem created_workers_first_failure (outcome : Jl (List Nat)) (n : Int) (timeout flags : String)
    (tests : Bool) (stage : String → Jl Unit) :
    ((runCreatedWorkers
      (fun n isLazy timeout flags => configureLogged (.add n isLazy timeout flags) outcome)
      (fun name procs => configureLogged (.step name procs) (stage name))
      n timeout flags tests).run []) =
      let first := ConfigureEvent.add n false timeout flags
      match outcome with
      | .error e => (.error e, [first])
      | .ok ps =>
        let importing := ConfigureEvent.step "import" ps
        let transfer := ConfigureEvent.step "move-functions" ps
        let moduleTest := ConfigureEvent.step "test-module" ps
        let pipeline := ConfigureEvent.step "test-pipeline" ps
        match stage "import" with
        | .error e => (.error e, [first, importing])
        | .ok _ =>
          match stage "move-functions" with
          | .error e => (.error e, [first, importing, transfer])
          | .ok _ =>
            if !tests then (.ok (ps, true), [first, importing, transfer])
            else match stage "test-module" with
              | .error e => (.error e, [first, importing, transfer, moduleTest])
              | .ok _ => ((stage "test-pipeline").map (fun _ => (ps, true)),
                [first, importing, transfer, moduleTest, pipeline]) := by
  cases outcome <;> cases tests <;>
    cases hi : stage "import" <;> cases hm : stage "move-functions" <;>
    cases ht : stage "test-module" <;> cases hp : stage "test-pipeline" <;>
    simp [runCreatedWorkers, configureLogged, hi, hm, ht, hp, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, StateT.bind, StateT.run, Pure.pure, ExceptT.pure, Except.map] <;> rfl

end SymReg.Infra
