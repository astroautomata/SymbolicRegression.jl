import DynExpr.NodeUtils.Nodes

namespace SymReg.Ext
open DynExpr

attribute [local simp] DynExpr.NodeUtils.bindOk DynExpr.NodeUtils.bindError
  DynExpr.NodeUtils.mapOk DynExpr.NodeUtils.mapError

inductive JsonCall (Trace : Type) where
  | openFile (path mode : String)
  | serialize (io : Nat) (trace : Trace) (allowNan : Bool)
  | newline (io : Nat)
  | close (io : Nat)

structure JsonIO (Trace W : Type) where
  openFile : String → String → W → Jl Nat × W
  serialize : Nat → Trace → Bool → W → Jl Unit × W
  writeNewline : Nat → W → Jl Nat × W
  close : Nat → W → Jl Unit × W

-- Source: ext/SymbolicRegressionJSONExt.jl:6-11
/-
function json_write(trace, tracing_file; append::Bool)
    open(tracing_file, append ? "a" : "w") do io
        JSON.json(io, trace; allownan=true)
        write(io, '\n')
    end
end
-/
def jsonWrite {Trace W : Type} (f : JsonIO Trace W) (trace : Trace)
    (path : String) (append : Bool) (initial : W) : Jl Nat × W × List (JsonCall Trace) :=
  let mode := if append then "a" else "w"
  let events := [JsonCall.openFile path mode]
  match f.openFile path mode initial with
  | (.error err, w) => (.error err, w, events)
  | (.ok io, w) =>
    let events := events ++ [.serialize io trace true]
    let (result, w, events) : Jl Nat × W × List (JsonCall Trace) := match f.serialize io trace true w with
      | (.error err, w') => (.error err, w', events)
      | (.ok (), w') =>
        let (r, w'') := f.writeNewline io w'
        (r, w'', events ++ [.newline io])
    match f.close io w with
    | (.ok (), w') => (result, w', events ++ [.close io])
    | (.error e, w') => (.error e, w', events ++ [.close io])

def jsonTraceAndMode : Prop :=
  ∀ (Trace W : Type) (f : JsonIO Trace W) trace path append initial n final events,
    jsonWrite f trace path append initial = (.ok n, final, events) →
    ∃ io, events = [.openFile path (if append then "a" else "w"),
      .serialize io trace true, .newline io, .close io]

theorem jsonTraceAndMode_holds : jsonTraceAndMode := by
  intro Trace W f trace path append initial n final events h
  rcases ho : f.openFile path (if append then "a" else "w") initial with ⟨opened, w⟩
  cases opened with
  | error e => simp [jsonWrite, ho] at h
  | ok io =>
    rcases hs : f.serialize io trace true w with ⟨serialized, w'⟩
    cases serialized with
    | error e =>
      rcases hc : f.close io w' with ⟨closed, w''⟩
      cases closed <;> simp [jsonWrite, ho, hs, hc] at h
      all_goals rename_i u; cases u; simp [jsonWrite, ho, hs, hc] at h
    | ok u =>
      cases u
      rcases hw : f.writeNewline io w' with ⟨written, w''⟩
      rcases hc : f.close io w'' with ⟨closed, w'''⟩
      cases closed with
      | error e => simp [jsonWrite, ho, hs, hw, hc] at h
      | ok u =>
        cases u
        simp [jsonWrite, ho, hs, hw, hc] at h
        exact ⟨io, h.2.2.symm⟩

private def textFileIO {Trace : Type} (json : Trace → Bool → Jl String) : JsonIO Trace String where
  openFile := fun _ mode old => (.ok 0, if mode = "a" then old else "")
  serialize := fun _ trace nan old =>
    match json trace nan with
    | .ok bytes => (.ok (), old ++ bytes)
    | .error err => (.error err, old)
  writeNewline := fun _ old => (.ok 1, old ++ "\n")
  close := fun _ old => (.ok (), old)

def jsonAppendOverwrite : Prop :=
  ∀ (Trace : Type) (json : Trace → Bool → Jl String) (trace : Trace) old bytes,
    json trace true = .ok bytes →
    (jsonWrite (textFileIO json) trace "" true old).2.1 = old ++ bytes ++ "\n" ∧
    (jsonWrite (textFileIO json) trace "" false old).2.1 = bytes ++ "\n"

theorem jsonAppendOverwrite_holds : jsonAppendOverwrite := by
  intro Trace json trace old bytes h
  simp [jsonWrite, textFileIO, h]

example : (fun (_ : Unit) (_ : Bool) => (.ok "{\"loss\":NaN}" : Jl String)) () true =
    .ok "{\"loss\":NaN}" := rfl

def jsonErrorPropagation : Prop :=
  ∀ (Trace W : Type) (f : JsonIO Trace W) trace path append initial io opened err mid,
    f.openFile path (if append then "a" else "w") initial = (.ok io, opened) →
    f.serialize io trace true opened = (.error err, mid) →
    let (cleanup, closed) := f.close io mid
    jsonWrite f trace path append initial =
      ((match cleanup with | .ok () => .error err | .error e => .error e), closed,
        [.openFile path (if append then "a" else "w"), .serialize io trace true, .close io])

theorem jsonErrorPropagation_holds : jsonErrorPropagation := by
  intro Trace W f trace path append initial io opened err mid ho hs
  rcases hc : f.close io mid with ⟨result, closed⟩
  cases result with
  | error => simp [jsonWrite, ho, hs, hc]
  | ok x => cases x; simp [jsonWrite, ho, hs, hc]

example : (fun (_ : Unit) (_ : Bool) => (.error .boundsError : Jl String)) () true =
    .error .boundsError := rfl

/-- `ext/SymbolicRegressionTablesExt.jl:14,16-17`: external predicates,
columns and matrix functions receive the original object and transpose flag. -/
def tablesIstable {X : Type} (istable : X → Bool) (x : X) := istable x

def tablesColumns {X C : Type} (columns : X → Jl C) (x : X) := columns x

def tablesMatrix {X M : Type} (matrix : X → Bool → Jl M) (x : X) (transpose : Bool := false) :=
  matrix x transpose

/-- `ext/SymbolicRegressionTablesExt.jl:15`: columns are obtained before
columnnames, then collect(Symbol, ...) retains iteration order. Symbol identity
is a String in this model; the Symbol constructor is an arbitrary function. -/
def tablesColnames {X C N : Type} (columns : X → Jl C) (names : C → Jl (List N))
    (symbol : N → String) (x : X) : Jl (List String) := do
  let cols ← columns x
  let ns ← names cols
  pure (ns.map symbol)

/-- `ext/SymbolicRegressionTablesExt.jl:18-23`: header is Symbol.(names),
the matrix is untouched, and the materializer runs only for a present prototype. -/
def tablesTable {M N P T : Type} (symbol : N → String)
    (table : M → List String → Jl T) (materialize : P → T → Jl T)
    (matrix : M) (names : List N) (prototype : Option P) : Jl T := do
  let matrixTable ← table matrix (names.map symbol)
  match prototype with
  | none => pure matrixTable
  | some p => materialize p matrixTable

def tablesInputRouting : Prop :=
  ∀ (X C M : Type) istable columns (matrix : X → Bool → Jl M) (x : X) transpose,
    tablesIstable istable x = istable x ∧
    tablesColumns (C := C) columns x = columns x ∧
    tablesMatrix matrix x transpose = matrix x transpose ∧
    tablesMatrix matrix x = tablesMatrix matrix x false

def tablesNameOrder : Prop :=
  ∀ (X C N : Type) columns names symbol (x : X) (cols : C) (ns : List N),
    columns x = .ok cols → names cols = .ok ns →
    tablesColnames columns names symbol x = .ok (ns.map symbol) ∧
      (ns.map symbol).length = ns.length

theorem tablesNameOrder_holds : tablesNameOrder := by
  intro X C N columns names symbol x cols ns hc hn
  simp [tablesColnames, hc, hn]

example : (fun (_ : Unit) => (.ok () : Jl Unit)) () = .ok () ∧
    (fun (_ : Unit) => (.ok ["b", "a"] : Jl (List String))) () = .ok ["b", "a"] :=
  ⟨rfl, rfl⟩

def tablesPrototypeRouting : Prop :=
  ∀ (M N P T : Type) symbol table materialize (matrix : M) (names : List N) (p : P) (out : T),
    table matrix (names.map symbol) = .ok out →
    tablesTable symbol table materialize matrix names none = .ok out ∧
    tablesTable symbol table materialize matrix names (some p) = materialize p out

theorem tablesPrototypeRouting_holds : tablesPrototypeRouting := by
  intro M N P T symbol table materialize matrix names p out h
  simp [tablesTable, h]

example : (fun (_ : Unit) (_ : List String) => (.ok () : Jl Unit)) () ["b", "a"] = .ok () := rfl

-- Source: src/MLJInterface.jl:346
-- is_extension_loaded(::Val) = false
def extensionLoaded (installed : List String) (tag : String) : Bool :=
  installed.contains tag

-- Source: ext/SymbolicRegressionTablesExt.jl:12
-- is_extension_loaded(::Val{:Tables}) = true
def installTables (installed : List String) : List String := "Tables" :: installed

def tablesLoadedProperty : Prop :=
  ∀ installed : List String, "Tables" ∉ installed →
    extensionLoaded installed "Tables" = false ∧
    extensionLoaded (installTables installed) "Tables" = true ∧
    ∀ tag, tag ≠ "Tables" →
      extensionLoaded (installTables installed) tag = extensionLoaded installed tag

theorem tablesLoadedProperty_holds : tablesLoadedProperty := by
  intro installed h
  refine ⟨by simp [extensionLoaded, h], rfl, ?_⟩
  intro tag ht
  simp [extensionLoaded, installTables, ht, Ne.symm ht]

example : "Tables" ∉ ["JSON"] := by decide

/-- Keywords constructed by `pysr_shaped_workload`,
`ext/SymbolicRegressionPythonCallExt.jl:41-63`. These are the only checkable
runtime semantics in this file; it defines no Python conversion implementation. -/
structure PySRWorkload (O : Type) where
  operators : O
  externalStop : Nat
  variableNames : List String
  displayVariableNames : List String
  yVariableNames : Option (List String)
  xUnits : Option (List String)
  yUnits : Option String
  logger : Option Nat
  runId : String
  progress : Bool
  runtests : Bool
  parallelism : String
  verbosity : Nat
  precompileSerialization : Bool

def pysrSettings {O : Type} (operators : O) (stop : Nat) : PySRWorkload O :=
  ⟨operators, stop, ["x0", "x1", "x2"], ["x0", "x1", "x2"], none, none,
    none, none, "precompile", true, true, "multithreading", 1, true⟩

def pysrWorkload {Mode O Result : Type} (doPrecompilation : Mode → PySRWorkload O → Jl Result)
    (makeStop : Unit → Nat) (mode : Mode) (operators : O) :=
  doPrecompilation mode (pysrSettings operators (makeStop ()))

/-- Default OperatorEnum construction reads the ordered unary/binary function
identities ((), (+,-,/,*)). Operator construction itself is external. -/
def pysrDefaultWorkload {Mode O Result : Type}
    (makeOperators : List (List String) → O)
    (doPrecompilation : Mode → PySRWorkload O → Jl Result)
    (makeStop : Unit → Nat) (mode : Mode) :=
  pysrWorkload doPrecompilation makeStop mode (makeOperators [[], ["+", "-", "/", "*"]])

def pysrWorkloadRouting : Prop :=
  ∀ (Mode O Result : Type) doPrecompilation makeStop (mode : Mode) (operators : O),
    pysrWorkload (Result := Result) doPrecompilation makeStop mode operators =
      doPrecompilation mode ⟨operators, makeStop (), ["x0", "x1", "x2"],
        ["x0", "x1", "x2"], none, none, none, none, "precompile", true, true,
        "multithreading", 1, true⟩

theorem pysrWorkloadRouting_holds : pysrWorkloadRouting := by
  unfold pysrWorkloadRouting; intros; rfl

def pysrDefaultRouting : Prop :=
  ∀ (Mode O : Type) makeOperators makeStop (mode : Mode),
    let observe := fun (m : Mode) (settings : PySRWorkload O) => (.ok (m, settings.operators) : Jl (Mode × O))
    pysrDefaultWorkload makeOperators observe makeStop mode =
      .ok (mode, makeOperators [[], ["+", "-", "/", "*"]])

theorem pysrDefaultRouting_holds : pysrDefaultRouting := by
  unfold pysrDefaultRouting
  intros
  rfl

end SymReg.Ext
