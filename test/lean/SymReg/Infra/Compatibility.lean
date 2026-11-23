import SymReg.HofMig.Core
import Init.Data.List.SplitOn

namespace SymReg.Infra
open DynExpr

-- A Unicode scalar with the annotations covering its bytes.
abbrev StyledChar := Char × List (String × Nat)
abbrev MeterString := List StyledChar
abbrev Postfix := List (MeterString × MeterString)

structure MeterUpdate where
  value : Int
  values : Postfix
  valueColor : String := "none"

inductive MeterCall where
  | width (bar : Nat)
  | update (bar : Nat) (args : MeterUpdate)
  | finish (bar : Nat)

/-- WrappedProgressBar constructor, src/ProgressBars.jl:9-23. desc overwrites
the same keyword supplied by a caller; devnull is selected by exact env equality. -/
structure ProgressConfiguration where
  total : Int
  description : String
  nullOutput : Bool
  values : List (String × String) := []
  deriving DecidableEq, Repr

def wrappedProgressBar (n iterations : Int) (testEnv : String) : ProgressConfiguration :=
  ⟨n,"Evolving for " ++ toString iterations ++ " iterations...",testEnv == "true",[]⟩

/-- barlen uses Progress.barlen when present, stdout width otherwise,
src/ProgressBars.jl:25-27. -/
def barLength (stored : Option Int) (stdoutWidth : Int) : Int := stored.getD stdoutWidth

private def meterSpaces (n : Nat) : MeterString := List.replicate n (' ', [])

private def meterLines : MeterString → List MeterString
  | [] => [[]]
  | c :: cs =>
    let lines := meterLines cs
    if c.1 = '\n' then [] :: lines
    else match lines with
      | [] => [[c]]
      | line :: rest => (c :: line) :: rest

private theorem meterLines_spec (s : MeterString) :
    meterLines s = s.splitOnP (fun c => c.1 == '\n') := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    simp only [meterLines, ih, List.splitOnP_cons_eq_ite_modifyHead, beq_iff_eq]
    split
    · simp_all
    · have hn := List.splitOnP_ne_nil (fun (x : StyledChar) => x.1 == '\n') cs
      cases hc : cs.splitOnP (fun x => x.1 == '\n') with
      | nil => exact False.elim (hn hc)
      | cons line rest => simp_all [List.modifyHead]

-- Source: src/ProgressBars.jl:53-55
-- function newlines_to_spaces(s::AbstractString, width::Integer)
--     return join(rpad(line, width) for line in split(s, '\n'))
-- end
def newlinesToSpaces (s : MeterString) (width : Int) (textwidth : Char → Nat) : MeterString :=
  (meterLines s).flatMap fun line =>
    line ++ meterSpaces (width.toNat - (line.map (textwidth ∘ Prod.fst)).sum)

-- Source: src/ProgressBars.jl:42-51
-- function format_for_meter((k, s), width::Integer)
--     new_s = if occursin('\n', s)
--         left_margin = length("  $(string(k)):  ")
--         left_padding = ' '^(width - left_margin)
--         annotatedstring(left_padding, newlines_to_spaces(s, width))
--     else
--         s
--     end
--     return (k, new_s)
-- end
def formatForMeter (key value : MeterString) (width : Int) (textwidth : Char → Nat) :
    Jl (MeterString × MeterString) :=
  if value.any (fun c => c.1 == '\n') then
    let margin : Int := key.length + 5
    if width < margin then .error (.argumentError
      ("can't repeat a character " ++ toString (width-margin) ++ " times"))
    else .ok (key, meterSpaces (width-margin).toNat ++ newlinesToSpaces value width textwidth)
  else .ok (key,value)

-- Source: src/ProgressBars.jl:35-40
-- function manually_iterate!(pbar::WrappedProgressBar, value::Int)
--     width = barlen(pbar)
--     postfix = map(Fix{2}(format_for_meter, width), pbar.postfix)
--     ProgressMeter.update!(pbar.bar, value; showvalues=postfix, valuecolor=:none)
--     return nothing
-- end
def manuallyIterate (bar : Nat) (values : Postfix) (value : Int)
    (selectWidth : Nat → Jl Int) (textwidth : Char → Nat) (update : Nat → MeterUpdate → Jl Nat) :
    Jl Unit × List MeterCall :=
  match selectWidth bar with
  | .error e => (.error e, [.width bar])
  | .ok width =>
    match values.mapM (fun (k,s) => formatForMeter k s width textwidth) with
    | .error e => (.error e, [.width bar])
    | .ok formatted =>
      let args : MeterUpdate := ⟨value,formatted,"none"⟩
      ((update bar args).map (fun _ => ()), [.width bar,.update bar args])

-- Source: src/ProgressBars.jl:29-32
-- function ProgressMeter.finish!(pbar::WrappedProgressBar)
--     ProgressMeter.finish!(pbar.bar)
--     return nothing
-- end
def finishProgress (bar : Nat) (finish : Nat → Jl Nat) : Jl Unit × List MeterCall :=
  ((finish bar).map (fun _ => ()), [.finish bar])

def progressConstructor : Prop := ∀ n iterations env stored width,
  (wrappedProgressBar n iterations env).total = n ∧
  (wrappedProgressBar n iterations env).values = [] ∧
  (wrappedProgressBar n iterations env).nullOutput = (env == "true") ∧
  barLength (some stored) width = stored ∧ barLength none width = width

theorem progressConstructor_holds : progressConstructor := by
  intro n iterations env stored width; exact ⟨rfl,rfl,rfl,rfl,rfl⟩

def progressAbsoluteValue : Prop := ∀ bar value selectWidth textwidth update,
  let result := manuallyIterate bar [] value selectWidth textwidth update
  (∀ w, selectWidth bar = .ok w →
    result = ((update bar ⟨value,[],"none"⟩).map (fun _ => ()),
      [.width bar,.update bar ⟨value,[],"none"⟩])) ∧
  (∀ e, selectWidth bar = .error e → result = (.error e,[.width bar]))

theorem progressAbsoluteValue_holds : progressAbsoluteValue := by
  intro bar value selectWidth textwidth update
  constructor <;> intro outcome h <;> simp [manuallyIterate,h] <;> rfl

def progressSingleLine : Prop := ∀ key value width textwidth,
  value.any (fun c => c.1 == '\n') = false →
  formatForMeter key value width textwidth = .ok (key,value)

theorem progressSingleLine_holds : progressSingleLine := by
  intro key value width textwidth h
  simp [formatForMeter,h]
example : ([] : MeterString).any (fun c => c.1 == '\n') = false := rfl

def progressNarrowMultiline : Prop := ∀ key value width textwidth,
  0 < width → ∃ formatted, formatForMeter key value width textwidth = .ok formatted

theorem progressNarrowMultiline_refuted : ¬ progressNarrowMultiline := by
  intro h
  let plain : String → MeterString := fun s => s.toList.map fun c => (c, [])
  rcases h (plain "label") (plain "a\nb") 3 (fun _ => 1) (by decide) with ⟨formatted,hf⟩
  have nl : (plain "a\nb").any (fun c => c.1 == '\n') = true := by decide
  have small : (3 : Int) < Int.ofNat (plain "label").length + 5 := by decide
  simp only [formatForMeter, nl, if_true] at hf
  split at hf
  · contradiction
  · omega

private def expectedMeterText (key value : MeterString) (width : Int)
    (textwidth : Char → Nat) : MeterString :=
  if value.any (fun c => c.1 == '\n') then
    List.replicate (width - (Int.ofNat key.length + 5)).toNat (' ', []) ++
      ((value.splitOnP (fun c => c.1 == '\n')).map fun line =>
        let cols := (line.map (fun c => textwidth c.1)).sum
        line ++ List.replicate (width.toNat - cols) (' ', [])).flatten
  else value

def progressFormattedUpdate : Prop := ∀ bar values value selectWidth textwidth update w,
  selectWidth bar = .ok w →
  (∀ k s, (k,s) ∈ values → s.any (fun c => c.1 == '\n') = true → Int.ofNat k.length + 5 ≤ w) →
  let expected := values.map fun (k,s) => (k, expectedMeterText k s w textwidth)
  (manuallyIterate bar values value selectWidth textwidth update).2 =
    [.width bar,.update bar ⟨value,expected,"none"⟩]

private theorem formatPostfix (values : Postfix) (w : Int) (textwidth : Char → Nat)
    (margin : ∀ k s, (k,s) ∈ values → s.any (fun c => c.1 == '\n') = true →
      Int.ofNat k.length + 5 ≤ w) :
    values.mapM (fun (k,s) => formatForMeter k s w textwidth) =
      .ok (values.map fun (k,s) => (k, expectedMeterText k s w textwidth)) := by
  induction values with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨k,s⟩ := pair
    have hr := ih (fun a b hm => margin a b (by simp [hm]))
    have hf : formatForMeter k s w textwidth = .ok (k,expectedMeterText k s w textwidth) := by
      cases h : s.any (fun c => c.1 == '\n')
      · simp [formatForMeter, expectedMeterText,h]
      · have hn := margin k s (by simp) h
        simp [formatForMeter, expectedMeterText,h,newlinesToSpaces,meterSpaces,
          List.flatMap,Function.comp_def,meterLines_spec] <;> omega
    simp [List.mapM_cons, hf, hr] <;> rfl

theorem progressFormattedUpdate_holds : progressFormattedUpdate := by
  intro bar values value selectWidth textwidth update w hw margin
  simp [manuallyIterate, hw, formatPostfix values w textwidth margin]

example : ∀ (s : MeterString), (s,s) ∉ ([] : Postfix) := by simp

def progressFinishForwarding : Prop := ∀ bar finish,
  let result := finishProgress bar finish
  result.2 = [.finish bar] ∧
  (∀ n, finish bar = .ok n → result.1 = .ok ()) ∧
  (∀ e, finish bar = .error e → result.1 = .error e)

theorem progressFinishForwarding_holds : progressFinishForwarding := by
  intro bar finish
  refine ⟨rfl, ?_, ?_⟩ <;> intro outcome h <;> simp [finishProgress,h] <;> rfl

def progressPaddingRetains : Prop := ∀ s width textwidth,
  newlinesToSpaces s width textwidth =
    ((s.splitOnP (fun c => c.1 == '\n')).map fun line =>
      let columns := (line.map (fun c => textwidth c.1)).sum
      if columns ≥ width.toNat then line
      else line ++ List.replicate (width.toNat-columns) (' ',[])).flatten

theorem progressPaddingRetains_holds : progressPaddingRetains := by
  intro s width textwidth
  unfold newlinesToSpaces
  simp only [List.flatMap, meterLines_spec]
  apply congrArg List.flatten
  apply congrArg (fun f : MeterString → MeterString => List.map f (s.splitOnP (fun c => c.1 == '\n')))
  funext line
  simp only [Function.comp_def]
  split
  · rename_i hn
    simp [meterSpaces, Nat.sub_eq_zero_of_le hn]
  · rfl

/-- Deprecated best_of_sample adapts only AdaptiveParsimonyPlugin states,
src/deprecates.jl:12-29. Other plugins receive nothing, preserving tuple order. -/
def legacyPluginStates (adaptive : List Bool) (statistics : Nat) : List (Option Nat) :=
  adaptive.map (fun b => if b then some statistics else none)

def legacyBestOfSample (population options statistics : Nat) (plugins : List Bool)
    (replacement : Nat → Nat → List (Option Nat) → Jl Nat) : Jl Nat :=
  replacement population options (legacyPluginStates plugins statistics)

-- Source: src/deprecates.jl:40-47
-- @deprecate(
--     calculate_pareto_frontier(X, y, hallOfFame, options; weights=nothing),
--     calculate_pareto_frontier(hallOfFame)
-- )
-- @deprecate(
--     calculate_pareto_frontier(dataset, hallOfFame, options),
--     calculate_pareto_frontier(hallOfFame)
-- )
structure LegacyHall where
  memberArray : Nat
  existenceArray : Nat
  value : HofMig.Hof

private abbrev LegacyFrontier (W : Type) := LegacyHall → W → Jl (List HofMig.Member) × W
private abbrev LegacyFrontierM (W : Type) :=
  ExceptT JlError (StateM (W × List (Nat × Nat))) (List HofMig.Member)

private def observeLegacyFrontier (replacement : LegacyFrontier W) (hall : LegacyHall) :
    LegacyFrontierM W :=
  ExceptT.mk fun (before, calls) =>
    let (result, after) := replacement hall before
    (result, (after, calls ++ [(hall.memberArray, hall.existenceArray)]))

-- Source: src/deprecates.jl:40-43
def legacyParetoArrays (_x _y : Nat) (hall : LegacyHall) (_options : Nat)
    (_weights : Option Nat) (replacement : LegacyHall → LegacyFrontierM W) : LegacyFrontierM W :=
  replacement hall

-- Source: src/deprecates.jl:44-47
def legacyParetoDataset (_dataset : Nat) (hall : LegacyHall) (_options : Nat)
    (replacement : LegacyHall → LegacyFrontierM W) : LegacyFrontierM W :=
  replacement hall

-- Source: src/deprecates.jl:10
-- Base.@deprecate_binding EvalOptions EvalContext
def contextBinding (bindings : String → Option Nat) (name : String) : Option Nat :=
  if name = "EvalOptions" then bindings "EvalContext" else bindings name

/-- Generic matrix/vector/dataset EquationSearch overloads, src/deprecates.jl:49-59.
Keyword values and ordering are preserved, including callbacks and saved states,
represented by identity tokens. -/
def legacyEquationSearch (args : List Nat) (keywords : List (String × Nat))
    (replacement : List Nat → List (String × Nat) → Jl Nat) : Jl Nat :=
  replacement args keywords

/-- Same-type matrix overload's explicit defaults/keyword order,
src/deprecates.jl:61-95. multithreaded is forwarded unchanged; the modern API
rejects non-nothing values rather than remapping them to parallelism. -/
structure LegacySearchKeywords where
  iterations : Int := 10
  weights : Option Nat := none
  variableNames : Option Nat := none
  options : Nat
  parallelism : String := "multithreading"
  numprocs : Option Int := none
  procs : Option (List Nat) := none
  addprocs : Option Nat := none
  runtests : Bool := true
  savedState : Option Nat := none
  lossType : Nat := 0
  multithreaded : Option Bool := none
  deriving DecidableEq, Repr

def legacyMatrixSearch (X y : Nat) (k : LegacySearchKeywords)
    (replacement : Nat → Nat → LegacySearchKeywords → Jl Nat) : Jl Nat :=
  replacement X y k

/-- Dataset-vector overload, src/deprecates.jl:97-120, forwards exactly its
listed eight keywords. Arguments absent from that overload are not synthesized. -/
structure LegacyDatasetKeywords where
  iterations : Int := 10
  options : Nat
  parallelism : String := "multithreading"
  numprocs : Option Int := none
  procs : Option (List Nat) := none
  addprocs : Option Nat := none
  runtests : Bool := true
  savedState : Option Nat := none
  deriving DecidableEq, Repr

def legacyDatasetsSearch (datasets : List Nat) (k : LegacyDatasetKeywords)
    (replacement : List Nat → LegacyDatasetKeywords → Jl Nat) : Jl Nat :=
  replacement datasets k

def deprecationForwarding : Prop := ∀ args keywords search X y k matrix datasets dk dsSearch,
  legacyEquationSearch args keywords search = search args keywords ∧
  legacyMatrixSearch X y k matrix = matrix X y k ∧
  legacyDatasetsSearch datasets dk dsSearch = dsSearch datasets dk

theorem deprecationForwarding_holds : deprecationForwarding := by
  intro args keywords search X y k matrix datasets dk dsSearch; exact ⟨rfl,rfl,rfl⟩

def deprecationPluginMapping : Prop := ∀ population options statistics plugins replacement,
  legacyBestOfSample population options statistics plugins replacement =
    replacement population options (plugins.map (fun b => if b then some statistics else none)) ∧
  (legacyPluginStates plugins statistics).length = plugins.length

theorem deprecationPluginMapping_holds : deprecationPluginMapping := by
  intro population options statistics plugins replacement
  simp [legacyBestOfSample,legacyPluginStates]

def deprecationDiscardedArguments : Prop :=
  (∀ (W : Type) (hall : LegacyHall) x y dataset options weights
      (replacement : LegacyFrontier W) (before after : W) (calls : List (Nat × Nat))
      (result : Jl (List HofMig.Member)),
    replacement hall before = (result, after) →
    (legacyParetoArrays x y hall options weights (observeLegacyFrontier replacement)).run (before, calls) =
      (result, (after, calls ++ [(hall.memberArray, hall.existenceArray)])) ∧
    (legacyParetoDataset dataset hall options (observeLegacyFrontier replacement)).run (before, calls) =
      (result, (after, calls ++ [(hall.memberArray, hall.existenceArray)]))) ∧
  (∀ bindings, contextBinding bindings "EvalOptions" = bindings "EvalContext" ∧
    contextBinding bindings "EvalContext" = bindings "EvalContext")

theorem deprecationDiscardedArguments_holds : deprecationDiscardedArguments := by
  constructor
  · intro W hall x y dataset options weights replace before after calls result h
    simp [legacyParetoArrays, legacyParetoDataset, observeLegacyFrontier, ExceptT.run, ExceptT.mk, h]
  · intro bindings
    exact ⟨rfl, rfl⟩

example : contextBinding (fun name => if name = "EvalContext" then some 42 else some 17)
    "EvalOptions" = some 42 := rfl


end SymReg.Infra
