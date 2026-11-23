import SymReg.HofMig.Display

namespace SymReg.HofMig
open DynExpr

def prefix_exact : Prop := ∀ tree scale name,
  (∀ (units : DisplayUnit) hasInput,
    let text := if units.magnitude = .fin 1 then
      if units.dimensionless then "" else "[" ++ units.dimensionText ++ "]"
      else "[" ++ units.quantityText ++ "]"
    runPrefix tree scale ⟨name, some units, hasInput⟩ =
      (name ++ text ++ " = ", [some units])) ∧
  runPrefix tree scale ⟨name, none, true⟩ = (name ++ "[?] = ", [none]) ∧
  runPrefix tree scale ⟨name, none, false⟩ = (name ++ " = ", [none])

theorem prefix_exact_holds : prefix_exact := by
  intro tree scale name
  refine ⟨?_, by simp [runPrefix, formatOutputUnits, SymReg.Interface.formatDimensions,
    String.append_assoc], by simp [runPrefix, formatOutputUnits, SymReg.Interface.formatDimensions]⟩
  intro units hasInput
  by_cases h : units.magnitude = .fin 1 <;>
    simp [runPrefix, formatOutputUnits, SymReg.Interface.formatDimensions, h]

example : makePrefix 2 .linear ⟨"y", some ⟨.fin 2, false, "m", "2 m"⟩, true⟩ =
    "y[2 m] = " := rfl

def terminal_minimum : Prop := ∀ (width : Option Int), 100 ≤ terminalWidth width

theorem terminal_minimum_holds : terminal_minimum := by
  intro width
  cases width with
  | none => decide
  | some w => simp only [terminalWidth]; omega

def short_wrap : Prop := ∀ (equation : String) (left : Nat) (terminal : Int),
  splitLines equation = [equation] →
  (equation.toList.length : Int) ≤ terminal - 1 - (left : Int) - 3 →
  wrapEquation equation left terminal = .ok (equation ++ "\n")

theorem short_wrap_holds : short_wrap := by
  intro equation left terminal hs hw
  simp [wrapEquation, wrapRows, hs, wrapPieces, splitCharacters, hw, renderRow,
    pure, Except.pure, bind, Except.bind]

example : (splitLines "abc" = ["abc"]) ∧
    ("abc".toList.length : Int) ≤ 100 - 1 - (20 : Int) - 3 := by decide

def wrap_retains_equation : Prop := ∀ (equation : String) (left : Nat) (terminal : Int),
  equation ≠ "" → 100 ≤ terminal →
  ∃ wrapped, wrapEquation equation left terminal = .ok wrapped ∧ wrapped ≠ ""

theorem wrap_retains_equation_refuted : ¬ wrap_retains_equation := by
  intro hp
  obtain ⟨out, ho, hn⟩ := hp "abc" 100 100 (by decide) (by decide)
  have he : wrapEquation "abc" 100 100 = .ok "" := by decide
  rw [he] at ho
  cases ho
  exact hn rfl

def show_absent : Prop := ∀ (renderMember : Member → String) (index : Nat) (m : Member),
  runShowSlot renderMember index ⟨m, false⟩ =
    ("    .exists[" ++ toString index ++ "] = false\n" ++
     "    .members[" ++ toString index ++ "] = undef\n", []) ∧
  (runShowSlot renderMember index ⟨m, true⟩).2 = [m.objectId]

theorem show_absent_holds : show_absent := by
  intro renderMember index m
  constructor
  · simp [runShowSlot, stripJulia, splitLines, splitLineChars, String.append_assoc]
  · simp only [runShowSlot, if_true]
    split <;> rfl

def empty_table : Prop := ∀ (rt : ScalarRuntime) (text : TextRuntime) (scale : LossScale)
    (compute : Nat → Int) (data : DisplayData) (fresh : Nat) (width : Option Int) (pretty : Bool),
  let rule := String.ofList (List.replicate (terminalWidth width - 1).toNat '─')
  stringPareto rt text scale compute data ⟨[]⟩ fresh width pretty =
    .ok (rule ++ "\n" ++ header scale ++ rule, fresh)

theorem empty_table_holds : empty_table := by
  intro rt text scale compute data fresh width pretty
  simp [stringPareto, runTable, formatHof, calculatePareto, frontRaw, copyMembers, scoreRows,
    firstNegative, typedScoreRows, Except.map, tableRows, pure, Except.pure, bind, Except.bind]

def table_failure : Prop := ∀ (text : TextRuntime) (scale : LossScale)
    (data : DisplayData) (width : Option Int) (pretty : Bool) (e : JlError)
    (format : Unit → Jl (Formatted × Nat)),
  let w := terminalWidth width - 1
  let heading := TableEvent.header
    (if scale = .log then ["Complexity", "Loss", "Score", "Equation"]
      else ["Complexity", "Loss", "Equation"])
  (runTable text scale data width pretty (fun _ => .error e) format =
    (.error e, [.upper w])) ∧
  (runTable text scale data width pretty
    (fun event => match event with | .upper _ => .ok () | _ => .error e) format =
    (.error e, [.upper w, heading])) ∧
  (runTable text scale data width pretty (fun _ => .ok ()) (fun _ => .error e) =
    (.error e, [.upper w, heading, .format]))

theorem table_failure_holds : table_failure := by
  intro text scale data width pretty e format
  cases scale <;> simp [runTable, headerColumns, showScoreColumn]

private def scoresOfRows (trees : List Nat) (scores losses : List JF)
    (complexities : List Int) : List JF :=
  scores.take (min trees.length (min losses.length complexities.length))

private theorem tableRows_trace (text : TextRuntime) (scale : LossScale) (data : DisplayData)
    (pretty : Bool) (terminal : Int) (trees : List Nat) (scores losses : List JF)
    (complexities : List Int) (rows : List String) (events : List TableEvent)
    (h : tableRows text scale data pretty terminal trees scores losses complexities =
      (.ok rows, events)) :
    events = (scoresOfRows trees scores losses complexities).map
      (fun s => .row terminal (if scale = .log then some s else none)) := by
  induction trees generalizing scores losses complexities rows events with
  | nil => simp [tableRows, scoresOfRows] at h ⊢; exact h.2
  | cons t ts ih =>
    cases scores with
    | nil => simp [tableRows, scoresOfRows] at h ⊢; exact h.2
    | cons s ss =>
      cases losses with
      | nil => simp [tableRows, scoresOfRows] at h ⊢; exact h.2
      | cons l ls =>
        cases complexities with
        | nil => simp [tableRows, scoresOfRows] at h ⊢; exact h.2
        | cons c cs =>
          rcases hrow : tableRow text scale data pretty terminal t s l c with ⟨result, event⟩
          cases result with
          | error e => simp [tableRows, hrow] at h
          | ok row =>
            rcases hrest : tableRows text scale data pretty terminal ts ss ls cs with ⟨result, rest⟩
            cases result with
            | error e => simp [tableRows, hrow, hrest, Except.map] at h
            | ok tail =>
              have he : event = (tableRow text scale data pretty terminal t s l c).2 :=
                (congrArg Prod.snd hrow).symm
              have htail := ih ss ls cs tail rest hrest
              simp [tableRows, hrow, hrest, Except.map] at h
              rw [← h.2, htail]
              cases scale <;>
                simp [he, tableRow, showScoreColumn, scoresOfRows, Nat.succ_min_succ]

private theorem table_trace (text : TextRuntime) (scale : LossScale) (data : DisplayData)
    (width : Option Int) (pretty : Bool) (emit : TableEvent → Jl Unit)
    (format : Unit → Jl (Formatted × Nat)) (out : Formatted) (fresh : Nat)
    (value : String × Nat) (events : List TableEvent)
    (hf : format () = .ok (out, fresh))
    (h : runTable text scale data width pretty emit format = (.ok value, events)) :
    let w := terminalWidth width
    events = [.upper (w - 1), .header (if scale = .log then
      ["Complexity", "Loss", "Score", "Equation"] else ["Complexity", "Loss", "Equation"]), .format] ++
      (scoresOfRows out.trees out.scores out.losses out.complexities).map
        (fun s => .row w (if scale = .log then some s else none)) ++ [.lower (w - 1)] ∧
    let rule := String.ofList (List.replicate (w - 1).toNat '─')
    ∃ middle, value.1 = rule ++ middle ++ rule := by
  unfold runTable at h
  dsimp only at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · rcases hr : tableRows text scale data pretty (terminalWidth width)
          out.trees out.scores out.losses out.complexities with ⟨result, calls⟩
      cases result with
      | error e => simp [hf, hr] at h
      | ok rows =>
        have hrows := tableRows_trace text scale data pretty (terminalWidth width)
          _ _ _ _ rows calls hr
        simp only [hf, hr, Prod.mk.injEq] at h
        constructor
        · rw [← h.2, hrows]
          cases scale <;> rfl
        · refine ⟨"\n" ++ header scale ++ String.join rows, ?_⟩
          rw [← congrArg Prod.fst (Except.ok.inj h.1)]
          simp [String.append_assoc]

def score_column_consistency : Prop := ∀ (text : TextRuntime) (scale : LossScale) data width
    pretty emit (format : Unit → Jl (Formatted × Nat)) out fresh value events,
    format () = .ok (out, fresh) →
    runTable text scale data width pretty emit format = (.ok value, events) →
    events[1]? = some (.header (if scale = .log then
      ["Complexity", "Loss", "Score", "Equation"] else ["Complexity", "Loss", "Equation"])) ∧
    events.filterMap (fun e => match e with | .row _ s => some s | _ => none) =
      (scoresOfRows out.trees out.scores out.losses out.complexities).map
        (fun s => if scale = .log then some s else none)

theorem score_column_consistency_holds : score_column_consistency := by
  intro text scale data width pretty emit format out fresh value events hf h
  rw [(table_trace text scale data width pretty emit format out fresh value events hf h).1]
  simp [List.filterMap_append, List.filterMap_map, Function.comp_def]

def terminal_width_rendering : Prop := ∀ (text : TextRuntime) (scale : LossScale) data width
    pretty emit (format : Unit → Jl (Formatted × Nat)) out fresh value events,
    format () = .ok (out, fresh) →
    runTable text scale data width pretty emit format = (.ok value, events) →
    let selected := if 100 ≤ width.getD 100 then width.getD 100 else 100
    events.head? = some (.upper (selected - 1)) ∧
    events.getLast? = some (.lower (selected - 1)) ∧
    events.filterMap (fun e => match e with | .row w _ => some w | _ => none) =
      List.replicate (scoresOfRows out.trees out.scores out.losses out.complexities).length selected ∧
    let rule := String.ofList (List.replicate (selected - 1).toNat '─')
    ∃ middle, value.1 = rule ++ middle ++ rule

theorem terminal_width_rendering_holds : terminal_width_rendering := by
  intro text scale data width pretty emit format out fresh value events hf h
  have hw : terminalWidth width = if 100 ≤ width.getD 100 then width.getD 100 else 100 := by
    cases width with
    | none => decide
    | some w => by_cases hn : 100 ≤ w <;> simp [terminalWidth, hn] <;> omega
  have ht := table_trace text scale data width pretty emit format out fresh value events hf h
  rw [ht.1, hw]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [List.getLast?_append]
    rfl
  · simp [List.filterMap_append, List.filterMap_map, Function.comp_def, List.map_const']
  · simpa [hw] using ht.2

end SymReg.HofMig
