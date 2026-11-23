import SymReg.HofMig.Scores
import SymReg.Interface.Rendering

namespace SymReg.HofMig
open DynExpr

/-- The quantity observations consumed by format_dimensions. Dependency string
methods supply text for the dimension and the whole quantity separately. -/
structure DisplayUnit where
  magnitude : JF
  dimensionless : Bool
  dimensionText : String
  quantityText : String
  deriving DecidableEq, Repr

-- Source: src/InterfaceDynamicExpressions.jl:300-314
def formatOutputUnits : Option DisplayUnit → String
  | none => SymReg.Interface.formatDimensions false false false "" ""
  | some u => SymReg.Interface.formatDimensions true (u.magnitude == .fin 1)
      u.dimensionless u.dimensionText u.quantityText

/-- Dataset display metadata used in src/HallOfFame.jl:247-254. -/
structure DisplayData where
  yName : String
  yUnits : Option DisplayUnit
  xUnitsPresent : Bool
  deriving DecidableEq, Repr

-- Source: src/HallOfFame.jl:247-254
/-
function make_prefix(::AbstractExpression, ::AbstractOptions, dataset::Dataset)
    y_prefix = dataset.y_variable_name
    unit_str = format_dimensions(dataset.y_sym_units)
    y_prefix *= unit_str
    if dataset.y_sym_units === nothing && dataset.X_sym_units !== nothing
        y_prefix *= WILDCARD_UNIT_STRING
    end
    return y_prefix * " = "
end
-/
def runPrefix (_tree : Nat) (_scale : LossScale) (data : DisplayData) :
    String × List (Option DisplayUnit) :=
  (data.yName ++ formatOutputUnits data.yUnits ++
    (if data.yUnits.isNone && data.xUnitsPresent then "[?]" else "") ++ " = ", [data.yUnits])

def makePrefix (tree : Nat) (scale : LossScale) (data : DisplayData) : String :=
  (runPrefix tree scale data).1

/-- The minimum terminal width in src/HallOfFame.jl:208. -/
def terminalWidth (width : Option Int) : Int :=
  match width with | none => 100 | some w => max 100 w

/-- Unicode-character chunks from `split_string`, src/Utils.jl:55-59,
called at src/HallOfFame.jl:266. Zero step throws; a negative step with a
multi-character string gives an empty range, and length at most one indexes outside I. -/
def splitCharacters (s : String) (n : Int) : Jl (List String) :=
  if (s.toList.length : Int) ≤ n then pure [s]
  else if n = 0 then throw (.argumentError "step cannot be zero")
  else if n < 0 then
    if s.toList.length > 1 then pure [] else throw .boundsError
  else
    let width := n.toNat
    let count := (s.toList.length + width - 1) / width
    pure ((List.range count).map (fun i =>
      String.ofList ((s.toList.drop (i * width)).take width)))

/-- Julia's `split(s, '\\n')`, src/HallOfFame.jl:45,263, retaining empty
pieces and working on Unicode characters. -/
def splitLineChars : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '\n' then [] :: splitLineChars cs
    else match splitLineChars cs with
      | [] => [[c]]
      | line :: rest => (c :: line) :: rest

/-- String wrapper for Julia's newline split, src/HallOfFame.jl:45,263. -/
def splitLines (s : String) : List String := (splitLineChars s.toList).map String.ofList

/-- Output rows of `wrap_equation_string`, src/HallOfFame.jl:265-279. -/
structure WrappedRow where
  indent : Nat
  text : String
  dots : Bool
  deriving DecidableEq, Repr

/-- A forced line is split before ellipses are assigned, src/HallOfFame.jl:263-276. -/
def wrapPieces (pieces : List String) (width : Int) : Jl (List (String × Bool)) := do
  let groups ← pieces.mapM (fun piece => do
    let chunks ← splitCharacters piece width
    return chunks.zipIdx |>.map (fun (chunk, i) => (chunk, i + 1 < chunks.length)))
  return groups.flatten

/-- `wrap_equation_string`, src/HallOfFame.jl:257-281, retaining row structure
before rendering. Indentation starts only after the first emitted row, even across
explicit newlines; only nonfinal chunks within a forced line get dots. -/
def wrapRows (equation : String) (left : Nat) (terminal : Int) : Jl (List WrappedRow) := do
  let width := terminal - 1 - (left : Int) - 3
  let pieces ← wrapPieces (splitLines equation) width
  return pieces.zipIdx.map (fun ((text, dots), i) =>
    ⟨if i = 0 then 0 else left, text, dots⟩)

/-- Text output of src/HallOfFame.jl:272-281. -/
def renderRow (row : WrappedRow) : String :=
  String.ofList (List.replicate row.indent ' ') ++ row.text ++
    (if row.dots then "..." else "") ++ "\n"

/-- String-returning `wrap_equation_string`, src/HallOfFame.jl:257-281. -/
def wrapEquation (equation : String) (left : Nat) (terminal : Int) : Jl String := do
  return String.join ((← wrapRows equation left terminal).map renderRow)

-- Source: src/HallOfFame.jl:193-214
def headerColumns (scale : LossScale) : List (String × Nat) :=
  [("Complexity", 10), ("Loss", 9)] ++
    (if showScoreColumn scale then [("Score", 9)] else []) ++ [("Equation", 0)]

/-- Visible text of the styled header, src/HallOfFame.jl:193-214. -/
def header (scale : LossScale) : String :=
  let pad := fun (s, n) => s ++ String.ofList (List.replicate (n - s.toList.length) ' ')
  String.intercalate "  " ((headerColumns scale).map pad) ++ "\n"

/-- The external formatting services in src/HallOfFame.jl:220-234. The
expression renderer receives the caller's pretty flag and dataset. Printf is an
external deterministic scalar-to-text service, parameterized rather than rounded by JF. -/
structure TextRuntime where
  equation : Nat → DisplayData → Bool → String
  statistics : Int → JF → Option JF → String

inductive TableEvent where
  | upper (width : Int)
  | header (fields : List String)
  | format
  | row (terminal : Int) (score : Option JF)
  | lower (width : Int)
  deriving DecidableEq, Repr

-- Source: src/HallOfFame.jl:218-242
/-
        eqn_string = string_tree(
            tree,
            options;
            display_variable_names=dataset.display_variable_names,
            X_sym_units=dataset.X_sym_units,
            y_sym_units=dataset.y_sym_units,
            pretty,
        )
        prefix = make_prefix(tree, options, dataset)
        eqn_string = prefix * eqn_string
        stats_columns_string = if show_score_column(options)
            @sprintf("%-10d  %-8.3e  %-8.3e  ", complexity, loss, score)
        else
            @sprintf("%-10d  %-8.3e  ", complexity, loss)
        end
        left_cols_width = length(stats_columns_string)
        print(buffer, stats_columns_string)
        print(
            buffer,
            wrap_equation_string(
                eqn_string, left_cols_width + length(prefix), terminal_width
            ),
        )
-/
def tableRow (text : TextRuntime) (scale : LossScale) (data : DisplayData)
    (pretty : Bool) (terminal : Int) (tree : Nat) (score loss : JF) (complexity : Int) :
    Jl String × TableEvent :=
  let rendered := text.equation tree data pretty
  let eqPrefix := makePrefix tree scale data
  let score := if showScoreColumn scale then some score else none
  let stats := text.statistics complexity loss score
  ((wrapEquation (eqPrefix ++ rendered) (stats.toList.length + eqPrefix.toList.length) terminal).map
    (stats ++ ·), .row terminal score)

-- Source: src/HallOfFame.jl:218-243
def tableRows (text : TextRuntime) (scale : LossScale) (data : DisplayData)
    (pretty : Bool) (terminal : Int) :
    List Nat → List JF → List JF → List Int → Jl (List String) × List TableEvent
  | t :: ts, s :: ss, l :: ls, c :: cs =>
      match tableRow text scale data pretty terminal t s l c with
      | (.error err, call) => (.error err, [call])
      | (.ok row, call) =>
        let (out, calls) := tableRows text scale data pretty terminal ts ss ls cs
        (out.map (row :: ·), call :: calls)
  | _, _, _, _ => (.ok [], [])

-- Source: src/HallOfFame.jl:205-246
def runTable (text : TextRuntime) (scale : LossScale) (data : DisplayData)
    (width : Option Int) (pretty : Bool) (emit : TableEvent → Jl Unit)
    (format : Unit → Jl (Formatted × Nat)) : Jl (String × Nat) × List TableEvent :=
  let terminal := terminalWidth width
  let rule := String.ofList (List.replicate (terminal - 1).toNat '─')
  let upper := TableEvent.upper (terminal - 1)
  let heading := TableEvent.header ((headerColumns scale).map Prod.fst)
  match emit upper with
  | .error e => (.error e, [upper])
  | .ok () =>
    match emit heading with
    | .error e => (.error e, [upper, heading])
    | .ok () =>
      let preamble := [upper, heading, TableEvent.format]
      match format () with
      | .error e => (.error e, preamble)
      | .ok (out, f) =>
        match tableRows text scale data pretty terminal out.trees out.scores out.losses out.complexities with
        | (.error e, rows) => (.error e, preamble ++ rows)
        | (.ok rows, calls) => (.ok (rule ++ "\n" ++ header scale ++ String.join rows ++ rule, f),
            preamble ++ calls ++ [.lower (terminal - 1)])

def stringPareto (rt : ScalarRuntime) (text : TextRuntime) (scale : LossScale)
    (compute : Nat → Int) (data : DisplayData) (h : Hof) (fresh : Nat)
    (width : Option Int := none) (pretty : Bool := true) : Jl (String × Nat) :=
  (runTable text scale data width pretty (fun _ => .ok ())
    (fun _ => formatHof rt scale compute h fresh)).1

/-- Julia `isspace` and `strip`, used by src/HallOfFame.jl:45, including the
Unicode White_Space characters in Julia's character classification. -/
def stripJulia (s : String) : String :=
  let space := fun (c : Char) =>
    let n := c.toNat
    (9 ≤ n && n ≤ 13) || n == 32 || n == 133 || n == 160 || n == 5760 ||
      (8192 ≤ n && n ≤ 8202) || n == 8232 || n == 8233 || n == 8239 ||
      n == 8287 || n == 12288
  String.ofList ((s.toList.dropWhile space).reverse.dropWhile space).reverse

/-- `show(io, MIME"text/plain", hof)`, src/HallOfFame.jl:33-53. The
member renderer is supplied by PopMember's display method. Absent slots never
call it and display undef. Multiline output is stripped before line indentation. -/
def runShowSlot (renderMember : Member → String) (index : Nat) (slot : Slot) :
    String × List Nat :=
  let (memberText, calls) :=
    if slot.exists then (renderMember slot.member, [slot.member.objectId]) else ("undef", [])
  let lines := splitLines (stripJulia memberText)
  let start := "    .exists[" ++ toString index ++ "] = " ++
    (if slot.exists then "true" else "false") ++ "\n" ++
    "    .members[" ++ toString index ++ "] ="
  if lines.length = 1 then (start ++ " " ++ memberText ++ "\n", calls)
  else (start ++ "\n" ++ String.join (lines.map (fun line => "        " ++ line ++ "\n")), calls)

def showSlot (renderMember : Member → String) (index : Nat) (slot : Slot) : String :=
  (runShowSlot renderMember index slot).1

/-- Full `show` loop, src/HallOfFame.jl:36-53. -/
def showHof (renderMember : Member → String) (h : Hof) : String :=
  "HallOfFame{...}:\n" ++ String.join
    (h.slots.zipIdx.map (fun (slot, i) => showSlot renderMember (i + 1) slot))

end SymReg.HofMig
