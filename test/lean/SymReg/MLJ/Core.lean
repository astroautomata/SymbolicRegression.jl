import SymReg.HofMig.Scores

/-! The MLJ interface, src/MLJInterface.jl at SR daae84e5. Hall-of-fame
formatting reuses `SymReg.HofMig.formatHof`; expression content is the uninterpreted
`Nat` of `HofMig.Member.tree`. Expression evaluation, rendering, `Options`
construction, the warm-start check and `equation_search` are supplied services. -/

namespace SymReg.MLJ
open DynExpr
open SymReg.HofMig

/-! ## Julia comparisons and reductions on `Float64` (JF) -/

/-- IEEE `<=` at src/MLJInterface.jl:728; comparisons with NaN are false. -/
def lessEq (a b : JF) : Bool := less a b || (decide (a = b) && a != .nan)

/-- Base `isless` on floats: NaN is above every other value and equal to itself. -/
def isLess : JF → JF → Bool
  | .nan, _ => false
  | _, .nan => true
  | a, b => less a b

/-- Base `isgreater`, the order used by `findmin`: NaN is selected like a minimum. -/
def isGreater (a b : JF) : Bool :=
  if a = .nan ∨ b = .nan then isLess a b else isLess b a

/-- The empty-reduction error of `minimum`, `argmin` and `argmax`. -/
def emptyReduction : JlError :=
  .argumentError "reducing over an empty collection is not allowed; consider supplying `init` to the reducer"

/-- The `findmax`/`findmin` fold (`_rf_findmax`, `_rf_findmin`): the incumbent
`(m, im)` is replaced by `(x, ix)` exactly when `replace m x`. -/
def findAux (replace : JF → JF → Bool) : JF × Nat → List JF → Nat → JF × Nat
  | acc, [], _ => acc
  | (m, im), x :: xs, ix => findAux replace (if replace m x then (x, ix) else (m, im)) xs (ix + 1)

/-- One-based `argmax`, src/MLJInterface.jl:727. -/
def argmax : List JF → Jl Nat
  | [] => .error emptyReduction
  | x :: xs => .ok (findAux isLess (x, 1) xs 2).2

/-- One-based `argmin`, src/MLJInterface.jl:723. -/
def argmin : List JF → Jl Nat
  | [] => .error emptyReduction
  | x :: xs => .ok (findAux isGreater (x, 1) xs 2).2

/-- Float `min`, which returns NaN when either argument is NaN. -/
def jmin (a b : JF) : JF :=
  if a = .nan ∨ b = .nan then .nan else if less b a then b else a

/-- `minimum`, src/MLJInterface.jl:726: NaN-propagating reduction. -/
def minimum : List JF → Jl JF
  | [] => .error emptyReduction
  | x :: xs => .ok (xs.foldl jmin x)

/-! ## Selection, src/MLJInterface.jl:715-751 -/

/-- The comprehension of src/MLJInterface.jl:727-729: eligible rows read
`scores[i]` (a BoundsError when absent); the rest are `typemin(L) = -Inf`. -/
def maskScores (threshold : JF) : List JF → List JF → Jl (List JF)
  | [], _ => .ok []
  | l :: ls, ss => do
    let v ← if lessEq l threshold then
        (match ss with | s :: _ => pure s | [] => throw .boundsError)
      else pure .negInf
    let rest ← maskScores threshold ls ss.tail
    return v :: rest

/-- `choose_best`, src/MLJInterface.jl:715-730. `scale` is `options.loss_scale`,
`none` for `options=nothing`. `trees` and `complexities` are unused. -/
def chooseBest (losses scores : List JF) (scale : Option LossScale) : Jl Nat :=
  if scale = some .linear then argmin losses
  else do
    let m ← minimum losses
    argmax (← maskScores (.fin (3 / 2) * m) losses scores)


/-- The parts of an `Options` object read in src/MLJInterface.jl: formatting
(`loss_scale`, complexity), `string_tree` rendering (pretty=false) and `eval_tree_array`.
`rest` stands for every other field, compared by the warm-start check. -/
structure Opts where
  rt : ScalarRuntime
  scale : LossScale
  compute : Nat → Int
  render : Nat → List String → String
  eval : Nat → List (List JF) → List JF × Bool
  rest : Nat

/-- Selector argument values at a call, followed by the index that call returned. -/
structure SelectionCall where
  vectors : Formatted
  options : Opts
  index : Int

/-- The selector can write into its four vector arguments and update its closure state. -/
abbrev SelectionMethod := Formatted → Opts → Nat → Jl (Int × Formatted × Nat)

/-- The default `selection_method = choose_best`, src/MLJInterface.jl:86. -/
def chooseBestMethod : SelectionMethod := fun f o state => do
  let best ← chooseBest f.losses f.scores (some o.scale)
  return (Int.ofNat best, f, state)

-- Source: src/MLJInterface.jl:732-737
-- length(trees) == 0 && return 0
-- return m.selection_method(; trees, losses, scores, complexities, options)
def dispatch1 (sel : SelectionMethod) (f : Formatted) (o : Opts) (state : Nat) :
    Jl (Int × Formatted × Nat × List SelectionCall) := do
  if f.trees.isEmpty then return (0, f, state, [])
  let (best, updated, state') ← sel f o state
  return (best, updated, state', [⟨f, o, best⟩])

/-- Run the selector on each target in order, threading the closure state. -/
def selectTargets (sel : SelectionMethod) (o : Opts) :
    List Formatted → Nat → Jl (List Int × List Formatted × Nat × List SelectionCall)
  | [], state => .ok ([], [], state, [])
  | f :: fs, state => do
    let (best, updated, state') ← sel f o state
    let (bs, us, state'', calls) ← selectTargets sel o fs state'
    return (best :: bs, updated :: us, state'', ⟨f, o, best⟩ :: calls)

-- Source: src/MLJInterface.jl:738-751
-- any(t -> length(t) == 0, trees) && return fill(0, length(trees))
-- return [
--     m.selection_method(;
--         trees=trees[i],
--         losses=losses[i],
--         scores=scores[i],
--         complexities=complexities[i],
--         options,
--     ) for i in eachindex(trees)
-- ]
def dispatchK (sel : SelectionMethod) (fs : List Formatted) (o : Opts) (state : Nat) :
    Jl (List Int × List Formatted × Nat × List SelectionCall) :=
  if fs.any (fun f => f.trees.isEmpty) then .ok (fs.map fun _ => 0, fs, state, [])
  else selectTargets sel o fs state

/-! ## Options, model structs and fit results -/

/-- The four generated structs, src/MLJInterface.jl:129-134. -/
inductive ModelName where
  | srRegressor | multitargetSRRegressor | srTestRegressor | multitargetSRTestRegressor
  deriving DecidableEq, Repr

def ModelName.isTest : ModelName → Bool
  | .srTestRegressor | .multitargetSRTestRegressor => true
  | _ => false

def ModelName.isMulti : ModelName → Bool
  | .multitargetSRRegressor | .multitargetSRTestRegressor => true
  | _ => false

/-- `default_niterations` passed by src/MLJInterface.jl:129-134 to src/MLJInterface.jl:68,73. -/
def defaultNiterations (k : ModelName) : Int := if k.isTest then 1 else 100

/-- The default stated by the docstring hyper-parameter list, src/MLJInterface.jl:808. -/
def documentedNiterations : Int := 10

/-- A keyword value given for `parallelism`. -/
inductive KwValue where
  | symbol (s : String)
  | string (s : String)
  deriving DecidableEq, Repr

/-- Storing a keyword in the field `parallelism::Symbol`, src/MLJInterface.jl:74:
`@kwdef` passes it to the default constructor, which accepts only a `Symbol`. -/
def storeParallelism : KwValue → Jl String
  | .symbol s => .ok s
  | .string _ => .error (.methodError "no method matching SRRegressor(..., ::String, ...)")

/-- The regressor fields read by src/MLJInterface.jl (all four structs). -/
structure Regressor where
  name : ModelName
  niterations : Int
  selection : SelectionMethod
  parallelism : String
  selectionState : Nat := 0

/-- `SRRegressor(; ...)` with only `parallelism` given, src/MLJInterface.jl:72-88. -/
def construct (k : ModelName) (parallelism : KwValue) : Jl Regressor := do
  let p ← storeParallelism parallelism
  return ⟨k, defaultNiterations k, chooseBestMethod, p, 0⟩

/-- `MMI.clean!`, src/MLJInterface.jl:217: an empty message, no correction. -/
def clean (m : Regressor) : String × Regressor := ("", m)

/-- `DynamicQuantities` dimensions: decidable equality and `D()`, the
dimensionless value (`iszero` holds exactly for it). -/
class Dims (D : Type) where
  deq : DecidableEq D
  none : D

instance [Dims D] : DecidableEq D := Dims.deq

/-- A data entry: its stripped value and `dimension_with_fallback`, src/MLJInterface.jl:465-470
(plain numbers have dimension `D()`). -/
abbrev Cell (D : Type) := JF × D

/-- Feature or target inputs: a vector, a matrix given by its columns
(observations are rows), and a NamedTuple table of column vectors. -/
inductive Data (D : Type) where
  | vector (v : List (Cell D))
  | matrix (nrows : Nat) (cols : List (List (Cell D)))
  | table (cols : List (String × List (Cell D)))

/-- `Xm_t`: features (rows) by observations. -/
structure Mat where
  nobs : Nat
  rows : List (List JF)
  deriving DecidableEq, Repr

/-- The single-target search state `(populations, hall_of_fame)`; populations are opaque. -/
structure State1 where
  pops : Nat
  hof : Hof

/-- The multitarget search state, one hall of fame per target. -/
structure StateK where
  pops : Nat
  hofs : List Hof

/-- `SRFitResult`, src/MLJInterface.jl:162-181, for state `S` and target units `U`. -/
structure FitResult (S U D : Type) where
  model : Regressor
  state : S
  niterations : Int
  numTargets : Nat
  options : Opts
  variableNames : List String
  yVariableNames : Option (List String)
  yIsTable : Bool
  xUnits : Option (List D)
  yUnits : U

abbrev Fit1 (D : Type) := FitResult State1 (Option D) D
abbrev FitK (D : Type) := FitResult StateK (Option (List D)) D

/-! ## Reports, src/MLJInterface.jl:184-215,538-545,699-713 -/

structure Report1 where
  bestIdx : Int
  equations : List Nat
  equationStrings : Option (List String)
  losses : List JF
  complexities : List Int
  scores : List JF
  selectionState : Nat
  selectionCalls : List SelectionCall

structure ReportK where
  bestIdx : List Int
  equations : List (List Nat)
  equationStrings : Option (List (List String))
  losses : List (List JF)
  complexities : List (List Int)
  scores : List (List JF)
  selectionState : Nat
  selectionCalls : List SelectionCall

/-- Single-target `get_equation_strings_for`, src/MLJInterface.jl:699-705. -/
def strings1 (o : Opts) (trees : List Nat) (names : List String) : List String :=
  trees.map (o.render · names)

/-- Multitarget `get_equation_strings_for`, src/MLJInterface.jl:706-713. -/
def stringsK (o : Opts) (trees : List (List Nat)) (names : List String) : List (List String) :=
  trees.map (strings1 o · names)

/-- Single-target `full_report`, src/MLJInterface.jl:184-215. `fresh` is the
identity supply consumed by the frontier copies of `format_hall_of_fame`. -/
def fullReport1 (m : Regressor) (fr : FitResult State1 U D) (withStrings : Bool) (fresh : Nat) :
    Jl (Report1 × Nat) := do
  let o := fr.options
  let (f, fresh') ← formatHof o.rt o.scale o.compute fr.state.hof fresh
  let strs := if withStrings then some (strings1 o f.trees fr.variableNames) else none
  let (best, updated, state, calls) ← dispatch1 m.selection f o m.selectionState
  return (⟨best, updated.trees, strs, updated.losses, updated.complexities, updated.scores, state, calls⟩, fresh')

/-- Multitarget `full_report`, using the vector `format_hall_of_fame`. -/
def fullReportK (m : Regressor) (fr : FitResult StateK U D) (withStrings : Bool) (fresh : Nat) :
    Jl (ReportK × Nat) := do
  let o := fr.options
  let (fs, fresh') ← formatMany o.rt o.scale o.compute fr.state.hofs fresh
  let trees := fs.map Formatted.trees
  let strs := if withStrings then some (stringsK o trees fr.variableNames) else none
  let (best, updated, state, calls) ← dispatchK m.selection fs o m.selectionState
  return (⟨best, updated.map Formatted.trees, strs, updated.map Formatted.losses,
    updated.map Formatted.complexities, updated.map Formatted.scores, state, calls⟩, fresh')

/-- `MMI.fitted_params`, src/MLJInterface.jl:538-545. -/
def fittedParams1 (m : Regressor) (fr : FitResult State1 U D) (fresh : Nat) :
    Jl (Int × List Nat × Option (List String)) := do
  let (r, _) ← fullReport1 m fr true fresh
  return (r.bestIdx, r.equations, r.equationStrings)

def fittedParamsK (m : Regressor) (fr : FitResult StateK U D) (fresh : Nat) :
    Jl (List Int × List (List Nat) × Option (List (List String))) := do
  let (r, _) ← fullReportK m fr true fresh
  return (r.bestIdx, r.equations, r.equationStrings)

/-! ## Data and units, src/MLJInterface.jl:322-331,412-448,456-536 -/

variable {D : Type} [Dims D]

/-- `clean_units(::AbstractDimensions)`, src/MLJInterface.jl:322-326. -/
def cleanUnits (u : D) : Option D := if u = Dims.none then none else some u

/-- `clean_units(::Vector)`, src/MLJInterface.jl:327-331. -/
def cleanUnitsVec (us : List D) : Option (List D) :=
  if us.all (fun u => decide (u = Dims.none)) then none else some us

/-- The `dims` comprehension of src/MLJInterface.jl:524: `first(row)` of each feature. -/
def firstDims : List (List (Cell D)) → Jl (List D)
  | [] => .ok []
  | [] :: _ => .error .boundsError
  | (c :: _) :: rs => do return c.2 :: (← firstDims rs)

/-- The consistency loop of src/MLJInterface.jl:525-528, features numbered from `i`. -/
def checkRows (i : Nat) : List (List (Cell D)) → List D → Jl Unit
  | r :: rs, d :: ds =>
    if r.all (fun c => decide (c.2 = d)) then checkRows (i + 1) rs ds
    else .error (.errorException s!"Inconsistent units in feature {i} of matrix.")
  | _, _ => .ok ()

/-- Matrix `unwrap_units_single`, src/MLJInterface.jl:523-530. -/
def unwrapMatrix (rows : List (List (Cell D))) : Jl (List (List JF) × List D) := do
  let dims ← firstDims rows
  checkRows 1 rows dims
  return (rows.map (·.map Prod.fst), dims)

/-- Vector `unwrap_units_single`, src/MLJInterface.jl:531-536. -/
def unwrapVector (v : List (Cell D)) : Jl (List JF × D) :=
  match v with
  | [] => .error .boundsError
  | c :: _ =>
    if v.all (fun x => decide (x.2 = c.2)) then .ok (v.map Prod.fst, c.2)
    else .error (.errorException "Inconsistent units in vector.")

def Data.isTable : Data D → Bool
  | .table _ => true
  | _ => false

/-- `_matrix(X; transpose=true)` and the observation count, src/MLJInterface.jl:376-393:
a vector becomes one feature; a NamedTuple is `reduce(hcat, values)`. -/
def transposed : Data D → Jl (Nat × List (List (Cell D)))
  | .vector v => .ok (v.length, [v])
  | .matrix n cols => .ok (n, cols)
  | .table [] => .error emptyReduction
  | .table ((_, c) :: cs) =>
    if cs.all (fun p => p.2.length = c.length) then .ok (c.length, c :: cs.map Prod.snd)
    else .error (.dimensionMismatch "number of rows of each array must match")

/-- `get_matrix_and_info`, src/MLJInterface.jl:412-428. `subscript` is `subscriptify`
(src/Utils.jl:43-45). -/
def getMatrixAndInfo (subscript : Nat → String) (x : Data D) :
    Jl (Mat × List String × List String × List D) := do
  let (n, rows) ← transposed x
  let (names, display) := match x with
    | .table cols => (cols.map Prod.fst, cols.map Prod.fst)
    | _ => ((List.range rows.length).map (fun i => s!"x{i + 1}"),
        (List.range rows.length).map (fun i => "x" ++ subscript (i + 1)))
  let (stripped, units) ← unwrapMatrix rows
  return (⟨n, stripped⟩, names, display, units)

/-- Single-target `format_input_for`, src/MLJInterface.jl:430-440. -/
def formatY1 : Data D → Jl (List JF × Option (List String) × D)
  | .table _ => .error (.assertionError "For multi-output regression, please use `MultitargetSRRegressor`.")
  | .matrix _ cols =>
    if cols.length > 1 then
      .error (.assertionError "For multi-output regression, please use `MultitargetSRRegressor`.")
    else do
      let (v, u) ← unwrapVector cols.flatten
      return (v, none, u)
  | .vector v => do
    let (w, u) ← unwrapVector v
    return (w, none, u)

/-- Multitarget `format_input_for`, src/MLJInterface.jl:441-448. -/
def formatYK (subscript : Nat → String) (y : Data D) : Jl (Mat × List String × List D) :=
  let accepted := match y with
    | .table _ => true
    | .matrix _ cols => decide (cols.length > 1)
    | .vector _ => false
  if accepted then do
    let (t, names, _, units) ← getMatrixAndInfo subscript y
    return (t, names, units)
  else .error (.assertionError "For single-output regression, please use `SRRegressor`.")

/-- `all(X_units .== old_X_units)`, src/MLJInterface.jl:456-462: `nothing` broadcasts
as a scalar that equals only `nothing`; length-one vectors broadcast. -/
def unitsMatch : Option (List D) → Option (List D) → Jl Bool
  | none, none => .ok true
  | none, some b => .ok b.isEmpty
  | some a, none => .ok a.isEmpty
  | some a, some b =>
    if a.length = b.length then .ok ((a.zip b).all fun p => decide (p.1 = p.2))
    else match a, b with
      | _, [y] => .ok (a.all fun u => decide (u = y))
      | [x], _ => .ok (b.all fun u => decide (x = u))
      | _, _ => .error (.dimensionMismatch "arrays could not be broadcast")

/-- `validate_units`, src/MLJInterface.jl:456-462. -/
def validateUnits (a b : Option (List D)) : Jl Unit := do
  unless ← unitsMatch a b do
    throw (.assertionError "Units of new data do not match units of fitted regressor.")

/-- `validate_variable_names`, src/MLJInterface.jl:449-455. -/
def validateNames (names fitted : List String) : Jl Unit :=
  if names = fitted then .ok ()
  else .error (.assertionError "Variable names do not match fitted regressor.")

/-! ## Predictions, src/MLJInterface.jl:471-611 -/

/-- A prediction column with its units (`wrap_units`); `none` is a plain array. -/
structure Col (D : Type) where
  values : List JF
  unit : Option D
  deriving DecidableEq

/-- Multitarget output: a matrix of columns, or a table `_table(...; names)`. -/
inductive OutK (D : Type) where
  | matrix (cols : List (Col D))
  | table (names : List String) (cols : List (Col D))
  deriving DecidableEq

/-- `wrap_units(v, y_units, nothing)`, src/MLJInterface.jl:482-488. -/
def wrap1 (v : List JF) (u : Option D) : Col D := ⟨v, u⟩

/-- Julia one-based vector indexing. -/
def index (xs : List α) (i : Int) : Jl α :=
  if i < 1 then .error .boundsError
  else match xs[(i - 1).toNat]? with
    | some x => .ok x
    | none => .error .boundsError

/-- `wrap_units(v, y_units, i)`, src/MLJInterface.jl:475-481 (one-based `i`). -/
def wrapK (v : List JF) (us : Option (List D)) (i : Nat) : Jl (Col D) :=
  match us with
  | none => .ok ⟨v, none⟩
  | some us => do return ⟨v, some (← index us i)⟩

/-- Single-target `prediction_fallback`, src/MLJInterface.jl:490-496. -/
def fallback1 (fr : FitResult S (Option D) D) (x : Mat) : Col D :=
  wrap1 (List.replicate x.nobs (.fin 0)) fr.yUnits

/-- Multitarget `prediction_fallback`, src/MLJInterface.jl:497-512. -/
def fallbackK (fr : FitResult S (Option (List D)) D) (x : Mat) : Jl (OutK D) := do
  let cols ← (List.range fr.numTargets).mapM fun i =>
    wrapK (List.replicate x.nobs (.fin 0)) fr.yUnits (i + 1)
  return if fr.yIsTable then .table (fr.yVariableNames.getD []) cols else .matrix cols

/-- Single-target `eval_tree_mlj`, src/MLJInterface.jl:547-562. -/
def evalMlj1 (fr : FitResult S (Option D) D) (tree : Nat) (x : Mat) : Col D :=
  let (out, completed) := fr.options.eval tree x.rows
  if completed then wrap1 out fr.yUnits else fallback1 fr x

/-- One element of the multitarget `outs` comprehension: a column, or the whole
fallback output returned by `eval_tree_mlj` when evaluation fails. -/
inductive Piece (D : Type) where
  | column (c : Col D)
  | whole (o : OutK D)

/-- Multitarget `eval_tree_mlj` for target `i` (one-based). -/
def evalMljK (fr : FitResult S (Option (List D)) D) (tree : Nat) (x : Mat) (i : Nat) :
    Jl (Piece D) :=
  let (out, completed) := fr.options.eval tree x.rows
  if completed then do return .column (← wrapK out fr.yUnits i)
  else do return .whole (← fallbackK fr x)

/-- The `idx` argument: `nothing`, an integer, or an integer vector. -/
inductive Idx where
  | none
  | int (i : Int)
  | vec (is : List Int)
  deriving DecidableEq, Repr

/-- Prediction input: data, or the NamedTuple `(data=..., idx=...)`. -/
inductive PInput (D : Type) where
  | data (x : Data D)
  | select (x : PInput D) (idx : Idx)

/-- Prediction services outside this file. `vectorPair` is `_predict(m, fitresult,
Xnew.data, Xnew.idx)` for a feature table whose only columns are `data` and `idx`,
which passes two column vectors and is not modelled. -/
structure PredictServices (D : Type) where
  subscript : Nat → String
  vectorPair1 : List (Cell D) → List (Cell D) → Jl (Col D)
  vectorPairK : List (Cell D) → List (Cell D) → Jl (OutK D)

/-- Validation and index selection shared by both `_predict` methods,
src/MLJInterface.jl:578-592. Returns the feature matrix or the early fallback. -/
def prepare (sv : PredictServices D) (fr : FitResult S U D) (x : Data D) (empty : Bool) :
    Jl (Mat × Bool) := do
  let (xt, names, _, units) ← getMatrixAndInfo sv.subscript x
  if empty then return (xt, true)
  validateNames names fr.variableNames
  validateUnits (cleanUnitsVec units) fr.xUnits
  return (xt, false)

/-- Single-target `_predict` after unwrapping, src/MLJInterface.jl:578-597. -/
def predictCore1 (sv : PredictServices D) (m : Regressor) (fr : Fit1 D) (x : Data D) (idx : Idx)
    (fresh : Nat) : Jl (Col D) := do
  let (params, _) ← fullReport1 m fr false fresh
  let (xt, early) ← prepare sv fr x params.equations.isEmpty
  if early then return fallback1 fr xt
  let tree ← match idx with
    | .none => index params.equations params.bestIdx
    | .int i => index params.equations i
    | .vec is => do
      let _ ← is.mapM (index params.equations)
      throw (.methodError "no method matching eval_tree_mlj(::Vector, ...)")
  return evalMlj1 fr tree xt

/-- Concatenation `reduce(hcat, outs)` when no piece is a table. -/
def hcatPieces : List (Piece D) → Option (List (Col D))
  | [] => some []
  | .column c :: ps => (hcatPieces ps).map (c :: ·)
  | .whole (.matrix cs) :: ps => (hcatPieces ps).map (cs ++ ·)
  | .whole (.table _ _) :: _ => none

/-- `eachindex(_idx, params.equations)`, src/MLJInterface.jl:599-603: there is no
method for an integer `_idx`; mismatched index ranges throw DimensionMismatch. -/
def perTarget (idx : Idx) (best : List Int) (k : Nat) : Jl (List Int) := do
  let is ← match idx with
    | .none => pure best
    | .int _ => throw (.methodError "no method matching keys(::Int64, ::Vector)")
    | .vec is => pure is
  if is.length = k then return is
  else throw (.dimensionMismatch
    s!"all inputs to eachindex must have the same indices, got Base.OneTo({is.length}) and Base.OneTo({k})")

/-- One iteration of the `outs` comprehension, src/MLJInterface.jl:600-602, for
target `t` (zero-based) with its equations and index. -/
def targetPiece (fr : FitK D) (xt : Mat) : (List Nat × Int) × Nat → Jl (Piece D)
  | ((eqs, i), t) => do evalMljK fr (← index eqs i) xt (t + 1)

/-- Multitarget `_predict` after unwrapping, src/MLJInterface.jl:578-610. A
`none` concatenation (a failed target with a table target) is returned as `none`:
`hcat` of a NamedTuple with arrays is not modelled. -/
def predictCoreK (sv : PredictServices D) (m : Regressor) (fr : FitK D) (x : Data D) (idx : Idx)
    (fresh : Nat) : Jl (Option (OutK D)) := do
  let (params, _) ← fullReportK m fr false fresh
  let empty := params.equations.isEmpty || params.equations.any List.isEmpty
  let (xt, early) ← prepare sv fr x empty
  if early then return some (← fallbackK fr xt)
  let is ← perTarget idx params.bestIdx params.equations.length
  let pieces ← ((params.equations.zip is).zipIdx).mapM (targetPiece fr xt)
  return (hcatPieces pieces).map fun cols =>
    if fr.yIsTable then .table (fr.yVariableNames.getD []) cols else .matrix cols

/-- The selector branch of `_predict`, src/MLJInterface.jl:570-576, on the keys of a NamedTuple. -/
def selectorKeys (keys : List String) : Bool := keys.contains "idx" || keys.contains "data"

def selectorOk (keys : List String) : Bool :=
  keys.contains "idx" && keys.contains "data" && keys.length == 2

def selectorMessage : String :=
  "If specifying an equation index during prediction, you must use a named tuple with keys `idx` and `data`."

/-- Single-target `MMI.predict`/`_predict`, src/MLJInterface.jl:564-597. -/
def predict1 (sv : PredictServices D) (m : Regressor) (fr : Fit1 D) : PInput D → Idx → Nat → Jl (Col D)
  | .select x i, _, fresh => predict1 sv m fr x i fresh
  | .data (.table cols), idx, fresh =>
    let keys := cols.map Prod.fst
    if selectorKeys keys then
      if selectorOk keys then
        sv.vectorPair1 ((cols.lookup "data").getD []) ((cols.lookup "idx").getD [])
      else .error (.assertionError selectorMessage)
    else predictCore1 sv m fr (.table cols) idx fresh
  | .data x, idx, fresh => predictCore1 sv m fr x idx fresh

/-- Multitarget `MMI.predict`/`_predict`, src/MLJInterface.jl:564-611. -/
def predictK (sv : PredictServices D) (m : Regressor) (fr : FitK D) :
    PInput D → Idx → Nat → Jl (Option (OutK D))
  | .select x i, _, fresh => predictK sv m fr x i fresh
  | .data (.table cols), idx, fresh =>
    let keys := cols.map Prod.fst
    if selectorKeys keys then
      if selectorOk keys then
        (sv.vectorPairK ((cols.lookup "data").getD []) ((cols.lookup "idx").getD [])).map some
      else .error (.assertionError selectorMessage)
    else predictCoreK sv m fr (.table cols) idx fresh
  | .data x, idx, fresh => predictCoreK sv m fr x idx fresh

/-! ## Fitting, src/MLJInterface.jl:219-317,651-663 -/

/-- The `equation_search` arguments that depend on the MLJ wrapper. -/
structure Call (S Y W U D : Type) where
  niterations : Int
  x : Mat
  y : Y
  weights : Option W
  variableNames : List String
  displayNames : List String
  options : Opts
  saved : Option S
  xUnits : Option (List D)
  yUnits : U

abbrev Call1 (D : Type) := Call State1 (List JF) (List JF) (Option D) D
abbrev CallK (D : Type) := Call StateK Mat (List (List JF)) (Option (List D)) D

/-- `get_options` (generated at src/MLJInterface.jl:108-110), the warm-start check
(src/OptionsStruct.jl:341-363), `equation_search` and `subscriptify`. -/
structure FitServices (D : Type) where
  getOptions : Regressor → Jl Opts
  checkWarm : Opts → Opts → Jl Unit
  search1 : Call1 D → Jl State1
  searchK : CallK D → Jl StateK
  subscript : Nat → String

/-- `MMI.update`'s option handling, src/MLJInterface.jl:232-235. -/
def warmOptions (sv : FitServices D) (m : Regressor) (old : Option (FitResult S U D)) : Jl Opts := do
  let o ← sv.getOptions m
  match old with
  | some f => sv.checkWarm f.options o
  | none => pure ()
  return o

/-- Julia Base `Int` subtraction on the 64-bit host, with signed wraparound. -/
def iterationDifference (requested previous : Int) : Int :=
  (Int64.ofInt requested - Int64.ofInt previous).toInt

/-- Remaining iterations and the assertion, src/MLJInterface.jl:261-263. -/
def remaining (m : Regressor) (old : Option (FitResult S U D)) : Jl Int :=
  let n := match old with
    | none => m.niterations
    | some prior => iterationDifference m.niterations prior.niterations
  if n ≥ 0 then .ok n else .error (.assertionError "niterations >= 0")

/-- Single-target `MMI.update`/`_update`, src/MLJInterface.jl:223-317. The
returned report is `full_report(m, fitresult)`; the cache is `nothing`. -/
def update1 (sv : FitServices D) (m : Regressor) (old : Option (Fit1 D)) (x y : Data D)
    (w : Option (List JF)) (fresh : Nat) : Jl (Fit1 D × Report1 × Nat) := do
  let o ← warmOptions sv m old
  let (xt, names, display, xu) ← getMatrixAndInfo sv.subscript x
  let (yt, yNames, yu) ← formatY1 y
  let n ← remaining m old
  let st ← sv.search1 ⟨n, xt, yt, w, names, display, o, old.map FitResult.state,
    cleanUnitsVec xu, cleanUnits yu⟩
  let fr : Fit1 D := ⟨m, st, m.niterations, 1, o, names, yNames,
    y.isTable, cleanUnitsVec xu, cleanUnits yu⟩
  let (r, fresh') ← fullReport1 m fr true fresh
  return (fr, r, fresh')

/-- Multitarget `MMI.update`/`_update`; weights become `repeat(w', size(y_t, 1))`. -/
def updateK (sv : FitServices D) (m : Regressor) (old : Option (FitK D)) (x y : Data D)
    (w : Option (List JF)) (fresh : Nat) : Jl (FitK D × ReportK × Nat) := do
  let o ← warmOptions sv m old
  let (xt, names, display, xu) ← getMatrixAndInfo sv.subscript x
  let (yt, yNames, yu) ← formatYK sv.subscript y
  let wt := w.map fun w => List.replicate yt.rows.length w
  let n ← remaining m old
  let st ← sv.searchK ⟨n, xt, yt, wt, names, display, o, old.map FitResult.state,
    cleanUnitsVec xu, cleanUnitsVec yu⟩
  let fr : FitK D := ⟨m, st, m.niterations, yt.rows.length, o, names,
    some yNames, y.isTable, cleanUnitsVec xu, cleanUnitsVec yu⟩
  let (r, fresh') ← fullReportK m fr true fresh
  return (fr, r, fresh')

/-- `MMI.fit`, src/MLJInterface.jl:220-222. -/
def fit1 (sv : FitServices D) (m : Regressor) (x y : Data D) (w : Option (List JF)) (fresh : Nat) :=
  update1 sv m none x y w fresh

def fitK (sv : FitServices D) (m : Regressor) (x y : Data D) (w : Option (List JF)) (fresh : Nat) :=
  updateK sv m none x y w fresh

/-- The native `Machine`, src/MLJInterface.jl:621-627. -/
structure Machine1 (D : Type) where
  model : Regressor
  x : Data D
  y : Data D
  w : Option (List JF)
  fitresult : Option (Fit1 D)
  report : Option Report1

/-- `machine(model, X, y, w=nothing)`, src/MLJInterface.jl:637-640. -/
def machine1 (m : Regressor) (x y : Data D) (w : Option (List JF)) : Machine1 D :=
  ⟨m, x, y, w, none, none⟩

/-- `_check_fitted`, src/MLJInterface.jl:688-697. -/
def checkFitted (mach : Machine1 D) (fn : String) : Jl Unit :=
  if mach.fitresult.isNone then
    .error (.argumentError s!"This machine has not been fitted. Call `fit!(mach)` before `{fn}`.")
  else .ok ()

/-- `predict(mach, Xnew)` and `predict(mach)` (training features), src/MLJInterface.jl:671-675. -/
def machinePredict1 (sv : PredictServices D) (mach : Machine1 D) (xnew : Option (PInput D))
    (fresh : Nat) : Jl (Col D) := do
  checkFitted mach "predict"
  match mach.fitresult with
  | some fr => predict1 sv mach.model fr (xnew.getD (.data mach.x)) .none fresh
  | none => throw .undefRefError

/-- `report(mach)`, src/MLJInterface.jl:683-686. -/
def machineReport1 (mach : Machine1 D) : Jl (Option Report1) := do
  checkFitted mach "report"
  return mach.report

/-- `fit!(mach; force)`, src/MLJInterface.jl:651-663. -/
def machineFit1 (sv : FitServices D) (mach : Machine1 D) (force : Bool) (fresh : Nat) :
    Jl (Machine1 D × Nat) := do
  let (fr, r, f) ← if force || mach.fitresult.isNone then fit1 sv mach.model mach.x mach.y mach.w fresh
    else update1 sv mach.model mach.fitresult mach.x mach.y mach.w fresh
  return ({ mach with fitresult := some fr, report := some r }, f)

-- Source: src/MLJInterface.jl:346-347
/-
is_extension_loaded(::Val) = false
_has_tables_ext() = is_extension_loaded(Val(:Tables))
-/
def hasTablesExt (extensionActive : Bool) : Bool := extensionActive

-- Source: src/MLJInterface.jl:349-355
/-
function _istable(X::AbstractArray)
    # Exotic array types (e.g. StructArrays) can still be Tables.jl tables.
    _has_tables_ext() && return _tables_istable(X)
    return false
end
_istable(::AbstractVector{<:NamedTuple}) = true  # row table
_istable(X::NamedTuple) = all(Base.Fix2(isa, AbstractVector), values(X))
-/
inductive TableInputKind where
  | exoticArray | rowTable | namedTuple (vectorFields : List Bool)

def tableDispatch (extensionActive : Bool) (tablesIsTable : Jl Bool) : TableInputKind → Jl Bool
  | .exoticArray => if hasTablesExt extensionActive then tablesIsTable else .ok false
  | .rowTable => .ok true
  | .namedTuple fields => .ok (fields.all id)

def tablesDispatch : Prop := ∀ reply,
  tableDispatch false reply .exoticArray = .ok false ∧
  tableDispatch true reply .exoticArray = reply ∧
  (∀ (active : Bool) fields, tableDispatch active reply .rowTable = .ok true ∧
    (tableDispatch active reply (.namedTuple fields) = .ok true ↔ false ∉ fields))

theorem tablesDispatch_holds : tablesDispatch := by
  intro reply
  refine ⟨rfl, rfl, ?_⟩
  intro active fields
  refine ⟨rfl, ?_⟩
  induction fields with
  | nil => simp [tableDispatch]
  | cons hd tl ih => cases hd <;> simp_all [tableDispatch]

inductive OptionSyntax where
  | symbol (name : String)
  | expr (args : List OptionSyntax)
  | other

-- Source: src/MLJInterface.jl:113-123
/-
function getsymb(ex::Symbol)
    return ex
end
function getsymb(ex::Expr)
    for arg in ex.args
        isa(arg, Symbol) && return arg
        s = getsymb(arg)
        isa(s, Symbol) && return s
    end
    return nothing
end
-/
mutual
  def getSymb : OptionSyntax → Jl (Option String)
    | .symbol name => .ok (some name)
    | .expr args => getSymbArgs args
    | .other => .error (.methodError "getsymb")
  def getSymbArgs : List OptionSyntax → Jl (Option String)
    | [] => .ok none
    | .symbol name :: _ => .ok (some name)
    | a :: rest => do
      match ← getSymb a with
      | some name => pure (some name)
      | none => getSymbArgs rest
end

-- An independent depth-first stream of syntax leaves; an unsupported leaf terminates lookup.
private def syntaxLeaves : OptionSyntax → List (Option String)
  | .symbol s => [some s]
  | .other => [none]
  | .expr args => args.flatMap syntaxLeaves

private def firstSyntaxLeaf : List (Option String) → Jl (Option String)
  | [] => .ok none
  | some name :: _ => .ok (some name)
  | none :: _ => .error (.methodError "getsymb")

private theorem firstSyntaxAppend (xs ys : List (Option String)) :
    firstSyntaxLeaf (xs ++ ys) =
      (firstSyntaxLeaf xs >>= fun r => match r with | some n => pure (some n) | none => firstSyntaxLeaf ys) := by
  cases xs with
  | nil => rfl
  | cons x xs => cases x <;> rfl

mutual
  private theorem syntaxModel (x : OptionSyntax) : getSymb x = firstSyntaxLeaf (syntaxLeaves x) := by
    cases x with
    | symbol s => simp [getSymb, syntaxLeaves, firstSyntaxLeaf]
    | other => simp [getSymb, syntaxLeaves, firstSyntaxLeaf]
    | expr args => simpa [getSymb, syntaxLeaves] using syntaxArgsModel args
  private theorem syntaxArgsModel (args : List OptionSyntax) :
      getSymbArgs args = firstSyntaxLeaf (args.flatMap syntaxLeaves) := by
    cases args with
    | nil => rfl
    | cons x xs =>
      simp only [List.flatMap_cons, firstSyntaxAppend]
      cases x with
      | symbol s => simp [getSymbArgs, syntaxLeaves, firstSyntaxLeaf, bind, Except.bind, pure, Except.pure]
      | other => simp [getSymbArgs, getSymb, syntaxLeaves, firstSyntaxLeaf, bind, Except.bind]
      | expr inner =>
        simp only [syntaxLeaves] 
        rw [← syntaxArgsModel inner, ← syntaxArgsModel xs]
        simp [getSymbArgs, getSymb]
end

def symbolPriority : Prop := ∀ args, getSymb (.expr args) = firstSyntaxLeaf (args.flatMap syntaxLeaves)

theorem symbolPriority_holds : symbolPriority := by
  intro args
  simpa [getSymb] using syntaxArgsModel args

inductive HofType where
  | hall (numberType : Nat)
  | vector (elementType : HofType)

-- Source: src/MLJInterface.jl:318-320
/-
hof_eltype(::Type{H}) where {T,H<:HallOfFame{T}} = T
hof_eltype(::Type{V}) where {V<:Vector} = hof_eltype(eltype(V))
hof_eltype(h) = hof_eltype(typeof(h))
-/
def hofEltype : HofType → Nat
  | .hall t => t
  | .vector elt => hofEltype elt

-- Vector elements are typed by the runtime element type, including for empty vectors.
def HofValues : HofType → Type
  | .hall _ => Unit
  | .vector elt => List (HofValues elt)

def hofValueEltype (t : HofType) (_values : HofValues t) : Nat := hofEltype t

def hofVectorType : Prop := ∀ (t depth : Nat),
  ∀ (values : HofValues (.vector (Nat.rec (.hall t) (fun _ ty => .vector ty) depth))),
    hofValueEltype (.vector (Nat.rec (.hall t) (fun _ ty => .vector ty) depth)) values = t

theorem hofVectorType_holds : hofVectorType := by
  intro t depth
  induction depth with
  | zero => intro vals; rfl
  | succ depth ih => intro vals; exact ih []

-- Source: src/MLJInterface.jl:471-473
/-
function prediction_warn()
    @warn "Evaluation failed either due to NaNs detected or due to unfinished search. Using 0s for prediction."
end
-/
def predictionWarn {S : Type} (warn : String → S → S) (s : S) : S :=
  warn "Evaluation failed either due to NaNs detected or due to unfinished search. Using 0s for prediction." s

-- Source: src/MLJInterface.jl:490-496
/-
function prediction_fallback(
    ::Type{T}, m::AbstractSingletargetSRRegressor, Xnew_t, fitresult::SRFitResult, _
) where {T}
    prediction_warn()
    out = fill!(similar(Xnew_t, T, axes(Xnew_t, 2)), zero(T))
    return wrap_units(out, fitresult.y_units, nothing)
end
-/
def warnedFallback1 {A V O : Type} (similar : Jl A) (zero : Jl V)
    (fill : A → V → Jl A) (wrap : A → Jl O) (log : List String) : Jl O × List String :=
  let log := predictionWarn (fun msg xs => xs ++ [msg]) log
  let result := do
    let a ← similar
    let z ← zero
    let out ← fill a z
    wrap out
  (result, log)

def predictionWarning : Prop := ∀ (A V O : Type) similar zero (fill : A → V → Jl A)
    (wrap : A → Jl O) log,
  let r := warnedFallback1 similar zero fill wrap log
  r.2.drop log.length = ["Evaluation failed either due to NaNs detected or due to unfinished search. Using 0s for prediction."] ∧
  (∀ e, similar = .error e → r.1 = .error e) ∧
  (∀ a e, similar = .ok a → zero = .error e → r.1 = .error e) ∧
  (∀ a z e, similar = .ok a → zero = .ok z → fill a z = .error e → r.1 = .error e) ∧
  (∀ a z out, similar = .ok a → zero = .ok z → fill a z = .ok out → r.1 = wrap out)

theorem predictionWarning_holds : predictionWarning := by
  intro A V O similar zero fill wrap log
  refine ⟨by simp [warnedFallback1, predictionWarn], ?_, ?_, ?_, ?_⟩
  all_goals intros; simp_all [warnedFallback1, bind, Except.bind]

end SymReg.MLJ
