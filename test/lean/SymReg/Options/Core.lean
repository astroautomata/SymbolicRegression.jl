import SymReg.MutateGen.Weights
import SymReg.Population.Tournament
import SymReg.SimpCons.Builders
import SymReg.Complexity

/-!
Constructor normalization for `src/Options.jl:181-281,735-831,863-889,1288-1392`.
-/
namespace SymReg.Options
open DynExpr

/-- `inverse_opmap`, `src/Options.jl:202-220`. Arithmetic aliases are not restored. -/
def inverseOpmap (op : Nat) : Nat :=
  if 105 <= op ∧ op <= 118 then
    if op = 105 then 5 else op - 99
  else op

/-- Operator lookup lists are mapped by degree, `src/Options.jl:920-931`. -/
def mapOperators (ops : List (List Nat)) : List (List Nat) := ops.map (List.map opmap)

/-- `deprecated_options_mapping`, `src/Options.jl:257-281`. -/
def deprecatedAliases : List (String × String) :=
  [("mutationWeights", "mutation_weights"), ("hofMigration", "hof_migration"),
   ("shouldOptimizeConstants", "should_optimize_constants"),
   ("perturbationFactor", "perturbation_factor"), ("batchSize", "batch_size"),
   ("crossoverProbability", "crossover_probability"), ("warmupMaxsizeBy", "warmup_maxsize_by"),
   ("useFrequency", "use_frequency"), ("useFrequencyInTournament", "use_frequency_in_tournament"),
   ("ncyclesperiteration", "ncycles_per_iteration"), ("fractionReplaced", "fraction_replaced"),
   ("fractionReplacedHof", "fraction_replaced_hof"), ("probNegate", "probability_negate_constant"),
   ("optimize_probability", "optimizer_probability"), ("probPickFirst", "tournament_selection_p"),
   ("earlyStopCondition", "early_stop_condition"), ("stateReturn", "deprecated_return_state"),
   ("return_state", "deprecated_return_state"), ("enable_autodiff", "deprecated_enable_autodiff"),
   ("ns", "tournament_selection_n"), ("loss", "elementwise_loss"),
   ("use_recorder", "use_tracing"), ("recorder_file", "tracing_file")]

/-- Keyword payloads; opaque Julia objects keep an arbitrary identity. Scalar values
reuse DE's `JF`; mutation weight values reuse `SymReg.MutateGen.MutationWeights`. -/
inductive Value where
  | absent
  | flag (b : Bool)
  | integer (n : Int)
  | real (x : JF)
  | text (s : String)
  | object (identity : Nat)
  | weights (w : SymReg.MutateGen.MutationWeights)
  | weightVector (xs : List JF)
  deriving DecidableEq, Repr

abbrev Keywords := String → Value

/-- Assignment to the new keyword, `src/Options.jl:750-773`. -/
def setKey (kws : Keywords) (key : String) (value : Value) : Keywords :=
  fun name => if name = key then value else kws name

-- Source: src/Options.jl:774-789; src/MutationWeights.jl:64-80
-- if length(_mutation_weights) < n_fields
--     _mutation_weights = vcat(_mutation_weights, zeros(n_fields - length(_mutation_weights)))
-- end
-- mutation_weights = MutationWeights(_mutation_weights...)
structure LegacyConversions where
  promote : JF → Jl JF := fun x => pure (SymReg.Loss.LossPrecision.round .float64 x)
  zero : Jl JF := pure (.fin 0)
  field : JF → Jl JF := fun x => pure (SymReg.Loss.LossPrecision.round .float64 x)

def legacyWeights (xs : List JF) (cv : LegacyConversions := {}) : Jl Value := do
  let padded ← if xs.length < 15 then do
    let ys ← xs.mapM cv.promote
    let zeros ← (List.replicate (15 - xs.length) ()).mapM (fun _ => cv.zero)
    pure (ys ++ zeros)
  else pure xs
  if padded.length != 15 then throw (.methodError "no method matching MutationWeights")
  let ws ← padded.mapM cv.field
  pure (.weights (← SymReg.MutateGen.MutationWeights.ofList ws))

-- Source: src/Options.jl:750-773
-- k == :hofMigration && (hof_migration = kws[k]; true) && continue
private def assignmentTarget : String → Option String
  | "hofMigration" => some "hof_migration"
  | "shouldOptimizeConstants" => some "should_optimize_constants"
  | "perturbationFactor" => some "perturbation_factor"
  | "batchSize" => some "batch_size"
  | "crossoverProbability" => some "crossover_probability"
  | "warmupMaxsizeBy" => some "warmup_maxsize_by"
  | "useFrequency" => some "use_frequency"
  | "useFrequencyInTournament" => some "use_frequency_in_tournament"
  | "ncyclesperiteration" => some "ncycles_per_iteration"
  | "fractionReplaced" => some "fraction_replaced"
  | "fractionReplacedHof" => some "fraction_replaced_hof"
  | "probNegate" => some "probability_negate_constant"
  | "optimize_probability" => some "optimizer_probability"
  | "probPickFirst" => some "tournament_selection_p"
  | "earlyStopCondition" => some "early_stop_condition"
  | "return_state" => some "deprecated_return_state"
  | "stateReturn" => some "deprecated_return_state"
  | "ns" => some "tournament_selection_n"
  | "loss" => some "elementwise_loss"
  | "use_recorder" => some "use_tracing"
  | "recorder_file" => some "tracing_file"
  | _ => none

/-- One iteration of the deprecated keyword loop, `src/Options.jl:735-795`.
A throwing deprecation warning aborts before assignment. -/
def applyAlias (kws : Keywords) (key : String) (value : Value)
    (warn : String → String → Jl Unit := fun _ _ => pure ()) (cv : LegacyConversions := {}) : Jl Keywords := do
  let some p := deprecatedAliases.find? (fun p => p.1 = key)
    | throw (.errorException ("Unknown keyword argument: " ++ key))
  warn key p.2
  if key = "enable_autodiff" then return kws
  if key = "mutationWeights" then
    match value with
    | .weightVector xs => return setKey kws "mutation_weights" (← legacyWeights xs cv)
    | _ => return setKey kws "mutation_weights" value
  let some target := assignmentTarget key | throw (.errorException ("Unknown deprecated keyword argument: " ++ key))
  return setKey kws target value

/-- All deprecated keywords are processed in call order, `src/Options.jl:735`.
Two aliases for return_state therefore use the last value. -/
def applyAliases (kws : Keywords) (xs : List (String × Value))
    (warn : String → String → Jl Unit := fun _ _ => pure ()) : Jl Keywords :=
  xs.foldlM (fun current p => applyAlias current p.1 p.2 warn) kws

/-- Explicit older population-size names always overwrite modern names,
`src/Options.jl:797-804`. -/
def populationAliases (size populations npop npopulations : Option Int) : Option Int × Option Int :=
  (npop.or size, npopulations.or populations)

/-- `ArgumentError` message for passing both sign-flip keywords, `src/Options.jl:806-810`. -/
def flipConflictMessage : String :=
  "Pass only one of `probability_flip_constant_sign` and the deprecated `probability_negate_constant`."

-- Source: src/Options.jl:805-814
-- if probability_negate_constant !== nothing
--     probability_flip_constant_sign !== nothing && throw(ArgumentError("Pass only one of ..."))
--     Base.depwarn("`probability_negate_constant` is deprecated. ...", :Options)
/-- The deprecated keyword, also the target of the `probNegate` alias, conflicts with
the modern keyword before its deprecation warning runs. -/
def checkFlipProbability (warn : Jl Unit) (flip negate : Option JF) : Jl Unit := do
  if negate.isSome then
    if flip.isSome then throw (.argumentError flipConflictMessage)
    warn

-- Source: src/Options.jl:815
-- probability_flip_constant_sign = 1 - probability_negate_constant
/-- The keyword value after the deprecated complement is applied. `1 - p` is exact in
`JF`; the later `Float64` conversions round it once, as Julia does for Float64 and
exact real inputs. -/
def flipProbabilityInput (flip negate : Option JF) : Option JF :=
  match negate with
  | some p => some (JF.sub (.fin 1) p)
  | none => flip

/-- Version components relevant to the two comparisons in `default_options`,
`src/Options.jl:1288-1290,1386`. `prerelease` includes Julia's minimal '-' version. -/
structure Version where
  major : Nat
  minor : Nat := 0
  patch : Nat := 0
  prerelease : Bool := false
  deriving DecidableEq, Repr

def Version.beforeOne (v : Version) : Bool :=
  v.major == 0 || (v.major == 1 && v.minor == 0 && v.patch == 0 && v.prerelease)

def Version.fromTwo (v : Version) : Bool := v.major >= 2

inductive BatchMode where
  | disabled | enabled | auto | invalid (name : String)
  deriving DecidableEq, Repr

/-- Tables returned by `default_options`, `src/Options.jl:1291-1392`.
Decimal constants follow the shared exact-finite `JF` convention. -/
def literal64 (q : Rat) : JF := SymReg.Loss.LossPrecision.round .float64 (.fin q)

structure Defaults where
  ops : List (List Nat) := [[], [101, 103, 104, 102]]
  maxsize : Int := 30
  populations : Int := 31
  populationSize : Int := 27
  cycles : Int := 380
  parsimony : JF := literal64 0
  warmup : JF := literal64 0
  adaptiveScaling : JF := literal64 1040
  weightKw : List (String × JF) :=
    [("mutate_constant", literal64 (346 / 10000)), ("mutate_operator", literal64 (293 / 1000)),
     ("swap_operands", literal64 (198 / 1000)), ("rotate_tree", literal64 (426 / 100)),
     ("add_node", literal64 (247 / 100)), ("insert_node", literal64 (112 / 10000)),
     ("delete_node", literal64 (870 / 1000)), ("simplify", literal64 (209 / 100000)),
     ("randomize", literal64 (502 / 1000000)), ("do_nothing", literal64 (273 / 1000)),
     ("optimize", literal64 0), ("form_connection", literal64 (1 / 2)), ("break_connection", literal64 (1 / 10))]
  crossoverProbability : JF := literal64 (259 / 10000)
  annealing : Bool := true
  alpha : JF := literal64 (317 / 100)
  perturbation : JF := literal64 (129 / 1000)
  flipProbability : JF := literal64 (99257 / 100000)
  tournamentN : Int := 15
  tournamentP : JF := literal64 (982 / 1000)
  fraction : JF := literal64 (36 / 100000)
  fractionHof : JF := literal64 (614 / 10000)
  fractionGuesses : JF := literal64 (1 / 1000)
  topn : Int := 12
  batching : BatchMode := .disabled
  batchSize : Option Int := some 50
  deriving DecidableEq, Repr

/-- The version < 1 table, `src/Options.jl:1291-1335`; omitted feature/backsolve
weights are supplied by the existing `_mutation_weights` mirror. -/
def legacyDefaults : Defaults :=
  { maxsize := 20, populations := 15, populationSize := 33, cycles := 550,
    parsimony := literal64 (32 / 10000), adaptiveScaling := literal64 20,
    weightKw := [("mutate_constant", literal64 (48 / 1000)), ("mutate_operator", literal64 (47 / 100)),
      ("swap_operands", literal64 (1 / 10)), ("rotate_tree", literal64 0),
      ("add_node", literal64 (79 / 100)), ("insert_node", literal64 (51 / 10)),
      ("delete_node", literal64 (17 / 10)), ("simplify", literal64 (2 / 1000)),
      ("randomize", literal64 (23 / 100000)), ("do_nothing", literal64 (21 / 100)),
      ("optimize", literal64 0), ("form_connection", literal64 (1 / 2)), ("break_connection", literal64 (1 / 10))],
    crossoverProbability := literal64 (66 / 1000), annealing := false, alpha := literal64 (1 / 10),
    perturbation := literal64 (76 / 1000), flipProbability := literal64 (99 / 100),
    tournamentN := 12, tournamentP := literal64 (86 / 100), fractionHof := literal64 (35 / 1000) }

/-- `default_options`, `src/Options.jl:1288-1392`. -/
def defaultOptions (version : Option Version) : Defaults :=
  if version.any Version.beforeOne then legacyDefaults
  else if version.isNone || version.any Version.fromTwo then
    { ({} : Defaults) with crossoverProbability := literal64 (1 / 5), batching := .auto, batchSize := none }
  else {}

-- Source: src/Options.jl:235-236,871,1086
-- create_mutation_weights(w::MutationWeights) = w
-- create_mutation_weights(w::NamedTuple) = _mutation_weights(; w...)
structure WeightObject where
  identity : Option Nat
  fields : SymReg.MutateGen.MutationWeights

inductive WeightValue where
  | numeric (x : JF)
  | converted (outcome : Jl JF)

instance : SymReg.MutateGen.WeightConversion WeightValue where
  toFloat64
    | .numeric x => pure (SymReg.Loss.LossPrecision.round .float64 x)
    | .converted result => result

inductive WeightInput where
  | existing (identity : Nat) (w : SymReg.MutateGen.MutationWeights)
  | named (kws : List (String × WeightValue))

def createMutationWeights : WeightInput → Jl WeightObject
  | .existing identity w => pure ⟨some identity, w⟩
  | .named kws => (SymReg.MutateGen.mutationWeights kws).map (fun w => ⟨none,w⟩)

def resolveWeights (version : Option Version) (input : Option WeightInput) : Jl SymReg.MutateGen.MutationWeights :=
  match input with
  | some w => (createMutationWeights w).map WeightObject.fields
  | none => do
    let w ← SymReg.MutateGen.mutationWeights (defaultOptions version).weightKw
    SymReg.MutateGen.MutationWeights.ofList ((SymReg.MutateGen.convertVector w).map (SymReg.Loss.LossPrecision.round .float64))

/-- `with_max_degree_from_context`, `src/Options.jl:240-255`.
`some D` represents a node type with an explicit maximum degree. -/
def withMaxDegree (degree : Option Nat) (provided : Bool) (ops : List (List Nat)) : Nat :=
  degree.getD (if provided then ops.length else 2)

/-- Default recommendation method, `src/Options.jl:233`. -/
def recommendExpressionLoss (_expressionType : Option Nat) : Bool := false

-- Source: src/Options.jl:817-827
-- optimizer_algorithm = if optimizer_algorithm == "NelderMead"
--     Optim.NelderMead(; linesearch=LineSearches.BackTracking())
-- else
--     Optim.BFGS(; linesearch=LineSearches.BackTracking())
-- end
inductive OptimizerKind | nelderMead | bfgs deriving DecidableEq
inductive LineSearch | backTracking deriving DecidableEq

def optimizerFromString {m : Type → Type} [Monad m] {O : Type} (warn : m Unit)
    (make : OptimizerKind → LineSearch → m O) (name : String) : m O := do
  warn
  make (if name = "NelderMead" then .nelderMead else .bfgs) .backTracking

end SymReg.Options
