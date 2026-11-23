import SymReg.Options.Core
import SymReg.Plugins.Dispatch
import SymReg.PopMember.Core

/-!
`Options` constructor phases (`src/Options.jl:814-1271`) and complexity construction
(`src/OptionsStruct.jl:31-111`). Input unions are represented by typed fields;
integer fields range over the Julia Int domain when instantiated in Julia.
External constructors, plugin hooks, type promotion and ADTypes dispatch are supplied
services, with their errors propagated. The executable complexity constructor below
specializes the existing `Complexity.CMap` model to integer complexities.
-/
namespace SymReg.Options
open DynExpr SymReg.Complexity

-- Source: src/OptionsStruct.jl:24-31,41-111; Julia base/int.jl:807-822
inductive WeightType where
  | machine (bits : Nat) (unsigned : Bool)
  | big | integer | any
  deriving DecidableEq, Repr

def WeightType.int : WeightType := .machine 64 false

-- With different sizes promote to the wider type; at equal width unsigned wins.
def promoteWeight : WeightType → WeightType → WeightType
  | .any, _ | _, .any => .any
  | .integer, _ | _, .integer => .integer
  | .big, _ | _, .big => .big
  | .machine n u, .machine k v =>
    if n < k then .machine k v else if k < n then .machine n u else .machine n (u || v)

-- Source: Julia base/promotion.jl:328-330
-- promote_type(T, S, U) = (@inline; promote_type(promote_type(T, S), U))
def promotedTypes (rows : List WeightType) (v c : WeightType) : WeightType :=
  match rows with
  | [] => promoteWeight v c
  | t :: ts => ((ts ++ [v,c]).foldl promoteWeight t)

def WeightType.cast (t : WeightType) (x : Int) : Jl Int := do
  match t with
  | .machine n u =>
    let high : Int := 2 ^ (if u then n else n - 1)
    if x < (if u then 0 else -high) ∨ high ≤ x then throw .inexactError else return x
  | .big | .integer => return x
  | .any => throw (.methodError "Any(value)")

def WeightType.one : WeightType → Jl Int
  | .any => .error (.methodError "one(::Type{Any})")
  | _ => .ok 1

structure TypedMapping extends CMap where
  eltype : WeightType

def castVariable (t : WeightType) : VarC → Jl VarC
  | .scalar x => (t.cast x).map VarC.scalar
  | .vector xs => (xs.mapM t.cast).map VarC.vector

-- T = promote_type(map(eltype, op_complexities)..., T2, T3)
-- vc = map(T, variable_complexity)
-- return ComplexityMapping{T,typeof(vc),D}(
--     true, map(Base.Fix1(map, T), op_complexities), vc, T(constant_complexity)
-- )
def promotedMapping (ops : List (WeightType × List Int)) (variableC : WeightType × VarC)
    (constant : WeightType × Int) : Jl TypedMapping := do
  let t := promotedTypes (ops.map Prod.fst) variableC.1 constant.1
  let vc ← castVariable t variableC.2
  let rows ← ops.mapM (fun row => row.2.mapM t.cast)
  let c ← t.cast constant.2
  return ⟨⟨true,rows,vc,c⟩,t⟩

def lookupVariable (t : WeightType) : Option VarC → Jl VarC
  | some v => castVariable t v
  | none => t.one.map VarC.scalar

def lookupConstant (t : WeightType) : Option Int → Jl Int
  | some x => t.cast x
  | none => t.one

-- T = promote_type(VAR_T, CONST_T, OP_T)
-- op_complexities = ntuple(i -> T[get(_complexity_of_operators, op, one(T)) for op in operators[i]], Val(length(operators)))
def complexityMapping (opWeights : Option (List (Nat × Int))) (variables : Option VarC)
    (constant : Option Int) (ops : List (List Nat))
    (opType varType constType : WeightType := WeightType.int) : Jl TypedMapping := do
  if opWeights.isNone && variables.isNone && constant.isNone then
    return ⟨⟨false,ops.map (fun _ => []),.scalar 0,0⟩,WeightType.int⟩
  let t := promoteWeight (promoteWeight (if variables.isSome then varType else WeightType.int)
      (if constant.isSome then constType else WeightType.int)) (if opWeights.isSome then opType else WeightType.int)
  let dict := SymReg.SimpCons.toDict (opWeights.getD [])
  let rows ← ops.mapM fun row => row.mapM fun op => do
    let fallback ← t.one
    t.cast (((dict.find? (fun p => p.1 = op)).map Prod.snd).getD fallback)
  let vc ← lookupVariable t variables
  let c ← lookupConstant t constant
  promotedMapping (rows.map (t, ·)) (t,vc) (t,c)

/-- `Base.:(==)(::ComplexityMapping,::ComplexityMapping)`,
`src/OptionsStruct.jl:33-38`, for the integer complexity model. -/
def varEq : VarC → VarC → Bool
  | .scalar a, .scalar b => a == b
  | .vector a, .vector b => a == b
  | _, _ => false

def complexityEq (a b : CMap) : Bool :=
  a.use == b.use && a.opC == b.opC && varEq a.varC b.varC && a.constC == b.constC

/-- `Base.eltype(::ComplexityMapping{T})`, `src/OptionsStruct.jl:31`. -/
def mappingEltype (mapping : TypedMapping) : WeightType := mapping.eltype

/-- A supplied ComplexityMapping or arbitrary expression-complexity function. -/
inductive ComplexitySpec where
  | mapping (value : TypedMapping)
  | function (identity : Nat)

/-- An operator enum carries its function identities and whether it is the concrete
DynamicExpressions OperatorEnum, `src/Options.jl:915-917`. -/
structure Operators where
  ops : List (List Nat)
  standard : Bool := true
  typeId : Nat := 0
  deriving DecidableEq, Repr

-- Source: src/Options.jl:906-917,1017-1032; DE src/OperatorEnum.jl:8-28
-- operators = OperatorEnum(operators_by_degree)
inductive EnumType where
  | standard (tupleType : List (List Nat))
  | generic (typeId : Nat)
  deriving DecidableEq

def Operators.runtimeType (o : Operators) : EnumType :=
  if o.standard then .standard o.ops else .generic o.typeId

/-- Concrete OperatorEnum is rebuilt with safe operators; generic enums retain
their operators and only their lookup lists are mapped, `src/Options.jl:906-917,1017-1032`. -/
def resolveOperators (constructor : Option Nat → List (List Nat) → Jl Operators)
    (provided : Option Operators) (custom : Option Nat) (lookupOps : List (List Nat)) : Jl Operators :=
  match provided with
  | some o => pure (if o.standard then ⟨lookupOps,true,0⟩ else o)
  | none => constructor custom lookupOps

/-- Expression-spec metadata, read via DE's expression-spec accessors at
`src/Options.jl:966-991`. Type identities and arbitrary metadata stay opaque. -/
structure ExpressionContext where
  expressionType : Nat := 0
  expressionOptions : Nat := 0
  nodeType : Nat := 0
  maxDegree : Option Nat := none
  deriving DecidableEq, Repr

inductive OptimizerInput where
  | absent
  | keywords (values : List (String × Value))
  | existing (identity : Nat)

/-- `optimizer_algorithm` input, `src/Options.jl:669-671,803-813`.
Existing identity 0 denotes the default BFGS with BackTracking. -/
inductive AlgorithmInput where
  | existing (identity : Nat)
  | legacyName (name : String)
  deriving DecidableEq, Repr

/-- Mutation instance fields that Options constructs, `src/Options.jl:1081-1088`.
Other mutation payloads remain arbitrary identities. -/
structure MutationInstance where
  kind : SymReg.MutateGen.Kind
  payload : Nat := 0
  constantParameters : Option (JF × JF) := none
  deriving DecidableEq, Repr

/-- Legacy weight conversion reuses the existing mirror, then installs the
resolved ConstantMutation parameters, `src/Options.jl:1081-1091`. -/
def mutationBase (weights : SymReg.MutateGen.MutationWeights) (d : Defaults) :
    Jl (List (MutationInstance × JF)) := do
  let pairs ← SymReg.MutateGen.mutationsFromWeights weights
  pure (pairs.map fun (kind, weight) =>
    ({ kind, constantParameters := if kind = .constant then
        some (d.perturbation, d.negateProbability) else none }, weight))

/-- Typed constructor inputs, `src/Options.jl:560-730`. `unchanged` retains the
fields forwarded without any branch (migration, losses, seed, I/O, tracing, etc.). -/
-- Source: src/Options.jl:238,713
-- function default_popmember_type end
-- popmember_type::Type=default_popmember_type(),
def selectPopmemberType (requested : Option (Sum SymReg.PopMember.MemberType Nat)) :
    Sum SymReg.PopMember.MemberType Nat :=
  requested.getD (.inl SymReg.PopMember.defaultPopmemberType)

-- Source: src/Options.jl:733-747,765-766,1194,1259
inductive StateAlias | stateReturn | return_state

def stateAliasKey : StateAlias → String
  | .stateReturn => "stateReturn"
  | .return_state => "return_state"

def resolveReturnState (declared : Option Bool) (aliases : List (StateAlias × Bool))
    (warn : String → Jl Unit) : Jl (Option Bool) := do
  if aliases.isEmpty then return declared
  let kws ← applyAliases (fun _ => declared.elim .absent .flag)
    (aliases.map fun (key,b) => (stateAliasKey key,Value.flag b)) (fun key _ => warn key)
  match kws "deprecated_return_state" with
  | .absent => return none
  | .flag value => return some value
  | _ => throw (.userError "TypeError: deprecated_return_state")

structure Args where
  popmemberType : Option (Sum SymReg.PopMember.MemberType Nat) := none
  version : Option Version := none
  maxsize : Option Int := none
  maxdepth : Option Int := none
  populations : Option Int := none
  populationSize : Option Int := none
  npop : Option Int := none
  npopulations : Option Int := none
  cycles : Option Int := none
  parsimony : Option JF := none
  warmup : Option JF := none
  adaptiveScaling : Option JF := none
  weights : Option WeightInput := none
  crossoverProbability : Option JF := none
  annealing : Option Bool := none
  alpha : Option JF := none
  perturbation : Option JF := none
  negateProbability : Option JF := none
  tournamentN : Option Int := none
  tournamentP : Option JF := none
  fraction : Option JF := none
  fractionHof : Option JF := none
  fractionGuesses : Option JF := none
  topn : Option Int := none
  batching : Option BatchMode := none
  batchSize : Option Int := none
  outputFile : Option String := none
  operators : Option Operators := none
  binary : Option (List Nat) := none
  unary : Option (List Nat) := none
  enumConstructor : Option Nat := none
  elementwiseLoss : Option Nat := none
  lossFunction : Option Nat := none
  expressionLoss : Option Nat := none
  lossScale : String := "log"
  complexity : Option ComplexitySpec := none
  opWeights : Option (List (Nat × Int)) := none
  operatorWeightType : WeightType := WeightType.int
  variableWeightType : WeightType := WeightType.int
  constantWeightType : WeightType := WeightType.int
  operatorWeightValueTypeAny : Bool := false
  variableWeight : Option VarC := none
  constantWeight : Option Int := none
  shouldSimplify : Option Bool := none
  constraintSequence : Option (Jl SymReg.SimpCons.ConstraintInput) := none
  constraints : Option SymReg.SimpCons.ConstraintInput := none
  unaryConstraints : Option SymReg.SimpCons.DegreeInput := none
  binaryConstraints : Option SymReg.SimpCons.DegreeInput := none
  nested : Option SymReg.SimpCons.NestedInput := none
  expressionSpec : Option ExpressionContext := none
  expressionType : Option Nat := none
  expressionOptions : Option Nat := none
  nodeType : Option Nat := none
  explicitDegree : Option Nat := none
  earlyStop : Option JF := none
  earlyStopFunction : Option Nat := none
  algorithm : AlgorithmInput := .existing 0
  inputStream : Nat := 0
  optimizer : OptimizerInput := .absent
  optimizerIterations : Option Int := none
  optimizerCalls : Option Int := none
  defaultMutations : Option (List (MutationInstance × JF)) := none
  mutations : List (MutationInstance × JF) := []
  defaultCrossovers : Option (List (Nat × JF)) := none
  crossovers : List (Nat × JF) := []
  plugins : List Nat := []
  defaultPlugins : Option (List (Option Nat)) := none
  printPrecision : Int := 5
  deterministic : Bool := false
  fastCycle : Bool := false
  defineHelpers : Bool := true
  outputDirectory : Option String := none
  testingEnvironment : Bool := false
  dimensionPenalty : Option JF := none
  dimensionless : Bool := false
  turbo : Bool := false
  bumper : Bool := false
  migration : Bool := true
  hofMigration : Bool := true
  optimizeConstants : Bool := true
  useFrequency : Bool := true
  tournamentFrequency : Bool := true
  verbosity : Option Int := none
  saveToFile : Bool := true
  seed : Option Int := none
  progress : Option Bool := none
  terminalWidth : Option Int := none
  optimizerProbability : JF := .fin (14 / 100)
  optimizerRestarts : Int := 2
  tracingFile : String := "pysr_trace.jsonl"
  returnState : Option Bool := none
  stateAliases : List (StateAlias × Bool) := []
  timeout : Option JF := none
  maxEvals : Option Int := none
  skipFailures : Bool := true
  useTracing : Bool := false

/-- Resolved versioned defaults before the assertions, `src/Options.jl:849-875`. -/
def supplyDefaults (a : Args) : Defaults :=
  let d := defaultOptions a.version
  let populations := populationAliases a.populationSize a.populations a.npop a.npopulations
  { d with
    maxsize := a.maxsize.getD d.maxsize,
    populations := populations.2.getD d.populations,
    populationSize := populations.1.getD d.populationSize,
    cycles := a.cycles.getD d.cycles, parsimony := a.parsimony.getD d.parsimony,
    warmup := a.warmup.getD d.warmup, adaptiveScaling := a.adaptiveScaling.getD d.adaptiveScaling,
    crossoverProbability := a.crossoverProbability.getD d.crossoverProbability,
    annealing := a.annealing.getD d.annealing, alpha := a.alpha.getD d.alpha,
    perturbation := a.perturbation.getD d.perturbation,
    negateProbability := a.negateProbability.getD d.negateProbability,
    tournamentN := a.tournamentN.getD d.tournamentN,
    tournamentP := a.tournamentP.getD d.tournamentP,
    fraction := a.fraction.getD d.fraction, fractionHof := a.fractionHof.getD d.fractionHof,
    fractionGuesses := a.fractionGuesses.getD d.fractionGuesses,
    topn := a.topn.getD d.topn, batching := a.batching.getD d.batching,
    batchSize := a.batchSize.or d.batchSize }

/-- Constructor assertion order, `src/Options.jl:814-844`. -/
-- if !isnothing(loss_function) && recommend_loss_function_expression(expression_type)
--     @warn(
--         "You are using `loss_function` with `$(expression_type)`. " *
--             "You should use `loss_function_expression` instead, as it is designed to work with expressions directly."
--     )
-- end
def validateInitial (a : Args)
    (recommend : Option Nat → Jl Bool := fun t => pure (recommendExpressionLoss t))
    (warn : Option Nat → Jl Unit := fun _ => pure ()) : Jl Unit := do
  if a.outputFile.isSome then throw (.errorException "`output_file` is deprecated. Use `output_directory` instead.")
  if a.operators.isSome then
    if a.binary.isSome then throw (.assertionError "binary_operators === nothing")
    if a.unary.isSome then throw (.assertionError "unary_operators === nothing")
    if a.enumConstructor.isSome then throw (.assertionError "operator_enum_constructor === nothing")
  if ([a.elementwiseLoss, a.lossFunction, a.expressionLoss].filter Option.isSome).length > 1 then
    throw (.assertionError "Only one loss may be supplied")
  if a.lossFunction.isSome then
    if ← recommend a.expressionType then warn a.expressionType
  if a.complexity.isSome && (a.opWeights.isSome || a.variableWeight.isSome || a.constantWeight.isSome) then
    throw (.assertionError "Complexity mapping conflicts with individual complexities")

/-- Assertions on supplied version defaults, `src/Options.jl:889-892`.
`0 <= warmup` follows Julia's unordered NaN comparison. -/
def nonnegative : JF → Bool
  | .fin x => decide (0 <= x)
  | .posInf => true
  | _ => false

def validateScalars (d : Defaults) (lossScale : String) : Jl Unit := do
  if d.maxsize <= 3 then throw (.assertionError "maxsize > 3")
  if !nonnegative d.warmup then throw (.assertionError "warmup_maxsize_by >= 0")
  if d.tournamentN >= d.populationSize then throw (.assertionError "tournament_selection_n < population_size")
  if lossScale != "log" && lossScale != "linear" then throw (.assertionError "loss_scale must be log or linear")

/-- Simplification defaults, `src/Options.jl:878-887`. -/
def resolveSimplify (a : Args) : Bool :=
  a.shouldSimplify.getD (a.lossFunction.isNone && a.expressionLoss.isNone &&
    a.nested.isNone && a.constraintSequence.isNone && a.constraints.isNone && a.binaryConstraints.isNone && a.unaryConstraints.isNone)

/-- Constraint routing and its additional assertions, `src/Options.jl:924-964`.
Building the tables is delayed until after expression-spec validation. -/
def routeConstraints (a : Args) (ops actualOps : List (List Nat)) :
    Jl (Option SymReg.SimpCons.ConstraintInput ×
      Option SymReg.SimpCons.DegreeInput × Option SymReg.SimpCons.DegreeInput) := do
  let global ← match a.constraintSequence with
    | some convert => convert.map some
    | none => pure a.constraints
  if let some constraints := global then
    if a.binaryConstraints.isSome || a.unaryConstraints.isSome then
      throw (.assertionError "all(isnothing, (bin_constraints, una_constraints))")
    if a.operators.isSome then
      if !(decide actualOps.flatten.Nodup) then
        throw (.errorException "Operator appears in multiple degrees. You can't use constraints.")
      return (some constraints, none, none)
    else
      let unary := ops[0]?.getD []
      let binary := ops[1]?.getD []
      if binary.any (fun op => unary.contains op) then
        throw (.assertionError "Operator appears in unary and binary operators")
      match constraints with
      | .operatorPairs pairs => return (none, some (.pairs pairs), some (.pairs pairs))
      | .degrees _ => throw (.methodError "Dict(constraints)")
  else
    if a.operators.isSome && (a.binaryConstraints.isSome || a.unaryConstraints.isSome) then
      throw (.assertionError "Use constraints with user_provided_operators")
    return (none, a.unaryConstraints, a.binaryConstraints)

structure SpecAccess where
  getType : ExpressionContext → Jl Nat := fun c => pure c.expressionType
  getOptions : ExpressionContext → Jl Nat := fun c => pure c.expressionOptions
  getNode : ExpressionContext → Jl (Nat × Option Nat) := fun c => pure (c.nodeType,c.maxDegree)

/-- Expression metadata and max-degree resolution, `src/Options.jl:966-991`. -/
def resolveExpression (a : Args) (defaultNode : Nat → Nat) (ops : List (List Nat))
    (access : SpecAccess := {}) :
    Jl (ExpressionContext × Nat) := do
  let ctx ← if let some ctx := a.expressionSpec then
    if a.expressionType.isSome then throw (.assertionError "expression_type === nothing")
    if a.expressionOptions.isSome then throw (.assertionError "expression_options === nothing")
    if a.nodeType.isSome then throw (.assertionError "node_type === nothing")
    let expressionType ← access.getType ctx
    let expressionOptions ← access.getOptions ctx
    let (nodeType, maxDegree) ← access.getNode ctx
    pure { expressionType, expressionOptions, nodeType, maxDegree }
  else
    let expressionType := a.expressionType.getD 0
    pure {
      expressionType, expressionOptions := a.expressionOptions.getD 0,
      nodeType := a.nodeType.getD (defaultNode expressionType), maxDegree := a.explicitDegree }
  pure (ctx, withMaxDegree ctx.maxDegree a.operators.isSome ops)

/-- Complexity routing, `src/Options.jl:1005-1013`; supplied custom functions or
mappings are preserved, and operator keys use the shared dictionary normalizer. -/
def resolveComplexity (a : Args) (ops : List (List Nat)) : Jl ComplexitySpec := do
  if let some c := a.complexity then return c
  let pairs ← match a.opWeights with
    | none => pure none
    | some ps => do pure (some (← SymReg.SimpCons.mapKeys opmap ps))
  return .mapping (← complexityMapping pairs a.variableWeight a.constantWeight ops
    (if a.operatorWeightValueTypeAny then .any else a.operatorWeightType) a.variableWeightType a.constantWeightType)

/-- Optim.Options parsing, `src/Options.jl:1042-1055`. Keywords are appended
last, so a value inside optimizer_options takes precedence over separate keywords. -/
def resolveOptimizer (a : Args) : Jl (OptimizerInput × Int × Int) := do
  match a.optimizer with
  | .existing id =>
    if a.optimizerIterations.isSome || a.optimizerCalls.isSome then
      throw (.assertionError "Existing Optim.Options conflicts with iteration/call keywords")
    pure (.existing id, 0, 0)
  | input => pure (input, a.optimizerIterations.getD 8, a.optimizerCalls.getD 10000)

/-- Merge explicit, plugin, default weighted instances by concrete type,
`src/Options.jl:1108-1121,1141-1156`. `sameType` compares concrete Julia types;
instance fields are retained unchanged. Plugin/default lists can repeat types. -/
def mergeWeighted {I : Type} (sameType : I → I → Bool)
    (explicit plugin defaults : List (I × JF)) : List (I × JF) :=
  let withPlugin := plugin ++ defaults.filter (fun d => !plugin.any (fun p => sameType p.1 d.1))
  explicit ++ withPlugin.filter (fun d => !explicit.any (fun p => sameType p.1 d.1))

-- Source: src/Options.jl:1093-1121,1125-1156
-- p.first => Float64(p.second) for p in something(mutations, ())
-- p.first => Float64(p.second) for plugin in plugin_tuple for p in plugin_mutations(plugin)
def convertEntries {m : Type → Type} [Monad m] {I : Type} (convert : JF → m JF)
    (entries : List (I × JF)) : m (List (I × JF)) :=
  entries.mapM fun (instanceId, weight) => do pure (instanceId, ← convert weight)

def resolveWeighted {m : Type → Type} [Monad m] {I : Type} (sameType : I → I → Bool)
    (convert : JF → m JF) (explicit : List (I × JF)) (defaults : Option (List (I × JF)))
    (base : m (List (I × JF))) (plugins : List Nat) (hook : Nat → m (List (I × JF))) : m (List (I × JF)) := do
  let ds ← match defaults with | none => base | some xs => convertEntries convert xs
  let es ← convertEntries convert explicit
  let ps ← match defaults with
    | some _ => pure []
    | none => do
      let chunks ← plugins.mapM fun p => do convertEntries convert (← hook p)
      pure chunks.flatten
  pure (mergeWeighted sameType es ps ds)

/-- Legacy mutation weights conflict with explicit default_mutations,
`src/Options.jl:1073-1079`; mutations itself remains compatible with both. -/
def validateMutationDefaults (weightsProvided defaultsProvided : Bool) : Jl Unit :=
  if weightsProvided && defaultsProvided then
    throw (.argumentError "`mutation_weights` and `default_mutations` cannot be used together.")
  else pure ()

-- Source: src/Options.jl:1072-1079
-- set_mutation_weights = create_mutation_weights(mutation_weights)
-- if mutation_weights_were_provided && default_mutations !== nothing
--     throw(ArgumentError("`mutation_weights` and `default_mutations` cannot be used together."))
-- end
def mutationStage (a : Args) : Jl SymReg.MutateGen.MutationWeights := do
  let weights ← resolveWeights a.version a.weights
  validateMutationDefaults a.weights.isSome a.defaultMutations.isSome
  return weights

-- Source: src/Options.jl:1158-1178; Julia base/gmp.jl:396-405
-- batch_size = batch_size === nothing ? nothing : Int(batch_size)
def fitsInt (n : Int) : Bool := decide (-9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807)

def toMachineInt (n : Int) : Jl Int :=
  if fitsInt n then pure n else throw .inexactError

def validateFinal (precision : Int) (batching : BatchMode) (batchSize : Option Int)
    (ad : Jl Nat) (directory : Jl (Option String)) : Jl (Nat × Option String × Option Int) := do
  if precision <= 0 then throw (.assertionError "print_precision > 0")
  let backend ← ad
  let dir ← directory
  if let .invalid _ := batching then throw (.argumentError "`batching` must be `true`, `false`, or `:auto`.")
  if batchSize.any (fun n => n < 1) then throw (.argumentError "`batch_size` must be at least 1.")
  let size ← batchSize.mapM toMachineInt
  pure (backend, dir, size)

-- Source: src/Options.jl:1034-1040,1258
-- stopping_point = Float64(early_stop_condition)
-- Base.Fix2(<, stopping_point) ∘ first ∘ tuple
inductive StopCondition where
  | absent
  | function (identity : Nat)
  | below (threshold : JF)
  deriving DecidableEq

def StopCondition.apply (f : Nat → JF → Int → Bool) (loss : JF) (complexity : Int) : StopCondition → Option Bool
  | .absent => none
  | .function identity => some (f identity loss complexity)
  | .below threshold => some (SymReg.Population.flt loss threshold)

def installStop {m : Type → Type} [Monad m] (threshold : Option JF) (fn : Option Nat) (convert : JF → m JF) : m StopCondition := do
  if let some t := threshold then return .below (← convert t)
  return fn.elim .absent .function

/-- External constructor calls imported by Options, `src/Options.jl:894-904,
1017-1032,1047-1052,1060-1070,1160-1172`. A service is a result including errors;
its opaque successful output is retained. -/
structure Services where
  threshold64 : JF → Jl JF := fun x => pure (SymReg.Loss.LossPrecision.round .float64 x)
  helpers : List (List Nat) → Jl Unit := fun _ => pure ()
  operatorConstructor : Option Nat → List (List Nat) → Jl Operators := fun _ ops => pure ⟨ops, true, 0⟩
  specAccess : SpecAccess := {}
  defaultNode : Nat → Nat := id
  pluginDefaults : Defaults → Args → Jl (List (Option Nat)) := fun _ _ => pure []
  pluginKind : Nat → Nat := id
  weight64 : JF → Jl JF := fun w => pure (SymReg.Loss.LossPrecision.round .float64 w)
  pluginMutations : Nat → Jl (List (MutationInstance × JF)) := fun _ => pure []
  pluginCrossovers : Nat → Jl (List (Nat × JF)) := fun _ => pure []
  optimizerConstructor : OptimizerInput → Int → Int → Jl Nat := fun _ _ _ => pure 0
  depwarn : String → Jl Unit := fun _ => pure ()
  makeAlgorithm : OptimizerKind → LineSearch → Jl Nat := fun kind _ => pure (if kind == .nelderMead then 1 else 0)
  autodiff : Args → Jl Nat := fun _ => pure 0
  temporaryDirectory : Jl String := pure "/tmp/options"
  crossoverBase : Jl (List (Nat × JF)) := pure [(0, .fin 1)]
  crossoverSameType : Nat → Nat → Bool := (· == ·)
  recommendLoss : Option Nat → Jl Bool := fun t => pure (recommendExpressionLoss t)
  lossWarning : Option Nat → Jl Unit := fun _ => pure ()

/-- Output directory resolution, `src/Options.jl:1166-1172`. -/
def resolveDirectory (directory : Option String) (testing : Bool)
    (temporaryDirectory : Jl String) : Jl (Option String) := do
  if directory.isNone && testing then pure (some (← temporaryDirectory))
  else pure directory

/-- Locals computed before the generated Options struct constructor,
`src/Options.jl:1180-1182`. -/
structure Parts where
  defaults : Defaults
  operators : Operators
  lookupOps : List (List Nat)
  constraints : List (List SymReg.SimpCons.ConstraintValue)
  nested : Option (List (Nat × Nat × List (Nat × Nat × Int)))
  complexity : ComplexitySpec
  expression : ExpressionContext
  maxDegree : Nat
  weights : SymReg.MutateGen.MutationWeights
  mutations : List (MutationInstance × JF)
  crossovers : List (Nat × JF)
  optimizer : Nat
  optimizerAlgorithm : Nat
  normalizedState : Option Bool
  stopCondition : StopCondition
  plugins : List Nat
  autodiff : Nat
  outputDirectory : Option String

/-- The generated Options struct constructor, `src/Options.jl:1182-1269`.
`source` supplies the untouched fields; constructor-only inputs such as fast_cycle
have no corresponding output field. -/
structure ValField (α : Type) where
  value : α

structure Result extends Parts where
  dimensionPenalty : Option JF
  dimensionless : Bool
  turbo : ValField (Bool)
  bumper : ValField (Bool)
  migration : Bool
  hofMigration : Bool
  optimizeConstants : Bool
  useFrequency : Bool
  tournamentFrequency : Bool
  verbosity : Option Int
  saveToFile : Bool
  seed : Option Int
  progress : Option Bool
  terminalWidth : Option Int
  optimizerProbability : JF
  optimizerRestarts : Int
  tracingFile : String
  returnState : ValField (Option Bool)
  timeout : Option JF
  maxEvals : Option Int
  skipFailures : Bool
  useTracing : ValField (Bool)
  deterministic : Bool
  printPrecision : ValField (Int)
  inputStream : Nat
  lossScale : String
  lossFunction : Option Nat
  expressionLoss : Option Nat
  defineHelpers : Bool
  nops : List Nat
  maxdepth : Int
  shouldSimplify : Bool
  elementwiseLoss : Nat
  popmemberType : Sum SymReg.PopMember.MemberType Nat := .inl .family

def assemble (a : Args) (parts : Parts) : Result :=
  { toParts := parts,
    dimensionPenalty := a.dimensionPenalty.map (SymReg.Loss.LossPrecision.round .float64),
    dimensionless := a.dimensionless,
    turbo := ⟨a.turbo⟩,
    bumper := ⟨a.bumper⟩,
    migration := a.migration,
    hofMigration := a.hofMigration,
    optimizeConstants := a.optimizeConstants,
    useFrequency := a.useFrequency,
    tournamentFrequency := a.tournamentFrequency,
    verbosity := a.verbosity,
    saveToFile := a.saveToFile,
    seed := a.seed,
    progress := a.progress,
    terminalWidth := a.terminalWidth,
    optimizerProbability := SymReg.Loss.LossPrecision.round .float64 a.optimizerProbability,
    optimizerRestarts := a.optimizerRestarts,
    tracingFile := a.tracingFile,
    returnState := ⟨parts.normalizedState⟩,
    timeout := a.timeout.map (SymReg.Loss.LossPrecision.round .float64),
    maxEvals := a.maxEvals,
    skipFailures := a.skipFailures,
    useTracing := ⟨a.useTracing⟩,
    deterministic := a.deterministic,
    printPrecision := ⟨a.printPrecision⟩,
    inputStream := a.inputStream,
    lossScale := a.lossScale,
    lossFunction := a.lossFunction,
    expressionLoss := a.expressionLoss,
    defineHelpers := a.defineHelpers,
    nops := parts.operators.ops.map List.length,
    maxdepth := a.maxdepth.getD parts.defaults.maxsize,
    shouldSimplify := resolveSimplify a, elementwiseLoss := a.elementwiseLoss.getD 0,
    popmemberType := selectPopmemberType a.popmemberType }

/-- `Options`, `src/Options.jl:803-1271`, after deprecated-keyword normalization.
Imported methods are supplied as services; no deterministic/parallelism check occurs.
Numeric type conversion is represented after successful exact Int/Float64 conversion. -/
def constructParts (s : Services) (a : Args) : Jl Parts := do
  let normalizedState ← resolveReturnState a.returnState a.stateAliases s.depwarn
  if a.npop.isSome then s.depwarn "npop"
  if a.npopulations.isSome then s.depwarn "npopulations"
  let optimizerAlgorithm ← match a.algorithm with
    | .existing identity => pure identity
    | .legacyName name => optimizerFromString (s.depwarn "optimizer_algorithm") s.makeAlgorithm name
  validateInitial a s.recommendLoss s.lossWarning
  let d := supplyDefaults a
  validateScalars d a.lossScale
  let rawOps := match a.operators with
    | some o => o.ops
    | none => [a.unary.getD (d.ops[0]?.getD []), a.binary.getD (d.ops[1]?.getD [])]
  if a.defineHelpers && a.operators.isNone then s.helpers rawOps
  let lookupOps := mapOperators rawOps
  let nested ← SymReg.SimpCons.buildNested opmap lookupOps a.nested
  let actualOps := match a.operators with
    | some o => if o.standard then lookupOps else rawOps
    | none => lookupOps
  let (generic, unary, binary) ← routeConstraints a lookupOps actualOps
  let (expression, maxDegree) ← resolveExpression a s.defaultNode lookupOps s.specAccess
  let constraints ← SymReg.SimpCons.buildConstraints opmap lookupOps generic unary binary
  let complexity ← resolveComplexity a lookupOps
  let operators ← resolveOperators s.operatorConstructor a.operators a.enumConstructor lookupOps
  let stopCondition ← installStop a.earlyStop a.earlyStopFunction s.threshold64
  let (optimizerInput, iterations, calls) ← resolveOptimizer a
  let optimizer ← match optimizerInput with
    | .existing id => pure id
    | _ => s.optimizerConstructor optimizerInput iterations calls
  let defaults ← match a.defaultPlugins with
    | some ds => pure ds
    | none => s.pluginDefaults d a
  let plugins := SymReg.Plugins.mergeDefaults s.pluginKind a.plugins defaults
  let weights ← mutationStage a
  let mutations ← resolveWeighted (fun a b => a.kind == b.kind) s.weight64 a.mutations
    a.defaultMutations (mutationBase weights d) plugins s.pluginMutations
  let crossovers ← resolveWeighted s.crossoverSameType s.weight64 a.crossovers
    a.defaultCrossovers s.crossoverBase plugins s.pluginCrossovers
  let (autodiff, outputDirectory, batchSize) ← validateFinal a.printPrecision d.batching d.batchSize
    (s.autodiff a) (resolveDirectory a.outputDirectory a.testingEnvironment s.temporaryDirectory)
  let integers := [d.tournamentN, d.maxsize, a.maxdepth.getD d.maxsize, d.populations,
      d.populationSize, d.cycles, d.topn] ++ [a.verbosity,a.seed,a.terminalWidth,a.maxEvals].filterMap id
  if !integers.all fitsInt then throw .inexactError
  let stored := { d with
    batchSize := batchSize,
    tournamentP := SymReg.Loss.LossPrecision.round .float64 d.tournamentP,
    parsimony := SymReg.Loss.LossPrecision.round .float64 d.parsimony,
    perturbation := SymReg.Loss.LossPrecision.round .float64 d.perturbation,
    crossoverProbability := SymReg.Loss.LossPrecision.round .float64 d.crossoverProbability,
    warmup := SymReg.Loss.LossPrecision.round .float64 d.warmup,
    adaptiveScaling := SymReg.Loss.LossPrecision.round .float64 d.adaptiveScaling,
    fraction := SymReg.Loss.LossPrecision.round .float64 d.fraction,
    fractionHof := SymReg.Loss.LossPrecision.round .float64 d.fractionHof,
    fractionGuesses := SymReg.Loss.LossPrecision.round .float64 d.fractionGuesses,
    negateProbability := SymReg.Loss.LossPrecision.round .float64 d.negateProbability }
  pure {
    defaults := stored, operators, lookupOps, constraints, nested, complexity, expression, maxDegree, weights,
    mutations, crossovers,
    optimizer, optimizerAlgorithm, normalizedState, stopCondition, plugins, autodiff, outputDirectory }

/-- `Options`, `src/Options.jl:1182-1271`: construct the final immutable struct only
after every preceding computation succeeds. -/
def construct (s : Services) (a : Args) : Jl Result :=
  (constructParts s a).map (assemble a)

def popmemberDefaultOverride : Prop := ∀ (a : Args) (parts : Parts) ty,
    (assemble { a with popmemberType := some ty } parts).popmemberType = ty ∧
    (assemble { a with popmemberType := none } parts).popmemberType = .inl .family

theorem popmemberDefaultOverride_holds : popmemberDefaultOverride := by
  intro a parts ty
  exact ⟨rfl, rfl⟩

end SymReg.Options
