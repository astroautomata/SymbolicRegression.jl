import SymReg.Options.Struct
import SymReg.MutateGen.WeightsProps

namespace SymReg.Options
open DynExpr SymReg.Complexity SymReg.HeapLemmas

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

@[local simp] private theorem jlThrow {α : Type} (e : JlError) :
    (throw e : Jl α) = .error e := rfl
attribute [local simp] pure_ok ok_bind

/-- The source and target identities follow the table in src/Options.jl:181-201. -/
def canonical : Nat → Nat
  | 1 => 101
  | 2 => 102
  | 3 => 103
  | 4 => 104
  | 5 => 105
  | 6 => 105
  | 7 => 106
  | 8 => 107
  | 9 => 108
  | 10 => 109
  | 11 => 110
  | 12 => 111
  | 13 => 112
  | 14 => 113
  | 15 => 114
  | 16 => 115
  | 17 => 116
  | 18 => 117
  | 19 => 118
  | op => op

private theorem canonical_eq (op : Nat) : opmap op = canonical op := by
  iterate 20 (cases op <;> first | rfl | rename_i op)

def operatorIdempotent : Prop := ∀ op, opmap op = canonical op ∧ opmap (opmap op) = canonical op

theorem operatorIdempotent_holds : operatorIdempotent := by
  intro op
  refine ⟨canonical_eq op, ?_⟩
  rw [← canonical_eq op]
  unfold opmap
  repeat' first | omega | split

def operatorArity : Prop := ∀ ops : List (List Nat), mapOperators ops = ops.map (List.map canonical)

theorem operatorArity_holds : operatorArity := by
  intro ops
  rw [mapOperators, funext canonical_eq]

def inverseNormalized : Prop :=
  ([105,106,107,108,109,110,111,112,113,114,115,116,117,118].map inverseOpmap =
   [5,7,8,9,10,11,12,13,14,15,16,17,18,19]) ∧
  (∀ op, op < 105 ∨ 118 < op → inverseOpmap op = op) ∧
  ∀ op, opmap (inverseOpmap (opmap op)) = opmap op

theorem inverseNormalized_holds : inverseNormalized := by
  refine ⟨rfl, ?_, ?_⟩
  · intro op h
    simp [inverseOpmap, show ¬(105 ≤ op ∧ op ≤ 118) by omega]
  · intro op
    unfold opmap inverseOpmap
    repeat' first | omega | split

/-- Source: assignments at src/Options.jl:748-771, independently of the warning table. -/
private def ordinaryAliases : List (String × String) :=
  [("hofMigration", "hof_migration"),
   ("shouldOptimizeConstants", "should_optimize_constants"),
   ("perturbationFactor", "perturbation_factor"),
   ("batchSize", "batch_size"),
   ("crossoverProbability", "crossover_probability"),
   ("warmupMaxsizeBy", "warmup_maxsize_by"),
   ("useFrequency", "use_frequency"),
   ("useFrequencyInTournament", "use_frequency_in_tournament"),
   ("ncyclesperiteration", "ncycles_per_iteration"),
   ("fractionReplaced", "fraction_replaced"),
   ("fractionReplacedHof", "fraction_replaced_hof"),
   ("probNegate", "probability_negate_constant"),
   ("optimize_probability", "optimizer_probability"),
   ("probPickFirst", "tournament_selection_p"),
   ("earlyStopCondition", "early_stop_condition"),
   ("return_state", "deprecated_return_state"),
   ("stateReturn", "deprecated_return_state"),
   ("ns", "tournament_selection_n"),
   ("loss", "elementwise_loss"),
   ("use_recorder", "use_tracing"),
   ("recorder_file", "tracing_file")]

def aliasPrecedence : Prop := ∀ (kws : Keywords) (value : Value) (warn : String → String → Jl Unit),
  ∀ p ∈ ordinaryAliases, applyAlias kws p.1 value warn =
    (warn p.1 p.2).map (fun _ q => if q = p.2 then value else kws q)

theorem aliasPrecedence_holds : aliasPrecedence := by
  intro kws value warn p hp
  have step (w : Jl Unit) (k : Keywords) : (w >>= fun _ => pure k) = w.map (fun _ => k) := by cases w <;> rfl
  simp only [ordinaryAliases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply step

def ignoredAutodiffAlias : Prop := ∀ (kws : Keywords) value (e : JlError) rest,
  applyAlias kws "enable_autodiff" value = .ok kws ∧
  applyAliases kws (("enable_autodiff",value) :: rest) (fun _ _ => .error e) = .error e

theorem ignoredAutodiffAlias_holds : ignoredAutodiffAlias := by
  intro kws value e rest
  exact ⟨rfl,rfl⟩

/-- Unknown extra keywords fail before any defaults are supplied. -/
def unknownKeyword : Prop := ∀ (kws : Keywords) key value,
  deprecatedAliases.find? (fun p => p.1 = key) = none →
  applyAlias kws key value = .error (.errorException ("Unknown keyword argument: " ++ key))

theorem unknownKeyword_holds : unknownKeyword := by
  intro kws key value h
  simp [applyAlias, h]

example : deprecatedAliases.find? (fun p => p.1 = "parallelism") = none := by decide

def populationAliasPrecedence : Prop := ∀ (a : Args) size pops,
  let d := defaultOptions a.version
  let base := { a with npop := none, npopulations := none }
  ((supplyDefaults base).populationSize, (supplyDefaults base).populations) =
    (a.populationSize.getD d.populationSize, a.populations.getD d.populations) ∧
  ((supplyDefaults { base with npop := some size }).populationSize,
    (supplyDefaults { base with npop := some size }).populations) = (size, a.populations.getD d.populations) ∧
  ((supplyDefaults { base with npopulations := some pops }).populationSize,
    (supplyDefaults { base with npopulations := some pops }).populations) = (a.populationSize.getD d.populationSize, pops) ∧
  ((supplyDefaults { base with npop := some size, npopulations := some pops }).populationSize,
    (supplyDefaults { base with npop := some size, npopulations := some pops }).populations) = (size,pops)

theorem populationAliasPrecedence_holds : populationAliasPrecedence := by
  intro a size pops
  exact ⟨rfl,rfl,rfl,rfl⟩

def returnStateAliasOrder : Prop := ∀ (declared : Option Bool) (a b : Bool),
  let readFlag := fun (aliases : List (StateAlias × Bool)) =>
    (construct {} { returnState := declared, stateAliases := aliases }).map (fun o => o.returnState.value)
  readFlag [(.stateReturn,a),(.return_state,b)] = .ok (some b) ∧
  readFlag [(.return_state,b),(.stateReturn,a)] = .ok (some a) ∧ readFlag [] = .ok declared ∧
  readFlag [(.stateReturn,a)] = .ok (some a) ∧ readFlag [(.return_state,b)] = .ok (some b)

theorem returnStateAliasOrder_holds : returnStateAliasOrder := by
  intro declared a b
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

def weightCreation : Prop := ∀ (w : SymReg.MutateGen.MutationWeights) kws (keywords : Keywords) identity (e : JlError),
  createMutationWeights (.existing identity w) = .ok ⟨some identity,w⟩ ∧
  createMutationWeights (.named kws) = (SymReg.MutateGen.mutationWeights kws).map (fun x => ⟨none,x⟩) ∧
  createMutationWeights (.named [("mutate_constant",.converted (.error e))]) = .error e ∧
  applyAlias keywords "mutationWeights" (.object identity) = .ok (setKey keywords "mutation_weights" (.object identity))

private def expectedLegacy : Defaults := {
    ops := [[],[101,103,104,102]],
    maxsize := 20,
    populations := 15,
    populationSize := 33,
    cycles := 550,
    parsimony := literal64 (2 / 625),
    warmup := literal64 0,
    adaptiveScaling := literal64 20,
    weightKw := [("mutate_constant", literal64 (6 / 125)),
      ("mutate_operator", literal64 (47 / 100)),
      ("swap_operands", literal64 (1 / 10)),
      ("rotate_tree", literal64 0),
      ("add_node", literal64 (79 / 100)),
      ("insert_node", literal64 (51 / 10)),
      ("delete_node", literal64 (17 / 10)),
      ("simplify", literal64 (1 / 500)),
      ("randomize", literal64 (23 / 100000)),
      ("do_nothing", literal64 (21 / 100)),
      ("optimize", literal64 0),
      ("form_connection", literal64 (1 / 2)),
      ("break_connection", literal64 (1 / 10))],
    crossoverProbability := literal64 (33 / 500),
    annealing := false,
    alpha := literal64 (1 / 10),
    perturbation := literal64 (19 / 250),
    negateProbability := literal64 (1 / 100),
    tournamentN := 12,
    tournamentP := literal64 (43 / 50),
    fraction := literal64 (9 / 25000),
    fractionHof := literal64 (7 / 200),
    fractionGuesses := literal64 (1 / 1000),
    topn := 12,
    batching := .disabled,
    batchSize := some 50 }

private def expectedOne : Defaults := {
    ops := [[],[101,103,104,102]],
    maxsize := 30,
    populations := 31,
    populationSize := 27,
    cycles := 380,
    parsimony := literal64 0,
    warmup := literal64 0,
    adaptiveScaling := literal64 1040,
    weightKw := [("mutate_constant", literal64 (173 / 5000)),
      ("mutate_operator", literal64 (293 / 1000)),
      ("swap_operands", literal64 (99 / 500)),
      ("rotate_tree", literal64 (213 / 50)),
      ("add_node", literal64 (247 / 100)),
      ("insert_node", literal64 (7 / 625)),
      ("delete_node", literal64 (87 / 100)),
      ("simplify", literal64 (209 / 100000)),
      ("randomize", literal64 (251 / 500000)),
      ("do_nothing", literal64 (273 / 1000)),
      ("optimize", literal64 0),
      ("form_connection", literal64 (1 / 2)),
      ("break_connection", literal64 (1 / 10))],
    crossoverProbability := literal64 (259 / 10000),
    annealing := true,
    alpha := literal64 (317 / 100),
    perturbation := literal64 (129 / 1000),
    negateProbability := literal64 (743 / 100000),
    tournamentN := 15,
    tournamentP := literal64 (491 / 500),
    fraction := literal64 (9 / 25000),
    fractionHof := literal64 (307 / 5000),
    fractionGuesses := literal64 (1 / 1000),
    topn := 12,
    batching := .disabled,
    batchSize := some 50 }

private def expectedLatest : Defaults :=
  { expectedOne with crossoverProbability := literal64 (1 / 5), batching := .auto, batchSize := none }

private def materializedDefaults : Prop :=
  let vector := fun v => (resolveWeights v none).map SymReg.MutateGen.convertVector
  vector (some ⟨0,0,0,false⟩) = .ok [literal64 (6 / 125),literal64 (47 / 100),literal64 (1 / 10),literal64 (1 / 10),literal64 0,literal64 (79 / 100),literal64 (51 / 10),literal64 (17 / 10),literal64 (1 / 500),literal64 (23 / 100000),literal64 (21 / 100),literal64 0,literal64 0,literal64 (1 / 2),literal64 (1 / 10)] ∧
  vector (some ⟨1,0,0,false⟩) = .ok [literal64 (173 / 5000),literal64 (293 / 1000),literal64 (1 / 10),literal64 (99 / 500),literal64 (213 / 50),literal64 (247 / 100),literal64 (7 / 625),literal64 (87 / 100),literal64 (209 / 100000),literal64 (251 / 500000),literal64 (273 / 1000),literal64 0,literal64 0,literal64 (1 / 2),literal64 (1 / 10)] ∧
  vector none = vector (some ⟨1,0,0,false⟩)

def versionTables : Prop := materializedDefaults ∧
  defaultOptions none = expectedLatest ∧ ∀ v : Version,
    defaultOptions (some v) = if v.major = 0 ∨ (v.major = 1 ∧ v.minor = 0 ∧ v.patch = 0 ∧ v.prerelease) then expectedLegacy
      else if v.major ≥ 2 then expectedLatest else expectedOne

theorem versionTables_holds : versionTables := by
  refine ⟨by unfold materializedDefaults; decide +kernel,?_⟩
  constructor
  · decide +kernel
  · intro v
    by_cases h : v.major = 0 ∨ (v.major = 1 ∧ v.minor = 0 ∧ v.patch = 0 ∧ v.prerelease)
    · have h' : v.beforeOne = true := by simpa [Version.beforeOne,and_assoc] using h
      simp only [defaultOptions,Option.any_some,h',if_true,h]; decide +kernel
    · have h' : v.beforeOne = false := by simpa [Version.beforeOne,and_assoc] using h
      by_cases hm : v.major ≥ 2 <;> simp [defaultOptions,h,h',Version.fromTwo,hm] <;> decide +kernel

example : defaultOptions (some ⟨1,0,0,true⟩) = expectedLegacy := by decide +kernel
example : defaultOptions (some ⟨1,0,0,false⟩) = expectedOne := by decide +kernel
example : defaultOptions (some ⟨2,0,0,true⟩) = expectedLatest := by decide +kernel

/-- An explicit user maxsize/parsimony/batch size overrides every version table. -/
def explicitDefaultsWin : Prop := ∀ (a : Args) maxsize parsimony batchSize,
  (supplyDefaults { a with
    maxsize := some maxsize, parsimony := some parsimony, batchSize := some batchSize }).maxsize = maxsize ∧
  (supplyDefaults { a with
    maxsize := some maxsize, parsimony := some parsimony, batchSize := some batchSize }).parsimony = parsimony ∧
  (supplyDefaults { a with
    maxsize := some maxsize, parsimony := some parsimony, batchSize := some batchSize }).batchSize = some batchSize

theorem explicitDefaultsWin_holds : explicitDefaultsWin := by
  intro a maxsize parsimony batchSize
  exact ⟨rfl, rfl, rfl⟩

/-- Exactly the four scalar assertions determine acceptance at this phase. -/
def scalarValidationExact : Prop := ∀ (d : Defaults) scale,
  validateScalars d scale = .ok () ↔
    3 < d.maxsize ∧ nonnegative d.warmup = true ∧ d.tournamentN < d.populationSize ∧
    (scale = "log" ∨ scale = "linear")

theorem scalarValidationExact_holds : scalarValidationExact := by
  intro d scale
  by_cases hsize : d.maxsize <= 3
  · simp [validateScalars, hsize]; omega
  by_cases hwarm : nonnegative d.warmup = true
  · by_cases ht : d.tournamentN >= d.populationSize
    · simp [validateScalars, hsize, hwarm, ht]; omega
    · by_cases hlog : scale = "log"
      · simp [validateScalars, hsize, hwarm, ht, hlog]; omega
      · by_cases hlinear : scale = "linear"
        · simp [validateScalars, hsize, hwarm, ht, hlinear]; omega
        · simp [validateScalars, hsize, hwarm, ht, hlog, hlinear]
  · simp [validateScalars, hsize, hwarm]

example : 3 < (defaultOptions none).maxsize ∧ nonnegative (defaultOptions none).warmup = true ∧
    (defaultOptions none).tournamentN < (defaultOptions none).populationSize := by decide

/-- maxsize <=3 is rejected irrespective of every other scalar input. -/
def smallMaxsizeRejected : Prop := ∀ (d : Defaults) scale,
  d.maxsize <= 3 → validateScalars d scale = .error (.assertionError "maxsize > 3")

theorem smallMaxsizeRejected_holds : smallMaxsizeRejected := by
  intro d scale h
  simp [validateScalars, h]

example : (3 : Int) <= 3 := by decide

def finalValidationExact : Prop := ∀ precision batching size ad directory,
  validateFinal precision batching size ad directory =
    if precision ≤ 0 then .error (.assertionError "print_precision > 0") else
    match ad, directory with
    | .error e, _ => .error e
    | .ok _, .error e => .error e
    | .ok backend, .ok dir => match batching, size with
      | .invalid _, _ => .error (.argumentError "`batching` must be `true`, `false`, or `:auto`.")
      | _, none => .ok (backend, dir, none)
      | _, some n => if n < 1 then .error (.argumentError "`batch_size` must be at least 1.")
        else if n > 9223372036854775807 then .error .inexactError else .ok (backend, dir, some n)

theorem finalValidationExact_holds : finalValidationExact := by
  intro precision batching size ad dir
  by_cases hp : precision ≤ 0
  · simp [validateFinal,hp]
  · cases ad <;> cases dir <;> cases batching <;> cases size <;>
      simp [validateFinal,hp,toMachineInt,fitsInt] <;> repeat' first | split | omega | contradiction | rfl

def uncheckedScalars : Prop := ∀ (depth pops cycles : Int) (p parsimony crossover fraction hof guesses : JF) (det : Bool),
  let a : Args := {
    maxdepth := some depth, populations := some pops, cycles := some cycles,
    tournamentP := some p, parsimony := some parsimony, crossoverProbability := some crossover,
    fraction := some fraction, fractionHof := some hof, fractionGuesses := some guesses,
    deterministic := det, defaultPlugins := some []}
  let readFields := fun (o : Result) => (o.maxdepth,o.defaults.populations,o.defaults.cycles,o.deterministic,
    o.defaults.tournamentP,o.defaults.parsimony,o.defaults.crossoverProbability,o.defaults.fraction,o.defaults.fractionHof,o.defaults.fractionGuesses)
  let round := SymReg.Loss.LossPrecision.round .float64
  (construct {} a).map readFields = if fitsInt depth && fitsInt pops && fitsInt cycles then
    .ok (depth,pops,cycles,det,round p,round parsimony,round crossover,round fraction,round hof,round guesses)
    else .error .inexactError

/-- Nonpositive population_size also passes if tournament_n is still smaller. -/
def nonpositivePopulationAccepted : Prop := ∀ size tournament : Int,
  tournament < size →
  validateScalars (supplyDefaults { populationSize := some size, tournamentN := some tournament }) "log" = .ok ()

theorem nonpositivePopulationAccepted_holds : nonpositivePopulationAccepted := by
  intro size tournament h
  simp [validateScalars, supplyDefaults, defaultOptions, populationAliases, nonnegative, literal64, SymReg.Loss.LossPrecision.round,
    show ¬tournament >= size by omega]

example : (-1 : Int) < 0 := by decide

/-- With explicit max-degree node types, no context overrides their degree;
otherwise explicit enums select their number of degree slots and defaults select 2. -/
def maxDegreeContext : Prop := ∀ degree provided ops,
  withMaxDegree (some degree) provided ops = degree ∧
  withMaxDegree none true ops = ops.length ∧ withMaxDegree none false ops = 2

theorem maxDegreeContext_holds : maxDegreeContext := by
  intro degree provided ops
  exact ⟨rfl, rfl, rfl⟩


def simplificationDefault : Prop := ∀ (a : Args) (parts : Parts),
  (assemble a parts).shouldSimplify =
    match a.shouldSimplify with
    | some choice => choice
    | none => decide (a.lossFunction = none ∧ a.expressionLoss = none ∧ a.nested.isNone = true ∧ a.constraintSequence.isNone = true ∧
        a.constraints.isNone = true ∧ a.binaryConstraints.isNone = true ∧ a.unaryConstraints.isNone = true)

theorem simplificationDefault_holds : simplificationDefault := by
  intro a parts
  cases h : a.shouldSimplify <;> simp [assemble, resolveSimplify,h,Bool.decide_and,Bool.and_assoc,Option.isNone_iff_eq_none] <;>
    cases a.lossFunction <;> cases a.expressionLoss <;> cases a.nested <;> cases a.constraintSequence <;> cases a.constraints <;> cases a.binaryConstraints <;> cases a.unaryConstraints <;> rfl

/-- Observe the stored closure after stock construction, including Float64 conversion and bypass. -/
def earlyStopStrict : Prop := ∀ (t loss : JF) (c : Int) (fn : Nat) (f : Nat → JF → Int → Bool) (e : JlError),
  let rounded := SymReg.Loss.LossPrecision.round .float64 t
  let args : Args := { earlyStop := some t }
  (construct {} args).map (fun o => o.stopCondition) = .ok (.below rounded) ∧
  (construct {} args).map (fun o => o.stopCondition.apply f loss c) =
    .ok (some (SymReg.Population.flt loss rounded)) ∧
  (construct {} args).map (fun o => o.stopCondition.apply f rounded c) = .ok (some false) ∧
  (construct {} args).map (fun o => o.stopCondition.apply f .nan c) = .ok (some false) ∧
  (construct {} { earlyStop := some .nan }).map (fun o => o.stopCondition.apply f loss c) = .ok (some false) ∧
  (construct { threshold64 := fun _ => .error e } { args with optimizer := .existing 2, optimizerCalls := some 1 }).map
    (fun o => o.stopCondition) = .error e ∧
  (construct { threshold64 := fun _ => .error e } { earlyStopFunction := some fn }).map
    (fun o => o.stopCondition) = .ok (.function fn) ∧
  (construct { threshold64 := fun _ => .error e } {}).map (fun o => o.stopCondition) = .ok .absent ∧
  ∀ converted : JF, (construct { threshold64 := fun _ => .ok converted } args).map
    (fun o => o.stopCondition.apply f loss c) = .ok (some (SymReg.Population.flt loss converted)) ∧
    (installStop (m := StateM (List JF)) (some t) none (fun x => do modify (· ++ [x]); pure converted)).run [] =
      (.below converted,[t])

theorem earlyStopStrict_holds : earlyStopStrict := by
  intro t loss c fn f e
  dsimp only
  refine ⟨rfl, rfl, ?_, rfl, ?_, rfl, rfl, rfl,fun _ => ⟨rfl,rfl⟩⟩
  · change (Except.ok (some (SymReg.Population.flt (SymReg.Loss.LossPrecision.round .float64 t) (SymReg.Loss.LossPrecision.round .float64 t))) : Jl (Option Bool)) = .ok (some false)
    cases SymReg.Loss.LossPrecision.round .float64 t <;> simp [SymReg.Population.flt]
  · cases loss <;> rfl

example : (construct {} { earlyStop := some (.fin (1 + 1 / 2^54)) }).map
    (fun o => o.stopCondition.apply (fun _ _ _ => true) (.fin 1) 0) = .ok (some false) := by
  have h : SymReg.Population.flt (.fin 1) (SymReg.Loss.LossPrecision.round .float64 (.fin (1 + 1 / 2^54))) = false := by decide +kernel
  exact congrArg (fun b => (Except.ok (some b) : Jl (Option Bool))) h

/-- Optim.Options instances conflict with either separate stopping keyword. -/
def optimizerConflict : Prop := ∀ (a : Args) id,
  (a.optimizerIterations.isSome || a.optimizerCalls.isSome) = true →
  resolveOptimizer { a with optimizer := .existing id } =
    .error (.assertionError "Existing Optim.Options conflicts with iteration/call keywords")

theorem optimizerConflict_holds : optimizerConflict := by
  intro a id h
  simp [resolveOptimizer, h]

example : ((some (8 : Int)).isSome || (none : Option Int).isSome) = true := rfl

def optimizerString : Prop := ∀ name (e : JlError) (make : OptimizerKind → LineSearch → Jl Nat),
  optimizerFromString (.error e) make name = .error e ∧
  optimizerFromString (.ok ()) make name = make (if name = "NelderMead" then .nelderMead else .bfgs) .backTracking ∧
  (optimizerFromString (m := StateM (List (Option (OptimizerKind × LineSearch))))
      (modify (· ++ [none])) (fun k l => modify (· ++ [some (k,l)])) name).run [] =
    ((), [none,some ((if name = "NelderMead" then .nelderMead else .bfgs), .backTracking)])

theorem optimizerString_holds : optimizerString := by
  intro name e make
  exact ⟨rfl,rfl,rfl⟩

private theorem bindSuccess {α β : Type} {x : Jl α} {f : α → Jl β} {z : β}
    (h : (x >>= f) = .ok z) : ∃ y, x = .ok y ∧ f y = .ok z := by
  cases x with
  | error e => contradiction
  | ok y => exact ⟨y,rfl,h⟩

private theorem mapSuccess {α β : Type} (f : α → Jl β) (g : α → β)
    (hf : ∀ x y, f x = .ok y → y = g x) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : ys = xs.map g := by
  induction xs generalizing ys with
  | nil => exact (Except.ok.inj h).symm
  | cons a xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b,hb,h⟩ := bindSuccess h
    obtain ⟨bs,hbs,h⟩ := bindSuccess h
    cases (Except.ok.inj h)
    simp [hf _ _ hb,ih _ hbs]

private theorem cast_ok (t : WeightType) (x y : Int) (h : t.cast x = .ok y) : y = x := by
  cases t with
  | big | integer => exact (Except.ok.inj h).symm
  | any => contradiction
  | machine bits unsigned =>
    cases unsigned <;> dsimp [WeightType.cast] at h <;> split at h <;> first | contradiction | exact (Except.ok.inj h).symm

private theorem var_ok (t : WeightType) (x y : VarC) (h : castVariable t x = .ok y) : y = x := by
  cases x with
  | scalar x =>
    cases hx : t.cast x with
    | error e => simp [castVariable,hx,Except.map] at h
    | ok v => simpa [castVariable,hx,Except.map,cast_ok t x v hx] using h.symm
  | vector xs =>
    cases hx : xs.mapM t.cast with
    | error e => simp [castVariable,hx,Except.map] at h
    | ok vs => simpa [castVariable,hx,Except.map,mapSuccess _ id (cast_ok t) xs vs hx] using h.symm

private theorem one_ok (t : WeightType) (x : Int) (h : t.one = .ok x) : x = 1 := by
  cases t <;> simp_all [WeightType.one]

def complexityPromotionShape : Prop :=
  (promotedMapping [(.machine 64 true,[1,2])] (.machine 64 false,.scalar 3) (.machine 64 false,4)).map mappingEltype = .ok (.machine 64 true) ∧
  (promotedMapping [(.machine 64 true,[1,2])] (.machine 128 false,.scalar 3) (.machine 64 false,4)).map mappingEltype = .ok (.machine 128 false) ∧
  ∀ ops v c result,
  promotedMapping ops v c = .ok result → result.use = true ∧
    result.eltype = promotedTypes (ops.map Prod.fst) v.1 c.1 ∧
    result.opC = ops.map Prod.snd ∧ result.varC = v.2 ∧ result.constC = c.2

theorem complexityPromotionShape_holds : complexityPromotionShape := by
  refine ⟨rfl,rfl,?_⟩
  intro ops v c result h
  let t := promotedTypes (ops.map Prod.fst) v.1 c.1
  obtain ⟨vc,hv,h⟩ := bindSuccess (x := castVariable t v.2) h
  obtain ⟨rows,hr,h⟩ := bindSuccess (x := ops.mapM (fun row => row.2.mapM t.cast)) h
  obtain ⟨cc,hc,h⟩ := bindSuccess (x := t.cast c.2) h
  cases (Except.ok.inj h)
  exact ⟨rfl,rfl,mapSuccess _ Prod.snd (fun p ys hy => by simpa using mapSuccess _ id (cast_ok t) p.2 ys hy) _ _ hr,
    var_ok _ _ _ hv,cast_ok _ _ _ hc⟩

def complexityLeaves : Prop :=
  (complexityMapping (some [(11,7)]) (some (.vector [2,3])) none [[11,12],[]] .integer =
      .ok ⟨⟨true,[[7,1],[]],.vector [2,3],1⟩,.integer⟩) ∧
  ∀ (dict : Option (List (Nat × Int))) (v : Option VarC) (c : Option Int) ops ot vt ct result,
  (dict.isNone && v.isNone && c.isNone) = false →
  complexityMapping dict v c ops ot vt ct = .ok result → result.use = true ∧
    result.varC = v.getD (.scalar 1) ∧ result.constC = c.getD 1 ∧ result.opC.map List.length = ops.map List.length

def complexityUseExact : Prop :=
  (complexityMapping (some [(11,7)]) (some (.vector [2,3])) none [[11,12],[]] .integer =
      .ok ⟨⟨true,[[7,1],[]],.vector [2,3],1⟩,.integer⟩) ∧
  (∀ ops, complexityMapping none none none ops = .ok ⟨⟨false,ops.map (fun _ => []),.scalar 0,0⟩,WeightType.int⟩) ∧
  (∀ (dict : Option (List (Nat × Int))) (v : Option VarC) (c : Option Int) ops ot vt ct result, (dict.isNone && v.isNone && c.isNone) = false →
    complexityMapping dict v c ops ot vt ct = .ok result → result.use = true) ∧
  complexityMapping (some []) (some (.scalar (-1))) none [] (.machine 64 true) = .error .inexactError

private theorem mapM_lengths {α β : Type} (f : α → Jl β) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => cases Except.ok.inj h; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y, _, h⟩ := bindSuccess h
    obtain ⟨tail, htail, h⟩ := bindSuccess h
    cases Except.ok.inj h
    simp [ih _ htail]

private theorem mapM_observe {α β γ : Type} (f : α → Jl β) (before : α → γ)
    (after : β → γ) (hf : ∀ x y, f x = .ok y → after y = before x)
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys) :
    ys.map after = xs.map before := by
  induction xs generalizing ys with
  | nil => cases Except.ok.inj h; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bindSuccess h
    obtain ⟨tail, htail, h⟩ := bindSuccess h
    cases Except.ok.inj h
    simp [hf _ _ hy, ih _ htail]

private theorem lookupVariable_ok (t : WeightType) (v : Option VarC) (y : VarC)
    (h : lookupVariable t v = .ok y) : y = v.getD (.scalar 1) := by
  cases v with
  | some x => exact var_ok t x y h
  | none => cases t <;> simp_all [lookupVariable, WeightType.one, Except.map]

private theorem lookupConstant_ok (t : WeightType) (c : Option Int) (y : Int)
    (h : lookupConstant t c = .ok y) : y = c.getD 1 := by
  cases c with
  | some x => exact cast_ok t x y h
  | none => exact one_ok t y h

theorem complexityLeaves_holds : complexityLeaves := by
  refine ⟨rfl, ?_⟩
  intro dict v c ops ot vt ct result custom h
  simp only [complexityMapping, custom, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨rows, hr, h⟩ := bindSuccess h
  obtain ⟨vc, hv, h⟩ := bindSuccess h
  obtain ⟨cc, hc, h⟩ := bindSuccess h
  obtain ⟨hu, _, ho, hv', hc'⟩ := complexityPromotionShape_holds.2.2 _ _ _ _ h
  refine ⟨hu, hv'.trans (lookupVariable_ok _ _ _ hv),
    hc'.trans (lookupConstant_ok _ _ _ hc), ?_⟩
  rw [ho, List.map_map]
  simpa only [List.map_map, Function.comp_def] using mapM_observe _ List.length List.length
    (fun row out hout => (mapM_lengths _ row out hout).symm) ops rows hr

theorem complexityUseExact_holds : complexityUseExact := by
  refine ⟨complexityLeaves_holds.1, fun _ => rfl, ?_, rfl⟩
  intro dict v c ops ot vt ct result custom h
  exact (complexityLeaves_holds.2 dict v c ops ot vt ct result custom h).1

def complexityEqualityLaws : Prop := ∀ a b : TypedMapping,
  (complexityEq a.toCMap b.toCMap = true ↔ a.use = b.use ∧ a.opC = b.opC ∧ a.varC = b.varC ∧ a.constC = b.constC) ∧
  mappingEltype a = a.eltype

private theorem varEq_iff (a b : VarC) : varEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [varEq]

theorem complexityEqualityLaws_holds : complexityEqualityLaws := by
  intro a b
  exact ⟨by simp [complexityEq,varEq_iff,and_assoc],rfl⟩

/-- The documented mutation defaults agree with the defaults used by Options. -/
def documentedMutationDefaults : Prop := ∀ field : SymReg.MutateGen.WName,
  (resolveWeights none none).map (fun w => w.get field) =
    .ok (SymReg.MutateGen.defaultOfField field)

theorem documentedMutationDefaults_refuted : ¬ documentedMutationDefaults := by
  intro h
  have hconstant := h .mutate_constant
  change (Except.ok (SymReg.Loss.LossPrecision.round .float64 (literal64 (346 / 10000))) : Jl JF) = .ok (.fin (353 / 10000)) at hconstant
  exact (by decide +kernel : SymReg.Loss.LossPrecision.round .float64 (literal64 (346 / 10000)) ≠ .fin (353 / 10000)) (Except.ok.inj hconstant)

-- Source: src/Options.jl:830-835
-- if !isnothing(loss_function) && recommend_loss_function_expression(expression_type)
--     @warn "The expression type you are using recommends using `loss_function_expression` instead of `loss_function`."
-- end
private def requestsLossWarning (recommend : Option Nat → Bool) (typeId loss : Option Nat) : Bool :=
  loss.isSome && recommend typeId

def lossRecommendation : Prop :=
  (∀ typeId, recommendExpressionLoss typeId = false) ∧
  ∀ typeId loss, requestsLossWarning recommendExpressionLoss typeId loss = false

theorem stockLossRecommendation_skips_warning (a : Args) (warn : Option Nat → Jl Unit) :
    validateInitial a (warn := warn) = validateInitial a := by
  simp [validateInitial, recommendExpressionLoss, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem lossRecommendation_holds : lossRecommendation := by
  exact ⟨fun _ => rfl, fun typeId loss => by
    simp [requestsLossWarning, recommendExpressionLoss]⟩

example (loss : Nat) (e : JlError) :
    validateInitial { lossFunction := some loss } (warn := fun _ => .error e) = .ok () := rfl

end SymReg.Options
