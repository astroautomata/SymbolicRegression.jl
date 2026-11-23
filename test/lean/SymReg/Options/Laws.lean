import SymReg.Options.Properties

namespace SymReg.Options
open DynExpr SymReg.Complexity SymReg.HeapLemmas

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

@[local simp] private theorem exceptThrow {ε α : Type} (e : ε) :
    (throw e : Except ε α) = .error e := rfl
attribute [local simp] pure_ok ok_bind

private theorem ofList_exact (xs : List JF) (h : xs.length = 15) :
    ∃ w, SymReg.MutateGen.MutationWeights.ofList xs = .ok w ∧
      SymReg.MutateGen.convertVector w = xs := by
  rcases xs with _ | ⟨a, xs⟩
  · simp at h
  rcases xs with _ | ⟨b, xs⟩
  · simp at h
  rcases xs with _ | ⟨c, xs⟩
  · simp at h
  rcases xs with _ | ⟨d, xs⟩
  · simp at h
  rcases xs with _ | ⟨e, xs⟩
  · simp at h
  rcases xs with _ | ⟨f, xs⟩
  · simp at h
  rcases xs with _ | ⟨g, xs⟩
  · simp at h
  rcases xs with _ | ⟨i, xs⟩
  · simp at h
  rcases xs with _ | ⟨j, xs⟩
  · simp at h
  rcases xs with _ | ⟨k, xs⟩
  · simp at h
  rcases xs with _ | ⟨l, xs⟩
  · simp at h
  rcases xs with _ | ⟨m, xs⟩
  · simp at h
  rcases xs with _ | ⟨n, xs⟩
  · simp at h
  rcases xs with _ | ⟨o, xs⟩
  · simp at h
  rcases xs with _ | ⟨p, xs⟩
  · simp at h
  have hz : xs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
  subst xs
  exact ⟨⟨a,b,c,d,e,f,g,i,j,k,l,m,n,o,p⟩, rfl, rfl⟩

def legacyWeightPadding : Prop := ∀ (xs : List JF) (cv : LegacyConversions) (e : JlError) (k : Keywords),
  let convert : Jl (List JF) := do
    if xs.length < 15 then
      let ys ← xs.mapM cv.promote
      let zeros ← (List.replicate (15 - xs.length) ()).mapM (fun _ => cv.zero)
      (ys ++ zeros).mapM cv.field
    else if xs.length = 15 then xs.mapM cv.field else throw (.methodError "no method matching MutationWeights")
  applyAlias k "mutationWeights" (.weightVector xs) (fun _ _ => .error e) cv = .error e ∧
  (legacyWeights xs cv).map (fun v => match v with | .weights w => SymReg.MutateGen.convertVector w | _ => []) = convert



/-- The initial explicit assertions reject precisely output_file, enum/legacy-op
conflicts, multiple objectives, and combined whole/per-item complexity options. -/
def initialValidationExact : Prop := ∀ a : Args,
  validateInitial a = .ok () ↔
    a.outputFile.isSome = false ∧
    (a.operators.isSome = true → a.binary.isSome = false ∧ a.unary.isSome = false ∧ a.enumConstructor.isSome = false) ∧
    ([a.elementwiseLoss, a.lossFunction, a.expressionLoss].filter Option.isSome).length <= 1 ∧
    ¬ (a.complexity.isSome = true ∧
      (a.opWeights.isSome = true ∨ a.variableWeight.isSome = true ∨ a.constantWeight.isSome = true))

theorem initialValidationExact_holds : initialValidationExact := by
  intro a
  unfold validateInitial
  simp only [recommendExpressionLoss, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Bool.false_eq_true, ite_false, ite_self]
  generalize a.outputFile.isSome = output at *
  generalize a.operators.isSome = provided at *
  generalize a.binary.isSome = binary at *
  generalize a.unary.isSome = unary at *
  generalize a.enumConstructor.isSome = enum at *
  generalize a.complexity.isSome = complexity at *
  generalize a.opWeights.isSome = operators at *
  generalize a.variableWeight.isSome = variables at *
  generalize a.constantWeight.isSome = constants at *
  cases output <;> try simp_all
  all_goals cases provided <;> try simp_all
  all_goals cases binary <;> try simp_all
  all_goals cases unary <;> try simp_all
  all_goals cases enum <;> try simp_all
  all_goals cases complexity <;> try simp_all
  all_goals cases operators <;> try simp_all
  all_goals cases variables <;> try simp_all
  all_goals cases constants <;> try simp_all
  all_goals first | omega | (split <;> simp_all <;> omega)

example : validateInitial ({} : Args) = .ok () := rfl

def constraintRoutingConflict : Prop := ∀ (a : Args) constraints ops actualOps (e : JlError),
  (a.binaryConstraints.isSome || a.unaryConstraints.isSome) = true →
  (routeConstraints { a with constraintSequence := none, constraints := some constraints } ops actualOps =
    .error (.assertionError "all(isnothing, (bin_constraints, una_constraints))")) ∧
  (routeConstraints { a with constraintSequence := some (.error e) } ops actualOps = .error e) ∧
  ((do let _ ← SymReg.SimpCons.buildNested opmap ops a.nested
       routeConstraints { a with constraintSequence := some (.error e) } ops actualOps) =
    match SymReg.SimpCons.buildNested opmap ops a.nested with
    | .error first => .error first
    | .ok _ => .error e)

def expressionSpecExact : Prop := ∀ (a : Args) spec defaultNode ops (access : SpecAccess),
  resolveExpression { a with expressionSpec := some spec } defaultNode ops access =
    if a.expressionType.isSome then .error (.assertionError "expression_type === nothing")
    else if a.expressionOptions.isSome then .error (.assertionError "expression_options === nothing")
    else if a.nodeType.isSome then .error (.assertionError "node_type === nothing") else
    match access.getType spec,access.getOptions spec,access.getNode spec with
    | .error e,_,_ | .ok _,.error e,_ | .ok _,.ok _,.error e => .error e
    | .ok ty,.ok opts,.ok (node,degree) => .ok (⟨ty,opts,node,degree⟩,degree.getD (if a.operators.isSome then ops.length else 2))

def mutationDefaultsConflict : Prop := ∀ (a : Args), mutationStage a =
  match resolveWeights a.version a.weights with
  | .error e => .error e
  | .ok w => if a.weights.isSome && a.defaultMutations.isSome then
      .error (.argumentError "`mutation_weights` and `default_mutations` cannot be used together.") else .ok w

theorem mutationDefaultsConflict_holds : mutationDefaultsConflict := by
  intro a
  cases hw : resolveWeights a.version a.weights <;>
    cases h₁ : a.weights.isSome <;> cases h₂ : a.defaultMutations.isSome <;>
    simp [mutationStage,validateMutationDefaults,hw,h₁,h₂]

example (id : Nat) (w : SymReg.MutateGen.MutationWeights) : mutationStage
    { weights := some (.existing id w), defaultMutations := some [] } =
    .error (.argumentError "`mutation_weights` and `default_mutations` cannot be used together.") := rfl

example : mutationStage { weights := some (.named [("unknown", .numeric (.fin 1))]), defaultMutations := some [] } =
    .error (SymReg.MutateGen.unknownWeight "unknown") := rfl

/-- A supplied complexity function or mapping is preserved, independently of
operator lookup order and all per-item options (which the earlier assertion checks). -/
def suppliedComplexityPreserved : Prop := ∀ (a : Args) value ops,
  resolveComplexity { a with complexity := some value } ops = .ok value

theorem suppliedComplexityPreserved_holds : suppliedComplexityPreserved := by
  intro a value ops
  simp [resolveComplexity]

def weightedResolution : Prop :=
  (∀ (same : Nat → Nat → Bool) explicit plugins base,
    mergeWeighted same explicit plugins base = explicit ++
      plugins.filter (fun x => !explicit.any (fun p => same p.1 x.1)) ++
      (base.filter (fun x => !plugins.any (fun p => same p.1 x.1))).filter (fun x => !explicit.any (fun p => same p.1 x.1))) ∧
  ∀ (key : Nat) (x y : JF) (e : JlError),
    resolveWeighted (m := Jl) (· == ·) (fun v => if v = y then .error e else .ok (SymReg.Loss.LossPrecision.round .float64 v))
      [(key,x)] none (.ok []) [0] (fun _ => .ok [(key,y)]) = .error e

def weightedDefaultsDisabled : Prop := ∀ (same : Nat → Nat → Bool) (xs : List (Nat × JF))
    (convert : JF → Jl JF) (base : Jl (List (Nat × JF))) plugins hook,
  resolveWeighted same convert xs (some []) base plugins hook = convertEntries convert xs

theorem resolveWeighted_emptyDefaults {m : Type → Type} [Monad m] [LawfulMonad m] {I : Type}
    (same : I → I → Bool) (convert : JF → m JF) (xs : List (I × JF))
    (base : m (List (I × JF))) (plugins : List Nat) (hook : Nat → m (List (I × JF))) :
    resolveWeighted same convert xs (some []) base plugins hook = convertEntries convert xs := by
  simp [resolveWeighted, convertEntries, mergeWeighted]

theorem weightedDefaultsDisabled_holds : weightedDefaultsDisabled := by
  intro same xs convert base plugins hook
  exact resolveWeighted_emptyDefaults same convert xs base plugins hook

theorem weightedResolution_holds : weightedResolution := by
  constructor
  · intro same explicit plugins base
    simp [mergeWeighted, List.filter_append, List.append_assoc]
  · intro key x y e
    by_cases h : x = y <;>
      simp [resolveWeighted, convertEntries, h, Bind.bind, Except.bind, Pure.pure, Except.pure]

def constructorFields : Prop := ∀ (s : Services) (a : Args) result,
  construct s a = .ok result →
  result.maxdepth = a.maxdepth.getD result.defaults.maxsize ∧
  result.nops = result.operators.ops.map List.length ∧
  result.dimensionPenalty = a.dimensionPenalty.map (SymReg.Loss.LossPrecision.round .float64) ∧
  result.dimensionless = a.dimensionless ∧
  result.turbo.value = a.turbo ∧
  result.bumper.value = a.bumper ∧
  result.migration = a.migration ∧
  result.hofMigration = a.hofMigration ∧
  result.optimizeConstants = a.optimizeConstants ∧
  result.useFrequency = a.useFrequency ∧
  result.tournamentFrequency = a.tournamentFrequency ∧
  result.verbosity = a.verbosity ∧
  result.saveToFile = a.saveToFile ∧
  result.seed = a.seed ∧
  result.progress = a.progress ∧
  result.terminalWidth = a.terminalWidth ∧
  result.optimizerProbability = SymReg.Loss.LossPrecision.round .float64 a.optimizerProbability ∧
  result.optimizerRestarts = a.optimizerRestarts ∧
  result.tracingFile = a.tracingFile ∧
  result.returnState.value = result.normalizedState ∧
  result.timeout = a.timeout.map (SymReg.Loss.LossPrecision.round .float64) ∧
  result.maxEvals = a.maxEvals ∧
  result.skipFailures = a.skipFailures ∧
  result.useTracing.value = a.useTracing ∧
  result.deterministic = a.deterministic ∧
  result.printPrecision.value = a.printPrecision ∧
  result.inputStream = a.inputStream ∧
  result.lossScale = a.lossScale ∧
  result.lossFunction = a.lossFunction ∧
  result.expressionLoss = a.expressionLoss ∧
  result.defineHelpers = a.defineHelpers ∧
  result.shouldSimplify = resolveSimplify a

theorem constructorFields_holds : constructorFields := by
  intro s a result h
  unfold construct at h
  cases hp : constructParts s a with
  | error e => simp [hp, Except.map] at h
  | ok parts =>
    simp only [hp, Except.map] at h
    cases h
    repeat' constructor
    all_goals rfl

example : ∃ result, construct ({} : Services) ({} : Args) = .ok result := ⟨_,rfl⟩

/-- Directory overrides survive, ordinary omission remains nothing, and only the
testing environment calls the supplied temporary-directory service. -/
def directoryResolution : Prop := ∀ directory testing tmp,
  resolveDirectory (some directory) testing tmp = .ok (some directory) ∧
  resolveDirectory none false tmp = .ok none ∧
  resolveDirectory none true tmp = tmp.map some

theorem directoryResolution_holds : directoryResolution := by
  intro directory testing tmp
  cases tmp <;> simp [resolveDirectory, Except.map]

-- Source: src/SearchUtils.jl:914-925
-- output_directory = joinpath(something(options.output_directory, "outputs"), ropt.run_id)
-- Model ordinary relative run IDs as one path component and leave filesystem effects out.
def runDirectoryComponents (base : Option String) (runId : String) : String × String :=
  (base.getD "outputs", runId)

def documentedDirectoryDefault : Prop := ∀ (tmp : Jl String) base runId,
  (resolveDirectory none false tmp).map (fun directory => runDirectoryComponents directory runId) =
    .ok ("outputs", runId) ∧
  (resolveDirectory (some base) false tmp).map (fun directory => runDirectoryComponents directory runId) =
    .ok (base, runId)

theorem documentedDirectoryDefault_holds : documentedDirectoryDefault := by
  intro tmp base runId
  rw [(directoryResolution_holds base false tmp).2.1, (directoryResolution_holds base false tmp).1]
  exact ⟨rfl, rfl⟩

/-- Free observations distinguish repeated reads, early returns and the queried signature. -/
inductive BatchRead where
  | mode | count | size | query (dataset : Nat) (argument : BatchArgument)
  deriving DecidableEq

private abbrev TraceM := StateM (List BatchRead)
private def observe {α : Type} (event : BatchRead) (value : α) : TraceM α := do
  modify (· ++ [event])
  return value

private abbrev BatchEffects := ExceptT JlError (StateM (List BatchRead))
private def onRead {α : Type} (event : BatchRead) (out : Jl α) : BatchEffects α := do
  modify (· ++ [event])
  match out with | .ok x => pure x | .error e => throw e

private def readTwice {α : Type} (event : BatchRead) (first next : Jl α) : BatchEffects α := do
  let log ← get
  onRead event (if log.contains event then next else first)

def selectionEffects : Prop := ∀ (a b : Jl BatchMode) (n : Jl Int) ty (has : Jl Bool),
  ((readBatching (readTwice .mode a b) (onRead .count n) ty (fun t arg => onRead (.query t arg) has)).run).run [] =
    match a with
    | .error e => (.error e,[.mode])
    | .ok .enabled => (.ok true,[.mode])
    | .ok _ => match b with
      | .error e => (.error e,[.mode,.mode])
      | .ok .auto => match n with
        | .error e => (.error e,[.mode,.mode,.count])
        | .ok k => if 1000 < k then (has,[.mode,.mode,.count,.query ty .machineInt]) else (.ok false,[.mode,.mode,.count])
      | .ok _ => (.ok false,[.mode,.mode])

private theorem selectionEffects_holds : selectionEffects := by
  intro a b n ty has
  cases a with
  | error => rfl
  | ok a => cases a <;> cases b with
    | error => rfl
    | ok b => cases b <;> cases n with
      | error => rfl
      | ok k =>
        first | rfl | (by_cases h : 1000 < k <;> cases has <;> simp [readBatching,readTwice,onRead,h,show k ≤ 1000 ↔ ¬1000 < k by omega] <;> rfl)

def batchingSelection : Prop := selectionEffects

theorem batchingSelection_holds : batchingSelection := selectionEffects_holds

/-- Automatic batch sizes obey every documented threshold; explicit sizes are
capped by the dataset size, including an empty dataset. -/
def batchSizeThresholds : Prop := ∀ n size,
  getBatchSize (some size) n = min size n ∧
  (n <= 1000 → getBatchSize none n = n) ∧
  (1000 < n → n < 5000 → getBatchSize none n = 128) ∧
  (5000 <= n → n < 50000 → getBatchSize none n = 256) ∧
  (50000 <= n → getBatchSize none n = 512)

theorem batchSizeThresholds_holds : batchSizeThresholds := by
  intro n size
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro h; simp [getBatchSize, automaticSize, h]
  · intro h h2; simp [getBatchSize, automaticSize, show ¬n <= 1000 by omega, h2]
  · intro h h2; simp [getBatchSize, automaticSize, show ¬n <= 1000 by omega, show ¬n < 5000 by omega, h2]
  · intro h; simp [getBatchSize, automaticSize, show ¬n <= 1000 by omega, show ¬n < 5000 by omega, show ¬n < 50000 by omega]

example : (1000 : Int) < 1001 ∧ (1001 : Int) < 5000 := by decide
example : (5000 : Int) <= 5000 ∧ (5000 : Int) < 50000 := by decide
example : (50000 : Int) <= 50000 := by decide

/-- Positive requested batch sizes on nonnegative dataset sizes always stay
between zero and n; automatic batching uses a strict subset exactly above 1000. -/
def batchSizeBounds : Prop := ∀ n size, 0 <= n → 1 <= size →
  0 <= getBatchSize (some size) n ∧ getBatchSize (some size) n <= n ∧
  0 <= getBatchSize none n ∧ getBatchSize none n <= n ∧
  (getBatchSize none n < n ↔ 1000 < n)

theorem batchSizeBounds_holds : batchSizeBounds := by
  intro n size hn hs
  simp only [getBatchSize, automaticSize, Int.min_def]
  repeat' first | omega | split

example : 0 <= (0 : Int) ∧ 1 <= (1 : Int) := by decide

private def requiredEffects : Prop := ∀ (n₁ n₂ : Jl Int) (s₁ s₂ : Jl (Option Int)),
  let missing := JlError.methodError "min(nothing, n)"
  ((readBatchingRequired (pure true) (readTwice .count n₁ n₂) (readTwice .size s₁ s₂) (throw missing)).run).run [] =
    match n₁,s₁ with
    | .error e,_ => (.error e,[.count])
    | .ok _,.error e => (.error e,[.count,.size])
    | .ok n,.ok none => (n₂.map (fun last => decide (automaticSize n < last)),[.count,.size,.count])
    | .ok n,.ok (some _) => match s₂ with
      | .error e => (.error e,[.count,.size,.size])
      | .ok none => (.error missing,[.count,.size,.size])
      | .ok (some k) => (n₂.map (fun last => decide (min k n < last)),[.count,.size,.size,.count])

private theorem requiredEffects_holds : requiredEffects := by
  intro n₁ n₂ s₁ s₂
  cases n₁ <;> cases n₂ <;> cases s₁ with
  | error => rfl
  | ok first => cases first <;> cases s₂ with
    | error => rfl
    | ok second => cases second <;> rfl

def batchingRequiredExact : Prop := requiredEffects ∧
  (∀ n has, batchingRequired .auto none n has = (decide (1000 < n) && has)) ∧
  (∀ size n has, batchingRequired .disabled size n has = false) ∧
  (∀ n k has, batchingRequired .enabled (some k) n has = decide (k < n)) ∧
  (∀ n has, batchingRequired .enabled none n has = decide (1000 < n)) ∧
  ∀ (size : Option Int) (n : Int) (use : Bool),
    ((readBatchingRequired (pure use) (observe .count n) (observe .size size) (pure 0)).run []).2 =
      if !use then [] else if size.isSome then [.count,.size,.size,.count] else [.count,.size,.count]

theorem batchingRequiredExact_holds : batchingRequiredExact := by
  refine ⟨requiredEffects_holds, ?_, ?_, ?_, ?_, ?_⟩
  · intro n has
    change (if !(decide (1000 < n) && has) then false else decide (automaticSize n < n)) =
      (decide (1000 < n) && has)
    by_cases h : 1000 < n
    · have hb : 0 ≤ n := by omega
      have hlt : automaticSize n < n := (batchSizeBounds_holds n 1 hb (by decide)).2.2.2.2.mpr h
      rw [decide_eq_true h, decide_eq_true hlt]
      cases has <;> rfl
    · rw [decide_eq_false h]
      rfl
  · intros; rfl
  · intro n k has
    change decide (min k n < n) = decide (k < n)
    by_cases h : k < n
    · rw [Int.min_eq_left (by omega)]
    · rw [Int.min_eq_right (by omega)]
      simp [h]
  · intro n has
    change decide (automaticSize n < n) = decide (1000 < n)
    by_cases h : 1000 < n
    · have hb : 0 ≤ n := by omega
      have hlt : automaticSize n < n := (batchSizeBounds_holds n 1 hb (by decide)).2.2.2.2.mpr h
      rw [decide_eq_true h, decide_eq_true hlt]
    · rw [decide_eq_false h]
      simp [automaticSize, show n ≤ 1000 by omega]
  · intro size n use
    cases use <;> cases size <;> rfl

/-- Display hides exactly the algorithm/options/plugin payloads and the legacy
backsolve name; all ordinary field values use their actual rendering. -/
def printFieldPolicy : Prop := ∀ (render : String → String) field,
  (["optimizer_algorithm", "optimizer_options", "plugins", "backsolve"].contains field = true →
    renderField render field = field ++ "=...") ∧
  (["optimizer_algorithm", "optimizer_options", "plugins", "backsolve"].contains field = false →
    renderField render field = field ++ "=" ++ render field) ∧
  showOptions render = printOptions render

theorem printFieldPolicy_holds : printFieldPolicy := by
  intro render field
  refine ⟨?_, ?_, rfl⟩
  · intro h; simp_all [renderField, String.append_assoc]
  · intro h; simp_all [renderField]

example : ["optimizer_algorithm", "optimizer_options", "plugins", "backsolve"].contains "maxsize" = false := by decide

/-- Specializing an Options value changes only its operator type, preserves all
field contents/identities, and is idempotent; AbstractOptions fallback is identity. -/
def specializationPreservesFields : Prop := ∀ (o : TypedOptions),
  (o.isOptions = true → (specializedOptions o).operatorType = some o.operators.runtimeType) ∧
  (specializedOptions o).otherTypeParameters = o.otherTypeParameters ∧
  (specializedOptions o).operators = o.operators ∧ (specializedOptions o).fields = o.fields ∧
  specializedOptions (specializedOptions o) = specializedOptions o ∧
  (o.isOptions = false → specializedOptions o = o)

theorem specializationPreservesFields_holds : specializationPreservesFields := by
  intro o
  cases h : o.isOptions <;> simp [specializedOptions,h]

example : (specializedOptions ⟨true,none,⟨[[110]],true,0⟩,fun _ => .absent,[]⟩).operatorType = some (.standard [[110]]) := rfl

def warmStartExact : Prop := ∀ (m : Type → Type) [Monad m] (old new : String → m Value)
    (ne : Value → Value → m (Option Bool)) (badCondition : m Bool),
  let guardBool := fun (b : Option Bool) => b.elim badCondition pure
  let fields : List String := ["operators", "op_constraints", "nested_constraints", "complexity_mapping",
     "dimensionless_constants_only", "maxsize", "maxdepth", "populations", "population_size",
     "node_type", "expression_type", "expression_options"]
  checkWarmWith true old new ne guardBool =
    (fun changed => if changed = [] then Except.ok () else .error (WarmStartError.mk changed)) <$>
      (fields.filterM fun field => do
        let a ← old field
        let b ← new field
        let comparison ← ne a b
        match comparison with | some value => pure value | none => badCondition)

theorem warmStartExact_holds : warmStartExact := by
  intro m inst old new ne bad
  have hg : (fun (x : Option Bool) => x.elim bad pure) =
      (fun x => match x with | some v => pure v | none => bad) := by funext x; cases x <;> rfl
  have ho : warmOutcome = (fun xs => if xs = [] then Except.ok () else .error (WarmStartError.mk xs)) := by
    funext xs; cases xs <;> rfl
  dsimp only
  rw [checkWarmWith,ho,hg]
  rfl

def warmStartFallbackAndDisplay : Prop := ∀ (old new : String → StateM Nat Value)
    (ne : Value → Value → StateM Nat (Option Bool)) (guardBool : Option Bool → StateM Nat Bool) log changed,
  (warmChanges false old new ne guardBool).run log = ([],log) ∧
  showWarmStartError ⟨changed⟩ = "Warm start incompatible due to changed field(s): " ++
    String.intercalate ", " changed ++ ". Use `fit!(mach, force=true)` to restart training."

theorem warmStartFallbackAndDisplay_holds : warmStartFallbackAndDisplay := by
  intro old new ne guardBool log changed
  exact ⟨rfl,rfl⟩

end SymReg.Options
