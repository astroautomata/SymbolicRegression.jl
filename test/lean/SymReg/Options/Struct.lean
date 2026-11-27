import SymReg.Options.Constructor

namespace SymReg.Options
open DynExpr

-- Source: src/OptionsStruct.jl:268-286
-- return options.batching === true || (options.batching === :auto &&
--     dataset.n > 1000 && hasmethod(batch, Tuple{typeof(dataset),Int}))
inductive BatchArgument | machineInt deriving DecidableEq

def readBatching {m : Type → Type} [Monad m] (mode : m BatchMode) (n : m Int)
    (datasetType : Nat) (hasMethod : Nat → BatchArgument → m Bool) : m Bool := do
  if (← mode) == .enabled then return true
  if (← mode) != .auto then return false
  if (← n) <= 1000 then return false
  hasMethod datasetType .machineInt

def useBatching (mode : BatchMode) (n : Int) (hasBatch : Bool) : Bool :=
  mode == .enabled || (mode == .auto && n > 1000 && hasBatch)

-- Source: src/OptionsStruct.jl:274-282
-- bs = options.batch_size
-- bs !== nothing && return min(bs, n)
def automaticSize (n : Int) : Int :=
  if n <= 1000 then n else if n < 5000 then 128 else if n < 50000 then 256 else 512

def readBatchSize {m : Type → Type} [Monad m] (size : m (Option Int)) (n : Int)
    (_minNothing : m Int) : m Int := do
  match ← size with
  | some k => return min k n
  | none => return automaticSize n

def getBatchSize (size : Option Int) (n : Int) : Int :=
  match size with
  | some k => min k n
  | none => automaticSize n

-- Source: src/OptionsStruct.jl:284-286
-- return use_batching(options, dataset) && get_batch_size(options, dataset.n) < dataset.n
def readBatchingRequired {m : Type → Type} [Monad m] (use : m Bool) (n : m Int)
    (size : m (Option Int)) (minNothing : m Int) : m Bool := do
  if !(← use) then return false
  let first ← n
  let chosen ← readBatchSize size first minNothing
  let last ← n
  return decide (chosen < last)

def batchingRequired (mode : BatchMode) (size : Option Int) (n : Int) (hasBatch : Bool) : Bool :=
  readBatchingRequired (m := Id) (useBatching mode n hasBatch) n size 0

/-- The actual fieldnames used by `print`, `src/OptionsStruct.jl:198-265,288-309`.
No nuna, nbin or backsolve field is present in this version. -/
def optionFieldNames : List String :=
  ["operators", "op_constraints", "nested_constraints", "complexity_mapping",
   "tournament_selection_n", "tournament_selection_p", "parsimony",
   "dimensional_constraint_penalty", "dimensionless_constants_only", "maxsize", "maxdepth",
   "turbo", "bumper", "migration", "hof_migration", "should_simplify", "should_optimize_constants",
   "output_directory", "populations", "perturbation_factor", "batching", "batch_size",
   "mutations", "crossovers", "crossover_probability", "warmup_maxsize_by", "use_frequency",
   "use_frequency_in_tournament", "adaptive_parsimony_scaling", "population_size",
   "ncycles_per_iteration", "fraction_replaced", "fraction_replaced_hof", "fraction_replaced_guesses",
   "topn", "verbosity", "v_print_precision", "save_to_file", "probability_negate_constant", "nops",
   "seed", "elementwise_loss", "loss_function", "loss_function_expression", "loss_scale",
   "node_type", "expression_type", "expression_options", "progress", "terminal_width",
   "optimizer_algorithm", "optimizer_probability", "optimizer_nrestarts", "optimizer_options",
   "autodiff_backend", "tracing_file", "prob_pick_first", "early_stop_condition", "return_state",
   "timeout_in_seconds", "max_evals", "input_stream", "skip_mutation_failures", "deterministic",
   "define_helper_functions", "use_tracing", "popmember_type", "plugins"]

/-- One auto-rendered field, `src/OptionsStruct.jl:297-301`. `render` is the
arbitrary Julia interpolation of the supplied field value. -/
def renderField (render : String → String) (field : String) : String :=
  field ++ "=" ++ if ["optimizer_algorithm", "optimizer_options", "plugins", "backsolve"].contains field
    then "..." else render field

/-- `Base.print(::Options)`, `src/OptionsStruct.jl:288-309`. -/
def printOptions (render : String → String) : String :=
  "Options(operators=" ++ render "operators" ++ ", " ++
    String.intercalate ", " ((optionFieldNames.filter
      (fun f => !["operators", "nuna", "nbin"].contains f)).map (renderField render)) ++ ")"

/-- `Base.show` for text/plain delegates to print, `src/OptionsStruct.jl:310-312`. -/
def showOptions (render : String → String) : String := printOptions render

/-- OperatorEnum type parameters are erased from ordinary Options; a generic
operator enum's concrete type is retained, `src/OptionsStruct.jl:118-124`. -/
def operatorSpecialization (standard : Bool) (concreteType : Nat) (_expressionType : Nat) : Nat :=
  if standard then 0 else concreteType

/-- `specialized_options`/`_specialized_options`, `src/OptionsStruct.jl:314-327`.
Only the operator type parameter changes. Fields and object identities are retained. -/
structure TypedOptions where
  isOptions : Bool
  operatorType : Option EnumType
  operators : Operators
  fields : Keywords
  otherTypeParameters : List Nat := []

def specializedOptions (o : TypedOptions) : TypedOptions :=
  if o.isOptions then { o with operatorType := some o.operators.runtimeType } else o

/-- Fields whose changes prevent warm starts, `src/OptionsStruct.jl:341-355`. -/
def incompatibleFields : List String :=
  ["operators", "op_constraints", "nested_constraints", "complexity_mapping",
   "dimensionless_constants_only", "maxsize", "maxdepth", "populations", "population_size",
   "node_type", "expression_type", "expression_options"]

/-- `WarmStartIncompatibleError`, `src/OptionsStruct.jl:329-331`. -/
structure WarmStartError where
  fields : List String
  deriving DecidableEq, Repr

/-- `Base.showerror`, `src/OptionsStruct.jl:333-337`. -/
def showWarmStartError (e : WarmStartError) : String :=
  "Warm start incompatible due to changed field(s): " ++ String.intercalate ", " e.fields ++
    ". Use `fit!(mach, force=true)` to restart training."

-- Source: src/OptionsStruct.jl:339-362
-- changed = [f for f in incompatible_fields if getproperty(old_options, f) != getproperty(new_options, f)]
-- isempty(changed) || throw(WarmStartIncompatibleError(changed))
-- A missing or otherwise non-Boolean comparison fails at the comprehension guard.
def warmChanges {m : Type → Type} [Monad m] {α β : Type}
    (both : Bool) (old new : String → m α) (ne : α → α → m β) (guardBool : β → m Bool) : m (List String) := do
  if !both then return []
  incompatibleFields.filterM fun field => do
    let a ← old field
    let b ← new field
    guardBool (← ne a b)

def warmOutcome (fields : List String) : Except WarmStartError Unit :=
  if fields.isEmpty then .ok () else .error ⟨fields⟩

def checkWarmWith {m : Type → Type} [Monad m] {α β : Type} (both : Bool)
    (old new : String → m α) (ne : α → α → m β) (guardBool : β → m Bool) : m (Except WarmStartError Unit) :=
  warmOutcome <$> warmChanges both old new ne guardBool

def checkWarmStart (bothOptions : Bool) (equal : String → Bool) : Except WarmStartError Unit :=
  checkWarmWith (m := Id) bothOptions id id (fun field _ => !equal field) id

-- no-behaviour: MyOptions (src/OptionsStruct.jl:147-172) appears only in a docstring example.

end SymReg.Options
