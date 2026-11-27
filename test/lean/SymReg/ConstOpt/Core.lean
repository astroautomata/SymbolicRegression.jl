import SymReg.HofMig.Core
import SymReg.Loss.Core
import DynExpr.ParamStruct.ScalarLaws

namespace SymReg.ConstOpt
open DynExpr
open SymReg.HofMig (Member less)
abbrev Effect (S A : Type) := S → Jl A × S

def Effect.bind {S A B : Type} (p : Effect S A) (f : A → Effect S B) : Effect S B :=
  fun s => match p s with
    | (.ok a, after) => f a after
    | (.error e, after) => (.error e, after)

instance {S : Type} : Monad (Effect S) where
  pure a := fun s => (.ok a, s)
  bind := Effect.bind

@[simp] theorem effect_bind {S A B : Type} (p : Effect S A) (f : A → Effect S B) (s : S) :
    (p >>= f) s = (match p s with
      | (.ok a, after) => f a after
      | (.error e, after) => (.error e, after)) := rfl

@[simp] theorem effect_pure {S A : Type} (a : A) (s : S) :
    (pure a : Effect S A) s = (.ok a, s) := rfl

/-- Scalar operations in `src/ConstantOptimization.jl:217-219`. The element type
of x0, including a real or complex scalar type, supplies these operations. -/
structure ScalarOps (C : Type) where
  isZero : C → Bool
  one : C
  half : C
  add : C → C → C
  mul : C → C → C

/-- The shared DE scalar instance, with its exact-finite arithmetic boundary. -/
def jfOps (precision : SymReg.Loss.LossPrecision) : ScalarOps JF :=
  ⟨fun x => decide (x = .fin 0), .fin 1, .fin (1 / 2),
    fun a b => precision.round (JF.add a b), fun a b => precision.round (JF.mul a b)⟩

/-- One coordinate of the restart initialization, `src/ConstantOptimization.jl:219`. -/
def perturb {C : Type} (ops : ScalarOps C) (x noise : C) : C :=
  let zero := ops.isZero x
  let scaled := ops.mul x (ops.add ops.one (ops.mul ops.half noise))
  if zero then noise else scaled

/-- `randn(rng, eltype(x0), size(x0)...)` has the original shape. The arbitrary
noise stream supplies one scalar for each original coordinate, `src/ConstantOptimization.jl:215-220`. -/
def restartPoint {C : Type} (ops : ScalarOps C) (x0 : List C) (noise : Nat → C) : List C :=
  x0.zipIdx.map (fun (x, i) => perturb ops x (noise i))

inductive Algorithm where
  | newton
  | configured (identity : Nat)
  deriving DecidableEq, Repr

inductive ObjectiveKind where
  | value
  | valueGradient
  deriving DecidableEq, Repr

/-- Algorithm selection in `src/ConstantOptimization.jl:151-175`. -/
def selectAlgorithm (nconst : Nat) (isComplex : Bool) (configured : Algorithm) : Algorithm :=
  if nconst = 1 && !isComplex then .newton else configured

/-- Objective dispatch in `_optimize_constants_inner`, `src/ConstantOptimization.jl:205-209`. -/
def objectiveKind (algorithm : Algorithm) (backend : Option Nat) : ObjectiveKind :=
  if algorithm = .newton || backend.isNone then .value else .valueGradient

/-- Successful wrapper effects, `src/ConstantOptimization.jl:210-237,262-304`.
Logs are proof instrumentation; optimizer-reported counters remain independent. -/
inductive Call (C : Type) where
  | write (root : Nat) (values : List C)
  | loss (root : Nat) (regularization : Bool)
  | gradient (root : Nat)
  | optimizer (start : List C) (algorithm : Algorithm) (kind : ObjectiveKind)
  deriving DecidableEq, Repr


structure PrepObject where
  identity : Nat
  typeId : Nat
  deriving DecidableEq

structure PrepStore where
  task : Nat := 0
  taskCaches : Nat → Option Nat := fun _ => none
  nextDictionary : Nat := 0
  dictionaries : Nat → Nat → Option PrepObject := fun _ _ => none

def failEffect {S A : Type} (e : JlError) : Effect S A :=
  fun s => (.error e, s)

def inspectEffect {S A : Type} (f : S → A) : Effect S A :=
  fun s => (.ok (f s), s)

def modifyEffect {S : Type} (f : S → S) : Effect S Unit :=
  fun s => (.ok (), f s)

@[simp] theorem inspectEffect_apply {S A : Type} (f : S → A) (s : S) :
    inspectEffect f s = (.ok (f s), s) := rfl

@[simp] theorem modifyEffect_apply {S : Type} (f : S → S) (s : S) :
    modifyEffect f s = (.ok (), f s) := rfl

@[simp] theorem failEffect_apply {S A : Type} (e : JlError) (s : S) :
    (failEffect e : Effect S A) s = (.error e, s) := rfl
/-- Expression storage and the mutable loss context are threaded through every
objective call. H can be DE's node heap or a structured-expression heap. -/
structure EvalState (C H : Type) where
  heap : H
  context : Option SymReg.Loss.Context := none
  log : List (Call C) := []
  preparations : PrepStore := {}
  members : Nat → Option Member := fun _ => none

/-- Opaque references returned by get_optimizable_parameters are reused unchanged
by the setter, `src/ConstantOptimization.jl:73-83,105-119`. -/
structure ParameterHooks (C H R : Type) where
  get : Nat → H → Jl (List C × R)
  set : Nat → List C → R → H → Jl H

/-- EvaluatorContext and Evaluator fields, `src/ConstantOptimization.jl:246-260`.
The partially applied loss service holds the dataset and options fixed. -/
structure Evaluator (C H R : Type) where
  tree : Nat
  refs : R
  set : Nat → List C → R → Effect (EvalState C H) Unit
  loss : Nat → Bool → Effect (EvalState C H) JF

-- Source: src/ConstantOptimization.jl:263
-- set_optimizable_parameters!(e.tree, x, e.refs)
def writeParameters {C H R : Type} (e : Evaluator C H R) (x : List C) :
    Effect (EvalState C H) Unit := do
  modifyEffect fun s => {s with log := s.log ++ [.write e.tree x]}
  e.set e.tree x e.refs

-- Source: src/ConstantOptimization.jl:251-255
-- function (c::EvaluatorContext)(tree; regularization=false)
--     return eval_loss(
--         tree, c.dataset, c.options; regularization, eval_context=c.eval_context
--     )
-- end
def callContext {C H R : Type} (e : Evaluator C H R) (regularization : Bool) :
    Effect (EvalState C H) JF := do
  modifyEffect fun s => {s with log := s.log ++ [.loss e.tree regularization]}
  e.loss e.tree regularization

-- Source: src/ConstantOptimization.jl:262-265
-- function (e::Evaluator)(x::AbstractVector; regularization=false)
--     set_optimizable_parameters!(e.tree, x, e.refs)
--     return e.ctx(e.tree; regularization)
-- end
def evaluate {C H R : Type} (e : Evaluator C H R) (regularization : Bool) (x : List C) :
    Effect (EvalState C H) JF := do
  writeParameters e x
  callContext e regularization

/-- Context construction in `_optimize_constants`, `src/ConstantOptimization.jl:181-187`. -/
def initialContext {S : Type} (backend : Option Nat)
    (create : Int → Effect S (Option SymReg.Loss.Context)) :
    Effect S (Option SymReg.Loss.Context) :=
  if backend.isNone then create 0 else pure none

structure PrepServices (S : Type) where
  read : S → PrepStore
  write : PrepStore → S → S
  hash : Nat × Nat × Nat → Effect S Nat
  treeType : Nat → S → Nat
  acceptsType : Nat → Nat → Nat → PrepObject → S → Bool
  prepare : Nat → Nat → Nat → Effect S PrepObject

-- Source: src/Utils.jl:208-216
-- function Base.getindex(cache::PerTaskCache{T}) where {T}
--     tls = Base.task_local_storage()
--     if haskey(tls, cache)
--         return tls[cache]::T
--     else
--         value = cache.constructor()::T
--         tls[cache] = value
--         return value
--     end
-- end
def taskDictionary {S : Type} (svc : PrepServices S) : Effect S Nat := do
  let store ← inspectEffect svc.read
  match store.taskCaches store.task with
  | some dictionary => pure dictionary
  | none =>
    let dictionary := store.nextDictionary
    let taskCaches := fun task =>
      if task = store.task then some dictionary else store.taskCaches task
    modifyEffect (svc.write {store with taskCaches := taskCaches, nextDictionary := dictionary + 1})
    pure dictionary

-- Source: src/Utils.jl:282-284
-- @unstable function stable_get!(f::F, dict, key) where {F}
--     return get!(f, dict, key)::(Base.promote_op(f))
-- end
def stablePrep {S : Type} (svc : PrepServices S) (ctx backend tree dictionary key : Nat) :
    Effect S PrepObject := do
  let entry ← inspectEffect fun s => (svc.read s).dictionaries dictionary key
  let object ← match entry with
    | some object => pure object
    | none => do
      let object ← svc.prepare ctx backend tree
      modifyEffect fun s =>
        let store := svc.read s
        let old := store.dictionaries
        let dictionaries := fun d k => if d = dictionary ∧ k = key then some object else old d k
        svc.write { store with dictionaries := dictionaries } s
      pure object
  let compatible ← inspectEffect (svc.acceptsType ctx backend tree object)
  if compatible then pure object
  else failEffect (.errorException "TypeError in stable_get!")

-- Source: src/ConstantOptimization.jl:280-287
-- @unstable function _cached_prep(ctx, backend, example_tree)
--     # We avoid hashing on the tree _value_ because it should not
--     # affect the prep. We want to cache as much as possible!
--     key = hash((ctx, backend, typeof(example_tree)))
--     stable_get!(CachedPrep[], key) do
--         prepare_gradient(ctx, backend, example_tree)
--     end
-- end
def cachedPrep {S : Type} (svc : PrepServices S) (ctx backend tree : Nat) :
    Effect S PrepObject := do
  let treeType ← inspectEffect (svc.treeType tree)
  let key ← svc.hash (ctx, backend, treeType)
  let dictionary ← taskDictionary svc
  stablePrep svc ctx backend tree dictionary key

-- Source: src/ConstantOptimization.jl:273-276
-- @unstable function GradEvaluator(e::Evaluator, backend)
--     prep = isnothing(backend) ? nothing : _cached_prep(e.ctx, backend, e.tree)
--     return GradEvaluator(e, prep, backend, nothing)
-- end
def prepareGrad {S : Type} (svc : PrepServices S) (ctx tree : Nat)
    (backend : Option Nat) : Effect S (Option PrepObject × Option Unit) := do
  match backend with
  | none => pure (none, none)
  | some ad =>
    let p ← cachedPrep svc ctx ad tree
    pure (some p, none)

/-- Gradient callback data, `src/ConstantOptimization.jl:267-271,289-304`.
AD's tree gradient and the preparation object remain arbitrary types. -/
structure GradEvaluator (C H R G P : Type) where
  evaluator : Evaluator C H R
  prep : Option P
  backend : Option Nat
  valueGradient : Option P → Option Nat → Nat → Effect (EvalState C H) (JF × Option G)
  extract : G → Nat → R → Effect (EvalState C H) Nat
  length : Nat → Effect (EvalState C H) Int
  broadcast : Nat → Nat → Effect (EvalState C H) Unit

/-- `AD` at `src/ConstantOptimization.jl:290` is the type parameter, a Julia
Type object. Testing that object with `isa AutoEnzyme` is false. Backend failures
therefore propagate from value_and_gradient rather than this friendly-error guard. -/
def autoEnzymeTypeGuard (_backendType : Nat) : Bool := false

@[simp] theorem autoEnzymeTypeGuard_false (backendType : Nat) :
    autoEnzymeTypeGuard backendType = false := rfl

-- Source: src/ConstantOptimization.jl:289-305
-- function (g::GradEvaluator{<:Any,AD})(_, G, x::AbstractVector) where {AD}
--     AD isa AutoEnzyme && error("Please load the `Enzyme.jl` package.")
--     set_optimizable_parameters!(g.e.tree, x, g.e.refs)
--     maybe_prep = isnothing(g.prep) ? () : (g.prep,)
--     (val, grad) = value_and_gradient(g.e.ctx, maybe_prep..., g.backend, g.e.tree)
--     if G !== nothing && grad !== nothing
--         extracted_gradient = extract_optimizable_gradient(grad, g.e.tree, g.e.refs)
--         length(extracted_gradient) == length(G) || throw(
--             DimensionMismatch(
--                 "extracted $(length(extracted_gradient)) parameter gradients for " *
--                 "an optimization vector of length $(length(G))",
--             ),
--         )
--         G .= extracted_gradient
--     end
--     return val
-- end
def gradient {C H R G P : Type} (g : GradEvaluator C H R G P) (_requested : Option JF)
    (buffer : Option Nat) (x : List C) : Effect (EvalState C H) JF := do
  if autoEnzymeTypeGuard (g.backend.getD 0) then
    failEffect (.errorException "Please load the `Enzyme.jl` package.")
  writeParameters g.evaluator x
  modifyEffect fun s => {s with log := s.log ++ [.gradient g.evaluator.tree]}
  let (value, grad) ← g.valueGradient g.prep g.backend g.evaluator.tree
  match buffer, grad with
  | some buffer, some grad =>
    let extracted ← g.extract grad g.evaluator.tree g.evaluator.refs
    let sourceLength ← g.length extracted
    let destinationLength ← g.length buffer
    if sourceLength ≠ destinationLength then
      let n ← g.length extracted
      let m ← g.length buffer
      failEffect (.dimensionMismatch
        s!"extracted {n} parameter gradients for an optimization vector of length {m}")
    g.broadcast buffer extracted
    pure value
  | _, _ => pure value

-- Source: src/ConstantOptimization.jl:178-193
-- function _optimize_constants(
--     dataset, member::P, x0, refs, options, algorithm, optimizer_options, rng
-- )::Tuple{P,Float64} where {T,L,N,P<:AbstractPopMember{T,L,N}}
--     tree = member.tree
--     eval_context = if options.autodiff_backend === nothing
--         create_eval_context(dataset, options, 0)
--     else
--         nothing
--     end
--     ctx = EvaluatorContext(dataset, options, eval_context)
--     f = Evaluator(tree, refs, ctx)
--     fg! = GradEvaluator(f, options.autodiff_backend)
--     return _optimize_constants_inner(
--         f, fg!, x0, refs, dataset, member, options, algorithm, optimizer_options, rng
--     )
-- end
def buildEvaluators {C H R G : Type}
    (set : Nat → List C → R → Effect (EvalState C H) Unit) (tree : Nat) (refs : R)
    (loss : Nat → Nat → Bool → Effect (EvalState C H) JF)
    (create : Int → Effect (EvalState C H) (Option SymReg.Loss.Context))
    (allocate : Option SymReg.Loss.Context → Effect (EvalState C H) Nat)
    (backend : Option Nat) (prep : PrepServices (EvalState C H))
    (valueGradient : Nat → Option PrepObject → Option Nat → Nat →
      Effect (EvalState C H) (JF × Option G))
    (extract : G → Nat → R → Effect (EvalState C H) Nat)
    (length : Nat → Effect (EvalState C H) Int)
    (broadcast : Nat → Nat → Effect (EvalState C H) Unit) :
    Effect (EvalState C H) (Evaluator C H R × GradEvaluator C H R G PrepObject) := do
  let context ← initialContext backend create
  let ctx ← allocate context
  let e : Evaluator C H R := ⟨tree, refs, set, loss ctx⟩
  let (prep, _) ← prepareGrad prep ctx tree backend
  pure (e, ⟨e, prep, backend, valueGradient ctx, extract, length, broadcast⟩)

/-- Optim sees either f or only_fg!(fg!), `src/ConstantOptimization.jl:205-209`. -/
abbrev FG (C H : Type) := Option JF → Option Nat → List C → Effect (EvalState C H) JF

inductive Objective (C H : Type) where
  | value (run : List C → Effect (EvalState C H) JF)
  | valueGradient (run : FG C H)

def Objective.kind {C H : Type} : Objective C H → ObjectiveKind
  | .value _ => .value
  | .valueGradient _ => .valueGradient

/-- Arbitrary Optim return fields read by this source, plus counters it does not
read, `src/ConstantOptimization.jl:211-237`. No optimizer correctness is assumed. -/
structure OptimResult (C : Type) where
  minimizer : List C
  minimum : JF
  fCalls : Nat
  gCalls : Nat := 0
  hCalls : Nat := 0
  iterations : Nat := 0
  deriving DecidableEq, Repr

abbrev Optimizer (C H : Type) := Objective C H → List C → Algorithm → Nat →
  Effect (EvalState C H) (OptimResult C)

structure Config where
  algorithm : Algorithm
  backend : Option Nat
  optimizerOptions : Nat
  restarts : Int
  rng : Nat

def round64 := SymReg.Loss.LossPrecision.round .float64

def floatInt (n : Int) : JF := round64 (.fin (Rat.ofInt n))

def weightedCalls (count : Nat) (fraction : JF) : JF :=
  round64 (floatInt (Int.ofNat count) * fraction)

-- Source: src/Dataset.jl:115,260
-- dataset_fraction(d::SubDataset) = d.n / get_full_dataset(d).n
-- dataset_fraction(d::BasicDataset) = 1.0
def datasetFraction {S : Type} (indices : Option Nat) (readLength : Nat → S → Jl Int × S)
    (fullCount : S → Int) (s : S) : Jl JF × S :=
  match indices with
  | none => (.ok (.fin 1), s)
  | some selected =>
    match readLength selected s with
    | (.error e, after) => (.error e, after)
    | (.ok n, after) => (.ok (round64 (floatInt n / floatInt (fullCount after))), after)

/-- The strict best-result update, `src/ConstantOptimization.jl:225-227`. -/
def chooseResult {C : Type} (best candidate : OptimResult C) : OptimResult C :=
  if less candidate.minimum best.minimum then candidate else best

/-- One call of Optim.optimize; the implementation is quantified over,
`src/ConstantOptimization.jl:211,221`. -/
def runOptimizer {C H : Type} (optimizer : Optimizer C H) (obj : Objective C H)
    (x : List C) (cfg : Config) : Effect (EvalState C H) (OptimResult C) := do
  modifyEffect fun s => {s with log := s.log ++ [.optimizer x cfg.algorithm obj.kind]}
  optimizer obj x cfg.algorithm cfg.optimizerOptions

structure RestartServices (C H : Type) where
  size : List C → Effect (EvalState C H) (List Nat)
  eltype : List C → Effect (EvalState C H) Nat
  randn : Nat → Nat → List Nat → Effect (EvalState C H) (List C)
  broadcast : Nat → List C → List C → Effect (EvalState C H) (List C)

-- Source: src/ConstantOptimization.jl:215-228
-- for _ in 1:(options.optimizer_nrestarts)
--     xt = let
--         ET = eltype(x0)
--         eps = randn(rng, ET, size(x0)...)
--         @. ifelse(iszero(x0), eps, x0 * (ET(1) + ET(1 // 2) * eps))
--     end
--     tmpresult = Optim.optimize(obj, xt, algorithm, optimizer_options)
--     num_evals += tmpresult.f_calls * eval_fraction
--     # TODO: Does this need to take into account h_calls?
--
--     if tmpresult.minimum < result.minimum
--         result = tmpresult
--     end
-- end
def runRestarts {C H : Type} (restart : RestartServices C H)
    (optimizer : Optimizer C H) (obj : Objective C H) (cfg : Config) (x0 : List C)
    (fraction : JF) : Nat → OptimResult C → JF → Effect (EvalState C H) (OptimResult C × JF)
  | 0, best, evals => pure (best, evals)
  | n + 1, best, evals => do
    let element ← restart.eltype x0
    let dims ← restart.size x0
    let eps ← restart.randn cfg.rng element dims
    let point ← restart.broadcast element x0 eps
    let candidate ← runOptimizer optimizer obj point cfg
    let count := round64 (evals + weightedCalls candidate.fCalls fraction)
    runRestarts restart optimizer obj cfg x0 fraction n (chooseResult best candidate) count

structure FinishServices (C H : Type) where
  tree : Nat → Effect (EvalState C H) Nat
  assignLoss : Nat → JF → Effect (EvalState C H) Unit
  cost : Nat → Effect (EvalState C H) JF
  assignCost : Nat → JF → Effect (EvalState C H) Unit
  birth : Effect (EvalState C H) Int
  assignBirth : Nat → Int → Effect (EvalState C H) Unit

def readAllocatedMember {C H : Type} (addr : Nat) : Effect (EvalState C H) Member :=
  fun s => match s.members addr with
    | some m => (.ok m, s)
    | none => (.error .undefRefError, s)

def updateAllocatedMember {C H : Type} (addr : Nat) (f : Member → Member) :
    Effect (EvalState C H) Unit := do
  let m ← readAllocatedMember addr
  modifyEffect fun s =>
    let members := fun a => if a = addr then some (f m) else s.members a
    { s with members := members }

-- Source: src/PopMember.jl:187-201
-- function compute_complexity(
--     member::AbstractPopMember, options::AbstractOptions; break_sharing=Val(false)
-- )::Int
--     complexity = getfield(member, :complexity)
--     complexity == -1 && return recompute_complexity!(member, options; break_sharing)
--     return complexity
-- end
-- function recompute_complexity!(
--     member::AbstractPopMember, options::AbstractOptions; break_sharing=Val(false)
-- )::Int
--     complexity = compute_complexity(member.tree, options; break_sharing)
--     setfield!(member, :complexity, complexity)
--     return complexity
-- end
def memberComplexity {C H : Type} (complexity : Nat → Effect (EvalState C H) Int)
    (addr : Nat) : Effect (EvalState C H) Int := do
  let m ← readAllocatedMember addr
  if m.complexity ≠ -1 then return m.complexity
  let size ← complexity m.tree
  updateAllocatedMember addr fun current => { current with complexity := size }
  pure size

-- Source: src/ConstantOptimization.jl:232-236; src/PopMember.jl:44-57
def stockFinishServices {C H : Type}
    (complexity : Nat → Effect (EvalState C H) Int)
    (countedCost : JF → Int → Effect (EvalState C H) JF)
    (birth : Effect (EvalState C H) Int) : FinishServices C H where
  tree addr := do
    let m ← readAllocatedMember addr
    pure m.tree
  assignLoss addr loss := updateAllocatedMember addr fun m => { m with loss := loss }
  cost addr := do
    let m ← readAllocatedMember addr
    let size ← memberComplexity complexity addr
    countedCost m.loss size
  assignCost addr cost := updateAllocatedMember addr fun m => { m with cost := cost }
  birth := birth
  assignBirth addr birthOrder := updateAllocatedMember addr fun m => { m with birth := birthOrder }

-- Source: src/ConstantOptimization.jl:230-243
-- if result.minimum < baseline
--     set_optimizable_parameters!(member.tree, result.minimizer, refs)
--     member.loss = f(result.minimizer; regularization=true)
--     member.cost = loss_to_cost(
--         member.loss, dataset.use_baseline, dataset.baseline_loss, member, options
--     )
--     member.birth = get_birth_order(; deterministic=options.deterministic)
--     num_evals += eval_fraction
-- else
--     # Reset to original state
--     set_optimizable_parameters!(member.tree, x0, refs)
-- end
-- return member, num_evals
def finish {C H R : Type} (e : Evaluator C H R) (svc : FinishServices C H)
    (x0 : List C) (baseline : JF) (best : OptimResult C) (evals fraction : JF)
    (member : Nat) : Effect (EvalState C H) JF := do
  if less best.minimum baseline then
    let current ← svc.tree member
    writeParameters {e with tree := current} best.minimizer
    let loss ← evaluate e true best.minimizer
    svc.assignLoss member loss
    let score ← svc.cost member
    svc.assignCost member score
    let birth ← svc.birth
    svc.assignBirth member birth
    pure (round64 (evals + fraction))
  else
    let current ← svc.tree member
    writeParameters {e with tree := current} x0
    pure evals

structure OptimServices (C H : Type) where
  onlyFG : FG C H → Effect (EvalState C H) (FG C H)
  optimizer : Optimizer C H
  indices : Option Nat
  length : Nat → Effect (EvalState C H) Int
  fullCount : EvalState C H → Int
  restart : RestartServices C H
  finish : FinishServices C H

-- Source: src/ConstantOptimization.jl:205-214
-- obj = if algorithm isa Optim.Newton || options.autodiff_backend === nothing
--     f
-- else
--     NLSolversBase.only_fg!(fg!)
-- end
-- baseline = f(x0)
-- result = Optim.optimize(obj, x0, algorithm, optimizer_options)
-- eval_fraction = dataset_fraction(dataset)
-- num_evals = result.f_calls * eval_fraction
def optimizeInner {C H R : Type} (svc : OptimServices C H) (e : Evaluator C H R)
    (fg : FG C H) (cfg : Config) (x0 : List C) (member : Nat) :
    Effect (EvalState C H) JF := do
  let obj ← if objectiveKind cfg.algorithm cfg.backend = .value then
      pure (.value (evaluate e false))
    else do
      let wrapper ← svc.onlyFG fg
      pure (.valueGradient wrapper)
  let baseline ← evaluate e false x0
  let first ← runOptimizer svc.optimizer obj x0 cfg
  let fraction ← datasetFraction svc.indices svc.length svc.fullCount
  let (best, n) ← runRestarts svc.restart svc.optimizer obj cfg x0 fraction cfg.restarts.toNat
    first (weightedCalls first.fCalls fraction)
  finish e svc.finish x0 baseline best n fraction member

-- Source: src/ConstantOptimization.jl:178-193
def optimizePrepared {C H R G : Type}
    (construct : Nat → R → Effect (EvalState C H) (Evaluator C H R × GradEvaluator C H R G PrepObject))
    (svc : OptimServices C H) (cfg : Config) (x0 : List C) (refs : R) (member : Nat) :
    Effect (EvalState C H) JF := do
  let current ← svc.finish.tree member
  let (f, fg) ← construct current refs
  optimizeInner svc f (gradient fg) cfg x0 member


structure Invocation where
  dataset : Nat
  member : Nat
  options : Nat
  algorithm : Algorithm
  optimizerOptions : Nat
  rng : Nat
  deriving DecidableEq

inductive DatasetElement where
  | noncomplex (typeId : Nat)
  | complex (typeId : Nat)
  deriving DecidableEq

inductive EntryCall (R : Type) where
  | eligibility (tree options : Nat)
  | getter (tree options : Nat)
  | length (vector : Nat)
  | specializedOptions (options : Nat)
  | configuredAlgorithm (options : Nat)
  | optimizerOptions (options : Nat)
  | prepared (args : Invocation) (vector : Nat) (refs : R)

structure EntryStore (H R : Type) where
  heap : H
  events : List (EntryCall R) := []

def traceEntry {H R : Type} (event : EntryCall R) : Effect (EntryStore H R) Unit :=
  fun s => (.ok (), { s with events := s.events ++ [event] })

structure EntryHooks (H R : Type) where
  memberTree : Nat → H → Nat
  eligible : Nat → Nat → Effect (EntryStore H R) Bool
  getter : Nat → Nat → Effect (EntryStore H R) (Nat × R)
  length : Nat → Effect (EntryStore H R) Int
  autodiffBackend : Nat → Option Nat
  specialize : Nat → Effect (EntryStore H R) Nat
  configuredAlgorithm : Nat → Effect (EntryStore H R) Algorithm
  optimizerOptions : Nat → Effect (EntryStore H R) Nat

abbrev Prepared (H R : Type) :=
  Invocation → Nat → R → Effect (EntryStore H R) JF

def readMemberTree {H R : Type} (hooks : EntryHooks H R) (member : Nat) : Effect (EntryStore H R) Nat :=
  fun s => (.ok (hooks.memberTree member s.heap), s)

def getSelection {H R : Type} (hooks : EntryHooks H R) (args : Invocation) :
    Effect (EntryStore H R) (Nat × R) := do
  let tree ← readMemberTree hooks args.member
  traceEntry (.getter tree args.options)
  hooks.getter tree args.options

def invokePrepared {H R : Type} (inner : Prepared H R) (args : Invocation)
    (x0 : Nat) (refs : R) : Effect (EntryStore H R) JF := do
  traceEntry (.prepared args x0 refs)
  inner args x0 refs

-- Source: src/ConstantOptimization.jl:194-201
-- function _optimize_constants(
--     dataset, member::P, options, algorithm, optimizer_options, rng
-- )::Tuple{P,Float64} where {T,L,N,P<:AbstractPopMember{T,L,N}}
--     x0, refs = get_optimizable_parameters(member.tree, options)
--     return _optimize_constants(
--         dataset, member, x0, refs, options, algorithm, optimizer_options, rng
--     )
-- end
def optimizeRaw {H R : Type} (hooks : EntryHooks H R) (inner : Prepared H R)
    (args : Invocation) : Effect (EntryStore H R) (Nat × JF) := do
  let (x0, refs) ← getSelection hooks args
  let count ← invokePrepared inner args x0 refs
  pure (args.member, count)

-- Source: src/ConstantOptimization.jl:141-174
-- @unstable function optimize_constants(...)
--     ...
--     opt_options =
--         options.autodiff_backend === nothing ? options : specialized_options(options)
--     ...
def optimizeCount {H R : Type} (hooks : EntryHooks H R) (element : DatasetElement)
    (inner : Prepared H R) (args : Invocation) : Effect (EntryStore H R) JF := do
  let tree ← readMemberTree hooks args.member
  traceEntry (.eligibility tree args.options)
  if !(← hooks.eligible tree args.options) then return .fin 0
  let (x0, refs) ← getSelection hooks args
  traceEntry (.length x0)
  let n ← hooks.length x0
  if n = 0 then return .fin 0
  let useNewton := n == 1 && (match element with | .noncomplex _ => true | .complex _ => false)
  let options ← match hooks.autodiffBackend args.options with
    | none => pure args.options
    | some _ => do
      traceEntry (.specializedOptions args.options)
      hooks.specialize args.options
  let algorithm ← if useNewton then pure .newton else do
    traceEntry (.configuredAlgorithm args.options)
    hooks.configuredAlgorithm args.options
  traceEntry (.optimizerOptions args.options)
  let optimizerOptions ← hooks.optimizerOptions args.options
  invokePrepared inner
    { args with algorithm := algorithm, options := options, optimizerOptions := optimizerOptions }
    x0 refs

def optimizeConstants {H R : Type} (hooks : EntryHooks H R) (element : DatasetElement)
    (inner : Prepared H R) (args : Invocation) : Effect (EntryStore H R) (Nat × JF) := do
  let count ← optimizeCount hooks element inner args
  pure (args.member, count)

def prepareOnStore {C H R G : Type}
    (construct : Invocation → Nat → R →
      Effect (EvalState C H) (Evaluator C H R × GradEvaluator C H R G PrepObject))
    (services : Invocation → OptimServices C H)
    (backend : Nat → Option Nat) (restarts : Nat → Int)
    (values : Nat → Effect (EvalState C H) (List C)) : Prepared (EvalState C H) R :=
  fun args vector refs s =>
    let run : Effect (EvalState C H) JF := do
      let x0 ← values vector
      optimizePrepared (construct args) (services args)
        ⟨args.algorithm, backend args.options, args.optimizerOptions, restarts args.options, args.rng⟩
        x0 refs args.member
    let (result, heap) := run s.heap
    (result, {s with heap := heap})

-- Source: src/ConstantOptimization.jl:141-244
def optimizeComplete {C H R G : Type} (hooks : EntryHooks (EvalState C H) R)
    (element : DatasetElement)
    (construct : Invocation → Nat → R →
      Effect (EvalState C H) (Evaluator C H R × GradEvaluator C H R G PrepObject))
    (services : Invocation → OptimServices C H) (backend : Nat → Option Nat)
    (restarts : Nat → Int) (values : Nat → Effect (EvalState C H) (List C))
    (args : Invocation) :=
  optimizeConstants hooks element (prepareOnStore construct services backend restarts values) args

/-- The Number subtype method and the expression-to-type delegation,
`src/ConstantOptimization.jl:22-27`. -/
def canOptimizeNumber (_typeIdentity : Nat) : Bool := true
def canOptimizeExpression {S : Type} (typeMethod : Nat → Nat → S → Jl Bool × S)
    (elementType options : Nat) (state : S) : Jl Bool × S :=
  typeMethod elementType options state


end SymReg.ConstOpt
