import SymReg.MutateGen.Condition

/-!
The mutation engine of `src/Mutate.jl`: the `mutate!` methods (except the simplify
handler, `src/Mutate.jl:895-928`, which is an abstract handler here), `next_generation`,
`_next_generation`, `_fire_on_mutation_end!` and `_mutation_weights_scratch`.

Abstraction level:
* Expressions are values of an arbitrary type `E`. `copy_into!(node_storage, member.tree)`
  yields a fresh copy, so tree mutations of the copy are modelled as functions `E → E`
  (consuming the task-local RNG); the parent's tree is never reached through them.
* Population members are objects in a store (`St.objs`, object id → contents), because
  `next_generation` returns a member object and `optimize_constants` mutates its argument
  in place (`src/ConstantOptimization.jl:230-243`). `create_child` (`src/PopMember.jl:210-230`)
  allocates a new object with fresh `ref` and `birth` (both drawn from the allocation
  counter) and `parent = parent_ref`.
* Tree-level mutation functions (`src/MutationFunctions.jl`), `check_constraints`,
  `eval_cost`, `compute_complexity` and plugin hooks are arbitrary functions. Plugin hooks
  are pure functions of their inputs (their state is captured); `on_mutation_end!` calls
  are recorded in a call log, together with `mutate!`, `check_constraints` and `eval_cost`
  calls, so properties can count them. Tracing (`tmp_trace`) only records strings and is
  omitted.
* The engine rounds each `num_evals` addition to Float64.
-/

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw)

/-- Stock `PopMember` fields (`src/PopMember.jl:30-41`). -/
structure Member (E : Type) where
  tree : E
  cost : JF
  loss : JF
  birth : Nat
  ref : Nat
  parent : Nat
  complexity : Int
  deriving DecidableEq, Repr

/-- `MutationEvent(accepted, before_cost, after_cost, before_loss, after_loss, mutation_idx)`
(`src/Mutate.jl:428-435,472,500,531-533,558`). -/
structure Event where
  accepted : Bool
  beforeCost : JF
  afterCost : Option JF
  beforeLoss : JF
  afterLoss : Option JF
  idx : Nat
  deriving DecidableEq, Repr

/-- Recorded calls. `mutate a ev imm ok` is a `mutate!` call with `attempt = a` whose result
reported `num_evals = ev`, `return_immediately = imm` and `success = ok`; `choose k idx`
records the sampled `mutation_choice` and `mutation_idx` (`src/Mutate.jl:328-329`). -/
inductive Call (E : Type) where
  | mutate (attempt : Nat) (evals : JF) (imm ok : Bool)
  | constraints (tree : E) (ok : Bool)
  | eval (tree : E)
  | onEnd (plugin : Nat) (k : Kind) (ev : Event)
  | choose (k : Kind) (idx : Nat)

/-- Mutable world: member objects, the allocation counter (also the source of fresh `ref`
and `birth` values), the task-local RNG, the per-task weight scratch vector
`MUTATION_WEIGHTS_SCRATCH[]` (`none` is an `#undef` slot) and the call log. -/
structure St (E : Type) where
  objs : Nat → Option (Member E)
  next : Nat
  rng : RNG
  scratch : List (Option (Kind × JF))
  log : List (Call E)

/-- Every allocated object id is below the allocation counter. -/
def St.Inv {E : Type} (s : St E) : Prop := ∀ o m, s.objs o = some m → o < s.next

/-- Write `m` at object id `o`. -/
def St.write {E : Type} (s : St E) (o : Nat) (m : Member E) : St E :=
  { s with objs := fun o' => if o' = o then some m else s.objs o' }

/-- `create_child(parent, tree, cost, loss, options; parent_ref)` (`src/PopMember.jl:210-230`). -/
def createChild {E : Type} (s : St E) (tree : E) (cost loss : JF) (parentRef : Nat)
    (complexity : Int) :
    Nat × St E :=
  let o := s.next
  (o, { s.write o ⟨tree, cost, loss, o, o, parentRef, complexity⟩ with next := o + 1 })

/-- `mutate!` output: the `tree` field; a member made by `create_child(parent_member, ...;
parent_ref)`; the member `OptimizeMutation` makes with `create_child(parent_member, new_tree,
cost, loss, options; parent_ref)` and then hands to `optimize_constants`, which optionally
updates its tree, cost and loss in place (with a new birth, `src/ConstantOptimization.jl:231-236`);
or, for an abstract handler (simplify, user methods), the `parent_member` object itself,
optionally after such an in-place update. -/
inductive HOut (E : Type) where
  | tree (t : E)
  | child (t : E) (cost loss : JF)
  | optimized (t : E) (cost loss : JF) (update : Option (E × JF × JF))
  | parent (update : Option (E × JF × JF))

/-- A `MutationResult` before the member it may carry is materialised. -/
structure HRes (E : Type) where
  out : HOut E
  evals : JF := .fin 0
  imm : Bool := false
  success : Bool := true

/-- A `MutationResult{N,P}` (`src/Mutate.jl:99-121`): either a tree or a member object id. -/
inductive Out (E : Type) where
  | tree (t : E)
  | member (o : Nat)

/-- Advance the task-local stream by `n` draws: abstract functions read the stream at its
cursor and report how many draws they consumed, so the stream itself is never replaced. -/
def adv (rng : RNG) (n : Nat) : RNG := { rng with cursor := rng.cursor + n }

/-- A tree-level mutation function from `src/MutationFunctions.jl`, on the copy: the new
tree and the number of draws consumed. -/
abbrev TreeFn (E : Type) := E → RNG → E × Nat

def mul64 (x y : JF) : JF := SymReg.Loss.LossPrecision.round .float64 (x * y)

/-- Inputs of the backsolve handler (`src/Mutate.jl:749-892`) besides the copy and parent.
`nodeOf` is `rand(NodeSampler(; tree, filter=Base.Fix2(!==, tree)))` returning a node
position; `sub t n` is the node object at that position and `splice t n x` is
`set_child!(parent, x, idx)` with `(parent, idx) = _find_parent(tree, node)`. -/
structure BS (E : Type) where
  isExpression : Bool
  binaryNode : Bool
  leaf : E → Bool
  sharing : Bool
  hasTarget : Bool
  hasOps : Bool
  parentComplexity : Int
  minValidRows : Nat
  nodeAttempts : Nat
  curmaxsize : Int
  nodeOf : E → RNG → Nat × Nat
  validRows : E → Nat → Nat
  nodeComplexity : E → Nat → Int
  setupEvaluated : E → Nat → RNG → Nat × Nat
  fit : E → Nat → Nat → Int → RNG → Option E × Nat
  sub : E → Nat → E
  splice : E → Nat → E → E
  complexity : E → Int
  constraints : E → Int → Bool
  evalCost : E → JF × JF
  subDataset : Bool
  freshParentCost : JF
  frac : JF

/-- The improvement gate of `src/Mutate.jl:866-870` (`1e-10` is modelled by `1/10^10`). -/
def improvedGate (gate after : JF) : Bool :=
  match gate with
  | .fin g =>
    let m := if 1 ≤ g then g else if 1 ≤ -g then -g else 1
    jlt after (.fin (g - m / 10000000000))
  | _ => isFinite after

/-- The node loop of the backsolve handler (`src/Mutate.jl:791-888`). `setup` is the node
whose `prepare_backsolve_setup` result is reused (`setup === nothing` before the first). -/
def bsLoop {E : Type} (b : BS E) (parentCost : JF) :
    Nat → E → Option Nat → JF → RNG → HRes E × RNG
  | 0, t, _, ev, rng => ({ out := .tree t, evals := ev, success := false }, rng)
  | n + 1, t, setup, ev, rng =>
    let (node, d) := b.nodeOf t rng
    let rng := adv rng d
    let ev := weightAdd ev b.frac
    if b.validRows t node < b.minValidRows then bsLoop b parentCost n t setup ev rng
    else
      let budget := b.curmaxsize - (b.parentComplexity - b.nodeComplexity t node)
      if budget < 1 then bsLoop b parentCost n t setup ev rng
      else
        let (sn, ev, rng) := match setup with
          | some sn => (sn, ev, rng)
          | none =>
            let (k, d) := b.setupEvaluated t node rng
            (node, weightAdd ev (mul64 (.fin k) b.frac), adv rng d)
        let (fitted, d) := b.fit t node sn budget rng
        let rng := adv rng d
        let ev := weightAdd ev (mul64 (.fin 2) b.frac)
        match fitted with
        | none => bsLoop b parentCost n t (some sn) ev rng
        | some newNode =>
          let orig := b.sub t node
          let t' := b.splice t node newNode
          let cc := b.complexity t'
          if !b.constraints t' cc then
            bsLoop b parentCost n (b.splice t' node orig) (some sn) ev rng
          else
            let (ac, al) := b.evalCost t'
            let ev := weightAdd ev b.frac
            let (gate, ev) := if b.subDataset then (b.freshParentCost, weightAdd ev b.frac) else (parentCost, ev)
            if improvedGate gate ac then
              ({ out := .child t' ac al, evals := ev, imm := true }, rng)
            else bsLoop b parentCost n (b.splice t' node orig) (some sn) ev rng

-- Source: src/Mutate.jl:765-768
/-
    function backsolve_fail(reason)
        trace_mutation_result!(trace, "reject", reason)
        return MutationResult{N,P}(; tree=new_tree, num_evals, success=false)
    end
-/
@[simp] def backsolveFail {E : Type} (t : E) (evals : JF) (reason : String)
    (trace : Option (String × String)) : HRes E × Option (String × String) :=
  ({ out := .tree t, evals, success := false }, trace.map (fun _ => ("reject", reason)))

-- Source: src/Mutate.jl:774-783
def earlyBacksolveRejection {E : Type} (b : BS E) (t : E) : Option String :=
  if !b.isExpression then some "backsolve_unsupported_expression"
  else if !b.binaryNode then some "backsolve_unsupported_node_type"
  else if b.leaf t then some "backsolve_single_node"
  else if b.sharing then some "backsolve_shared_nodes"
  else if !b.hasTarget then some "backsolve_missing_target"
  else if !b.hasOps then some "backsolve_missing_operators" else none

structure BacksolveTrace where
  mutationType : String
  result : String
  reason : String

def backsolvePrecheck {E : Type} (b : BS E) (t : E) (trace : Option BacksolveTrace) :=
  let trace := trace.map fun tr => { tr with mutationType := "backsolve" }
  (earlyBacksolveRejection b t).map fun reason =>
    let (r, status) := backsolveFail t (.fin 0) reason (trace.map fun tr => (tr.result, tr.reason))
    (r, trace.bind fun tr => status.map fun (result, reason) => { tr with result, reason })

def backsolveFailureTrace : Prop := ∀ (E : Type) (b : BS E) (t : E) previous,
  b.isExpression = false →
  ∃ r, backsolvePrecheck b t (some previous) =
      some (r, some ⟨"backsolve", "reject", "backsolve_unsupported_expression"⟩) ∧
    r.success = false ∧ r.imm = false ∧ r.evals = .fin 0 ∧ r.out = .tree t ∧
    backsolvePrecheck b t none = some (r, none)

theorem backsolveFailureTrace_holds : backsolveFailureTrace := by
  intro E b t previous h
  simp [backsolvePrecheck, earlyBacksolveRejection, h]

/-- Backsolve mutation, including the early failures at src/Mutate.jl:774-783. -/
def backsolveH {E : Type} (b : BS E) (parent : Member E) (t : E) (rng : RNG) : HRes E × RNG :=
  if !b.isExpression || !b.binaryNode || b.leaf t || b.sharing || !b.hasTarget || !b.hasOps then
    ((backsolveFail t (.fin 0) ((earlyBacksolveRejection b t).getD "backsolve_missing_operators") none).1, rng)
  else bsLoop b parent.cost b.nodeAttempts t none (.fin 0) rng

/-- An abstract `mutate!` method: given the parent member, the copy and the attempt number. -/
abbrev Handler (E : Type) := Member E → E → Nat → RNG → HRes E × Nat

/-- The tree-level functions the `mutate!` methods call (`src/Mutate.jl:609-991`), with
`options`, `nfeatures` and `curmaxsize` fixed for the call. `optimize t` is
`optimize_constants(dataset, member, options)` on a member with tree `t`, which is the only
field it reads (`src/ConstantOptimization.jl:147-243`): `none` resets the constants
(lines 238-241), `some` stores optimized tree, loss and cost into the member (lines 230-236);
either way the member itself is returned. `simplify` is the simplify handler (another slice)
and `custom n` the method for user type `n`, if any. -/
structure MF (E : Type) where
  mutateConstant : JF → TreeFn E
  mutateOperator : TreeFn E
  mutateFeature : TreeFn E
  swapOperands : TreeFn E
  appendRandomOp : TreeFn E
  prependRandomOp : TreeFn E
  insertRandomOp : TreeFn E
  deleteRandomOp : TreeFn E
  formConnection : TreeFn E
  breakConnection : TreeFn E
  rotate : TreeFn E
  randomize : TreeFn E
  optimize : E → RNG → (Option (E × JF × JF) × JF) × Nat
  backsolve : BS E
  customTypeDisplay : Nat → String
  simplify : Handler E
  custom : Nat → Option (Handler E)

/-- A tree mutation's `MutationResult{N,P}(; tree=new_tree)`. -/
def treeStep {E : Type} (f : TreeFn E) (t : E) (rng : RNG) : HRes E × RNG :=
  let (t', d) := f t rng
  ({ out := .tree t' }, adv rng d)

/-- `mutate!(new_tree, parent_member, mutation, options; ...)` dispatched on the kind
(`src/Mutate.jl:605-991`). `scale` is `context.scale` for `ConstantMutation`. -/
def mutateH {E : Type} (mf : MF E) (k : Kind) (scale : JF) (parent : Member E) (t : E)
    (attempt : Nat) (rng : RNG) : Jl (HRes E × RNG) :=
  match k with
  | .constant => pure (treeStep (mf.mutateConstant scale) t rng)
  | .operator => pure (treeStep mf.mutateOperator t rng)
  | .feature => pure (treeStep mf.mutateFeature t rng)
  | .swapOperands => pure (treeStep mf.swapOperands t rng)
  | .addNode =>
    let (u, rng) := draw rng
    if u < 1 / 2 then pure (treeStep mf.appendRandomOp t rng)
    else pure (treeStep mf.prependRandomOp t rng)
  | .insertNode => pure (treeStep mf.insertRandomOp t rng)
  | .deleteNode => pure (treeStep mf.deleteRandomOp t rng)
  | .formConnection => pure (treeStep mf.formConnection t rng)
  | .breakConnection => pure (treeStep mf.breakConnection t rng)
  | .rotateTree => pure (treeStep mf.rotate t rng)
  | .backsolve => pure (backsolveH mf.backsolve parent t rng)
  | .simplify => let (r, d) := mf.simplify parent t attempt rng; pure (r, adv rng d)
  | .randomize => pure (treeStep mf.randomize t rng)
  | .optimize =>
    let ((upd, ev), d) := mf.optimize t rng
    pure ({ out := .optimized t parent.cost parent.loss upd, evals := ev, imm := true }, adv rng d)
  | .doNothing => pure ({ out := .child t parent.cost parent.loss, imm := true }, rng)
  | .custom n =>
    match mf.custom n with
    | some h => let (r, d) := h parent t attempt rng; pure (r, adv rng d)
    | none => throw (.errorException ("Unknown mutation type: " ++ mf.customTypeDisplay n))

/-- Materialise a handler output in the store: `create_child` allocates; an in-place
optimisation updates the optimized object (new birth from the counter). -/
def materialise {E : Type} (s : St E) (po : Nat) (parentRef : Nat) (complexity : E → Int) :
    HOut E → Out E × St E
  | .tree t => (.tree t, s)
  | .child t c l => let (o, s) := createChild s t c l parentRef (complexity t); (.member o, s)
  | .optimized t c l none => let (o, s) := createChild s t c l parentRef (complexity t); (.member o, s)
  | .optimized t c l (some (t', c', l')) =>
    let (o, s) := createChild s t c l parentRef (complexity t)
    (.member o, { s.write o ⟨t', c', l', s.next, o, parentRef, complexity t⟩ with next := s.next + 1 })
  | .parent none => (.member po, s)
  | .parent (some (t, c, l)) =>
    match s.objs po with
    | some m =>
      let m' := { m with tree := t, cost := c, loss := l, birth := s.next, complexity := -1 }
      (.member po, { s.write po m' with next := s.next + 1 })
    | none => (.member po, s)

/-- A plugin (`src/Plugin.jl`): the hooks `condition_mutation_weights!`
(`src/Mutate.jl:224-228`), `condition_mutation!` on a `ConstantMutationContext`
(`src/Plugin.jl:475`) and `mutation_acceptance_multiplier` (`src/Plugin.jl:338-342`, given
parent, new tree, before and after cost). -/
structure Plugin (E : Type) where
  condWeights : Weights → Weights
  condScale : JF → JF
  accept : Member E → E → JF → JF → JF

/-- Options and dataset facts fixed for one `next_generation` call. -/
structure Cfg (E : Type) where
  mutations : Weights
  plugins : List (Plugin E)
  D : Nat
  treeOf : E → Tree JF
  preserveSharing : Bool
  scalarConsts : E → Nat
  complexity : E → Int
  shouldSimplify : Bool
  nfeatures : Int
  constraints : E → Int → Bool
  evalCost : E → JF × JF
  batchRows : Option Int := none
  fullRows : Int := 0
  mf : MF E
  isTemplate : Bool := false

-- Source: src/Dataset.jl:115,260
/-- A basic dataset has fraction one. A subdataset uses its selected
row count and the full dataset's row count. -/
def Cfg.frac {E : Type} (cfg : Cfg E) : JF :=
  match cfg.batchRows with
  | none => .fin 1
  | some n =>
    let round64 := SymReg.Loss.LossPrecision.round .float64
    round64 (round64 (.fin (Rat.ofInt n)) / round64 (.fin (Rat.ofInt cfg.fullRows)))

/-- `_fire_on_mutation_end!(options, plugin_states, mutation, event, dataset)`
(`src/Mutate.jl:275-286`): `on_mutation_end!` for every plugin in tuple order. -/
def fireEnd {E : Type} (cfg : Cfg E) (k : Kind) (ev : Event) (s : St E) : St E :=
  { s with log := s.log ++ (List.range cfg.plugins.length).map (fun i => Call.onEnd i k ev) }

/-- `resize!(weights, n)`: truncation or `#undef` padding. -/
def resizeScratch {α : Type} (xs : List (Option α)) (n : Nat) : List (Option α) :=
  xs.take n ++ List.replicate (n - xs.length) none

/-- `copyto!(dest, src)`: the first `length(src)` slots, a `BoundsError` if `dest` is shorter. -/
def copyTo {α : Type} (dst : List (Option α)) (src : List α) : Jl (List (Option α)) :=
  if src.length ≤ dst.length then pure (src.map some ++ dst.drop src.length)
  else throw .boundsError

/-- `_mutation_weights_scratch(options)` (`src/Mutate.jl:268-272`) on the previous scratch
contents. -/
def mutationWeightsScratch {α : Type} (prior : List (Option α)) (muts : List α) :
    Jl (List (Option α)) :=
  copyTo (resizeScratch prior muts.length) muts

/-- Reading every slot of the scratch vector: `#undef` is an `UndefRefError`. -/
def readAll {α : Type} (xs : List (Option α)) : Jl (List α) :=
  xs.mapM fun o => match o with | some x => pure x | none => throw .undefRefError

/-- Product of the plugin multipliers, `prod(strictmap(...))` (`src/Mutate.jl:519-523`);
`prod(())` is `1.0`. -/
def prodJF : List JF → JF
  | [] => .fin 1
  | x :: xs => xs.foldl (· * ·) x

/-- How the retry loop of `_next_generation` ended (`src/Mutate.jl:396-458`). -/
inductive LoopEnd (E : Type) where
  | immediate (o : Nat)
  | finished (successful : Bool) (tree : E)

/-- The retry loop `while (!successful_mutation) && attempts < max_attempts`
(`src/Mutate.jl:396-456`), `max_attempts = 10`. `fuel = 10 - attempts`. -/
def retry {E : Type} (cfg : Cfg E) (k : Kind) (scale : JF) (po : Nat) (parent : Member E)
    (parentRef : Nat) (curmaxsize : Int) : Nat → Nat → JF → St E → Jl ((LoopEnd E × JF) × St E)
  | 0, _, ev, s => pure ((.finished false parent.tree, ev), s)
  | fuel + 1, attempts, ev, s =>
    let t0 := parent.tree
    match mutateH cfg.mf k scale parent t0 (attempts + 1) s.rng with
    | .error e => .error e
    | .ok (r, rng) =>
      let s := { s with rng := rng, log := s.log ++ [.mutate (attempts + 1) r.evals r.imm r.success] }
      let (out, s) := materialise s po parentRef cfg.complexity r.out
      let ev := weightAdd ev r.evals
      if r.imm && r.success then
        match out with
        | .member o => pure ((.immediate o, ev), s)
        | .tree _ => throw (.assertionError "Mutation result must return a `PopMember` if `return_immediately` is true")
      else if r.imm then pure ((.finished false t0, ev), s)
      else
        match out with
        | .member _ => throw (.assertionError "Mutation result must return a tree if `return_immediately` is false")
        | .tree t =>
          if !r.success then pure ((.finished false t, ev), s)
          else
            let ok := cfg.constraints t curmaxsize
            let s := { s with log := s.log ++ [.constraints t ok] }
            if ok then pure ((.finished true t, ev), s)
            else retry cfg k scale po parent parentRef curmaxsize fuel (attempts + 1) ev s

/-- `_next_generation(mutation_choice, mutation_idx, ...)` (`src/Mutate.jl:351-562`).
Returns the member object id, `mutation_accepted` and `num_evals`. -/
def nextGenCore {E : Type} (cfg : Cfg E) (k : Kind) (idx : Nat) (po : Nat) (m : Member E)
    (curmaxsize : Int) (s : St E) : Jl ((Nat × Bool × JF) × St E) :=
  let scale : JF := if k = .constant then cfg.plugins.foldl (fun sc p => p.condScale sc) (.fin 1)
    else .fin 1
  let curTree (s : St E) : E := ((s.objs po).map Member.tree).getD m.tree
  let rejectBefore (ev : JF) (s : St E) : Nat × Bool × JF × St E :=
    let s := fireEnd cfg k ⟨false, m.cost, none, m.loss, none, idx⟩ s
    let tree := curTree s
    let (o, s) := createChild s tree m.cost m.loss m.ref (cfg.complexity tree)
    (o, false, ev, s)
  match retry cfg k scale po m m.ref curmaxsize 10 0 (.fin 0) s with
  | .error e => .error e
  | .ok ((.immediate o, ev), s) =>
    match s.objs o with
    | some r => pure ((o, true, ev), fireEnd cfg k ⟨true, m.cost, some r.cost, m.loss, some r.loss, idx⟩ s)
    | none => throw .undefRefError
  | .ok ((.finished false _, ev), s) =>
    let (o, b, ev, s) := rejectBefore ev s
    pure ((o, b, ev), s)
  | .ok ((.finished true t, ev), s) =>
    let (c, l) := cfg.evalCost t
    let s := { s with log := s.log ++ [.eval t] }
    let ev := weightAdd ev cfg.frac
    if c = .nan then
      let (o, b, ev, s) := rejectBefore ev s
      pure ((o, b, ev), s)
    else
      let p := prodJF (cfg.plugins.map fun pl => pl.accept m t m.cost c)
      let (u, rng) := draw s.rng
      let s := { s with rng := rng }
      if jlt p (.fin u) then
        let s := fireEnd cfg k ⟨false, m.cost, some c, m.loss, some l, idx⟩ s
        let tree := curTree s
        let (o, s) := createChild s tree m.cost m.loss m.ref (cfg.complexity tree)
        pure ((o, false, ev), s)
      else
        let (o, s) := createChild s t c l m.ref (cfg.complexity t)
        pure ((o, true, ev), fireEnd cfg k ⟨true, m.cost, some c, m.loss, some l, idx⟩ s)

-- Source: src/PopMember.jl:186-200
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
-- Generic leaves return before calling compute_complexity (src/Mutate.jl:179-203).
-- Templates call it unconditionally (src/TemplateExpression.jl:935).
def conditionParent {E : Type} (cfg : Cfg E) (m : Member E) : Member E :=
  { m with complexity :=
      (if cfg.isTemplate || (cfg.treeOf m.tree).degree != 0 then
        if m.complexity = -1 then cfg.complexity m.tree else m.complexity
      else m.complexity) }

/-- The weights `next_generation` samples from: scratch copy of `options.mutations`,
engine conditioning, then each plugin's `condition_mutation_weights!` in tuple order
(`src/Mutate.jl:319-326`). -/
def conditionedWeights {E : Type} (cfg : Cfg E) (m : Member E) (curmaxsize : Int)
    (ws : Weights) : Weights :=
  let c : CondIn := ⟨cfg.D, cfg.treeOf m.tree, cfg.preserveSharing, cfg.scalarConsts m.tree,
    (conditionParent cfg m).complexity, curmaxsize, cfg.nfeatures, cfg.shouldSimplify, cfg.isTemplate⟩
  cfg.plugins.foldl (fun w p => p.condWeights w) (conditionMutationWeights ws c)

/-- `next_generation(dataset, member, curmaxsize, options; ...)` (`src/Mutate.jl:299-349`)
on the member object `po`. Returns the member object id, `mutation_accepted` and
`num_evals`. -/
def nextGeneration {E : Type} (cfg : Cfg E) (po : Nat) (curmaxsize : Int) (s : St E) :
    Jl ((Nat × Bool × JF) × St E) :=
  match s.objs po with
  | none => throw .undefRefError
  | some m =>
    match mutationWeightsScratch s.scratch cfg.mutations with
    | .error e => .error e
    | .ok sc =>
      match readAll sc with
      | .error e => .error e
      | .ok ws =>
        let ws := conditionedWeights cfg m curmaxsize ws
        let m := conditionParent cfg m
        let s := { s.write po m with scratch := ws.map some }
        match sampleMutationR ws s.rng with
        | (.error e, _) => .error e
        | (.ok idx, rng) =>
          match ws[idx - 1]? with
          | none => throw .boundsError
          | some (k, _) =>
            nextGenCore cfg k idx po m curmaxsize { s with rng := rng, log := s.log ++ [.choose k idx] }

end SymReg.MutateGen
