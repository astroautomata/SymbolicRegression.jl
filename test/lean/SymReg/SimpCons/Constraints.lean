import SymReg.ConstraintsProofs
import SymReg.Crossover
import SymReg.Loss.Core

namespace SymReg.SimpCons
open DynExpr DynExpr.NodeBase SymReg.Complexity SymReg.Constraints SymReg.HeapLemmas

@[simp] theorem errBind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

@[simp] theorem errMap {ε α β : Type} (e : ε) (f : α → β) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl

inductive CustomResult where
  | machineInt (value : Int64)
  | other

/-- Already-promoted operator and leaf weights from `src/OptionsStruct.jl:24-29`. -/
structure WeightTable (W : Type) where
  operators : List (List W)
  variables : Sum W (List W)
  constant : W

/-- Source: `src/Complexity.jl:20-27,29-40`. -/
inductive Mapping (E : Type) where
  | weights (cmap : CMap)
  | floating (precision : SymReg.Loss.LossPrecision) (weights : WeightTable JF)
  | custom (f : E → Jl CustomResult)

private def int64 (n : Int) : Int := (Int64.ofInt n).toInt

/-- Source: DynamicExpressions `src/base.jl:160-166,271-280`.
`sizeHint` models the allocation primitive independently of the heap read. -/
def countedSize {T : Type} (g : SGraph T) (D : Nat) (isGraph bs : Bool)
    (fuel root : Nat) (sizeHint : Int → Jl Unit) : Jl Int := do
  if isGraph && !bs then
    let unfolded ← countNodesH g D false true fuel root
    sizeHint (int64 unfolded)
  let n ← countNodesH g D isGraph bs fuel root
  pure (int64 n)

/-- Constraint options at `src/CheckConstraints.jl:66-99`, including `options.maxsize`. -/
structure CheckOpts (E : Type) where
  base : Opts
  mapping : Mapping E
  maxsize : Int
  sizeHint : Int → Jl Unit := fun _ => pure ()

-- Source: src/Complexity.jl:37
-- return round(Int, raw_complexity)
private def roundWeight : JF → Jl Int
  | .fin q => do
    let magnitude := SymReg.Loss.nearestEven q
    let n : Int := if q < 0 then -(magnitude : Int) else (magnitude : Int)
    if n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n then throw .inexactError
    pure n
  | _ => .error .inexactError

/-- Source: `src/Complexity.jl:43-62`.
```
return tree_mapreduce(
    let vc = cmap.variable_complexity, cc = cmap.constant_complexity
        if vc isa AbstractVector
            t -> t.constant ? cc : @inbounds(vc[t.feature])
        else
            t -> t.constant ? cc : vc
        end
    end,
    let op_complexities = cmap.op_complexities
        t -> @inbounds(op_complexities[t.degree][t.op])
    end,
    +,
    tree,
    CT;
    break_sharing=break_sharing,
    f_on_shared=(result, is_shared) -> is_shared ? zero(CT) : result,
)
```
Julia's variadic `+` starts with the parent and adds child results left to right. -/
private def weightedSize {T : Type} (g : SGraph T) (D : Nat) (isGraph bs : Bool)
    (fuel root : Nat) (cacheHint : Int → Jl Unit) (w : WeightTable JF)
    (p : SymReg.Loss.LossPrecision) : Jl Int := do
  if isGraph && !bs then
    let unfolded ← countNodesH g D false true fuel root
    cacheHint (int64 unfolded)
  let raw ← (treeMapreduceH (σ := Unit) g D isGraph bs
    (fun _ c => StateT.lift (if c.constant then pure w.constant else
      match w.variables with
      | .inl v => pure v
      | .inr vs => idx1 vs c.feature))
    (fun _ c => StateT.lift (idx1 w.operators c.degree >>= fun ws => idx1 ws c.op))
    (fun parent children => pure (children.foldl (fun a b => p.round (a + b)) parent))
    (fun value shared => if shared then .fin 0 else value) fuel root).run' ()
  roundWeight raw

/-- Source: `src/Complexity.jl:29-40`.
```
complexity_mapping = options.complexity_mapping
if complexity_mapping isa ComplexityMapping && complexity_mapping.use
    raw_complexity = _compute_complexity(tree, options.complexity_mapping; break_sharing)
    return round(Int, raw_complexity)
else
    return count_nodes(tree; break_sharing)
end
```
In this mapping variant all weights are machine `Int`; wrapping the final
integer sum gives the same result as wrapping each integer addition. -/
def nodeComplexity {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat)
    (isGraph bs : Bool) (fuel root : Nat) : Jl Int := do
  match o.mapping with
  | .weights cm =>
    if cm.use then
      if isGraph && !bs then
        let unfolded ← countNodesH g D false true fuel root
        o.sizeHint (int64 unfolded)
      let n ← computeComplexityH g D isGraph bs cm fuel root
      pure (int64 n)
    else countedSize g D isGraph bs fuel root o.sizeHint
  | .floating p w => weightedSize g D isGraph bs fuel root o.sizeHint w p
  | .custom _ => countedSize g D isGraph bs fuel root o.sizeHint

/-- Source: `src/Complexity.jl:20-27`.
```
if options.complexity_mapping isa Function
    return options.complexity_mapping(tree)::Int
else
    return compute_complexity(get_tree(tree), options; break_sharing)
end
```
`JlError` encodes the Julia exception class in a string when it has no
dedicated constructor. -/
def expressionComplexityWith {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {E : Type}
    (mapping : Option (E → m CustomResult)) (ex : E) (getTree : E → m Addr)
    (nodeSize : Addr → m Int) : m Int := do
  match mapping with
  | some f =>
    match ← f ex with
    | .machineInt n => pure n.toInt
    | .other => throw (.errorException "TypeError")
  | none =>
    let root ← getTree ex
    nodeSize root

def expressionComplexity {E T : Type} (o : CheckOpts E) (ex : E) (getTree : E → Jl Addr)
    (g : SGraph T) (D : Nat) (isGraph bs : Bool) (fuel : Nat) : Jl Int :=
  expressionComplexityWith (match o.mapping with | .custom f => some f | _ => none)
    ex getTree (nodeComplexity o g D isGraph bs fuel)

inductive SizeLimit where
  | integer (n : Int64)
  | bigRational (q : Rat)
  | ieee (precision : SymReg.Loss.LossPrecision) (value : SymReg.Loss.SignedFloat)
  | other (compare : Int → Jl (Jl Bool))

/-- Source: `src/Complexity.jl:7-11`, `return compute_complexity(tree, options) > limit`.
The return annotation converts a non-Boolean comparison result to `Bool`.
For user-dispatched comparisons the outer result is the comparison's result
and the inner result is its return conversion. -/
def compareSize (n : Int) : SizeLimit → Jl Bool
  | .integer k => pure (decide (k.toInt < n))
  | .bigRational q => pure (decide (q < (n : Rat)))
  -- Base 1.12.0 base/float.jl:645-687 corrects the Float32/64 cast
  -- on equality by comparing the integer back, so use the exact order.
  | .ieee _ value => pure (match value.value with
    | .fin q => decide (q < (n : Rat))
    | .negInf => true
    | .posInf | .nan => false)
  | .other compare => do
    let converted ← compare n
    converted

-- Source: src/Complexity.jl:7-11
-- return compute_complexity(tree, options) > limit
def pastLimitWith {m : Type → Type} [Monad m] (complexity : m Int)
    (compare : Int → m Bool) : m Bool :=
  complexity >>= compare

/-- Source: `src/Complexity.jl:7-11`, node dispatch. -/
def pastComplexityLimit {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat)
    (isGraph : Bool) (fuel root : Nat) (limit : SizeLimit) : Jl Bool :=
  pastLimitWith (nodeComplexity o g D isGraph false fuel root) (compareSize · limit)

/-- Source: `src/Complexity.jl:7-11`, generic expression dispatch. -/
def pastExpressionLimit {E T : Type} (o : CheckOpts E) (ex : E) (getTree : E → Jl Addr)
    (g : SGraph T) (D : Nat) (graph : Bool) (fuel : Nat) (limit : SizeLimit) : Jl Bool :=
  pastLimitWith (expressionComplexity o ex getTree g D graph false fuel) (compareSize · limit)

/-- `count_depth`, called by `src/CheckConstraints.jl:82`; DE `src/NodeUtils.jl:25-28`
explicitly breaks sharing. -/
def depthH {T : Type} (g : SGraph T) (D fuel root : Nat) : Jl Int :=
  (treeMapreduceH (σ := Unit) g D true true (fun _ _ => StateT.lift (pure (1 : Int)))
    (fun _ _ => StateT.lift (pure (1 : Int)))
    (fun p cs => StateT.lift (pure (p + maxList cs))) (fun r _ => r) fuel root).run' ()

/-- `count_max_nestedness`, `src/CheckConstraints.jl:34-45`. Both depth and nesting
visit every unfolded path, even when multiple edges point at the same object. -/
def nestedH {T : Type} (g : SGraph T) (D fuel root degree op : Nat) : Jl Int := do
  let n ← (treeMapreduceH (σ := Unit) g D true true (fun _ _ => StateT.lift (pure (0 : Int)))
    (fun _ c => StateT.lift (pure (if c.degree = degree ∧ c.op = op then (1 : Int) else 0)))
    (fun p cs => StateT.lift (pure (p + maxList cs))) (fun r _ => r) fuel root).run' ()
  let c ← g.read root
  pure (n - if c.degree = degree ∧ c.op = op then 1 else 0)

/-- `_check_operator_constraints`, `src/CheckConstraints.jl:24-32`, on heap children. -/
def checkOpH {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat) (isGraph : Bool)
    (fuel root degree : Nat) (cons : List Int) : Jl Bool := do
  if degree = 0 then throw (.assertionError "degree != 0")
  anyListM (fun i => do
    let ci ← match cons[i - 1]? with
      | some ci => pure ci
      | none => throw .boundsError
    if ci = -1 then pure false else do
      let child ← getChild g D root i
      pastComplexityLimit o g D isGraph fuel child (.integer (Int64.ofInt ci))) (List.range' 1 degree)

/-- `flag_operator_complexity`, `src/CheckConstraints.jl:14-21`. The DE `any`
traversal does not use an identity cache. -/
def flagOpH {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat) (isGraph : Bool)
    (fuel root degree op : Nat) (cons : List Int) : Jl Bool :=
  (SymReg.Crossover.anyH g D (fun a c => StateT.lift
    (if c.degree = degree ∧ c.op = op then checkOpH o g D isGraph fuel a degree cons
      else pure false)) fuel root).run' ()

/-- `flag_illegal_nests`, `src/CheckConstraints.jl:48-62`. -/
def flagNestsH {E T : Type} (o : CheckOpts E) (g : SGraph T) (D fuel root : Nat) : Jl Bool :=
  match o.base.nested with
  | none => pure false
  | some ncs => (SymReg.Crossover.anyH g D (fun a c => StateT.lift
      (anyListM (fun (degree, op, inner) =>
        if c.degree = degree ∧ c.op = op then
          anyListM (fun (nd, no, mx) => do
            let n ← nestedH g D fuel a nd no
            pure (decide (mx < n))) inner
        else pure false) ncs)) fuel root).run' ()

/-- `check_constraints(::AbstractExpressionNode, ...)`, `src/CheckConstraints.jl:75-94`.
A supplied cache bypasses only the first complexity computation. Per-degree checks
are evaluated with `mapM`, before their Boolean results are combined. -/
def checkH {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat) (isGraph : Bool)
    (fuel root : Nat) (maxsize : Int) (cached : Option Int) : Jl Bool := do
  let n ← match cached with
    | some n => pure n
    | none => nodeComplexity o g D isGraph false fuel root
  if n > maxsize then return false
  if (← depthH g D fuel root) > o.base.maxdepth then return false
  let invalid ← (enum1 o.base.opCons).mapM (fun (degree, ops) =>
    anyListM (fun (op, cons) => if cons.any (· ≠ -1) then
      flagOpH o g D isGraph fuel root degree op cons else pure false) (enum1 ops))
  if invalid.any id then return false
  if ← flagNestsH o g D fuel root then return false
  return true

-- Source: src/CheckConstraints.jl:66-74
/-
function check_constraints(
    ex::AbstractExpression,
    options::AbstractOptions,
    maxsize::Int,
    cached_size::Union{Int,Nothing}=nothing,
)::Bool
    tree = get_tree(ex)
    return check_constraints(tree, options, maxsize, cached_size)
end
-/
def checkExpression {E T : Type} (o : CheckOpts E) (ex : E) (getTree : E → Jl Addr)
    (g : SGraph T) (D : Nat) (isGraph : Bool) (fuel : Nat)
    (maxsize : Int) (cached : Option Int) : Jl Bool := do
  let root ← getTree ex
  checkH o g D isGraph fuel root maxsize cached


structure TemplateInner (E : Type) where
  expr : E
  getTree : E → Jl Addr
  featureLimit : Nat → Jl Bool

/-- Source: `src/TemplateExpression.jl:1159-1165`.
```
return contains_features_greater_than(get_tree(tree), max_feature)
# Nodes:
any(tree) do node
    node.degree == 0 && !node.constant && node.feature > max_feature
end
```
`featureLimit` is the dispatched `>(feature, max_feature)` in Boolean context;
the constructor checks the keys of `num_features` but leaves its values untyped. -/
def invalidInner {E T : Type} (g : SGraph T) (D fuel : Nat) (inner : TemplateInner E) : Jl Bool := do
  let root ← inner.getTree inner.expr
  (SymReg.Crossover.anyH (σ := Unit) g D (fun _ c => StateT.lift
    (if c.degree = 0 && !c.constant then inner.featureLimit c.feature else pure false))
    fuel root).run' ()

/-- Source: `src/TemplateExpression.jl:707-715`.
```
return sum(ex -> ComplexityModule.compute_complexity(ex, options; break_sharing),
           values(get_contents(tree)))
```
Inner entries and limits are paired by key and stored in contents iteration order. -/
def templateSizeWith {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {E : Type}
    (size : E → m Int) (inners : List E) : m Int := do
  if inners.isEmpty then throw (.argumentError "reducing over an empty collection is not allowed")
  let sizes ← inners.mapM size
  pure (int64 sizes.sum)

def templateSize {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat)
    (isGraph bs : Bool) (fuel : Nat) (inners : List (TemplateInner E)) : Jl Int :=
  templateSizeWith (fun i => expressionComplexity o i.expr i.getTree g D isGraph bs fuel) inners

/-- Source: `src/TemplateExpression.jl:1142-1144`, `src/CheckConstraints.jl:66-74`. -/
private def innerConstraintCheck {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat)
    (isGraph : Bool) (fuel : Nat) (maxsize : Int) (i : TemplateInner E) : Jl Bool := do
  let root ← i.getTree i.expr
  checkH o g D isGraph fuel root maxsize none

/-- Source: `src/Complexity.jl:7-11` and `src/TemplateExpression.jl:707-715`. -/
def pastTemplateLimit {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat)
    (isGraph : Bool) (fuel : Nat) (inners : List (TemplateInner E)) (limit : SizeLimit) : Jl Bool :=
  pastLimitWith (templateSize o g D isGraph false fuel inners) (compareSize · limit)

/-- Source: `src/TemplateExpression.jl:1125-1147,1150-1157`.
```
if has_invalid_variables(ex)
    return false
end
@something(cursize, ComplexityModule.compute_complexity(ex, options)) > maxsize &&
    return false
raw_contents = get_contents(ex)
for t in values(raw_contents)
    if !CC.check_constraints(t, options, maxsize, nothing)
        return false
    end
end
return true
```
-/
def checkTemplate {E T : Type} (o : CheckOpts E) (g : SGraph T) (D : Nat)
    (isGraph : Bool) (fuel : Nat) (inners : List (TemplateInner E))
    (maxsize : Int) (cached : Option Int) : Jl Bool := do
  if ← anyListM (invalidInner g D fuel) inners then return false
  let n ← match cached with
    | some n => pure n
    | none => templateSize o g D isGraph false fuel inners
  if n > maxsize then return false
  let bad ← anyListM (fun i => do
    let valid ← innerConstraintCheck o g D isGraph fuel maxsize i
    pure (!valid)) inners
  pure (!bad)

inductive ConstraintSubject (E : Type) where
  | node (root : Addr)
  | expr (value : E)
  | template (inners : List (TemplateInner E))

-- Source: src/CheckConstraints.jl:97-99
/-
check_constraints(ex::Union{AbstractExpression,AbstractExpressionNode}, options::AbstractOptions)::Bool = check_constraints(
    ex, options, options.maxsize
)
-/
def checkDefault {E T : Type} (o : CheckOpts E) (ex : ConstraintSubject E)
    (getTree : E → Jl Addr) (g : SGraph T) (D : Nat) (isGraph : Bool) (fuel : Nat) : Jl Bool :=
  match ex with
  | .node root => checkH o g D isGraph fuel root o.maxsize none
  | .expr ex => checkExpression o ex getTree g D isGraph fuel o.maxsize none
  | .template inners => checkTemplate o g D isGraph fuel inners o.maxsize none

/-- The supplied cache is trusted, including inconsistent values. -/
def cacheTrusted : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (g : SGraph T) D graph fuel root maxsize cached,
    maxsize < cached → checkH o g D graph fuel root maxsize (some cached) = .ok false

theorem cacheTrusted_holds : cacheTrusted := by
  intro E T o g D graph fuel root maxsize cached h
  simp [checkH, h, pure_ok, ok_bind]

def expressionForward : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (e : E) (getTree : E → Jl Addr)
    (g : SGraph T) D graph fuel maxsize cache,
    (∀ err, getTree e = .error err →
      checkExpression o e getTree g D graph fuel maxsize cache = .error err) ∧
    ∀ root, getTree e = .ok root →
      checkExpression o e getTree g D graph fuel maxsize cache =
        checkH o g D graph fuel root maxsize cache ∧
      ∀ cached, cache = some cached → maxsize < cached →
        checkExpression o e getTree g D graph fuel maxsize cache = .ok false

theorem expressionForward_holds : expressionForward := by
  intro E T o e getTree g D graph fuel maxsize cache
  refine ⟨?_, ?_⟩
  · intro err h
    simp [checkExpression, h, bind, Except.bind]
  · intro root ht
    simp only [checkExpression, ht, ok_bind, true_and]
    intro cached hc h
    subst cache
    exact cacheTrusted_holds E T o g D graph fuel root maxsize cached h

def defaultMaxsize : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (getTree : E → Jl Addr) (g : SGraph T) D graph fuel,
    (∀ root,
      (∀ err, nodeComplexity o g D graph false fuel root = .error err →
        checkDefault o (.node root) getTree g D graph fuel = .error err) ∧
      ∀ n, nodeComplexity o g D graph false fuel root = .ok n →
        (o.maxsize < n → checkDefault o (.node root) getTree g D graph fuel = .ok false) ∧
        (n ≤ o.maxsize → depthH g D fuel root = .ok 1 → 1 ≤ o.base.maxdepth →
          o.base.opCons = [] → o.base.nested = none →
          checkDefault o (.node root) getTree g D graph fuel = .ok true)) ∧
    (∀ e,
      (∀ err, getTree e = .error err → checkDefault o (.expr e) getTree g D graph fuel = .error err) ∧
      ∀ root, getTree e = .ok root →
        checkDefault o (.expr e) getTree g D graph fuel =
          checkDefault o (.node root) getTree g D graph fuel) ∧
    ∀ inners, anyListM (invalidInner g D fuel) inners = .ok false →
      (∀ err, templateSize o g D graph false fuel inners = .error err →
        checkDefault o (.template inners) getTree g D graph fuel = .error err) ∧
      ∀ n, templateSize o g D graph false fuel inners = .ok n → o.maxsize < n →
        checkDefault o (.template inners) getTree g D graph fuel = .ok false

theorem defaultMaxsize_holds : defaultMaxsize := by
  intro E T o getTree g D graph fuel
  refine ⟨?_, ?_, ?_⟩
  · intro root
    constructor
    · intro err he
      simp [checkDefault, checkH, he, pure_ok]
    · intro n hn
      constructor
      · intro hn'
        simp [checkDefault, checkH, hn, hn', pure_ok, ok_bind]
      · intro hn' hd hdepth ho hs
        simp [checkDefault, checkH, hn, hd, Int.not_lt.mpr hn', Int.not_lt.mpr hdepth,
          ho, hs, flagNestsH, enum1, pure_ok, ok_bind]
  · intro e
    constructor
    · intro err he
      simp [checkDefault, checkExpression, he, bind, Except.bind]
    · intro root hr
      simp [checkDefault, checkExpression, hr, ok_bind]
  · intro inners hi
    constructor
    · intro err he
      simp [checkDefault, checkTemplate, hi, he, pure_ok, ok_bind]
    · intro n hn hn'
      simp [checkDefault, checkTemplate, hi, hn, hn', pure_ok, ok_bind]


abbrev ComplexityM (S : Type) := EStateM JlError S

def customExpression : Prop :=
  ∀ (E S : Type) (f : E → ComplexityM S CustomResult) (e : E)
    (getTree : E → ComplexityM S Addr) (nodeSize : Addr → ComplexityM S Int) (s : S),
    let result := expressionComplexityWith (some f) e getTree nodeSize s
    (∀ n after, f e s = .ok (.machineInt n) after → result = .ok n.toInt after) ∧
    (∀ err after, f e s = .error err after → result = .error err after) ∧
    (∀ after, f e s = .ok .other after → result = .error (.errorException "TypeError") after)

theorem customExpression_holds : customExpression := by
  intro E S f e getTree nodeSize s
  refine ⟨?_, ?_, ?_⟩
  · intro n after hn
    simp [expressionComplexityWith, Bind.bind, EStateM.bind, hn] <;> rfl
  · intro err after he
    simp [expressionComplexityWith, Bind.bind, EStateM.bind, he]
  · intro after ht
    simp [expressionComplexityWith, Bind.bind, EStateM.bind, ht] <;> rfl

def customNodeCount : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (f : E → Jl CustomResult) (g : SGraph T)
    D graph bs fuel root (t : Tree T) (objects : List Addr),
    o.mapping = .custom f →
    let result := nodeComplexity o g D graph bs fuel root
    (Graph.unfold g.view fuel root = some t → DegLe D t → t.Representable →
      ((graph && !bs) = false → result = .ok (int64 t.size)) ∧
      ((graph && !bs) = true → objects.Nodup →
        (∀ a, a ∈ objects ↔ Graph.Reachable g.view root a) →
        o.sizeHint (int64 t.size) = .ok () → result = .ok (int64 objects.length))) ∧
    ((graph && !bs) = true →
      (∀ err, countNodesH g D false true fuel root = .error err → result = .error err) ∧
      (∀ n err, countNodesH g D false true fuel root = .ok n →
        o.sizeHint (int64 n) = .error err → result = .error err))

theorem customNodeCount_holds : customNodeCount := by
  intro E T o f g D graph bs fuel root t objects hm
  have hroute : nodeComplexity o g D graph bs fuel root =
      countedSize g D graph bs fuel root o.sizeHint := by simp [nodeComplexity, hm]
  dsimp only
  rw [hroute]
  constructor
  · intro ht hd _
    obtain ⟨hunfolded, hplain, visited, hnd, hreaches, hdistinct⟩ :=
      count_nodes_graph_holds T g D fuel root t ht hd
    constructor
    · intro h
      cases graph <;> cases bs <;> simp_all [countedSize, pure_ok, ok_bind]
    · intro h ho hall hs
      have hp : visited.Perm objects :=
        (List.perm_ext_iff_of_nodup hnd ho).mpr (fun a => (hreaches a).trans (hall a).symm)
      obtain ⟨rfl, rfl⟩ : graph = true ∧ bs = false := by
        cases graph <;> cases bs <;> simp_all
      simp [countedSize, hunfolded, hs, hdistinct, hp.length_eq, pure_ok, ok_bind]
  · intro h
    constructor
    · intro err he
      simp [countedSize, h, he]
    · intro n err hn he
      simp [countedSize, h, hn, he, pure_ok, ok_bind]

example : Graph.unfold leafX1.view 1 0 = some (.feature 1) ∧
    ([0] : List Addr).Nodup := ⟨rfl, by simp⟩

private def StrictOutcome (complexity : Jl Int) (run : SizeLimit → Jl Bool) : Prop :=
  (∀ err limit, complexity = .error err → run limit = .error err) ∧
  (∀ n, complexity = .ok n →
    (∀ k : Int64, k.toInt = n → run (.integer k) = .ok false) ∧
    run (.bigRational (n : Rat)) = .ok false ∧
    (∀ k : Int64, k.toInt < n → run (.integer k) = .ok true) ∧
    (∀ q, q < (n : Rat) → run (.bigRational q) = .ok true) ∧
    (∀ p (f : SymReg.Loss.SignedFloat), f.Representable p →
      (∀ q, f.value = .fin q →
        (run (.ieee p f) = .ok true ↔ q < (n : Rat))) ∧
      (f.value = .negInf → run (.ieee p f) = .ok true) ∧
      ((f.value = .posInf ∨ f.value = .nan) → run (.ieee p f) = .ok false)) ∧
    (∀ f err, f n = .error err ∨ f n = .ok (.error err) →
      run (.other f) = .error err))

def pastLimitStrict : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (g : SGraph T) D graph fuel root e getTree,
    StrictOutcome (nodeComplexity o g D graph false fuel root)
      (pastComplexityLimit o g D graph fuel root) ∧
    StrictOutcome (expressionComplexity o e getTree g D graph false fuel)
      (pastExpressionLimit o e getTree g D graph fuel) ∧
    ∀ inners, StrictOutcome (templateSize o g D graph false fuel inners)
      (pastTemplateLimit o g D graph fuel inners)

private theorem strictOutcome_bind (complexity : Jl Int) :
    StrictOutcome complexity (fun limit => complexity >>= fun n => compareSize n limit) := by
  constructor
  · intro err limit h
    simp [h]
  · intro n h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp [h, compareSize, hk, pure_ok, ok_bind]
    · simp [h, compareSize, pure_ok, ok_bind]
    · intro k hk
      simp [h, compareSize, hk, pure_ok, ok_bind]
    · intro q hq
      simp [h, compareSize, hq, pure_ok, ok_bind]
    · intro p f _
      refine ⟨?_, ?_, ?_⟩
      · intro q hf
        simp [h, compareSize, hf, pure_ok, ok_bind]
      · intro hf
        simp [h, compareSize, hf, pure_ok, ok_bind]
      · rintro (hf | hf) <;> simp [h, compareSize, hf, pure_ok, ok_bind]
    · intro f err he
      rcases he with he | he <;> simp [h, compareSize, he, ok_bind]

theorem pastLimitStrict_holds : pastLimitStrict := by
  intro E T o g D graph fuel root e getTree
  exact ⟨strictOutcome_bind _, strictOutcome_bind _, fun _ => strictOutcome_bind _⟩

example : compareSize ((2 : Int) ^ 53 + 1) (.ieee .float64 (.ordinary (.fin (2 ^ 53)))) =
    .ok true := by decide +kernel

example : compareSize 0 (.ieee .float32 .negativeZero) = .ok false := by decide +kernel

private inductive CheckedCalls {E S : Type} (f : E → ComplexityM S CustomResult) :
    List E → S → List Int → S → Prop
  | nil (s) : CheckedCalls f [] s [] s
  | cons {e es s n next ns after} :
      f e s = .ok (.machineInt n) next → CheckedCalls f es next ns after →
      CheckedCalls f (e :: es) s (n.toInt :: ns) after

private theorem checkedCalls_map {E S : Type} (f : E → ComplexityM S CustomResult)
    (getTree : E → ComplexityM S Addr) (nodeSize : Addr → ComplexityM S Int)
    {es : List E} {s : S} {ns : List Int} {after : S}
    (trace : CheckedCalls f es s ns after) :
    es.mapM (fun e => expressionComplexityWith (some f) e getTree nodeSize) s = .ok ns after := by
  induction trace with
  | nil => rfl
  | @cons e es s n next ns after h _ ih =>
    have head := (customExpression_holds E S f e getTree nodeSize s).1 n next h
    simp only [List.mapM_cons, Bind.bind, EStateM.bind, head, ih]
    rfl

private theorem checkedCalls_stop {E S : Type} (f : E → ComplexityM S CustomResult)
    (getTree : E → ComplexityM S Addr) (nodeSize : Addr → ComplexityM S Int)
    {pre : List E} {s : S} {ns : List Int} {next : S}
    (trace : CheckedCalls f pre s ns next) (e : E) (post : List E) (err : JlError) (after : S)
    (failure : f e next = .error err after ∨
      (err = .errorException "TypeError" ∧ f e next = .ok .other after)) :
    (pre ++ e :: post).mapM (fun e => expressionComplexityWith (some f) e getTree nodeSize) s =
      .error err after := by
  induction trace with
  | nil =>
    rcases failure with h | ⟨rfl, h⟩ <;>
      simp [List.mapM_cons, expressionComplexityWith, Bind.bind, EStateM.bind, h] <;> rfl
  | @cons e es s n step ns final h _ ih =>
    have head := (customExpression_holds E S f e getTree nodeSize s).1 n step h
    simp only [List.cons_append, List.mapM_cons, Bind.bind, EStateM.bind, head, ih failure]

def pastCustomFunction : Prop :=
  ∀ (E S : Type) (f : E → ComplexityM S CustomResult)
    (getTree : E → ComplexityM S Addr) (nodeSize : Addr → ComplexityM S Int)
    (e : E) (inners : List E) (s : S),
    let size := fun x => expressionComplexityWith (some f) x getTree nodeSize
    let cmp := fun limit n => fun w : S => EStateM.Result.ok (decide (limit < n)) w
    let scalar := fun limit => pastLimitWith (size e) (cmp limit) s
    let template := fun limit => pastLimitWith (templateSizeWith size inners) (cmp limit) s
    (∀ n after, f e s = .ok (.machineInt n) after → scalar n.toInt = .ok false after) ∧
    (∀ err after limit, f e s = .error err after → scalar limit = .error err after) ∧
    (∀ after limit, f e s = .ok .other after →
      scalar limit = .error (.errorException "TypeError") after) ∧
    (∀ ns after, inners ≠ [] → CheckedCalls f inners s ns after →
      template (int64 ns.sum) = .ok false after ∧
      ∀ k, k < int64 ns.sum → template k = .ok true after) ∧
    (∀ pre i post ns next err after limit, inners = pre ++ i :: post →
      CheckedCalls f pre s ns next →
      (f i next = .error err after ∨
        (err = .errorException "TypeError" ∧ f i next = .ok .other after)) →
      template limit = .error err after)

theorem pastCustomFunction_holds : pastCustomFunction := by
  intro E S f getTree nodeSize e inners s
  dsimp only
  obtain ⟨ok, fail, typeError⟩ := customExpression_holds E S f e getTree nodeSize s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n after h
    simp [pastLimitWith, Bind.bind, EStateM.bind, ok n after h]
  · intro err after limit h
    simp [pastLimitWith, Bind.bind, EStateM.bind, fail err after h]
  · intro after limit h
    simp [pastLimitWith, Bind.bind, EStateM.bind, typeError after h]
  · intro ns after nonempty trace
    have hm := checkedCalls_map f getTree nodeSize trace
    have hne : inners.isEmpty = false := by cases inners <;> simp_all
    refine ⟨?_, ?_⟩
    · simp [pastLimitWith, templateSizeWith, Bind.bind, Pure.pure, EStateM.bind,
        EStateM.pure, hne, hm]
    · intro k hk
      simp [pastLimitWith, templateSizeWith, Bind.bind, Pure.pure, EStateM.bind,
        EStateM.pure, hne, hm, hk]
  · intro pre i post ns next err after limit h trace hf
    subst inners
    have hm := checkedCalls_stop f getTree nodeSize trace i post err after hf
    have hne : (pre ++ i :: post).isEmpty = false := by cases pre <;> rfl
    simp only [pastLimitWith, templateSizeWith, Bind.bind, EStateM.bind, hne,
      Bool.false_eq_true, ↓reduceIte, hm]

private theorem anyListM_allFalse {A : Type} (f : A → Jl Bool) (xs : List A)
    (h : ∀ x ∈ xs, f x = .ok false) : anyListM f xs = .ok false := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [anyListM, ha, ht, ok_bind]

private theorem anyListM_stop {A : Type} (f : A → Jl Bool) (pre post : List A) (x : A)
    (h : ∀ y ∈ pre, f y = .ok false) :
    anyListM f (pre ++ x :: post) = anyListM f (x :: post) := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [anyListM, ha, ht, ok_bind]

def templateInvalid : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (g : SGraph T) D graph fuel
    (pre post : List (TemplateInner E)) i maxsize cached,
    (∀ prev ∈ pre, invalidInner g D fuel prev = .ok false) →
    (invalidInner g D fuel i = .ok true →
      checkTemplate o g D graph fuel (pre ++ i :: post) maxsize cached = .ok false) ∧
    (∀ err, invalidInner g D fuel i = .error err →
      checkTemplate o g D graph fuel (pre ++ i :: post) maxsize cached = .error err)

theorem templateInvalid_holds : templateInvalid := by
  intro E T o g D graph fuel pre post i maxsize cached hp
  constructor
  · intro hi
    unfold checkTemplate
    rw [anyListM_stop _ pre post i hp]
    simp [anyListM, hi, ok_bind, pure_ok]
  · intro err hi
    unfold checkTemplate
    rw [anyListM_stop _ pre post i hp]
    simp [anyListM, hi]

def templateCachedReject : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (g : SGraph T) D graph fuel inners maxsize cached,
    maxsize < cached →
    let result := checkTemplate o g D graph fuel inners maxsize (some cached)
    (∀ b, anyListM (invalidInner g D fuel) inners = .ok b → result = .ok false) ∧
    (∀ err, anyListM (invalidInner g D fuel) inners = .error err → result = .error err)

theorem templateCachedReject_holds : templateCachedReject := by
  intro E T o g D graph fuel inners maxsize cached h
  constructor
  · intro b hval
    cases b <;> simp [checkTemplate, hval, h, pure_ok, ok_bind]
  · intro err hval
    simp [checkTemplate, hval]

def templateInnerReject : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (g : SGraph T) D graph fuel inners maxsize cached,
    (∀ i ∈ inners, invalidInner g D fuel i = .ok false) →
    (match cached with
      | some n => n ≤ maxsize
      | none => ∃ n, templateSize o g D graph false fuel inners = .ok n ∧ n ≤ maxsize) →
    let inner := fun (i : TemplateInner E) =>
      i.getTree i.expr >>= fun root => checkH o g D graph fuel root maxsize none
    let result := checkTemplate o g D graph fuel inners maxsize cached
    ((∀ i ∈ inners, inner i = .ok true) → result = .ok true) ∧
    (∀ pre (i : TemplateInner E) post, inners = pre ++ i :: post →
      (∀ prev ∈ pre, inner prev = .ok true) →
      (inner i = .ok false → result = .ok false) ∧
      (∀ err, inner i = .error err → result = .error err))

theorem templateInnerReject_holds : templateInnerReject := by
  intro E T o g D graph fuel inners maxsize cached hv hs
  let inner := innerConstraintCheck o g D graph fuel maxsize
  let reject := fun i => do
    let valid ← inner i
    pure (!valid)
  have hvalidation := anyListM_allFalse _ inners hv
  have hstage :
      checkTemplate o g D graph fuel inners maxsize cached =
        (anyListM reject inners >>= fun bad => pure (!bad)) := by
    cases cached with
    | none =>
      obtain ⟨n, hn, hle⟩ := hs
      simp only [checkTemplate, hvalidation, ok_bind, Bool.false_eq_true, ↓reduceIte,
        hn, Int.not_lt.mpr hle, inner, reject]
    | some n =>
      have hle : n ≤ maxsize := hs
      simp only [checkTemplate, hvalidation, ok_bind, Bool.false_eq_true, ↓reduceIte,
        pure_ok, Int.not_lt.mpr hle, inner, reject]
  change
    ((∀ i ∈ inners, inner i = .ok true) →
      checkTemplate o g D graph fuel inners maxsize cached = .ok true) ∧
    (∀ pre i post, inners = pre ++ i :: post →
      (∀ prev ∈ pre, inner prev = .ok true) →
      (inner i = .ok false → checkTemplate o g D graph fuel inners maxsize cached = .ok false) ∧
      (∀ err, inner i = .error err → checkTemplate o g D graph fuel inners maxsize cached = .error err))
  constructor
  · intro h
    have hall : anyListM reject inners = .ok false := by
      apply anyListM_allFalse
      intro i hi
      simp [reject, h i hi, ok_bind, pure_ok]
    simp [hstage, hall, ok_bind, pure_ok]
  · intro pre i post heq hp
    have hprefix : ∀ j ∈ pre, reject j = .ok false := by
      intro j hj
      simp [reject, hp j hj, ok_bind, pure_ok]
    rw [hstage, heq, anyListM_stop _ pre post i hprefix]
    constructor
    · intro hf
      simp [anyListM, reject, hf, ok_bind, pure_ok]
    · intro err herr
      simp [anyListM, reject, herr]

def graphSizeSound : Prop :=
  ∀ (E T : Type) (o : CheckOpts E) (g : SGraph T) D fuel root maxsize,
    let size := nodeComplexity o g D true false fuel root
    let result := checkH o g D true fuel root maxsize none
    (∀ err, size = .error err → result = .error err) ∧
    (∀ n, size = .ok n → maxsize < n → result = .ok false) ∧
    (∀ n, size = .ok n → n ≤ maxsize →
      result = checkH o g D true fuel root maxsize (some n))

theorem graphSizeSound_holds : graphSizeSound := by
  intro E T o g D fuel root maxsize
  refine ⟨?_, ?_, ?_⟩
  · intro err h
    simp [checkH, h]
  · intro n h hn
    simp [checkH, h, hn, ok_bind, pure_ok]
  · intro n h _
    simp [checkH, h, ok_bind, pure_ok]

private theorem varTwoCovers : Covers varTwo (Tree.feature 1 : Tree Nat) := by
  intro _ s hs
  simp only [preorder, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  simp [InRange, varTwo]

/-- An explicit custom complexity function should determine the top-level maxsize
check for every whole expression and every well-formed contents heap. -/
def customSizeSound : Prop :=
  ∀ (E T : Type) (base : Opts) (f : E → Jl CustomResult) (e : E) (getTree : E → Addr)
    (g : SGraph T) D graph fuel (t : Tree T) maxsize n,
    Graph.unfold g.view fuel (getTree e) = some t → t.WF D (fun _ => 255) 65535 →
    f e = .ok (.machineInt n) → maxsize < n.toInt →
    checkExpression { base := base, mapping := .custom f, maxsize := maxsize } e
      (fun e => .ok (getTree e))
      g D graph fuel maxsize none = .ok false

theorem customSizeSound_refuted : ¬ customSizeSound := by
  intro h
  have hc := h Nat Nat ⟨varTwo, 10, [], none⟩ (fun _ => .ok (.machineInt 10)) 0 (fun _ => 0)
    leafX1 2 false 1 (.feature 1) 3 10 rfl (by simp [Tree.WF]) rfl (by decide)
  let o : CheckOpts Nat :=
    { base := ⟨varTwo, 10, [], none⟩
      mapping := .custom (fun _ => .ok (.machineInt 10))
      maxsize := 3 }
  have ha : checkExpression o
      0 (fun _ => .ok 0) leafX1 2 false 1 3 none = .ok true := by decide
  rw [ha] at hc
  cases hc

/-- An inconsistent cache should not make an actually oversized, well-formed
plain expression acceptable. -/
def staleCacheSound : Prop :=
  ∀ (T : Type) (g : SGraph T) D fuel root (t : Tree T) (cm : CMap) maxsize maxdepth cached,
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    Covers cm t → maxsize < wsize cm t →
    checkH (E := Unit) { base := ⟨cm, maxdepth, [], none⟩, mapping := .weights cm, maxsize := maxsize }
      g D false fuel root maxsize (some cached) = .ok false

theorem staleCacheSound_refuted : ¬ staleCacheSound := by
  intro h
  have hc := h Nat leafX1 2 1 0 (.feature 1) varTwo 1 10 1 rfl
    (by simp [Tree.WF]) varTwoCovers (by decide)
  have ha : checkH (E := Unit) { base := ⟨varTwo, 10, [], none⟩, mapping := .weights varTwo, maxsize := 1 }
      leafX1 2 false 1 0 1 (some 1) = .ok true := by decide
  rw [ha] at hc
  cases hc

example : (0 : Int) < 1 ∧ (mkGraph ([] : List (SCell Nat))).cells 0 = none := by decide
example : nodeComplexity (E := Unit)
    { base := ⟨varTwo, 10, [], none⟩, mapping := .weights varTwo, maxsize := 3 }
    (mkGraph [featC 1] : SGraph Nat) 2 false false 1 0 = .ok 2 := by decide

private def templateWitnessOpts : CheckOpts Unit :=
  { base := ⟨varTwo, 10, [], none⟩
    mapping := .custom (fun _ => .error (.userError "complexity"))
    maxsize := 0 }

private def invalidWitness : TemplateInner Unit :=
  ⟨(), fun _ => .ok 0, fun feature => .ok (decide (0 < feature))⟩

private def malformedWitness : TemplateInner Unit :=
  ⟨(), fun _ => .ok 0, fun _ => .error (.methodError ">")⟩

example :
    checkTemplate templateWitnessOpts leafX1 2 false 1
      [invalidWitness, malformedWitness] 0 none = .ok false ∧
    checkTemplate templateWitnessOpts leafX1 2 false 1
      [malformedWitness, invalidWitness] 0 (some 1) = .error (.methodError ">") := by decide

end SymReg.SimpCons
