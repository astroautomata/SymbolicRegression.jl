import SymReg.ConstOpt.TemplateBridge

namespace SymReg.Ext
open DynExpr
open SymReg.ConstOpt

/-- `ext/SymbolicRegressionEnzymeExt.jl:12-20`. Allocates zeroed tree, dataset,
and options shadows. External zeroing remains arbitrary. -/
structure EnzymeStorage (H : Type) where
  tree : H
  dataset : Nat
  options : Nat

def prepareEnzyme {H : Type} (zeroTree : H → H)
    (zeroDataset zeroOptions : Nat → Nat) (tree : H) (dataset options : Nat) :
    EnzymeStorage H :=
  ⟨zeroTree tree, zeroDataset dataset, zeroOptions options⟩


-- Source: ext/SymbolicRegressionEnzymeExt.jl:22-25
/-
function evaluator(tree, dataset, options, output)
    output[] = eval_loss(tree, dataset, options; regularization=false)
    return nothing
end
-/
def enzymeEvaluator {C H R : Type} (e : Evaluator C H R) (convertLoss : JF → Jl C) (output : C)
    (s : EvalState C H) : Jl Unit × (EvalState C H × C) :=
  match callContext e false s with
  | (.ok loss, after) =>
    match convertLoss loss with
    | .ok value => (.ok (), (after, value))
    | .error err => (.error err, (after, output))
  | (.error err, after) => (.error err, (after, output))

def enzymeObjectiveAgreement : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) (convertLoss : JF → Jl C) x (s written : EvalState C H) output,
    written.context = none →
    writeParameters e x s = (.ok (), written) →
    let (loss, after) := evaluate e false x s
    enzymeEvaluator e convertLoss output written = match loss with
      | .ok raw => match convertLoss raw with
        | .ok value => (.ok (), (after, value))
        | .error err => (.error err, (after, output))
      | .error err => (.error err, (after, output))

theorem enzymeObjectiveAgreement_holds : enzymeObjectiveAgreement := by
  intro C H R e convertLoss x s written output _ hs
  simp only [evaluate, effect_bind, hs, enzymeEvaluator]
  rcases callContext e false written with ⟨loss, after⟩
  cases loss <;> rfl

example : ({ heap := (), log := [.write 0 [JF.fin 1]] } : EvalState JF Unit).context = none := rfl

structure EnzymeArgs where
  tree : Nat
  treeShadow : Nat
  dataset : Nat
  datasetShadow : Nat
  options : Nat
  optionsShadow : Nat
  outputCell : Nat
  seedCell : Nat

inductive EnzymeCall (C R : Type) where
  | write (tree : Nat) (x : List C) (refs : R)
  | resetTree (tree : Nat)
  | resetDataset (dataset : Nat)
  | resetOptions (options : Nat)
  | allocate (value : C)
  | reverse (stacksize : Nat) (args : EnzymeArgs)
  | extract (shadowTree tree : Nat) (refs : R)
  | broadcast (buffer : Nat) (values : List C)
  | readOutput (cell : Nat)

structure EnzymeServices (C R W : Type) where
  paramSet : Nat → List C → R → Effect W Unit
  remakeZero : Nat → Effect W Unit
  allocate : C → Effect W Nat
  reverse : Nat → EnzymeArgs → Effect W Unit
  extract : Nat → Nat → R → Effect W (List C)
  broadcast : Nat → List C → Effect W Unit
  readOutput : Nat → Effect W C

private def enzymeCall {C R W A : Type} (event : EnzymeCall C R) (act : Effect W A) :
    Effect (W × List (EnzymeCall C R)) A := fun (w, events) =>
  let (r, w') := act w
  (r, (w', events ++ [event]))

abbrev enzymeStackSize : Nat := 32 * 1024 * 1024

-- Source: ext/SymbolicRegressionEnzymeExt.jl:29-64
/-
function (g::GradEvaluator{<:Any,<:AutoEnzyme})(_, G, x::AbstractVector{T}) where {T}
    set_optimizable_parameters!(g.e.tree, x, g.e.refs)
    remake_zero!(g.extra.storage_tree)
    remake_zero!(g.extra.storage_dataset)
    remake_zero!(g.extra.storage_options)

    output = [zero(T)]
    doutput = [one(T)]

    with_stacksize(32 * 1024 * 1024) do
        autodiff(
            Reverse,
            evaluator,
            Duplicated(g.e.tree, g.extra.storage_tree),
            Duplicated(g.e.ctx.dataset, g.extra.storage_dataset),
            Duplicated(g.e.ctx.options, g.extra.storage_options),
            Duplicated(output, doutput),
        )
    end

    if G !== nothing
        extracted_gradient = extract_optimizable_gradient(
            g.extra.storage_tree, g.e.tree, g.e.refs
        )
        if length(extracted_gradient) != length(G)
            throw(DimensionMismatch(...))
        end
        G .= extracted_gradient
    end
    return output[]
end
-/
def enzymeGradient {C R W : Type} [Zero C] [OfNat C 1] (f : EnzymeServices C R W)
    (tree dataset options : Nat) (refs : R) (shadow : EnzymeStorage Nat)
    (buffer : Option (Nat × Nat)) (x : List C) : Effect (W × List (EnzymeCall C R)) C := do
  enzymeCall (.write tree x refs) (f.paramSet tree x refs)
  enzymeCall (.resetTree shadow.tree) (f.remakeZero shadow.tree)
  enzymeCall (.resetDataset shadow.dataset) (f.remakeZero shadow.dataset)
  enzymeCall (.resetOptions shadow.options) (f.remakeZero shadow.options)
  let output ← enzymeCall (.allocate 0) (f.allocate 0)
  let seed ← enzymeCall (.allocate 1) (f.allocate 1)
  let args : EnzymeArgs :=
    ⟨tree, shadow.tree, dataset, shadow.dataset, options, shadow.options, output, seed⟩
  enzymeCall (.reverse enzymeStackSize args) (f.reverse enzymeStackSize args)
  if let some (g, gLen) := buffer then
    let values ← enzymeCall (.extract shadow.tree tree refs) (f.extract shadow.tree tree refs)
    if values.length ≠ gLen then
      fun st => (.error (.errorException "DimensionMismatch"), st)
    enzymeCall (.broadcast g values) (f.broadcast g values)
  enzymeCall (.readOutput output) (f.readOutput output)

def enzymeGradientRouting : Prop :=
  ∀ (C R W : Type) [Zero C] [OfNat C 1] (f : EnzymeServices C R W),
    ∀
    tree dataset options refs (shadow : EnzymeStorage Nat) g gLen x w events value out,
    enzymeGradient f tree dataset options refs shadow (some (g, gLen)) x (w, events) =
      (.ok value, out) →
    ∃ output seed values, values.length = gLen ∧ out.2 = events ++
        [.write tree x refs, .resetTree shadow.tree, .resetDataset shadow.dataset,
         .resetOptions shadow.options, .allocate 0, .allocate 1,
         .reverse (32 * 1024 * 1024)
            ⟨tree, shadow.tree, dataset, shadow.dataset, options, shadow.options, output, seed⟩,
         .extract shadow.tree tree refs, .broadcast g values, .readOutput output] ∧
      ∃ beforeRead, f.readOutput output beforeRead = (.ok value, out.1)

theorem enzymeGradientRouting_holds : enzymeGradientRouting := by
  intro C R W _ _ f tree dataset options refs shadow g gLen x w events value out h
  rcases h1 : f.paramSet tree x refs w with ⟨r1, w1⟩
  cases r1 <;> simp [enzymeGradient, enzymeCall, h1] at h
  rcases h2 : f.remakeZero shadow.tree w1 with ⟨r2, w2⟩
  cases r2 <;> simp [enzymeCall, h2] at h
  rcases h3 : f.remakeZero shadow.dataset w2 with ⟨r3, w3⟩
  cases r3 <;> simp [enzymeCall, h3] at h
  rcases h4 : f.remakeZero shadow.options w3 with ⟨r4, w4⟩
  cases r4 <;> simp [enzymeCall, h4] at h
  rcases ho : f.allocate 0 w4 with ⟨outCell, wOut⟩
  cases outCell with
  | error err => simp [enzymeCall, ho] at h
  | ok output =>
    rcases hd : f.allocate 1 wOut with ⟨seedCell, wSeed⟩
    cases seedCell with
    | error err => simp [enzymeCall, ho, hd] at h
    | ok seed =>
      simp [enzymeCall, ho, hd] at h
      rcases h5 : f.reverse enzymeStackSize
          ⟨tree, shadow.tree, dataset, shadow.dataset, options, shadow.options, output, seed⟩ wSeed
        with ⟨r5, w5⟩
      cases r5 <;> simp [enzymeCall, h5] at h
      rcases h6 : f.extract shadow.tree tree refs w5 with ⟨r6, w6⟩
      cases r6 with
      | error _ => simp [enzymeCall, h6] at h
      | ok values =>
        simp [enzymeCall, h6] at h
        by_cases hlen : values.length = gLen
        · simp [hlen] at h
          rcases h7 : f.broadcast g values w6 with ⟨r7, w7⟩
          cases r7 <;> simp [enzymeCall, h7] at h
          rcases h8 : f.readOutput output w7 with ⟨r8, w8⟩
          cases r8 with
          | error _ => simp [enzymeCall, h8] at h
          | ok _ =>
            simp only [enzymeCall, h8, Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨output, seed, values, hlen, by simp [List.append_assoc], w7, h8⟩
        · simp [hlen] at h

def enzymeNoBuffer : Prop :=
  ∀ (C R W : Type) [Zero C] [OfNat C 1] (f : EnzymeServices C R W),
    ∀ tree dataset options refs (shadow : EnzymeStorage Nat) x w events value out,
    enzymeGradient f tree dataset options refs shadow none x (w, events) =
      (.ok value, out) →
    ∃ output seed, out.2 = events ++
        [.write tree x refs, .resetTree shadow.tree, .resetDataset shadow.dataset,
         .resetOptions shadow.options, .allocate 0, .allocate 1,
         .reverse (32 * 1024 * 1024)
            ⟨tree, shadow.tree, dataset, shadow.dataset, options, shadow.options, output, seed⟩,
         .readOutput output] ∧
      ∃ beforeRead, f.readOutput output beforeRead = (.ok value, out.1)

theorem enzymeNoBuffer_holds : enzymeNoBuffer := by
  intro C R W _ _ f tree dataset options refs shadow x w events value out h
  rcases h1 : f.paramSet tree x refs w with ⟨r1, w1⟩
  cases r1 <;> simp [enzymeGradient, enzymeCall, h1] at h
  rcases h2 : f.remakeZero shadow.tree w1 with ⟨r2, w2⟩
  cases r2 <;> simp [enzymeCall, h2] at h
  rcases h3 : f.remakeZero shadow.dataset w2 with ⟨r3, w3⟩
  cases r3 <;> simp [enzymeCall, h3] at h
  rcases h4 : f.remakeZero shadow.options w3 with ⟨r4, w4⟩
  cases r4 <;> simp [enzymeCall, h4] at h
  rcases ho : f.allocate 0 w4 with ⟨outCell, wOut⟩
  cases outCell with
  | error err => simp [enzymeCall, ho] at h
  | ok output =>
    rcases hd : f.allocate 1 wOut with ⟨seedCell, wSeed⟩
    cases seedCell with
    | error err => simp [enzymeCall, ho, hd] at h
    | ok seed =>
      simp [enzymeCall, ho, hd] at h
      rcases h5 : f.reverse enzymeStackSize
          ⟨tree, shadow.tree, dataset, shadow.dataset, options, shadow.options, output, seed⟩ wSeed
        with ⟨r5, w5⟩
      cases r5 <;> simp [enzymeCall, h5] at h
      rcases h6 : f.readOutput output w5 with ⟨r6, w6⟩
      cases r6 with
      | error _ => simp [enzymeCall, h6] at h
      | ok _ =>
        simp only [enzymeCall, h6, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨output, seed, by simp [List.append_assoc], w5, h6⟩

inductive TaskCall (A : Type) where
  | create (f : Unit → Jl A) (stacksize : Int)
  | schedule (task : Nat)
  | fetch (task : Nat)

-- Source: ext/SymbolicRegressionEnzymeExt.jl:37
-- with_stacksize(f::F, n) where {F} = fetch(schedule(Task(f, n)))
def withStacksize {A : Type} (create : (Unit → Jl A) → Int → Jl Nat)
    (schedule : Nat → Jl Nat) (fetch : Nat → Jl A)
    (f : Unit → Jl A) (n : Int) : Jl A × List (TaskCall A) :=
  match create f n with
  | .error e => (.error e, [.create f n])
  | .ok task =>
    match schedule task with
    | .error e => (.error e, [.create f n, .schedule task])
    | .ok scheduled => (fetch scheduled, [.create f n, .schedule task, .fetch scheduled])

def stacksizeRouting : Prop :=
  ∀ (A : Type) create schedule (fetch : Nat → Jl A) f n,
    (∀ err, create f n = .error err →
      withStacksize create schedule fetch f n = (.error err, [.create f n])) ∧
    (∀ task err, create f n = .ok task → schedule task = .error err →
      withStacksize create schedule fetch f n = (.error err, [.create f n, .schedule task])) ∧
    ∀ task scheduled, create f n = .ok task → schedule task = .ok scheduled →
      withStacksize create schedule fetch f n =
        (fetch scheduled, [.create f n, .schedule task, .fetch scheduled])

theorem stacksizeRouting_holds : stacksizeRouting := by
  intro A create schedule fetch f n
  exact ⟨fun err h => by simp [withStacksize, h],
    fun task err h h' => by simp [withStacksize, h, h'],
    fun task scheduled h h' => by simp [withStacksize, h, h']⟩

/-- `ext/SymbolicRegressionEnzymeExt.jl:49`: the Enzyme wrapper calls
`set_optimizable_parameters!(g.e.tree, x, g.e.refs)`, dispatching directly to the
template optimizer setter (`src/TemplateExpression.jl:486-508`). -/
def enzymeTemplateWrite {T : Type} (x : SymReg.Templates.TConst T)
    (values : List T) (refs : SymReg.Templates.TOptRefs) : Jl (SymReg.Templates.TConst T) :=
  match SymReg.Templates.optSet x values refs with
  | .ok () state => .ok state
  | .err error _ => .error error

def enzymeOptimizableHooks : Prop :=
  ∀ (T : Type) fuel root (x : SymReg.Templates.TConst T) original refs,
    (templateHooks T fuel).get root x = .ok (original, refs) →
    enzymeTemplateWrite x original refs = (templateHooks T fuel).set root original refs x

theorem enzymeOptimizableHooks_holds : enzymeOptimizableHooks := by
  intro T fuel root x original refs _
  simp only [enzymeTemplateWrite, templateHooks]
  cases SymReg.Templates.optSet x original refs <;> rfl

/-- `ext/SymbolicRegressionMooncakeExt.jl:13-21`. Zip stops at the shorter
sequence; NoTangent is an assertion failure. Inner extraction remains arbitrary. -/
def mooncakeTrees {G T : Type} (extract : G → Nat → Jl (List T)) :
    List (Option G) → List Nat → Jl (List T)
  | some g :: gs, root :: roots => do
      let values ← extract g root
      let rest ← mooncakeTrees extract gs roots
      pure (values ++ rest)
  | none :: _, _ :: _ => .error (.assertionError "Unexpected input type: NoTangent")
  | _, _ => pure []

/-- Parameter tangents' _data order, lines 23-35. The primal parameter
is used only by zip, not to select/reorder any gradient coordinate. -/
def mooncakeParams {T : Type} : List (Option (List T)) → List (List T) → Jl (List T)
  | some values :: gs, _ :: ps => do
      let rest ← mooncakeParams gs ps
      pure (values ++ rest)
  | none :: _, _ :: _ => .error (.assertionError "Unexpected input type: NoTangent")
  | _, _ => pure []

/-- Sequential packing into undef output at lines 10-12,19-20,32-37.
Unwritten slots remain uninitialized; a write past the allocated count under
@inbounds has undefined behavior. Numeric scalar slots reuse DE's scalar value type. -/
def mooncakePack {T : Type} (n : Nat) (values : List T) : Jl (List (Option T)) :=
  if values.length ≤ n then
    .ok (values.map some ++ List.replicate (n - values.length) none)
  else .error (.undefinedBehavior "gradient packing past scalar count")

/-- Template extraction, lines 7-38. count_scalar_constants is the allocated
capacity; all inner gradients precede all parameter gradients. -/
def mooncakeTemplate {G T : Type} (extract : G → Nat → Jl (List T)) (n : Nat)
    (trees : List (Option G)) (roots : List Nat) (hasParams : Bool)
    (params : List (Option (List T))) (primalParams : List (List T)) : Jl (List (Option T)) := do
  let treeValues ← mooncakeTrees extract trees roots
  let paramValues ← if hasParams then mooncakeParams params primalParams else pure []
  mooncakePack n (treeValues ++ paramValues)

def mooncakePackingOrder : Prop :=
  ∀ (G T : Type) extract n (trees : List (Option G)) roots hasParams params primalParams tv pv,
    mooncakeTrees extract trees roots = .ok tv →
    (if hasParams then mooncakeParams params primalParams else pure []) = (.ok pv : Jl (List T)) →
    n = tv.length + pv.length →
    mooncakeTemplate extract n trees roots hasParams params primalParams = .ok ((tv ++ pv).map some)

theorem mooncakePackingOrder_holds : mooncakePackingOrder := by
  intro G T extract n trees roots hasParams params primalParams tv pv ht hp hn
  cases hasParams with
  | false =>
      have he : pv = [] := by simpa using hp.symm
      subst pv
      simp [mooncakeTemplate, ht, mooncakePack, hn]
  | true =>
      have he : mooncakeParams params primalParams = .ok pv := hp
      simp [mooncakeTemplate, ht, he, mooncakePack, hn]

example : mooncakeTrees (fun (_ : Unit) (_ : Nat) => (.ok [JF.fin 2] : Jl (List JF)))
      [some ()] [0] = .ok [JF.fin 2] ∧
    (if true then mooncakeParams [some [JF.fin 3]] [[JF.fin 0]] else pure []) =
      (.ok [JF.fin 3] : Jl (List JF)) ∧ 2 = [JF.fin 2].length + [JF.fin 3].length :=
  ⟨rfl, rfl, rfl⟩

def mooncakeNoTangent : Prop :=
  ∀ (G T : Type) (extract : G → Nat → Jl (List T)) gs root roots ps (p : List T) primalParams,
    mooncakeTrees extract (none :: gs) (root :: roots) = .error (.assertionError "Unexpected input type: NoTangent") ∧
    mooncakeParams (none :: ps) (p :: primalParams) = .error (.assertionError "Unexpected input type: NoTangent")

theorem mooncakeNoTangent_holds : mooncakeNoTangent := by
  unfold mooncakeNoTangent; intros; exact ⟨rfl, rfl⟩

/-- `ext/SymbolicRegressionMooncakeExt.jl:39-41`: exactly the .tree component
and get_tree(ex) are forwarded, without template parameters or another tangent. -/
def mooncakeComposable {E G T : Type} (getTree : E → Nat) (treeField : G → G)
    (extract : G → Nat → Jl (List T)) (gradient : G) (ex : E) :=
  extract (treeField gradient) (getTree ex)

def mooncakeComposableRouting : Prop :=
  ∀ (E G T : Type) getTree treeField (extract : G → Nat → Jl (List T)) gradient (ex : E),
    mooncakeComposable getTree treeField extract gradient ex = extract (treeField gradient) (getTree ex)

/-- For matching tangent/primal arity, zip preserves chunk order and every
scalar coordinate within each chunk, lines 13-35. Inner extracted gradients
are supplied as data here to isolate packing from external differentiation. -/
def mooncakeChunkOrder : Prop :=
  ∀ (T : Type) (chunks : List (List T)) roots (primalParams : List (List T)),
    chunks.length = roots.length → chunks.length = primalParams.length →
    mooncakeTrees (fun values _ => .ok values) (chunks.map some) roots = .ok chunks.flatten ∧
    mooncakeParams (chunks.map some) primalParams = .ok chunks.flatten

theorem mooncakeChunkOrder_holds : mooncakeChunkOrder := by
  intro T chunks
  induction chunks with
  | nil =>
      intro roots primalParams _ _
      cases roots <;> cases primalParams <;> exact ⟨rfl, rfl⟩
  | cons chunk chunks ih =>
      intro roots primalParams hr hp
      cases roots with
      | nil => simp at hr
      | cons root roots =>
        cases primalParams with
        | nil => simp at hp
        | cons p primalParams =>
          have h := ih roots primalParams (by simpa using hr) (by simpa using hp)
          simp [mooncakeTrees, mooncakeParams, h.1, h.2]

example : ([ [JF.fin 1], [JF.fin 2, .fin 3] ] : List (List JF)).length =
    [0, 1].length ∧
    ([ [JF.fin 1], [JF.fin 2, .fin 3] ] : List (List JF)).length =
      ([[], []] : List (List JF)).length := ⟨rfl, rfl⟩

private def enzymePreparationRouting : Prop :=
  ∀ (H : Type) zeroTree zeroDataset zeroOptions (tree : H) dataset options,
    let s : EnzymeStorage H := prepareEnzyme zeroTree zeroDataset zeroOptions tree dataset options
    s.tree = zeroTree tree ∧
    s.dataset = zeroDataset dataset ∧ s.options = zeroOptions options

def enzymeShadowIsolation : Prop :=
  ∀ (zeroTree : List Nat → List Nat) zeroDataset zeroOptions
    (tree : List Nat) dataset options,
    let shadow := prepareEnzyme zeroTree zeroDataset zeroOptions tree dataset options
    ∀ a ∈ shadow.tree, a ∉ tree

def enzymePreparation : Prop := enzymePreparationRouting ∧ enzymeShadowIsolation

end SymReg.Ext
