import SymReg.ConstOpt.Core
import SymReg.HofMig.Hall
import SymReg.SimpCons.Members

namespace SymReg.ConstOpt
open DynExpr
open DynExpr.ParamStruct
open SymReg.HofMig (Member less)

/-- Numeric expressions are supported independently of their parameter values. -/
def numericSupport : Prop :=
  ∀ (S : Type) (elementType options : Nat) (state : S) (result : Jl Bool) (next : S),
    canOptimizeNumber elementType = true ∧
    canOptimizeExpression
      (fun t o s => if t = elementType ∧ o = options then (result,next) else (.ok false,s))
      elementType options state = (result,next)

theorem numericSupport_holds : numericSupport := by
  intro S t o s result next
  exact ⟨rfl, by simp [canOptimizeExpression]⟩

def disabledUnchanged : Prop :=
  ∀ (H R : Type) (hooks : EntryHooks H R) element inner args
    (s after : EntryStore H R),
    let tree := hooks.memberTree args.member s.heap
    hooks.eligible tree args.options
      {s with events := s.events ++ [.eligibility tree args.options]} = (.ok false, after) →
    optimizeConstants hooks element inner args s = (.ok (args.member, .fin 0), after)

theorem disabledUnchanged_holds : disabledUnchanged := by
  intro H R hooks element inner args s after
  dsimp only
  intro h
  simp [optimizeConstants, optimizeCount, readMemberTree, traceEntry, h]

def noParametersUnchanged : Prop :=
  ∀ (H R : Type) (hooks : EntryHooks H R) element inner args
    (s eligible selected after : EntryStore H R) x0 refs,
    let first := hooks.memberTree args.member s.heap
    let current := hooks.memberTree args.member eligible.heap
    hooks.eligible first args.options
      {s with events := s.events ++ [.eligibility first args.options]} = (.ok true, eligible) →
    hooks.getter current args.options
      {eligible with events := eligible.events ++ [.getter current args.options]} =
        (.ok (x0, refs), selected) →
    hooks.length x0 {selected with events := selected.events ++ [.length x0]} = (.ok 0, after) →
    optimizeConstants hooks element inner args s = (.ok (args.member, .fin 0), after)

theorem noParametersUnchanged_holds : noParametersUnchanged := by
  intro H R hooks element inner args s eligible selected after x0 refs
  dsimp only
  intro hc hg hl
  simp [optimizeConstants, optimizeCount, getSelection, readMemberTree, traceEntry, hc, hg, hl]

def rawParameterForwarding : Prop :=
  ∀ (H R : Type) (hooks : EntryHooks H R) inner args (s selected : EntryStore H R),
    let tree := hooks.memberTree args.member s.heap
    let input := {s with events := s.events ++ [.getter tree args.options]}
    (∀ err, hooks.getter tree args.options input = (.error err, selected) →
      optimizeRaw hooks inner args s = (.error err, selected)) ∧
    (∀ x0 refs, hooks.getter tree args.options input = (.ok (x0, refs), selected) →
      ∀ result after, inner args x0 refs
        {selected with events := selected.events ++ [.prepared args x0 refs]} = (result, after) →
      optimizeRaw hooks inner args s = ((fun n => (args.member, n)) <$> result, after))

theorem rawParameterForwarding_holds : rawParameterForwarding := by
  intro H R hooks inner args s selected
  dsimp only
  constructor
  · intro err hg; simp [optimizeRaw, getSelection, readMemberTree, traceEntry, hg]
  · intro x0 refs hg result after hi
    cases result <;> simp [optimizeRaw, getSelection, readMemberTree, traceEntry, invokePrepared, hg, hi]

def algorithmDispatch : Prop :=
  ∀ (H R : Type) (hooks : EntryHooks H R) element args
    (s eligible selected measured specialized : EntryStore H R) x0 refs n options,
    let first := hooks.memberTree args.member s.heap
    let current := hooks.memberTree args.member eligible.heap
    hooks.eligible first args.options
      {s with events := s.events ++ [.eligibility first args.options]} = (.ok true, eligible) →
    hooks.getter current args.options
      {eligible with events := eligible.events ++ [.getter current args.options]} =
        (.ok (x0, refs), selected) →
    hooks.length x0 {selected with events := selected.events ++ [.length x0]} = (.ok n, measured) →
    n ≠ 0 →
    hooks.specialize args.options
      {measured with events := measured.events ++ [.specializedOptions args.options]} =
        (.ok options, specialized) →
    let run := optimizeConstants hooks element (fun _ _ _ st => (.ok (.fin 0), st)) args s
    (∀ typeId found checked, element = .noncomplex typeId → n = 1 →
      hooks.optimizerOptions args.options
        {specialized with events := specialized.events ++ [.optimizerOptions args.options]} =
          (.ok found, checked) →
      run.2.events = checked.events ++
        [.prepared {args with options := options, algorithm := .newton, optimizerOptions := found} x0 refs]) ∧
    ((n ≠ 1 ∨ (∃ typeId, element = .complex typeId)) →
      ∀ algorithm configured found checked,
      hooks.configuredAlgorithm args.options
        {specialized with events := specialized.events ++ [.configuredAlgorithm args.options]} =
          (.ok algorithm, configured) →
      hooks.optimizerOptions args.options
        {configured with events := configured.events ++ [.optimizerOptions args.options]} =
          (.ok found, checked) →
      run.2.events = checked.events ++
        [.prepared {args with options := options, algorithm := algorithm, optimizerOptions := found} x0 refs])

theorem algorithmDispatch_holds : algorithmDispatch := by
  intro H R hooks element args s eligible selected measured specialized x0 refs n options
  dsimp only
  intro hc hg hl hn ho
  constructor
  · rintro typeId found checked rfl rfl hopt
    simp [optimizeConstants, optimizeCount, getSelection, readMemberTree, traceEntry, invokePrepared,
      hc, hg, hl, ho, hopt]
  · intro branch algorithm configured found checked halg hopt
    rcases branch with hn' | ⟨typeId, rfl⟩
    · cases element <;>
        simp [optimizeConstants, optimizeCount, getSelection, readMemberTree, traceEntry, invokePrepared,
          hc, hg, hl, hn, hn', ho, halg, hopt]
    · simp [optimizeConstants, optimizeCount, getSelection, readMemberTree, traceEntry, invokePrepared,
        hc, hg, hl, hn, ho, halg, hopt]

def objectiveDispatch : Prop :=
  ∀ algorithm backend,
    objectiveKind algorithm backend = .value ↔ algorithm = .newton ∨ backend = none

theorem objectiveDispatch_holds : objectiveDispatch := by
  intro algorithm backend
  cases algorithm <;> cases backend <;> simp [objectiveKind]

def populationEnableGate : Prop :=
  ∀ (E L G D : Type) simplify combine
    (optimize : D → SymReg.SimpCons.Member E L → G →
      Jl (SymReg.SimpCons.Member E L × JF × G))
    enabled selected (dataset : D) addr (members : SymReg.SimpCons.MemberStore E L)
    (state afterSimplify afterCombine : G) (simplified combined : E),
    let member := members addr
    simplify member.tree state = .ok (simplified, afterSimplify) →
    combine simplified afterSimplify = .ok (combined, afterCombine) →
    let updated := SymReg.SimpCons.assignTree member combined
    let step := SymReg.SimpCons.processPopulation
      (fun flag => SymReg.SimpCons.optimizeMember true enabled flag simplify combine (optimize dataset))
      [addr] [selected] members state
    (enabled = true → selected = true →
      (∀ returned count final, optimize dataset updated afterCombine = .ok (returned, count, final) →
        ∃ result, step = .ok (result, [count], final) ∧ result addr = returned) ∧
      (∀ error, optimize dataset updated afterCombine = .error error → step = .error error)) ∧
    (enabled = false ∨ selected = false →
      ∃ result, step = .ok (result, [.fin 0], afterCombine) ∧ result addr = updated)

theorem populationEnableGate_holds : populationEnableGate := by
  intro E L G D simplify combine optimize enabled selected dataset addr members
    state afterSimplify afterCombine simplified combined
  dsimp only
  intro hs hc
  constructor
  · rintro rfl rfl
    constructor
    · intro returned count final ho
      refine ⟨fun a => if a = addr then returned else members a, ?_, by simp⟩
      simp [SymReg.SimpCons.processPopulation, SymReg.SimpCons.optimizeMember, hs, hc, ho]
    · intro error ho
      simp [SymReg.SimpCons.processPopulation, SymReg.SimpCons.optimizeMember, hs, hc, ho]
  · rintro (rfl | rfl)
    all_goals
      refine ⟨fun a => if a = addr then SymReg.SimpCons.assignTree (members addr) combined
        else members a, ?_, by simp⟩
      simp [SymReg.SimpCons.processPopulation, SymReg.SimpCons.optimizeMember, hs, hc]

/-- Every restart has the original dimensionality; zero coordinates receive a
fresh normal draw rather than a multiplicative zero. -/
def restartShapeAndZero : Prop :=
  ∀ (C : Type) (ops : ScalarOps C) (x0 : List C) noise (zero : C),
    (restartPoint ops x0 noise).length = x0.length ∧
    (ops.isZero zero = true → ∀ draw, perturb ops zero draw = draw)

theorem restartShapeAndZero_holds : restartShapeAndZero := by
  intro C ops x0 noise zero
  constructor
  · simp [restartPoint]
  · intro hz draw; simp [perturb, hz]

example : (jfOps .float64).isZero (.fin 0) = true := by decide

/-- For nonzero finite real parameters the relative perturbation is 1+noise/2.
The noise is not added directly to a nonzero coordinate. -/
def restartRelativeScale : Prop :=
  ∀ (precision : SymReg.Loss.LossPrecision) (x noise : JF),
    x ≠ .fin 0 →
    perturb (jfOps precision) x noise =
      precision.round (JF.mul x (precision.round (JF.add (.fin 1)
        (precision.round (JF.mul (.fin (1 / 2)) noise)))))

theorem restartRelativeScale_holds : restartRelativeScale := by
  intro precision x noise hx
  simp [perturb, jfOps, hx]

example : (2 : Rat) ≠ 0 := by decide

/-- A non-improving restart leaves the entire previous result intact, including
its minimizer. A strictly smaller minimum selects the entire candidate. -/
def restartStrictSelection : Prop :=
  ∀ (C : Type) (best candidate : OptimResult C),
    (less candidate.minimum best.minimum = true → chooseResult best candidate = candidate) ∧
    (less candidate.minimum best.minimum = false → chooseResult best candidate = best) ∧
    (candidate.minimum = best.minimum → chooseResult best candidate = best)

theorem restartStrictSelection_holds : restartStrictSelection := by
  intro C best candidate
  refine ⟨fun h => by simp [chooseResult, h], fun h => by simp [chooseResult, h], ?_⟩
  intro h
  simp [chooseResult, h, SymReg.HofMig.less_self]

example : (OptimResult.mk (C := JF) [] (.fin 1) 0 0 0 0).minimum =
    (OptimResult.mk (C := JF) [] (.fin 1) 1 0 0 0).minimum := rfl

/-- A NaN initial minimum cannot be replaced by any restart. A NaN restart
minimum likewise never replaces an existing result. -/
def restartNaNBarrier : Prop :=
  ∀ (C : Type) (best candidate : OptimResult C),
    best.minimum = .nan ∨ candidate.minimum = .nan → chooseResult best candidate = best

theorem restartNaNBarrier_holds : restartNaNBarrier := by
  intro C best candidate h
  rcases h with h | h
  · cases hc : candidate.minimum <;>
      simp [chooseResult, less, DynExpr.Expressions.Sampling.greater, h, hc]
  · cases hb : best.minimum <;>
      simp [chooseResult, less, DynExpr.Expressions.Sampling.greater, h, hb]

example : (OptimResult.mk (C := JF) [] .nan 0 0 0 0).minimum = JF.nan := rfl

/-- Strict selection accepts ordered improvements even at infinite extrema. -/
def nonfiniteComparisons : Prop :=
  ∀ (q : Rat) (best candidate : OptimResult JF),
    (best.minimum = .posInf → candidate.minimum = .fin q → chooseResult best candidate = candidate) ∧
    (best.minimum = .fin q → candidate.minimum = .negInf → chooseResult best candidate = candidate) ∧
    (best.minimum = .nan ∨ candidate.minimum = .nan ∨ best.minimum = .negInf →
      chooseResult best candidate = best)

theorem nonfiniteComparisons_holds : nonfiniteComparisons := by
  intro q best candidate
  refine ⟨?_, ?_, ?_⟩
  · intro hb hc; simp [chooseResult, less, DynExpr.Expressions.Sampling.greater, hb, hc]
  · intro hb hc; simp [chooseResult, less, DynExpr.Expressions.Sampling.greater, hb, hc]
  · rintro (hb | hc | hb)
    · exact restartNaNBarrier_holds JF best candidate (.inl hb)
    · exact restartNaNBarrier_holds JF best candidate (.inr hc)
    · cases hc : candidate.minimum <;>
        simp [chooseResult, less, DynExpr.Expressions.Sampling.greater, hb, hc]

def rejectedRestores : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) svc x0 baseline best evals fraction member
    (s : EvalState C H) current read result after,
    less best.minimum baseline = false → svc.tree member s = (.ok current, read) →
    writeParameters {e with tree := current} x0 read = (result, after) →
    finish e svc x0 baseline best evals fraction member s = ((fun _ => evals) <$> result, after)

theorem rejectedRestores_holds : rejectedRestores := by
  intro C H R e svc x0 baseline best evals fraction member s current read result after h ht hw
  cases result <;> simp [finish, h, ht, hw]

def acceptedWriteback : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) svc x0 baseline best evals fraction member
    (s : EvalState C H) current read written loss evaluated,
    less best.minimum baseline = true → svc.tree member s = (.ok current, read) →
    writeParameters {e with tree := current} best.minimizer read = (.ok (), written) →
    evaluate e true best.minimizer written = (.ok loss, evaluated) →
    ∀ err after, svc.assignLoss member loss evaluated = (.error err, after) →
    finish e svc x0 baseline best evals fraction member s = (.error err, after)

theorem acceptedWriteback_holds : acceptedWriteback := by
  intro C H R e svc x0 baseline best evals fraction member s current read written loss evaluated
    h ht hw he err after ha
  simp [finish, h, ht, hw, he, ha]

def memberIdentity : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) svc x0 baseline best evals fraction member
    (s after : EvalState C H) count,
    finish e svc x0 baseline best evals fraction member s = (.ok count, after) →
    ∀ before current, s.members member = some before → after.members member = some current →
      before.objectId = current.objectId

def acceptanceAccounting : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) svc x0 baseline best evals fraction member
    (s after : EvalState C H) count,
    finish e svc x0 baseline best evals fraction member s = (.ok count, after) →
    count = if less best.minimum baseline then round64 (evals + fraction) else evals

theorem acceptanceAccounting_holds : acceptanceAccounting := by
  intro C H R e svc x0 baseline best evals fraction member s after count h
  by_cases hc : less best.minimum baseline = true
  · simp only [finish, hc, if_true, effect_bind, effect_pure] at h
    repeat' (split at h <;> try cases h)
    all_goals simp_all
  · have hf : less best.minimum baseline = false := Bool.eq_false_iff.mpr hc
    simp only [finish, hf, Bool.false_eq_true, ↓reduceIte, effect_bind, effect_pure] at h
    repeat' (split at h <;> try cases h)
    all_goals simp_all

def acceptedScoresFresh : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) x0 baseline best evals fraction member
    (s after : EvalState C H) count (m : Member) (loss : H → JF)
    (complexity : Nat → H → Int) (cost : JF → Int → JF) birth,
    (∀ st, e.loss e.tree true st = (.ok (loss st.heap), st)) →
    less best.minimum baseline = true →
    let svc := stockFinishServices (fun tree => inspectEffect (fun st => complexity tree st.heap))
      (fun raw n => pure (cost raw n)) birth
    finish e svc x0 baseline best evals fraction member s = (.ok count, after) →
    after.members member = some m →
    m.loss = loss after.heap ∧ m.cost = cost (loss after.heap) (complexity m.tree after.heap)

theorem acceptedScoresFresh_refuted : ¬ acceptedScoresFresh := by
  intro law
  let loss := fun (constant : Nat) => if constant = 3 then JF.fin 0 else .fin 4
  let complexity := fun (_ : Nat) (constant : Nat) => if constant < 2 then (1 : Int) else 3
  let cost := fun (raw : JF) (size : Int) => round64 (raw + .fin (Rat.ofInt size / 8))
  let m : Member := {
    cost := .fin 4, loss := .fin 4, complexity := 1, tree := 0,
    objectId := 1, treeId := 2, parent := 1 }
  let before : EvalState Nat Nat := { heap := 1, members := fun _ => some m }
  let e : Evaluator Nat Nat Unit :=
    ⟨0, (), fun _ x _ => modifyEffect (fun s => {s with heap := x.headD 0}),
      fun _ _ => inspectEffect (fun s => loss s.heap)⟩
  let birth : Effect (EvalState Nat Nat) Int := pure 2
  let svc := stockFinishServices (fun tree => inspectEffect (fun s => complexity tree s.heap))
    (fun raw n => pure (cost raw n)) birth
  let best : OptimResult Nat := ⟨[3], .fin 0, 1, 0, 0, 0⟩
  let out : Member := {m with loss := .fin 0, cost := cost (.fin 0) 1, birth := 2}
  let after : EvalState Nat Nat :=
    { before with
      heap := 3
      log := [.write 0 [3], .write 0 [3], .loss 0 true]
      members := fun a => if a = 0 then some out else some m }
  have improves : less best.minimum (.fin 4) = true := by decide
  have hr : finish e svc [1] (.fin 4) best (.fin 1) (.fin 1) 0 before =
      (.ok (round64 (.fin 1 + .fin 1)), after) := by
    simp [finish, e, svc, stockFinishServices, readAllocatedMember, updateAllocatedMember,
      before, m, memberComplexity, loss, improves, best,
      writeParameters, evaluate, callContext, birth, after, out, funext_iff] <;>
      (intro a; by_cases ha : a = 0 <;> simp [ha])
  have bad := (law Nat Nat Unit e [1] (.fin 4) best (.fin 1) (.fin 1) 0 before after
    (round64 (.fin 1 + .fin 1)) out loss complexity cost birth
    (by intro st; rfl) improves hr rfl).2
  have unequal : out.cost ≠ cost (loss after.heap) (complexity out.tree after.heap) := by decide +kernel
  exact unequal bad

/-- Batch counts include repeated selections; empty full datasets are allowed. -/
def batchingFraction : Prop :=
  ∀ (S : Type) selected (length : Nat → S → Jl Int × S) count (s : S),
    datasetFraction none length count s = (.ok (.fin 1), s) ∧
    (∀ e after, length selected s = (.error e, after) →
      datasetFraction (some selected) length count s = (.error e, after)) ∧
    (∀ n after, length selected s = (.ok n, after) →
      datasetFraction (some selected) length count s =
        (.ok (round64 (floatInt n / floatInt (count after))), after))

theorem batchingFraction_holds : batchingFraction := by
  intro S selected length count s
  exact ⟨rfl, fun e after h => by simp [datasetFraction, h],
    fun n after h => by simp [datasetFraction, h]⟩

/-- When `autodiff_backend === nothing` and a pooled `eval_context` is supplied,
`_optimize_constants` reuses it without calling `create_eval_context`; when
`supplied` is `none`, it allocates via `create_eval_context`; with AD present it
passes `none` (`src/ConstantOptimization.jl:199-207`). -/
def contextReusePooled : Prop :=
  ∀ (S : Type) (ctx : SymReg.Loss.Context) (ad : Nat)
    (create : Int → Effect S (Option SymReg.Loss.Context)) (s : S),
    initialContextPooled none (some ctx) create s = (.ok (some ctx), s) ∧
    initialContextPooled none none create s = create 0 s ∧
    initialContextPooled (some ad) (some ctx) create s = (.ok none, s)

theorem contextReusePooled_holds : contextReusePooled := by
  intro S ctx ad create s
  exact ⟨rfl, rfl, rfl⟩

/-- When `!has_units(dataset)` and no custom loss function is supplied, accepting
an improved optimum sets `member.loss = result.minimum` directly without an extra
regularized evaluation or an extra `eval_fraction` increment; otherwise it behaves
identically to `finish` (`src/ConstantOptimization.jl:251-267`). -/
def skipRedundantFinalEval : Prop :=
  ∀ (C H R : Type) (e : Evaluator C H R) svc x0 baseline best evals fraction member
    (s : EvalState C H),
    finishFast e svc false x0 baseline best evals fraction member s =
      finish e svc x0 baseline best evals fraction member s ∧
    (∀ current read written assignedLoss score scored assignedCost birth born final,
      less best.minimum baseline = true →
      svc.tree member s = (.ok current, read) →
      writeParameters {e with tree := current} best.minimizer read = (.ok (), written) →
      svc.assignLoss member best.minimum written = (.ok (), assignedLoss) →
      svc.cost member assignedLoss = (.ok score, scored) →
      svc.assignCost member score scored = (.ok (), assignedCost) →
      svc.birth assignedCost = (.ok birth, born) →
      svc.assignBirth member birth born = (.ok (), final) →
      finishFast e svc true x0 baseline best evals fraction member s = (.ok evals, final))

theorem skipRedundantFinalEval_holds : skipRedundantFinalEval := by
  intro C H R e svc x0 baseline best evals fraction member s
  constructor
  · cases hc : less best.minimum baseline <;> simp [finishFast, finish, hc]
  · intro current read written assignedLoss score scored assignedCost birth born final
      himp htree hwr hloss hcost hacost hbirth habirth
    simp [finishFast, himp, htree, hwr, hloss, hcost, hacost, hbirth, habirth]

example : less (.fin 1) (.fin 2) = true := by decide

end SymReg.ConstOpt
