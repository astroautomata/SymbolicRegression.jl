import SymReg.SimpCons.Simplification
import SymReg.Loss.Core
import SymReg.Options.Struct
import DynExpr.NodeBase.TraverseCopy

namespace SymReg.SimpCons
open DynExpr DynExpr.Simplify SymReg.HeapLemmas
open DynExpr.Expressions.Sampling (RNG draw)

/-- Population fields read or written in `src/Mutate.jl:895-927` and
`src/SingleIteration.jl:82-123`. Tree roots retain their heap identity. -/
structure Member (E L : Type) where
  tree : E
  cost : L
  loss : L
  complexity : Int
  ref : Nat
  parent : Nat
  birth : Nat

-- Source: src/PopMember.jl:97-140,170-179; src/Mutate.jl:380-397;
-- src/Migration.jl:33-34,41-43; src/HallOfFame.jl:131.
open DynExpr.NodeBase in
def sharedMemberStockCopy : Prop :=
  ∀ (T : Type) (g h : SGraph T) (D fuel source retained copyRoot : Nat)
    (t : Tree T) (isGraph breakSharing : Bool),
    g.view.unfold fuel source = some t → t.WF D (fun _ => 255) 65535 →
    (∀ a, Graph.Reachable g.view retained a → a < g.next) →
    copyNodeH g D isGraph breakSharing fuel source = .ok (copyRoot, h) →
    (∀ a, Graph.Reachable g.view retained a → h.cells a = g.cells a) ∧
    (∀ a, Graph.Reachable h.view retained a → ¬ Graph.Reachable h.view copyRoot a)

private theorem memberPathAppend {T : Type} {g : Graph T} {a b c : Addr}
    {p q : List Nat} (first : Graph.Path g a p b) (second : Graph.Path g b q c) :
    Graph.Path g a (p ++ q) c := by
  induction first with
  | nil _ => exact second
  | cons hread hchild _ ih => exact .cons hread hchild (ih second)

private theorem oldMemberPath {T : Type} {g h : Graph T}
    (frontier : Nat) (before : ∀ a, a < frontier → h.cells a = g.cells a)
    {root : Addr} (closed : ∀ a, Graph.Reachable g root a → a < frontier) :
    ∀ {a p b}, Graph.Reachable g root a → Graph.Path h a p b → Graph.Reachable g root b := by
  intro a p b reachable path
  induction path with
  | nil _ => exact reachable
  | @cons a c b i p cell ha hi _ ih =>
    have oldCell : g.cells a = some cell := (before a (closed a reachable)) ▸ ha
    obtain ⟨prior, hp⟩ := reachable
    exact ih ⟨prior ++ [i], memberPathAppend hp (.cons oldCell hi (.nil c))⟩

open DynExpr.NodeBase in
theorem sharedMemberStockCopy_holds : sharedMemberStockCopy := by
  intro T g h D fuel source retained copyRoot t isGraph breakSharing hu hw hclosed hcopy
  obtain ⟨r, h', run, before, _, hfresh, _, _⟩ :=
    copy_node_heap_holds T g D fuel source t isGraph breakSharing hu hw
  rw [hcopy] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
  refine ⟨fun a ha => before a (hclosed a ha), ?_⟩
  intro a ha hc
  obtain ⟨p, hp⟩ := ha
  have old := oldMemberPath g.next (fun b hb => by
    simp [SGraph.view, before b hb]) hclosed ⟨[], .nil retained⟩ hp
  exact (Nat.not_lt_of_ge (hfresh a hc)) (hclosed a old)

private theorem binaryEnum_counts (o : CEnum JF) : o.toOpEnum.nops = o.nops := by
  funext d
  rcases d with _ | _ | _ | d <;> simp [CEnum.toOpEnum, OpEnum.nops, CEnum.nops]

-- Source: src/SingleIteration.jl:94-109.
def sharedMemberSimplification : Prop := sharedMemberStockCopy ∧
  ∀ (g h : Graph JF) (o : CEnum JF) (fuel nf root retained : Nat) (t : Tree JF)
    (out : Ex JF Unit),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    (∀ a, Graph.Reachable g retained a → ¬ Graph.Reachable g root a) →
    simplifyMemberTree (⟨.expression, root, o, ()⟩ : Ex JF Unit) none fuel g = .ok (out, h) →
    ∀ a, Graph.Reachable g retained a → h.cells a = g.cells a

theorem sharedMemberSimplification_holds : sharedMemberSimplification := by
  refine ⟨sharedMemberStockCopy_holds, ?_⟩
  intro g h o fuel nf root retained t out hu hw ha hdisjoint hrun
  have hw' : t.WF 2 o.toOpEnum.nops nf := by rwa [binaryEnum_counts]
  obtain ⟨mid, u, fold, hu', hw', _⟩ :=
    simplify_wf_proof JF o.toOpEnum 2 nf fuel g root t hu hw'
  obtain ⟨mid', fold', noAlias⟩ :=
    simplify_preserves_noalias_proof JF o.toOpEnum 2 nf fuel g root t hu (by rwa [binaryEnum_counts]) ha
  rw [fold] at fold'
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj fold')
  obtain ⟨_, frame, reaches⟩ :=
    simplifyTree_frame o.toOpEnum 2 nf fuel hu (by rwa [binaryEnum_counts]) fold
  have hwu : u.WF 2 o.nops nf := by simpa only [binaryEnum_counts] using hw'
  simp only [simplifyMemberTree, composableSimplify, patchSimplify, Option.getD_none, fold,
    bind, Except.bind, pure, Except.pure, composableCombine, patchCombineDeprecated, patchCombine] at hrun
  cases combine : combineOps o fuel mid root with
  | error e => simp [combine] at hrun
  | ok value =>
    obtain ⟨r, final⟩ := value
    simp [combine] at hrun
    obtain ⟨_, rfl⟩ := hrun
    have hframe := (combineOps_frame o hu' hwu noAlias combine).1
    intro a ha
    exact (hframe a (fun hr => hdisjoint a ha (reaches a hr))).trans (frame a (hdisjoint a ha))

/-- `MutationResult` fields returned by `src/Mutate.jl:927`. -/
structure SimplifyResult (E L : Type) where
  member : Member E L
  numEvals : Nat := 0
  returnImmediately : Bool := true
  success : Bool := true

/-- `mutate!(..., ::SimplifyMutation, ...)`, `src/Mutate.jl:895-927`.
The simplifier's returned wrapper is discarded, the combiner's is used, complexity
and cost are recomputed, parent loss is reused, and the child returns immediately.
External computations remain arbitrary throwing functions; allocation supplies birth/ref. -/
def mutateSimplify {E L G : Type} (enabled : Bool)
    (simplify combine : E → G → Jl (E × G)) (complexity : E → G → Jl Int)
    (lossToCost : L → E → Int → Jl L) (parent : Member E L) (newTree : E)
    (parentRef newRef birth : Nat) (g : G) : Jl (SimplifyResult E L × G) := do
  if !enabled then throw (.assertionError "options.should_simplify")
  let (_, g) ← simplify newTree g
  let (tree, g) ← combine newTree g
  let n ← complexity tree g
  let cost ← lossToCost parent.loss tree n
  pure (⟨⟨tree, cost, parent.loss, n, newRef, parentRef, birth⟩, 0, true, true⟩, g)

/-- The successful immediate-return branch of `_next_generation`,
`src/Mutate.jl:419-438`, precedes its constraint check at line 450. -/
def acceptMutation {E L : Type} (r : SimplifyResult E L)
    (check : E → Jl Bool) : Jl Bool :=
  if r.returnImmediately && r.success then pure true
  else if r.returnImmediately then pure false
  else if r.success then check r.member.tree else pure false

/-- Assigning `.tree`, `src/SingleIteration.jl:99`, invalidates the complexity cache
via `src/PopMember.jl:44-57`; cost and loss retain their previous values. -/
def assignTree {E L : Type} (m : Member E L) (tree : E) : Member E L :=
  { m with tree := tree, complexity := -1 }

/-- The per-member work in `src/SingleIteration.jl:94-106`, in order. An
optimizer count occupies a Float64 slot in the population's array. -/
def optimizeMember {E L G : Type} (shouldSimplify shouldOptimize selected : Bool)
    (simplify combine : E → G → Jl (E × G))
    (optimize : Member E L → G → Jl (Member E L × JF × G))
    (m : Member E L) (g : G) : Jl (Member E L × JF × G) := do
  let (m, g) ← if shouldSimplify then do
    let (tree, g) ← simplify m.tree g
    let (tree, g) ← combine tree g
    pure (assignTree m tree, g)
    else pure (m, g)
  if shouldOptimize && selected then optimize m g else pure (m, .fin 0, g)

abbrev MemberStore (E L : Type) := Nat → Member E L

-- Source: src/LossFunctions.jl:226-246; src/PopMember.jl:187-200
-- result_loss = eval_loss(get_tree_from_member(member), dataset, options; eval_context)
-- complexity == -1 && return recompute_complexity!(member, options; break_sharing)
-- return cost, result_loss
def evaluatePopulationMember (full : SymReg.Loss.Basic) (options : SymReg.Loss.Options)
    (addr : Nat) (store : MemberStore SymReg.Loss.Expr JF) :
    Jl (JF × JF) × MemberStore SymReg.Loss.Expr JF :=
  let member := store addr
  match SymReg.Loss.evalLoss member.tree ⟨full, none⟩ options with
  | .error e => (.error e, store)
  | .ok (loss, _) =>
    let size := if member.complexity = -1 then options.complexity (.direct member.tree)
      else .ok member.complexity
    match size with
    | .error e => (.error e, store)
    | .ok n =>
      let after := if member.complexity = -1 then
        fun a => if a = addr then { member with complexity := n } else store a
        else store
      let cost := SymReg.Loss.lossToCost loss full.useBaseline full.baselineLoss
        (.population member.tree n) options (some n) full.lossPrecision
      (cost.map (fun c => (c, loss)), after)

-- Source: src/Population.jl:236-250
/-
    need_recalculate = use_batching(options, dataset)
    num_evals = 0.0
    if need_recalculate
        for member in 1:(pop.n)
            cost, loss = eval_cost(dataset, pop.members[member], options)
            pop.members[member].cost = cost
            pop.members[member].loss = loss
        end
        num_evals += pop.n
    end
    return (pop, num_evals)
-/
private def finalizeSlots {E L : Type}
    (evaluate : Nat → MemberStore E L → Jl (L × L) × MemberStore E L) :
    List Nat → MemberStore E L → Jl Unit × MemberStore E L
  | [], store => (.ok (), store)
  | addr :: slots, store =>
    match evaluate addr store with
    | (.error e, after) => (.error e, after)
    | (.ok (cost, loss), after) =>
      finalizeSlots evaluate slots
        (fun a => if a = addr then { after addr with cost, loss } else after a)

def finalizePopulation {E L : Type} (mode : SymReg.Options.BatchMode) (n : Int) (hasBatch : Bool)
    (evaluate : Nat → MemberStore E L → Jl (L × L) × MemberStore E L)
    (slots : List Nat) (store : MemberStore E L) : Jl (List Nat × JF) × MemberStore E L :=
  if SymReg.Options.useBatching mode n hasBatch then
    let (result, after) := finalizeSlots evaluate slots store
    (result.map (fun _ => (slots, SymReg.Loss.floatCount .float64 slots.length)), after)
  else (.ok (slots, .fin 0), store)

-- Source: src/SingleIteration.jl:85-86
-- array_num_evals = zeros(Float64, pop.n)
-- do_optimization = rand(pop.n) .< options.optimizer_probability
def optimizationMask (probability : JF) : Nat → RNG → List Bool × RNG
  | 0, rng => ([], rng)
  | n + 1, rng =>
    let u := draw rng
    let tail := optimizationMask probability n u.2
    (DynExpr.Expressions.Sampling.greater probability (.fin u.1) :: tail.1, tail.2)

/-- The member loop of `src/SingleIteration.jl:94-107`, retaining order and the
initial optimization mask while threading all node-heap effects. -/
def processPopulation {E L G : Type}
    (step : Bool → Member E L → G → Jl (Member E L × JF × G)) :
    List Nat → List Bool → MemberStore E L → G → Jl (MemberStore E L × List JF × G)
  | [], _, members, g => pure (members, [], g)
  | addr :: slots, selected :: mask, members, g => do
    let (m, n, g) ← step selected (members addr) g
    let members := fun a => if a = addr then m else members a
    let (members, ns, g) ← processPopulation step slots mask members g
    pure (members, n :: ns, g)
  | _ :: _, [], _, _ => throw .boundsError

abbrev ReferenceTrace := Nat × Nat × Nat × Bool

-- Source: src/SingleIteration.jl:112-121
-- for j in 1:(pop.n)
--     old_ref = pop.members[j].ref
--     new_ref = generate_reference()
--     pop.members[j].parent = old_ref
--     pop.members[j].ref = new_ref
--     trace_optimization!(
--         trace, pop.members[j], old_ref, new_ref, do_optimization[j], options
--     )
-- end
def refreshReferences {E L : Type} (fresh : Nat → Nat) (mask : Nat → Bool) :
    Nat → List Nat → MemberStore E L → MemberStore E L × List ReferenceTrace
  | _, [], store => (store, [])
  | i, addr :: addrs, store =>
    let member := store addr
    let next := fresh i
    let update := fun a => if a = addr then { member with parent := member.ref, ref := next } else store a
    let (store', trace) := refreshReferences fresh mask (i + 1) addrs update
    (store', (addr, member.ref, next, mask i) :: trace)

/-- `optimize_and_simplify_population`, `src/SingleIteration.jl:82-123`.
The dataset choice runs after all selection draws; its argument records how many
draws have been consumed. `step` receives that same dataset for every member, while
`evaluate` uses full data. The state can include the RNG and mutable node heap. -/
def optimizeAndSimplifyPopulation {E L G Data : Type} (rng : RNG) (probability : JF)
    (chooseDataset : RNG → G → Jl (Data × G))
    (step : Data → Bool → Member E L → G → Jl (Member E L × JF × G))
    (batching : SymReg.Options.BatchMode) (sampleCount : Int) (hasBatch : Bool)
    (evaluate : Nat → MemberStore E L → Jl (L × L) × MemberStore E L)
    (fresh : Nat → Nat) (slots : List Nat) (members : MemberStore E L) (g : G) :
    Jl (MemberStore E L × JF × G × List ReferenceTrace) := do
  let (mask, rng) := optimizationMask probability slots.length rng
  let (dataset, g) ← chooseDataset rng g
  let (processed, counts, g) ← processPopulation (step dataset) slots mask members g
  let total := SymReg.Loss.pairwiseSum .float64 counts
  let (result, store) := finalizePopulation batching sampleCount hasBatch evaluate slots processed
  let (_, nFinal) ← result
  let (store, trace) := refreshReferences fresh (fun i => mask[i]?.getD false) 0 slots store
  pure (store, SymReg.Loss.LossPrecision.round .float64
    (total + nFinal), g, trace)

/-- Simplification does no loss evaluation and returns a child carrying the parent's
loss, the supplied new lineage and the newly computed complexity/cost. -/
def mutationBookkeeping : Prop :=
  ∀ (E L G : Type) enabled simplify combine complexity lossToCost
    (parent : Member E L) newTree parentRef newRef birth (g : G) result g',
    mutateSimplify enabled simplify combine complexity lossToCost parent newTree
      parentRef newRef birth g = .ok (result, g') →
    result.member.loss = parent.loss ∧ result.member.parent = parentRef ∧
      result.member.ref = newRef ∧ result.member.birth = birth ∧
      result.numEvals = 0 ∧ result.returnImmediately = true ∧ result.success = true ∧
      complexity result.member.tree g' = .ok result.member.complexity ∧
      lossToCost parent.loss result.member.tree result.member.complexity = .ok result.member.cost

theorem mutationBookkeeping_holds : mutationBookkeeping := by
  intro E L G enabled simplify combine complexity lossToCost parent newTree parentRef newRef birth g result g' h
  cases enabled with
  | false =>
    change Except.error (JlError.assertionError "options.should_simplify") = .ok (result, g') at h
    cases h
  | true =>
    cases hs : simplify newTree g with
    | error e => simp [mutateSimplify, hs] at h
    | ok p =>
      rcases p with ⟨_, g1⟩
      cases hc : combine newTree g1 with
      | error e => simp [mutateSimplify, hs, hc, ok_bind] at h
      | ok p =>
        rcases p with ⟨tree, g2⟩
        cases hn : complexity tree g2 with
        | error e => simp [mutateSimplify, hs, hc, hn, ok_bind] at h
        | ok n =>
          cases hl : lossToCost parent.loss tree n with
          | error e => simp [mutateSimplify, hs, hc, hn, hl, ok_bind] at h
          | ok cost =>
            simp [mutateSimplify, hs, hc, hn, hl, ok_bind, pure_ok] at h
            rcases h with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hn, hl⟩

/-- A successful immediate mutation bypasses the size/operator constraint check. -/
def immediateBypass : Prop :=
  ∀ (E L : Type) (m : Member E L) check n,
    acceptMutation (⟨m, n, true, true⟩ : SimplifyResult E L) check = .ok true

theorem immediateBypass_holds : immediateBypass := by
  intro E L m check n
  rfl

/-- Population simplification invalidates only complexity and replaces the tree. -/
def populationCacheReset : Prop :=
  ∀ (E L : Type) (m : Member E L) tree,
    (assignTree m tree).complexity = -1 ∧ (assignTree m tree).cost = m.cost ∧
      (assignTree m tree).loss = m.loss ∧ (assignTree m tree).ref = m.ref

theorem populationCacheReset_holds : populationCacheReset := by
  intro E L m tree
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Without batching, finalization leaves all recorded loss/cost values untouched. -/
def finalizeUnbatched : Prop :=
  ∀ (E L : Type) mode n hasBatch evaluate slots (store : MemberStore E L),
    SymReg.Options.useBatching mode n hasBatch = false →
    finalizePopulation mode n hasBatch evaluate slots store = (.ok (slots, .fin 0), store)

theorem finalizeUnbatched_holds : finalizeUnbatched := by
  intro E L mode n hasBatch evaluate slots store h
  simp [finalizePopulation, h]

/-- The stock member fields hold the earlier score even when the evaluation
of a later alias fails, and its cache is read from the post-evaluation store. -/
def finalizeRepeatedFailure : Prop :=
  ∀ (E L : Type) n hasBatch (store : MemberStore E L) (addr : Nat) (cost loss : L)
    (cache : Int) (err : JlError),
    let evaluate := fun (a : Nat) (s : MemberStore E L) =>
      if (s a).complexity = -1 then
        (.ok (cost, loss), fun b => if b = a then { s b with complexity := cache } else s b)
      else (.error err, s)
    cache ≠ -1 → (store addr).complexity = -1 →
    let (result, after) := finalizePopulation .enabled n hasBatch evaluate [addr, addr] store
    result = .error err ∧
    after addr = { store addr with complexity := cache, cost, loss } ∧
    ∀ other, other ≠ addr → after other = store other

theorem finalizeRepeatedFailure_holds : finalizeRepeatedFailure := by
  unfold finalizeRepeatedFailure
  intro E L n hasBatch store addr cost loss cache err
  dsimp only
  intro hc hs
  simp [finalizePopulation, SymReg.Options.useBatching, SymReg.Options.readBatching,
    finalizeSlots, hs, hc, Except.map]
    <;> intro other h <;> simp [h]

private inductive StockScores (full : SymReg.Loss.Basic) (options : SymReg.Loss.Options) :
    List Nat → MemberStore SymReg.Loss.Expr JF → List (Nat × (JF × JF)) → Prop
  | nil (store) : StockScores full options [] store []
  | cons {addr slots store cached scores cost loss}
      (score : evaluatePopulationMember full options addr store = (.ok (cost, loss), cached))
      (rest : StockScores full options slots
        (fun a => if a = addr then { cached addr with cost, loss } else cached a) scores) :
      StockScores full options (addr :: slots) store ((addr, (cost, loss)) :: scores)

private theorem StockScores.keys {full options slots store scores}
    (h : StockScores full options slots store scores) :
    scores.map Prod.fst = slots := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

def finalizeBatched : Prop := finalizeRepeatedFailure ∧
  ∀ (full : SymReg.Loss.Basic) options mode n hasBatch
    (slots : List Nat) (store after : MemberStore SymReg.Loss.Expr JF) visited count,
    SymReg.Options.useBatching mode n hasBatch = true →
    finalizePopulation mode n hasBatch (evaluatePopulationMember full options) slots store =
      (.ok (visited, count), after) →
    visited = slots ∧ count = SymReg.Loss.floatCount .float64 slots.length ∧
    (∀ a, a ∉ slots → after a = store a) ∧
    (∀ a ∈ slots, (store a).complexity ≠ -1 →
      (after a).complexity = (store a).complexity) ∧
    ∃ scores, StockScores full options slots store scores ∧
      (∀ a ∈ slots, ((scores.reverse.find? fun reply => reply.1 == a).map Prod.snd) =
        some ((after a).cost, (after a).loss))

private theorem finalizeStockFrame (full : SymReg.Loss.Basic) (options : SymReg.Loss.Options)
    (slots : List Nat) (store : MemberStore SymReg.Loss.Expr JF) (a : Nat) :
    (a ∉ slots → (finalizeSlots (evaluatePopulationMember full options) slots store).2 a = store a) ∧
    ((store a).complexity ≠ -1 →
      ((finalizeSlots (evaluatePopulationMember full options) slots store).2 a).complexity =
        (store a).complexity) := by
  induction slots generalizing store with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons addr slots ih =>
    have step : ∀ s' : MemberStore SymReg.Loss.Expr JF,
        (a ≠ addr → s' a = store a) →
        ((store a).complexity ≠ -1 → (s' a).complexity = (store a).complexity) →
        (a ∉ addr :: slots →
          (finalizeSlots (evaluatePopulationMember full options) slots s').2 a = store a) ∧
        ((store a).complexity ≠ -1 →
          ((finalizeSlots (evaluatePopulationMember full options) slots s').2 a).complexity =
            (store a).complexity) := by
      intro s' hframe hcache
      refine ⟨?_, ?_⟩
      · intro h
        have ha : a ≠ addr := fun he => h (he ▸ List.mem_cons_self)
        exact ((ih s').1 (fun hm => h (List.mem_cons_of_mem _ hm))).trans (hframe ha)
      · intro h
        exact ((ih s').2 (fun he => h ((hcache h).symm.trans he))).trans (hcache h)
    have evaluateFrame :
        (a ≠ addr → (evaluatePopulationMember full options addr store).2 a = store a) ∧
        ((store a).complexity ≠ -1 →
          ((evaluatePopulationMember full options addr store).2 a).complexity =
            (store a).complexity) := by
      simp only [evaluatePopulationMember]
      cases hLoss : SymReg.Loss.evalLoss (store addr).tree ⟨full, none⟩ options with
      | error e => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | ok loss =>
        by_cases hc : (store addr).complexity = -1
        · simp only [hc, ↓reduceIte]
          cases hn : options.complexity (.direct (store addr).tree) with
          | error e => exact ⟨fun _ => rfl, fun _ => rfl⟩
          | ok n =>
            constructor
            · intro ha; simp [ha]
            · intro hw
              have ha : a ≠ addr := fun he => hw (he ▸ hc)
              simp [ha]
        · simp [hc]
    simp only [finalizeSlots]
    cases he : evaluatePopulationMember full options addr store with
    | mk computation after =>
      rw [he] at evaluateFrame
      cases computation with
      | error e =>
        exact ⟨fun h => evaluateFrame.1 (fun eq => h (eq ▸ List.mem_cons_self)), evaluateFrame.2⟩
      | ok pair =>
        rcases pair with ⟨cost, loss⟩
        apply step
        · intro ha
          simpa [ha] using evaluateFrame.1 ha
        · intro h
          by_cases ha : a = addr <;> simpa [ha] using evaluateFrame.2 h

private theorem finalizeStockScores (full : SymReg.Loss.Basic) (options : SymReg.Loss.Options)
    (slots : List Nat) (store after : MemberStore SymReg.Loss.Expr JF)
    (h : finalizeSlots (evaluatePopulationMember full options) slots store = (.ok (), after)) :
    ∃ scores, StockScores full options slots store scores ∧
      ∀ a ∈ slots, ((scores.reverse.find? fun reply => reply.1 == a).map Prod.snd) =
        some ((after a).cost, (after a).loss) := by
  induction slots generalizing store after with
  | nil => exact ⟨[], .nil _, by simp⟩
  | cons addr slots ih =>
    simp only [finalizeSlots] at h
    cases he : evaluatePopulationMember full options addr store with
    | mk outcome cached =>
      rw [he] at h
      cases outcome with
      | error e => cases h
      | ok pair =>
        rcases pair with ⟨cost, loss⟩
        let next := fun a => if a = addr then { cached addr with cost, loss } else cached a
        change finalizeSlots (evaluatePopulationMember full options) slots next = _ at h
        obtain ⟨scores, hsc, hlast⟩ := ih next after h
        refine ⟨(addr, (cost, loss)) :: scores, .cons he hsc, ?_⟩
        intro a ha
        rw [List.reverse_cons, List.find?_append]
        by_cases hs : a ∈ slots
        · have hfound := hlast a hs
          cases hf : scores.reverse.find? (fun reply => reply.1 == a) with
          | none => simp [hf] at hfound
          | some p => simpa [hf] using hfound
        · have ha' : a = addr := by simpa [hs] using ha
          subst a
          have keys := hsc.keys
          have hn : scores.reverse.find? (fun reply => reply.1 == addr) = none := by
            apply List.find?_eq_none.mpr
            intro p hp
            have hmem : p.1 ∈ slots := by
              rw [← keys]
              exact List.mem_map.mpr ⟨p, List.mem_reverse.mp hp, rfl⟩
            have hne : p.1 ≠ addr := fun e => hs (e ▸ hmem)
            simpa [hne]
          have hf := (finalizeStockFrame full options slots next addr).1 hs
          rw [h] at hf
          change after addr = next addr at hf
          simp [hn, hf, next]

theorem finalizeBatched_holds : finalizeBatched := by
  refine ⟨finalizeRepeatedFailure_holds, ?_⟩
  intro full options mode n hasBatch slots store after visited count hb hr
  simp only [finalizePopulation, hb, if_true] at hr
  cases hs : finalizeSlots (evaluatePopulationMember full options) slots store with
  | mk outcome result =>
    cases outcome with
    | error e => simp [hs, Except.map] at hr
    | ok unit =>
      cases unit
      simp [hs, Except.map] at hr
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
      refine ⟨rfl, rfl, ?_, ?_, finalizeStockScores full options slots store result hs⟩
      · intro a ha
        simpa [hs] using (finalizeStockFrame full options slots store a).1 ha
      · intro a _ ha
        simpa [hs] using (finalizeStockFrame full options slots store a).2 ha

/-- Every position consumes one Float64 draw and compares in source order.
The final cursor is the one passed to dataset selection. -/
def optimizerSelections : Prop :=
  ∀ (rng : RNG) probability n,
    let (mask, after) := optimizationMask probability n rng
    after.draws = rng.draws ∧ after.cursor = rng.cursor + n ∧ mask.length = n ∧
    ∀ i, i < n → mask[i]? = some
      (DynExpr.Expressions.Sampling.greater probability (.fin (rng.draws (rng.cursor + i))))

theorem optimizerSelections_holds : optimizerSelections := by
  intro rng probability n
  induction n generalizing rng with
  | zero => exact ⟨rfl, rfl, rfl, fun _ h => by omega⟩
  | succ n ih =>
    simp only [optimizationMask]
    obtain ⟨hdraw, hcur, hlen, hmask⟩ := ih (draw rng).2
    refine ⟨hdraw, ?_, by simp [hlen], ?_⟩
    · rw [hcur]
      simp only [draw]
      omega
    · intro i hi
      cases i with
      | zero => rfl
      | succ i =>
        have hx := hmask i (by omega)
        simpa [draw, Nat.add_assoc, Nat.add_comm 1 i] using hx

/-- The old reference at a visit comes from the last earlier visit of that
object, or from the initial store if this is its first visit. -/
def populationLineage : Prop :=
  ∀ (E L : Type) (fresh : Nat → Nat) (mask : Nat → Bool) (slots : List Nat)
    (members : MemberStore E L),
    let (after, events) := refreshReferences fresh mask 0 slots members
    events.length = slots.length ∧
    (∀ i addr, slots[i]? = some addr →
      let prior := ((List.range i).reverse.find? fun j => slots[j]? == some addr)
      let previous := (prior.map fresh).getD (members addr).ref
      events[i]? = some (addr, previous, fresh i, mask i)) ∧
    (∀ addr, match ((List.range slots.length).reverse.find? fun j => slots[j]? == some addr) with
      | none => after addr = members addr
      | some j => ∃ old, events[j]? = some (addr, old, fresh j, mask j) ∧
          after addr = { members addr with parent := old, ref := fresh j })

private def lastVisit (slots : List Nat) (limit a : Nat) : Option Nat :=
  (List.range limit).reverse.find? fun j => slots[j]? == some a

private theorem lastVisit_cons (slots : List Nat) (i head a : Nat) :
    lastVisit (head :: slots) (i + 1) a =
      ((lastVisit slots i a).map Nat.succ).or (if head = a then some 0 else none) := by
  simp only [lastVisit, List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
    List.find?_append, List.find?_map, Function.comp_def, List.find?_cons,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some_beq_some, List.find?_nil]
  by_cases he : head = a
  · have hb : (head == a) = true := beq_iff_eq.mpr he
    rw [hb, ite_eq_left he]
  · have hb : (head == a) = false := by
      cases hh : head == a
      · rfl
      · exact (he (beq_iff_eq.mp hh)).elim
    rw [hb, ite_eq_right he]

private theorem lineage_from {E L : Type} (fresh : Nat → Nat) (mask : Nat → Bool)
    (slots : List Nat) (store : MemberStore E L) (base : Nat) :
    let (after, events) := refreshReferences fresh mask base slots store
    events.length = slots.length ∧
    (∀ i addr, slots[i]? = some addr →
      let previous := ((lastVisit slots i addr).map (fun j => fresh (base + j))).getD (store addr).ref
      events[i]? = some (addr, previous, fresh (base + i), mask (base + i))) ∧
    ∀ addr, match lastVisit slots slots.length addr with
      | none => after addr = store addr
      | some j => ∃ old, events[j]? = some (addr, old, fresh (base + j), mask (base + j)) ∧
          after addr = { store addr with parent := old, ref := fresh (base + j) } := by
  induction slots generalizing store base with
  | nil => simp [lastVisit, refreshReferences]
  | cons head slots ih =>
    let update := fun a => if a = head then
      { store head with parent := (store head).ref, ref := fresh base } else store a
    let tail := refreshReferences fresh mask (base + 1) slots update
    have hTail := ih update (base + 1)
    change tail.2.length = slots.length ∧ _ at hTail
    obtain ⟨hlen, hevents, hlast⟩ := hTail
    dsimp only [refreshReferences]
    change ([(head, (store head).ref, fresh base, mask base)] ++ tail.2).length = _ ∧ _
    refine ⟨by simp [hlen], ?_, ?_⟩
    · intro i addr hi
      cases i with
      | zero =>
        have hm : head = addr := Option.some.inj hi
        subst addr
        rfl
      | succ i =>
        have hi' : slots[i]? = some addr := hi
        have hprev := hevents i addr hi'
        change tail.2[i]? = _ at hprev
        change tail.2[i]? = some (addr, _, fresh (base + (i + 1)), mask (base + (i + 1)))
        rw [lastVisit_cons]
        cases h : lastVisit slots i addr with
        | some j => simpa [h, Nat.add_assoc, Nat.add_comm 1] using hprev
        | none =>
          rw [h] at hprev
          by_cases he : head = addr
          · subst addr
            simpa [update, h, Nat.add_assoc, Nat.add_comm 1] using hprev
          · simpa [update, h, he, Ne.symm he, Nat.add_assoc, Nat.add_comm 1] using hprev
    · intro addr
      simp only [List.length_cons, lastVisit_cons]
      have hh := hlast addr
      cases h : lastVisit slots slots.length addr with
      | none =>
        simp only [h] at hh
        change tail.1 addr = update addr at hh
        by_cases he : addr = head
        · subst addr
          simp only [Option.map_none, ↓reduceIte, Option.none_or, Nat.add_zero]
          exact ⟨(store head).ref, rfl, by simpa [update] using hh⟩
        · simpa [he, Ne.symm he, update] using hh
      | some j =>
        simp only [h] at hh
        obtain ⟨old, htrace, hout⟩ := hh
        simp only [Option.map_some, Option.some_or]
        refine ⟨old, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm 1] using htrace
        · change tail.1 addr = _
          rw [hout]
          by_cases he : addr = head <;> simp [update, he, Nat.add_assoc, Nat.add_comm 1]

theorem populationLineage_holds : populationLineage := by
  intro E L fresh mask slots members
  simpa [lastVisit] using lineage_from fresh mask slots members 0

example :
    let init : MemberStore Unit Unit := fun _ => ⟨(), (), (), 0, 5, 0, 7⟩
    let (after, trace) := refreshReferences (· + 10) (fun _ => false) 0 [4, 4] init
    trace = [(4, 5, 10, false), (4, 10, 11, false)] ∧
      (after 4).parent = 10 ∧ (after 4).ref = 11 :=
  ⟨rfl, rfl, rfl⟩

/-- A non-eagerly-constructed constant expression, as accepted by
`src/SingleIteration.jl:96-99`. -/
def foldingTree : Tree JF := .branch 1 [.const (.fin 1), .const (.fin 2)]

/-- Observed stored cost and size-based score after the population member step,
`src/SingleIteration.jl:94-109`. Zero data loss and parsimony one give score=size. -/
def populationScores (fuel : Nat)
    (r : Jl (Member (Ex JF Unit) Int × JF × Graph JF)) : Jl (Int × Int) := do
  let (m, _, g) ← r
  let t ← match g.unfold fuel m.tree.tree with
    | some t => pure t
    | none => throw (.errorException "tree does not unfold")
  pure (m.cost, DynExpr.NodeBase.countNodesT 2 t)

/-- For zero data loss and parsimony one, a simplified unbatched member should
retain a cost equal to its new node count, for every well-formed input. -/
def populationCostFresh : Prop :=
  ∀ (o : CEnum JF) fuel (g : Graph JF) root (t : Tree JF) selected
    (optimizer : Member (Ex JF Unit) Int → Graph JF →
      Jl (Member (Ex JF Unit) Int × JF × Graph JF)),
    g.unfold fuel root = some t → t.WF 2 o.nops 1 → Graph.NoAlias g root →
    let ex : Ex JF Unit := ⟨.expression, root, o, ()⟩
    let m : Member (Ex JF Unit) Int := ⟨ex, t.size, 0, t.size, 1, 0, 0⟩
    ∃ c, populationScores fuel (optimizeMember true false selected
      (fun e h => composableSimplify e none fuel h)
      (fun e h => composableCombine e none fuel h) optimizer m g) = .ok (c, c)

theorem populationCostFresh_refuted : ¬ populationCostFresh := by
  intro h
  let g := (Graph.ofTree (Heap.empty : Graph JF) foldingTree).2
  let root := (Graph.ofTree (Heap.empty : Graph JF) foldingTree).1
  let optimizer := fun (_ : Member (Ex JF Unit) Int) (_ : Graph JF) =>
    (Except.error (.userError "optimizer must not be called") :
      Jl (Member (Ex JF Unit) Int × JF × Graph JF))
  have hu : g.unfold 10 root = some foldingTree :=
    Graph.unfold_ofTree _ _ (by simp [foldingTree, Tree.Representable]) _
      (by simp [foldingTree, Tree.depth])
  have hw : foldingTree.WF 2 opsPMTD.nops 1 := by
    simp [foldingTree, Tree.WF, CEnum.nops, opsPMTD]
  obtain ⟨c, hc⟩ := h opsPMTD 10 g root foldingTree false optimizer hu hw
    (Graph.noAlias_ofTree _ _)
  have he : populationScores 10 (optimizeMember true false false
      (fun e h => composableSimplify e none 10 h)
      (fun e h => composableCombine e none 10 h) optimizer
      ⟨⟨.expression, root, opsPMTD, ()⟩, foldingTree.size, 0, foldingTree.size, 1, 0, 0⟩ g) =
      .ok (3, 1) := by
    simp only [show foldingTree.size = 3 by simp [foldingTree, Tree.size]]
    decide +kernel
  rw [he] at hc
  have hpair : (3 : Int) = c ∧ (1 : Int) = c := by simpa using hc
  omega

example : (0 : Nat) < 1 := by decide
example : (Member.mk 3 (3 : Int) 0 3 1 0 0).cost = (3 : Int) := rfl
example : mutateSimplify true
    (fun (e : Nat) (g : Unit) => .ok (e, g)) (fun e g => .ok (e, g))
    (fun _ _ => .ok 1) (fun (l : Int) _ _ => .ok l)
    ⟨0, 0, 0, 1, 1, 0, 0⟩ 0 1 2 3 () =
      .ok (⟨⟨0, 0, 0, 1, 2, 1, 3⟩, 0, true, true⟩, ()) := rfl

example : (optimizationMask (.fin 1) 1 { draws := fun _ => 0 }).1[0]? = some true := by decide

example : (optimizationMask .nan 1 { draws := fun _ => 0 }).1[0]? = some false := by decide

end SymReg.SimpCons
