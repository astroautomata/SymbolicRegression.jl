import SymReg.MutateGen.EngineOutcome
import SymReg.MutateGen.SampleProps

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw greater)

attribute [local semireducible] Rat.add Rat.mul Rat.inv
attribute [local simp] List.filterMap_cons List.filter_cons attemptOf evalsOf isFailedCheck isImmOk
  isLoopCall isEval onEndOf chooseOf

/-! ## Lemmas -/

section
variable {E : Type}

/-- The store `next_generation` hands to `_next_generation`. -/
def preCore (cfg : Cfg E) (po : Nat) (m : Member E) (cms : Int) (s : St E)
    (k : Kind) (idx : Nat) (rng : RNG) : St E :=
  { s.write po (conditionParent cfg m) with
    scratch := (conditionedWeights cfg m cms cfg.mutations).map some, rng := rng,
           log := s.log ++ [.choose k idx] }

theorem preCore_inv (cfg : Cfg E) (po : Nat) (m : Member E) (cms : Int) (s : St E)
    (k : Kind) (idx : Nat) (rng : RNG) (hi : s.Inv) (hm : s.objs po = some m) :
    (preCore cfg po m cms s k idx rng).Inv := by
  intro x v hx
  change (if x = po then _ else s.objs x) = some v at hx
  change x < s.next
  split at hx
  · rename_i h; subst x; exact hi po m hm
  · exact hi x v hx

theorem ng_run (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat) (acc : Bool) (ev : JF)
    (h : nextGeneration cfg po cms s = .ok ((o, acc, ev), s')) :
    ∃ m idx k w rng, ∃ (scale : JF), ∃ e evr s2, s.objs po = some m ∧
      sampleMutationR (conditionedWeights cfg m cms cfg.mutations) s.rng = (.ok idx, rng) ∧
      (conditionedWeights cfg m cms cfg.mutations)[idx - 1]? = some (k, w) ∧
      RetryOK cfg po cms 10 0 (.fin 0) (preCore cfg po m cms s k idx rng) e evr s2 ∧
      Outcome cfg k idx po (conditionParent cfg m) e evr s2 o acc ev s' := by
  obtain ⟨m, idx, k, w, rng, hm, hs, hk, hc⟩ := ng_unfold cfg po cms s s' o acc ev h
  obtain ⟨scale, e, evr, s2, hr, hout⟩ := core_outcome cfg k idx po (conditionParent cfg m) cms _ s' o acc ev hc
  exact ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk,
    retry_ok cfg k scale po (conditionParent cfg m) m.ref cms 10 0 (.fin 0) _ e evr s2 hr, hout⟩

theorem sample_draws {α : Type} (ws : List (α × JF)) (rng : RNG) (r : Jl Nat) (rng' : RNG)
    (h : sampleMutationR ws rng = (r, rng')) : rng'.draws = rng.draws := by
  unfold sampleMutationR at h
  cases hc : checkedTotal (.fin 0) ws with
  | error e => simp only [hc, Prod.mk.injEq] at h; rw [← h.2]
  | ok total =>
    simp only [hc] at h
    by_cases hg : greater total (.fin 0) = true
    · simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, draw, Prod.mk.injEq] at h
      rw [← h.2]
    · simp only [hg, Bool.not_false, ↓reduceIte, Prod.mk.injEq] at h
      rw [← h.2]

theorem endsOf_filters (cfg : Cfg E) (k : Kind) (evt : Event) :
    (endsOf cfg k evt).filterMap evalsOf = [] ∧ (endsOf cfg k evt).filter isEval = [] ∧
    (endsOf cfg k evt).filterMap attemptOf = [] ∧ (endsOf cfg k evt).filter isFailedCheck = [] ∧
    (endsOf cfg k evt).filterMap chooseOf = [] ∧ (endsOf cfg k evt).any isImmOk = false ∧
    (endsOf cfg k evt).filterMap onEndOf = (List.range cfg.plugins.length).map (fun i => (i, k, evt)) := by
  simp [endsOf, List.filterMap_map, List.filter_map, Function.comp_def]

theorem loop_filters (L : List (Call E)) (h : L.all isLoopCall = true) :
    L.filter isEval = [] ∧ L.filterMap chooseOf = [] ∧ L.filterMap onEndOf = [] := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hc, hL⟩ := h
    obtain ⟨a, b, d⟩ := ih hL
    cases c <;> simp_all

theorem inv_fresh (s : St E) (hi : s.Inv) (o : Nat) (ho : s.next ≤ o) : s.objs o = none := by
  cases h : s.objs o with
  | none => rfl
  | some m => have := hi o m h; omega

end

/-! ## Properties of `next_generation` -/

/-- Round after each handler report, then add the dataset fraction only
for a direct engine score. -/
def ng_evals : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  (∀ a, a ∈ (s'.log.drop s.log.length).filterMap evalsOf →
    SymReg.Loss.LossPrecision.round .float64 a = a) →
  ∃ L, s'.log = s.log ++ L ∧ (L.filter isEval).length ≤ 1 ∧
    ev = let count := sumEvals L (.fin 0)
         if (L.filter isEval).length = 1 then weightAdd count cfg.frac else count

theorem ng_evals_holds : ng_evals := by
  intro E cfg po cms s s' o acc ev h _
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, hev, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, -, -, hcases⟩ := hout
  obtain ⟨e1, e2, -, -, -, -, -⟩ := endsOf_filters cfg k evt
  obtain ⟨l1, -, -⟩ := loop_filters L hall
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, ?_, ?_⟩
  · rw [hlog, hL]; simp [preCore]
  · rcases hcases with ⟨-, -, hev', rfl, -⟩ | ⟨-, -, hev', rfl, -⟩ | ⟨t, -, -, -, hev', rfl, -⟩ |
      ⟨t, c, l, -, -, -, hev', rfl, -⟩
    all_goals simp [List.filter_append, l1, e1, e2, sumEvals, hev', hev]

/-- `mutate!` is called with `attempt = 1, 2, ..., n` in order, at most `max_attempts = 10`
times and at least once, and every call after the first follows a `check_constraints`
call that rejected the previous mutated tree. -/
def ng_attempts : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ L, s'.log = s.log ++ L ∧
    L.filterMap attemptOf = List.range' 1 (L.filterMap attemptOf).length ∧
    1 ≤ (L.filterMap attemptOf).length ∧ (L.filterMap attemptOf).length ≤ 10 ∧
    (L.filterMap attemptOf).length ≤ (L.filter isFailedCheck).length + 1

theorem ng_attempts_holds : ng_attempts := by
  intro E cfg po cms s s' o acc ev h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, -, hatt, hlen, hpos, hfail, -, -, -, -, -, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, -, -, hcases⟩ := hout
  obtain ⟨-, -, e3, e4, -, -, -⟩ := endsOf_filters cfg k evt
  have hpre : pre.filterMap attemptOf = [] ∧ pre.filter isFailedCheck = [] := by
    rcases hcases with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨t, -, -, -, -, rfl, -⟩ |
      ⟨t, c, l, -, -, -, -, rfl, -⟩ <;> simp
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, ?_, ?_⟩
  · rw [hlog, hL]; simp [preCore]
  · simp only [List.filterMap_append, List.filter_append, e3, e4, hpre.1, hpre.2, List.append_nil,
      List.filterMap_cons, chooseOf, attemptOf, List.filterMap_nil, List.nil_append, List.filter_cons,
      isFailedCheck, List.filter_nil, List.length_append, List.length_nil]
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at *
    exact ⟨hatt, hpos (by decide), hlen, by simpa using hfail⟩

/-- Every `next_generation` call records exactly one sampled mutation and fires
`on_mutation_end!` once per plugin, in plugin order, with one event whose `accepted` flag
is the returned `mutation_accepted` and whose `mutation_idx` is the sampled index. -/
def ng_events : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ L k idx evt, s'.log = s.log ++ L ∧ L.filterMap chooseOf = [(k, idx)] ∧
    L.filterMap onEndOf = (List.range cfg.plugins.length).map (fun i => (i, k, evt)) ∧
    evt.accepted = acc ∧ evt.idx = idx

theorem ng_events_holds : ng_events := by
  intro E cfg po cms s s' o acc ev h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, hacc, hidx, hcases⟩ := hout
  obtain ⟨-, -, -, -, e5, -, e7⟩ := endsOf_filters cfg k evt
  obtain ⟨-, l2, l3⟩ := loop_filters L hall
  have hpre : pre.filterMap chooseOf = [] ∧ pre.filterMap onEndOf = [] := by
    rcases hcases with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨t, -, -, -, -, rfl, -⟩ |
      ⟨t, c, l, -, -, -, -, rfl, -⟩ <;> simp
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, k, idx, evt, ?_, ?_, ?_, hacc, hidx⟩
  · rw [hlog, hL]; simp [preCore]
  · simp [List.filterMap_append, l2, hpre.1, e5]
  · simp [List.filterMap_append, l3, hpre.2, e7]

/-- Dispatch uses the exact index from the sampling draw and the corresponding
entry in the engine- and plugin-conditioned weights. -/
def ng_sampled : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ m L k w idx rng, s.objs po = some m ∧ s'.log = s.log ++ L ∧ L.filterMap chooseOf = [(k, idx)] ∧
    let ws := conditionedWeights cfg m cms cfg.mutations
    sampleMutationR ws s.rng = (.ok idx, rng) ∧ ws[idx - 1]? = some (k, w)

theorem ng_sampled_holds : ng_sampled := by
  intro E cfg po cms s s' o acc ev h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, -, -, -, -, -, -, -, -, hsc, -, -, -, -⟩ := hr
  obtain ⟨-, hsc2, evt, pre, hlog, -, -, hcases⟩ := hout
  obtain ⟨-, -, -, -, e5, -, -⟩ := endsOf_filters cfg k evt
  obtain ⟨-, l2, -⟩ := loop_filters L hall
  have hpre : pre.filterMap chooseOf = [] := by
    rcases hcases with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨t, -, -, -, -, rfl, -⟩ |
      ⟨t, c, l, -, -, -, -, rfl, -⟩ <;> simp
  refine ⟨m, [.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, k, w, idx, rng, hm, ?_, ?_, hs, hk⟩
  · rw [hlog, hL]; simp [preCore]
  · simp [List.filterMap_append, l2, hpre, e5]

/-- A mutation `next_generation` reports as accepted either came from a `mutate!` call
that returned immediately with success, or is a newly allocated member whose tree passed
`check_constraints(tree, options, curmaxsize)`, whose cost and loss are `eval_cost` of that
tree, whose cost is not NaN, and whose parent is the input member. -/
def ng_accept_sound : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E)
  (o : Nat) (ev : JF), s.Inv → nextGeneration cfg po cms s = .ok ((o, true, ev), s') →
  ∃ L, s'.log = s.log ++ L ∧
    ((∃ a v, Call.mutate a v true true ∈ L) ∨
     ∃ m r, s.objs po = some m ∧ s.objs o = none ∧ s'.objs o = some r ∧
       cfg.constraints r.tree cms = true ∧ cfg.evalCost r.tree = (r.cost, r.loss) ∧ r.cost ≠ .nan ∧
       r.parent = m.ref)

theorem ng_accept_sound_holds : ng_accept_sound := by
  intro E cfg po cms s s' o ev hi h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o true ev h
  obtain ⟨L, hL, hall, -, -, -, -, -, himm, hfin, -, -, hnext, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, -, -, hcases⟩ := hout
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, by rw [hlog, hL]; simp [preCore], ?_⟩
  rcases hcases with ⟨he, -, -, -, -, -⟩ | ⟨-, hf, -⟩ | ⟨t, -, -, hf, -⟩ |
    ⟨t, c, l, he, hcl, hnan, -, -, -, hacc, -⟩
  · left
    have := himm.mp ⟨o, he⟩
    rw [List.any_eq_true] at this
    obtain ⟨x, hx, hxi⟩ := this
    cases x with
    | mutate a v i ok =>
      cases i <;> cases ok <;> simp at hxi
      exact ⟨a, v, by simp [hx]⟩
    | _ => simp at hxi
  · cases hf
  · cases hf
  · right
    obtain ⟨ho, hso, -, -⟩ := hacc rfl
    obtain ⟨hc, -⟩ := hfin t he
    refine ⟨m, _, hm, ?_, hso, hc, hcl, hnan, rfl⟩
    apply inv_fresh s hi
    rw [ho]
    have : (preCore cfg po m cms s k idx rng).next = s.next := rfl
    omega

/-- When `next_generation` reports a rejection, it returns a newly allocated member (not
any existing object) holding a copy of the parent's tree and the parent's cost and loss,
whose parent is the input member. -/
def ng_reject_copy : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E)
  (o : Nat) (ev : JF), s.Inv → nextGeneration cfg po cms s = .ok ((o, false, ev), s') →
  ∃ m r pm, s.objs po = some m ∧ s.objs o = none ∧ s'.objs o = some r ∧ s'.objs po = some pm ∧
    r.tree = pm.tree ∧ r.cost = m.cost ∧ r.loss = m.loss ∧ r.parent = m.ref

theorem ng_reject_copy_holds : ng_reject_copy := by
  intro E cfg po cms s s' o ev hi h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o false ev h
  obtain ⟨L, -, -, -, -, -, -, -, -, -, -, -, hnext, hinv, hkeep, -⟩ := hr
  obtain ⟨-, -, evt, pre, -, -, -, hcases⟩ := hout
  have hi1 := preCore_inv cfg po m cms s k idx rng hi hm
  have hi2 := hinv hi1
  have hpo : s2.objs po ≠ none := hkeep po (by simp [preCore, St.write])
  have hn1 : (preCore cfg po m cms s k idx rng).next = s.next := rfl
  have key : ChildStore s2 s' o ⟨curTreeOf po m s2, m.cost, m.loss, o, o, m.ref,
      cfg.complexity (curTreeOf po m s2)⟩ → ∃ m r pm,
      s.objs po = some m ∧ s.objs o = none ∧ s'.objs o = some r ∧ s'.objs po = some pm ∧
      r.tree = pm.tree ∧ r.cost = m.cost ∧ r.loss = m.loss ∧ r.parent = m.ref := by
    intro hcs
    obtain ⟨ho, hso, hoth, -⟩ := hcs
    cases hp2 : s2.objs po with
    | none => exact absurd hp2 hpo
    | some pm =>
      have hlt := hi2 po pm hp2
      have hne : po ≠ o := by omega
      refine ⟨m, _, pm, hm, inv_fresh s hi o (by omega), hso, by rw [hoth po hne, hp2], ?_, rfl, rfl, rfl⟩
      simp [curTreeOf, hp2]
  rcases hcases with ⟨-, hf, -⟩ | ⟨-, -, -, -, hc⟩ | ⟨t, -, -, -, -, -, hc⟩ |
    ⟨t, c, l, -, -, -, -, -, -, -, hc⟩
  · cases hf
  · exact key hc
  · exact key hc
  · exact key (hc rfl)

/-- A tree whose `eval_cost` cost is NaN is always rejected. -/
def ng_nan_reject : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ L, s'.log = s.log ++ L ∧ ∀ t, Call.eval t ∈ L → (cfg.evalCost t).1 = .nan → acc = false

/-- The only engine `eval_cost` call of a run is the one of its outcome. -/
private theorem eval_mem {E : Type} (cfg : Cfg E) (k : Kind) (idx : Nat) (evt : Event)
    (L : List (Call E)) (hall : L.all isLoopCall = true) (pre : List (Call E)) (t : E)
    (h : Call.eval t ∈ [Call.choose k idx] ++ L ++ pre ++ endsOf cfg k evt) : Call.eval t ∈ pre := by
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with ((h | h) | h) | h
  · cases h
  · have := List.all_eq_true.mp hall _ h; simp at this
  · exact h
  · simp [endsOf] at h

theorem ng_nan_reject_holds : ng_nan_reject := by
  intro E cfg po cms s s' o acc ev h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, -, -, hcases⟩ := hout
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, by rw [hlog, hL]; simp [preCore], ?_⟩
  intro t ht hn
  have := eval_mem cfg k idx evt L hall pre t ht
  rcases hcases with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨t', -, -, hacc, -, rfl, -⟩ |
    ⟨t', c, l, -, hcl, hnan, -, rfl, -⟩
  · simp at this
  · simp at this
  · exact hacc
  · simp at this; subst this; rw [hcl] at hn; exact absurd hn hnan

/-- The acceptance rule: when the engine evaluated a tree with a non-NaN cost, the mutation
is accepted exactly when the product `p` of the plugins' `mutation_acceptance_multiplier`s
does not satisfy `p < u` for a single uniform draw `u` in `[0, 1)` (so with probability
`min(1, p)`, and always when `p` is NaN or at least 1). -/
def ng_accept_rule : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), (∀ n, 0 ≤ s.rng.draws n ∧ s.rng.draws n < 1) →
  nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ L, s'.log = s.log ++ L ∧ ∀ t m, s.objs po = some m → Call.eval t ∈ L → (cfg.evalCost t).1 ≠ .nan →
    ∃ u, 0 ≤ u ∧ u < 1 ∧
      acc = !jlt (prodJF (cfg.plugins.map fun pl => pl.accept (conditionParent cfg m) t m.cost
        (cfg.evalCost t).1)) (.fin u)

theorem ng_accept_rule_holds : ng_accept_rule := by
  intro E cfg po cms s s' o acc ev hdr h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, -, -, -, -, -, -, -, hdr2, -, -, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, -, -, hcases⟩ := hout
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, by rw [hlog, hL]; simp [preCore], ?_⟩
  intro t m' hm' ht hn
  rw [hm] at hm'
  simp only [Option.some.injEq] at hm'
  subst hm'
  have := eval_mem cfg k idx evt L hall pre t ht
  have hd : s2.rng.draws = s.rng.draws := by
    rw [hdr2]; exact sample_draws _ _ _ _ hs
  rcases hcases with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨t', -, hnan, -, -, rfl, -⟩ |
    ⟨t', c, l, -, hcl, hnan, -, rfl, hacc, -⟩
  · simp at this
  · simp at this
  · simp at this; subst this; exact absurd hnan hn
  · simp at this; subst this
    refine ⟨s2.rng.draws s2.rng.cursor, ?_, ?_, ?_⟩
    · rw [hd]; exact (hdr _).1
    · rw [hd]; exact (hdr _).2
    · rw [hacc, hcl]
      rfl

/-- With no plugins (`prod(()) = 1.0`), every evaluated tree with a non-NaN cost is
accepted. -/
def ng_no_plugins_accept : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E)
  (o : Nat) (acc : Bool) (ev : JF), cfg.plugins = [] → (∀ n, 0 ≤ s.rng.draws n ∧ s.rng.draws n < 1) →
  nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ L, s'.log = s.log ++ L ∧ ∀ t, Call.eval t ∈ L → (cfg.evalCost t).1 ≠ .nan → acc = true

theorem ng_no_plugins_accept_holds : ng_no_plugins_accept := by
  intro E cfg po cms s s' o acc ev hp hdr h
  obtain ⟨L, hL, hrule⟩ := ng_accept_rule_holds E cfg po cms s s' o acc ev hdr h
  obtain ⟨m, -, -, -, -, -, -, -, -, hm, -⟩ := ng_run cfg po cms s s' o acc ev h
  refine ⟨L, hL, fun t ht hn => ?_⟩
  obtain ⟨u, -, hu1, hacc⟩ := hrule t m hm ht hn
  rw [hacc, hp]
  have : jlt (prodJF []) (.fin u) = false := by
    simp [prodJF, jlt, greater]; exact Rat.not_lt.mpr (Rat.le_of_lt hu1)
  simpa using this

/-- When a `mutate!` call returns immediately with success, `next_generation` accepts its
member without calling `eval_cost`. -/
def ng_immediate : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ L, s'.log = s.log ++ L ∧ ((∃ a v, Call.mutate a v true true ∈ L) → acc = true ∧ L.filter isEval = [])

theorem ng_immediate_holds : ng_immediate := by
  intro E cfg po cms s s' o acc ev h
  obtain ⟨m, idx, k, w, rng, scale, e, evr, s2, hm, hs, hk, hr, hout⟩ := ng_run cfg po cms s s' o acc ev h
  obtain ⟨L, hL, hall, -, -, -, -, -, himm, -, -, -, -, -, -, -⟩ := hr
  obtain ⟨-, -, evt, pre, hlog, -, -, hcases⟩ := hout
  obtain ⟨-, e2, -, -, -, e6, -⟩ := endsOf_filters cfg k evt
  obtain ⟨l1, -, -⟩ := loop_filters L hall
  refine ⟨[.choose k idx] ++ L ++ pre ++ endsOf cfg k evt, by rw [hlog, hL]; simp [preCore], ?_⟩
  intro ⟨a, v, hav⟩
  have hin : L.any isImmOk = true := by
    simp only [List.mem_append, List.mem_singleton] at hav
    rcases hav with ((h | h) | h) | h
    · cases h
    · exact List.any_eq_true.mpr ⟨_, h, rfl⟩
    · rcases hcases with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨t, -, -, -, -, rfl, -⟩ |
        ⟨t, c, l, -, -, -, -, rfl, -⟩ <;> simp at h
    · simp [endsOf] at h
  obtain ⟨o', he⟩ := himm.mpr hin
  rcases hcases with ⟨-, hacc, -, rfl, -⟩ | ⟨⟨t, hf⟩, -⟩ | ⟨t, hf, -⟩ | ⟨t, c, l, hf, -⟩
  · exact ⟨hacc, by simp [List.filter_append, l1, e2]⟩
  all_goals (rw [he] at hf; cases hf)

/-- When no abstract handler returns the parent, the result is freshly allocated
and only conditioning can change the input member. -/
theorem ng_fresh {E : Type} (cfg : Cfg E) (hf : cfg.mf.Fresh) (po : Nat) (cms : Int)
    (s s' : St E) (o : Nat) (acc : Bool) (ev : JF) (hi : s.Inv)
    (h : nextGeneration cfg po cms s = .ok ((o, acc, ev), s')) :
    po < s.next ∧ s.next ≤ o ∧ s'.objs po = (s.objs po).map (conditionParent cfg) := by
  obtain ⟨m, idx, k, w, rng, hm, -, -, hc⟩ := ng_unfold cfg po cms s s' o acc ev h
  obtain ⟨scale, e, evr, s2, hr, hout⟩ := core_outcome cfg k idx po (conditionParent cfg m) cms _ s' o acc ev hc
  obtain ⟨hfi, hobj⟩ := retry_fresh cfg hf k scale po (conditionParent cfg m) m.ref cms 10 0 (.fin 0) _ e evr s2 hr
  obtain ⟨L, -, -, -, -, -, -, -, -, -, -, -, hnext, -, -, -⟩ :=
    retry_ok cfg k scale po (conditionParent cfg m) m.ref cms 10 0 (.fin 0) _ e evr s2 hr
  simp only at hfi hobj hnext
  change s.next ≤ s2.next at hnext
  have hpo : po < s.next := hi po m hm
  have h2po : s2.objs po = (s.objs po).map (conditionParent cfg) := by
    rw [hobj po hpo]
    simp [St.write, hm]
  obtain ⟨-, -, evt, pre, -, -, -, hcases⟩ := hout
  have child : ∀ r, ChildStore s2 s' o r →
      po < s.next ∧ s.next ≤ o ∧ s'.objs po = (s.objs po).map (conditionParent cfg) := by
    rintro r ⟨ho, -, hoth, -⟩
    refine ⟨hpo, by omega, ?_⟩
    rw [hoth po (by omega), h2po]
  rcases hcases with ⟨he, -, -, -, hobjs, -⟩ | ⟨-, -, -, -, hcs⟩ | ⟨t, -, -, -, -, -, hcs⟩ |
    ⟨t, c, l, -, -, -, -, -, -, hacc, hrej⟩
  · exact ⟨hpo, hfi o he, by rw [hobjs, h2po]⟩
  · exact child _ hcs
  · exact child _ hcs
  · cases acc
    · exact child _ (hrej rfl)
    · exact child _ (hacc rfl)

/-- Stock allocation produces a distinct child; a successful immediate result
can return its existing member, including the parent. -/
def ng_no_alias : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat)
  (acc : Bool) (ev : JF), s.Inv →
  nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  (o = po → acc = true ∧
    ∃ k idx m rng w mid count scale,
      s.objs po = some m ∧
      sampleMutationR (conditionedWeights cfg m cms cfg.mutations) s.rng = (.ok idx, rng) ∧
      (conditionedWeights cfg m cms cfg.mutations)[idx - 1]? = some (k, w) ∧
      retry cfg k scale po (conditionParent cfg m) m.ref cms 10 0 (.fin 0) (preCore cfg po m cms s k idx rng) =
        .ok ((.immediate po, count), mid))

theorem ng_no_alias_immediate : ng_no_alias := by
  intro E cfg po cms s s' o acc ev hi h heq
  subst o
  obtain ⟨m, idx, k, w, rng, hm, hs, hk, hc⟩ := ng_unfold cfg po cms s s' po acc ev h
  obtain ⟨scale, e, count, mid, hr, hout⟩ := core_outcome cfg k idx po (conditionParent cfg m) cms _ s' po acc ev hc
  obtain ⟨_, -, -, -, -, -, -, -, -, -, -, -, hnext, -, -, -⟩ :=
    retry_ok cfg k scale po (conditionParent cfg m) m.ref cms 10 0 (.fin 0) _ e count mid hr
  change s.next ≤ mid.next at hnext
  have hp := hi po m hm
  have noChild : ∀ child, ¬ ChildStore mid s' po child := by
    rintro child ⟨hpo, -, -, -⟩
    omega
  obtain ⟨-, -, _, _, -, -, -, hcases⟩ := hout
  rcases hcases with ⟨rfl, ha, -, -, -, -⟩ | ⟨-, -, -, -, hcs⟩ | ⟨_, -, -, -, -, -, hcs⟩ |
    ⟨_, _, _, -, -, -, -, -, -, hacc, hrej⟩
  · exact ⟨ha, k, idx, m, rng, w, mid, count, scale, hm, hs, hk, hr⟩
  · exact (noChild _ hcs).elim
  · exact (noChild _ hcs).elim
  · cases acc
    · exact (noChild _ (hrej rfl)).elim
    · exact (noChild _ (hacc rfl)).elim

/-- The stock generation path preserves the parent except for its lazy complexity cache. -/
def ng_parent_unchanged : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E)
  (o : Nat) (acc : Bool) (ev : JF), s.Inv → cfg.mf.Fresh →
  nextGeneration cfg po cms s = .ok ((o, acc, ev), s') →
  ∃ before after, s.objs po = some before ∧ s'.objs po = some after ∧
    after.tree = before.tree ∧ after.cost = before.cost ∧ after.loss = before.loss ∧
    after.ref = before.ref ∧ after.parent = before.parent ∧ after.birth = before.birth ∧
    (after.complexity = before.complexity ∨
     before.complexity = -1 ∧ after.complexity = cfg.complexity before.tree)

theorem ng_parent_unchanged_holds : ng_parent_unchanged := by
  intro E cfg po cms s s' o acc ev hi hf h
  obtain ⟨m, -, -, -, -, hm, -⟩ := ng_unfold cfg po cms s s' o acc ev h
  have hf := (ng_fresh cfg hf po cms s s' o acc ev hi h).2.2
  rw [hm] at hf
  refine ⟨m, conditionParent cfg m, hm, hf, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [conditionParent]
  split
  · split
    · exact Or.inr ⟨by assumption, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- An `OptimizeMutation`-only configuration: the member `x1 * c` (tree `7`) has one constant,
and `optimize_constants` improves it to tree `5` with cost and loss `0` using 3 evaluations. -/
def optCfg : Cfg Nat where
  mutations := [(.optimize, .fin 1)]
  plugins := []
  D := 2
  treeOf := fun _ => .branch 1 [.feature 1, .const (.fin 1)]
  preserveSharing := false
  scalarConsts := fun _ => 1
  complexity := fun _ => 3
  shouldSimplify := true
  nfeatures := 2
  constraints := fun _ _ => true
  evalCost := fun _ => (.fin 0, .fin 0)
  mf := {
    mutateConstant := fun _ t _ => (t, 0), mutateOperator := fun t _ => (t, 0),
    mutateFeature := fun t _ => (t, 0), swapOperands := fun t _ => (t, 0),
    appendRandomOp := fun t _ => (t, 0), prependRandomOp := fun t _ => (t, 0),
    insertRandomOp := fun t _ => (t, 0), deleteRandomOp := fun t _ => (t, 0),
    formConnection := fun t _ => (t, 0), breakConnection := fun t _ => (t, 0),
    rotate := fun t _ => (t, 0), randomize := fun t _ => (t, 0),
    optimize := fun _ _ => ((some (5, .fin 0, .fin 0), .fin 3), 0),
    backsolve := {
      isExpression := false, binaryNode := true, leaf := fun _ => false, sharing := false,
      hasTarget := true, hasOps := true, parentComplexity := 3, minValidRows := 1, nodeAttempts := 1,
      curmaxsize := 10, nodeOf := fun _ _ => (1, 0), validRows := fun _ _ => 1,
      nodeComplexity := fun _ _ => 1, setupEvaluated := fun _ _ _ => (0, 0),
      fit := fun _ _ _ _ _ => (none, 0), sub := fun t _ => t, splice := fun t _ _ => t,
      complexity := fun _ => 3, constraints := fun _ _ => true, evalCost := fun _ => (.fin 0, .fin 0),
      subDataset := false, freshParentCost := .fin 0, frac := .fin 1 },
    simplify := fun _ t _ _ => ({ out := .tree t }, 0),
    custom := fun _ => none, customTypeDisplay := toString }

/-- The initial store: member object `0` with tree `7`, cost and loss `1`. -/
def optSt : St Nat where
  objs := fun o => if o = 0 then some ⟨7, .fin 1, .fin 1, 0, 0, 0, -1⟩ else none
  next := 1
  rng := { draws := fun _ => 0 }
  scratch := []
  log := []

theorem optSt_inv : optSt.Inv := by
  intro o m h
  simp only [optSt] at h
  split at h
  · simp_all [optSt]
  · cases h

/-- The object id returned by a run, if it succeeded. -/
def resultOid {E : Type} : Jl ((Nat × Bool × JF) × St E) → Option Nat
  | .ok ((o, _, _), _) => some o
  | .error _ => none

/-- The contents of object `o` after a run, if it succeeded. -/
def resultObj {E : Type} (o : Nat) : Jl ((Nat × Bool × JF) × St E) → Option (Member E)
  | .ok (_, s) => s.objs o
  | .error _ => none

example : optCfg.mf.Fresh := ⟨fun _ _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- The optimizer allocates object `1`. The parent's only change is its cached complexity. -/
example : resultOid (nextGeneration optCfg 0 10 optSt) = some 1 ∧
    resultObj 0 (nextGeneration optCfg 0 10 optSt) = some ⟨7, .fin 1, .fin 1, 0, 0, 0, 3⟩ ∧
    resultObj 1 (nextGeneration optCfg 0 10 optSt) = some ⟨5, .fin 0, .fin 0, 2, 1, 0, 3⟩ := by
  decide +kernel

example :
    let cfg := { optCfg with
      mutations := [(.custom 0, .fin 1)]
      mf := { optCfg.mf with
        custom := fun _ => some (fun _ _ _ _ => ({ out := .parent none, imm := true }, 0)) } }
    resultOid (nextGeneration cfg 0 10 optSt) = some 0 := by
  decide +kernel

/-- Observe the actual `(kind, index)` dispatched by a normally returning call. -/
def observedChoices {E : Type} (initial : St E) (r : Jl ((Nat × Bool × JF) × St E)) :
    Jl (List (Kind × Nat)) :=
  r.map fun (_, out) => (out.log.drop initial.log.length).filterMap chooseOf

def ng_positive : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s : St E)
    (m : Member E) (k : Kind) (i : Nat) (drawIndex : Fin (2^53)),
  s.objs po = some m → s.rng.draws s.rng.cursor = unitDraw drawIndex →
  FinNonneg (conditionedWeights cfg m cms cfg.mutations) →
  (∀ p ∈ conditionedWeights cfg m cms cfg.mutations, weightAdd (.fin 0) p.2 = p.2) →
  observedChoices s (nextGeneration cfg po cms s) = .ok [(k, i)] →
  ∃ w, (conditionedWeights cfg m cms cfg.mutations)[i - 1]? = some (k, w) ∧
    greater w (.fin 0) = true

private def extremeConfig : Cfg Nat :=
  { optCfg with
    treeOf := fun _ => .feature 1
    mutations := [(.rotateTree, .fin (1 / (2 : Rat)^1074)), (.doNothing, .fin 0)] }

private def extremeStore : St Nat :=
  { optSt with rng := { draws := fun _ => unitDraw ⟨3 * 2^51, by decide⟩ } }

theorem ng_positive_refuted : ¬ ng_positive := by
  intro h
  let m : Member Nat := ⟨7, .fin 1, .fin 1, 0, 0, 0, -1⟩
  have hw : conditionedWeights extremeConfig m 10 extremeConfig.mutations =
      [(.rotateTree, .fin (1 / (2 : Rat)^1074)), (.doNothing, .fin 0)] := rfl
  have hnonneg : FinNonneg (conditionedWeights extremeConfig m 10 extremeConfig.mutations) := by
    rw [hw]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact ⟨_, rfl, by decide +kernel⟩
    · exact ⟨_, rfl, by decide⟩
  have hformat : ∀ p ∈ conditionedWeights extremeConfig m 10 extremeConfig.mutations,
      weightAdd (.fin 0) p.2 = p.2 := by
    rw [hw]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl <;> decide +kernel
  have ⟨w, hi, hpos⟩ := h Nat extremeConfig 0 10 extremeStore m .doNothing 2
    ⟨3 * 2^51, by decide⟩ rfl rfl hnonneg hformat (by decide +kernel)
  rw [hw] at hi
  simp at hi
  subst w
  exact Bool.noConfusion hpos

/-- The same law on nonnegative, representable binary64 weights with
`|e| ≤ 510` for each nonzero weight, as in JuliaLean.Reasonable. -/
def ng_positive_normal : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s : St E)
    (m : Member E) (k : Kind) (i : Nat) (drawIndex : Fin (2^53)),
  s.objs po = some m → s.rng.draws s.rng.cursor = unitDraw drawIndex →
  (conditionedWeights cfg m cms cfg.mutations).length ≤ 2^63 - 1 →
  (∀ p ∈ conditionedWeights cfg m cms cfg.mutations,
    ∃ q, p.2 = .fin q ∧ (q = 0 ∨ 1 / (2 : Rat)^510 ≤ q ∧ q < (2 : Rat)^511)) →
  (∀ p ∈ conditionedWeights cfg m cms cfg.mutations, weightAdd (.fin 0) p.2 = p.2) →
  observedChoices s (nextGeneration cfg po cms s) = .ok [(k, i)] →
  ∃ w, (conditionedWeights cfg m cms cfg.mutations)[i - 1]? = some (k, w) ∧
    greater w (.fin 0) = true

theorem ng_positive_normal_holds : ng_positive_normal := by
  intro E cfg po cms s m k i d hm hd _ hn _ h
  cases hr : nextGeneration cfg po cms s with
  | error e => simp [observedChoices, hr, Except.map] at h
  | ok out =>
    obtain ⟨⟨o, acc, ev⟩, s'⟩ := out
    obtain ⟨m', L, k', w, i', rng, hm', hlog, hc, hs, hi⟩ :=
      ng_sampled_holds E cfg po cms s s' o acc ev hr
    rw [hm] at hm'
    cases hm'
    have hci : [(k', i')] = [(k, i)] := by
      simpa [observedChoices, hr, Except.map, hlog, List.drop_left, hc] using h
    cases hci
    obtain ⟨p, hp, hpos⟩ := sample_positive_normal _ _ _ d i hd hn hs
    rw [hi] at hp
    cases hp
    exact ⟨w, hi, hpos⟩

example :
    let cfg := { extremeConfig with
      mutations := [(.rotateTree, .fin 1), (.doNothing, .fin 0)] }
    observedChoices extremeStore (nextGeneration cfg 0 10 extremeStore) =
      .ok [(.rotateTree, 1)] := by decide +kernel

/-- `next_generation`'s result does not depend on what the per-task scratch vector held
before the call (`_mutation_weights_scratch` resizes it and copies `options.mutations`). -/
def ng_scratch : Prop := ∀ (E : Type) (cfg : Cfg E) (po : Nat) (cms : Int) (s : St E)
  (a b : List (Option (Kind × JF))),
  nextGeneration cfg po cms { s with scratch := a } = nextGeneration cfg po cms { s with scratch := b }

theorem ng_scratch_holds : ng_scratch := by
  intro E cfg po cms s a b
  simp only [nextGeneration, scratch_ok, readAll_map]
  rfl

end SymReg.MutateGen
