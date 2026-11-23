import SymReg.Population.Tournament

/-!
Model of `src/RegularizedEvolution.jl` (SymbolicRegression.jl `upstream/master` daae84e5):
`MutationStepLayer`, `build_mutation_step`, `_add_mutation_step_layer`, `MutationStep`,
`reset!` and `reg_evol_cycle`.

Population members are object identities (`Nat`); the `birth` field lives in a store function
and fresh identities come from the allocation counter `next`. The engine's collaborators are
abstract and quantified over pass by pass (`Iter`): the `rand()` draw, the tournament winners
(`best_of_sample` returns the population member at a position, see `pop-tournament-member`),
the outcome of `next_generation`, the `next_step` calls made by mutation middleware, and the
outcome of `crossover_generation`. Tracing is a no-op (`trace === nothing`) and is not modelled.
-/

namespace SymReg.Population
open DynExpr

/-! ## Middleware composition -/

/-- `MutationStepLayer(wrapper, next_step)` called on `parent` (`src/RegularizedEvolution.jl:29-35`)
is `wrapper(parent, next_step)`; `_add_mutation_step_layer` (lines 42-45) skips `nothing`
wrappers. A wrapper is `(parent, next_step) -> result`. -/
def addLayer {π ρ : Type} : Option (π → (π → ρ) → ρ) → (π → ρ) → (π → ρ)
  | none, inner => inner
  | some w, inner => fun p => w p inner

/-- `build_mutation_step(wrappers, base_step)`, `src/RegularizedEvolution.jl:37-41`. -/
def buildStep {π ρ : Type} : List (Option (π → (π → ρ) → ρ)) → (π → ρ) → (π → ρ)
  | [], base => base
  | w :: ws, base => addLayer w (buildStep ws base)

/-- Property `regevol-build-step`: `build_mutation_step(wrappers, base_step)` is the nesting of
the non-`nothing` wrappers, the first one outermost: calling it on `parent` runs
`w1(parent, p -> w2(p, ... base_step))`; with no non-`nothing` wrapper it is `base_step`. -/
def build_step_spec : Prop :=
  ∀ (π ρ : Type) (ws : List (Option (π → (π → ρ) → ρ))) (base : π → ρ),
    buildStep ws base = (ws.filterMap id).foldr (fun w inner p => w p inner) base

theorem build_step_spec_holds : build_step_spec := by
  intro π ρ ws base
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases w with
    | none => simp [buildStep, addLayer, ih]
    | some w => simp [buildStep, addLayer, ih]

/-! ## Engine state -/

/-- `typemax(Int)`. -/
def typemaxInt : Int := 9223372036854775807

/-- Store update `f[k] = v`. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun x => if x = k then v else f x

/-- Scan of `argmin(f, 1:n)` (Julia Base `_rf_findmin`: replace only on a strictly smaller
value, so the first minimum is kept), over 0-based positions. -/
def argminFrom (f : Nat → Int) : List Nat → Nat → Int → Nat
  | [], bi, _ => bi
  | i :: is, bi, bv => if f i < bv then argminFrom f is i (f i) else argminFrom f is bi bv

/-- `argmin(f, 1:n)` as a 0-based position; an empty range throws. -/
def argminIdx (f : Nat → Int) (n : Nat) : Jl Nat :=
  if n = 0 then throw (.argumentError "argmin over an empty collection")
  else pure (argminFrom f (List.range' 1 (n - 1)) 0 (f 0))

/-- Return of one `next_generation(dataset, parent, curmaxsize, options; ...)` call
(`src/Mutate.jl:299-562`), as far as object identity, the `birth` field, acceptance and the
evaluation count matter here. Every path returns a new member object (`mutgen-ng-no-alias`). -/
inductive Gen where
  /-- A `create_child(...)` result: the rejections at `src/Mutate.jl:475-487,503-515,536-547`,
  the acceptance at lines 551-561, and the immediate returns of `SimplifyMutation`
  (lines 918-927), `OptimizeMutation` (lines 945-968, the optimized `create_child` copy),
  `DoNothingMutation` (lines 980-990) and `BacksolveMutation` (lines 874-883).
  A new member object with birth `b` (`get_birth_order`). -/
  | child (accepted : Bool) (b : Int) (evals : Rat)

/-- `num_evals` of a `next_generation` call. -/
def Gen.evals : Gen → Rat
  | .child _ _ e => e

/-- Acceptance flag of a `next_generation` call. -/
def Gen.accepted : Gen → Bool
  | .child a _ _ => a

/-- One `next_step(parent)` call made by mutation middleware. -/
structure Attempt where
  parent : Nat
  gen : Gen

/-- Outcome of `crossover_generation(allstar1, allstar2, ...)` (`src/Crossover.jl:110-225`). -/
inductive Cx where
  /-- Two new children with births `b1`, `b2` (lines 194-224). -/
  | accepted (b1 b2 : Int) (evals : Rat)
  /-- Constraint failure after `max_tries`: returns `member1, member2` themselves (line 190). -/
  | rejected (evals : Rat)

def Cx.evals : Cx → Rat
  | .accepted _ _ e => e
  | .rejected e => e

/-- The abstract inputs of one pass of the `for i in 1:n_evol_cycles` loop
(`src/RegularizedEvolution.jl:129-230`). -/
structure Iter where
  /-- `rand()` at line 130. -/
  u : Rat
  /-- 0-based position in `pop.members` of the first `best_of_sample` winner (lines 131, 179). -/
  win1 : Nat
  /-- Position of the second winner (line 180). -/
  win2 : Nat
  /-- `next_generation` outcome when there is no mutation middleware. -/
  gen : Gen
  /-- The `next_step` calls the middleware makes, in order. -/
  attempts : List Attempt
  /-- `attempt_id` of the result the middleware returns. -/
  ret : Int
  /-- `crossover_generation` outcome. -/
  cx : Cx

/-- Options read by `reg_evol_cycle`. -/
structure Cfg where
  /-- `crossover_probability`. -/
  cp : Rat
  /-- `skip_mutation_failures`. -/
  skip : Bool
  /-- `tournament_selection_n`. -/
  ns : Nat
  /-- `has_mutation_wrappers` (line 111): some plugin's `wrap_mutation_step` is not `nothing`. -/
  wrappers : Bool

/-- Engine state: population member identities, the `birth` store, the allocation counter,
`num_evals`, the identities offered to `best_seen`, and the `MutationStep` buffers
`attempted_results` (`(member, accepted, attempt_id, num_evals)`) and `attempted_members`. -/
structure St where
  members : List Nat
  birth : Nat → Int
  next : Nat
  evals : Rat
  hof : List Nat
  results : List (Nat × Bool × Nat × Rat)
  copies : List Nat

/-- Effect of a `next_generation` call on `parent`: the new state, the returned member,
acceptance and `num_evals`. -/
def runGen (st : St) (_parent : Nat) : Gen → St × Nat × Bool × Rat
  | .child acc b ev => ({ st with next := st.next + 1, birth := upd st.birth st.next b }, st.next, acc, ev)

/-- `(step::MutationStep)(parent)` with the buffers present (mutation middleware present),
`src/RegularizedEvolution.jl:65-86`: run `next_generation`, push the result with
`attempt_id = length(attempted_results) + 1`, push `copy(member)` (fresh identity, same birth),
and offer accepted members to `best_seen`. -/
def stepCallRec (st : St) (parent : Nat) (g : Gen) : St :=
  let r := runGen st parent g
  { r.1 with
    results := r.1.results ++ [(r.2.1, r.2.2.1, r.1.results.length + 1, r.2.2.2)]
    copies := r.1.copies ++ [r.1.next]
    next := r.1.next + 1
    birth := upd r.1.birth r.1.next (r.1.birth r.2.1)
    hof := if r.2.2.1 then r.1.hof ++ [r.2.1] else r.1.hof }

/-- `reset!(step)`, `src/RegularizedEvolution.jl:88-93`: empty both buffers. -/
def reset (st : St) : St := { st with results := [], copies := [] }

/-- The middleware's `next_step` calls in order. -/
def runAttempts (st : St) : List Attempt → St
  | [] => st
  | a :: as => runAttempts (stepCallRec st a.parent a.gen) as

/-- Sum of evaluation counts. -/
def rsum (l : List Rat) : Rat := l.foldl (· + ·) 0

/-- Lines 155-171: `should_replace = mutation_accepted || !options.skip_mutation_failures`;
if so, `pop.members[argmin(i -> pop.members[i].birth, 1:pop.n)] = baby`. -/
def replaceOldest (skip : Bool) (st : St) (baby : Nat) (acc : Bool) : Jl St :=
  if acc || !skip then do
    let k ← argminIdx (fun i => st.birth (st.members.getD i 0)) st.members.length
    pure { st with members := st.members.set k baby }
  else pure st

/-- Lines 207-229: the two oldest members are replaced by `baby1`, `baby2`. -/
def replaceTwo (st : St) (b1 b2 : Nat) : Jl St := do
  let bf := fun i => st.birth (st.members.getD i 0)
  let k1 ← argminIdx bf st.members.length
  let k2 ← argminIdx (fun i => if i = k1 then typemaxInt else bf i) st.members.length
  pure { st with members := (st.members.set k1 b1).set k2 b2 }

/-- Mutation pass with middleware (lines 133-150, 152-171) once the middleware's `next_step`
calls have run (`st1`): the returned `attempt_id` `ret` must index `attempted_results`
(`checkbounds`, lines 139-144); `num_evals` gains every recorded attempt's evaluations; the
baby is the recorded copy `attempted_members[ret]`. -/
def mutWrapped (skip : Bool) (ret : Int) (st1 : St) : Jl St :=
  if 1 ≤ ret ∧ ret ≤ (st1.results.length : Int) then
    replaceOldest skip { st1 with evals := st1.evals + rsum (st1.results.map (·.2.2.2)) }
      (st1.copies.getD (ret.toNat - 1) 0) (st1.results.getD (ret.toNat - 1) (0, false, 0, 0)).2.1
  else throw (.argumentError "Mutation middleware must return a result from `next_step`.")

/-- Mutation pass without middleware (lines 133-138, 147-171): `r` is the result of the single
`next_generation` call; the baby is its member itself. -/
def mutPlain (skip : Bool) (r : St × Nat × Bool × Rat) : Jl St :=
  replaceOldest skip { r.1 with evals := r.1.evals + r.2.2.2 } r.2.1 r.2.2.1

/-- Mutation branch, `src/RegularizedEvolution.jl:131-171`: `allstar = best_of_sample(...)`,
`reset!(base_step)`, `wrapped_step(allstar)`. -/
def iterMutation (cfg : Cfg) (st : St) (it : Iter) : Jl St :=
  if cfg.wrappers then mutWrapped cfg.skip it.ret (runAttempts (reset st) it.attempts)
  else mutPlain cfg.skip (runGen (reset st) (st.members.getD it.win1 0) it.gen)

/-- `allstar1 === allstar2 && (allstar2 = copy(allstar2))`, lines 181-184: the state and the
second parent. -/
def dedupParents (st : St) (a1 a2 : Nat) : St × Nat :=
  if a1 = a2 then ({ st with next := st.next + 1, birth := upd st.birth st.next (st.birth a2) }, st.next)
  else (st, a2)

/-- Accepted `crossover_generation` (lines 186-200): two new children with births `b1`, `b2`,
both offered to `best_seen` (`_update_hall_of_fame_unchecked!`, lines 192-198). -/
def cxChildren (st : St) (b1 b2 : Int) (ev : Rat) : St :=
  { st with next := st.next + 2, birth := upd (upd st.birth st.next b1) (st.next + 1) b2,
            evals := st.evals + ev, hof := st.hof ++ [st.next, st.next + 1] }

/-- Rejected crossover without skipping: `baby1, baby2 = copy(baby1), copy(baby2)` of the
returned parents (lines 200-205). -/
def copyParents (st : St) (a1 a2 : Nat) (ev : Rat) : St :=
  { st with next := st.next + 2, birth := upd (upd st.birth st.next (st.birth a1)) (st.next + 1) (st.birth a2),
            evals := st.evals + ev }

/-- Crossover branch, `src/RegularizedEvolution.jl:173-229`: identical winners get
`allstar2 = copy(allstar2)`; rejected crossovers either skip the pass
(`options.skip_mutation_failures && continue`) or insert copies of the two parents; the two
oldest members are replaced. -/
def crossoverWith (cfg : Cfg) (a1 : Nat) (d : St × Nat) : Cx → Jl St
  | .accepted b1 b2 ev => replaceTwo (cxChildren d.1 b1 b2 ev) d.1.next (d.1.next + 1)
  | .rejected ev =>
    if cfg.skip then pure { d.1 with evals := d.1.evals + ev }
    else replaceTwo (copyParents d.1 a1 d.2 ev) d.1.next (d.1.next + 1)

/-- Crossover branch, `src/RegularizedEvolution.jl:173-229`, with `allstar1`, `allstar2` the
two tournament winners. -/
def iterCrossover (cfg : Cfg) (st : St) (it : Iter) : Jl St :=
  crossoverWith cfg (st.members.getD it.win1 0)
    (dedupParents st (st.members.getD it.win1 0) (st.members.getD it.win2 0)) it.cx

/-- Branch test `rand() > options.crossover_probability` (line 130) negated: the pass is a
crossover. -/
def isCrossover (cp u : Rat) : Bool := !decide (u > cp)

/-- One pass of the loop. -/
def iterStep (cfg : Cfg) (st : St) (it : Iter) : Jl St :=
  if isCrossover cfg.cp it.u then iterCrossover cfg st it else iterMutation cfg st it

/-- `n_evol_cycles = ceil(Int, pop.n / options.tournament_selection_n)` (line 108), for
`tournament_selection_n ≥ 1` and exact division of these small integers. -/
def nIter (n ns : Nat) : Nat := (n + ns - 1) / ns

/-- `reg_evol_cycle(dataset, pop, curmaxsize, options, trace; plugin_states, best_seen,
eval_context)`, `src/RegularizedEvolution.jl:97-233`; pass `i` uses the inputs `its i`. -/
def regEvolCycle (cfg : Cfg) (st : St) (its : Nat → Iter) : Jl St :=
  (List.range (nIter st.members.length cfg.ns)).foldlM (fun s i => iterStep cfg s (its i)) st

/-! ## Lemmas -/

theorem foldlM_pres (P : St → Prop) (f : St → Nat → Jl St)
    (h : ∀ s i s', P s → f s i = .ok s' → P s') :
    ∀ (l : List Nat) s s', P s → l.foldlM f s = .ok s' → P s' := by
  intro l
  induction l with
  | nil => intro s s' hs hf; cases hf; exact hs
  | cons i is ih =>
    intro s s' hs hf
    rw [List.foldlM_cons] at hf
    cases hfs : f s i with
    | error e => rw [hfs] at hf; cases hf
    | ok s1 =>
      rw [hfs] at hf
      exact ih s1 s' (h s i s1 hs hfs) hf

theorem argminFrom_spec (f : Nat → Int) :
    ∀ m s bi, bi < s → (∀ i, i < s → f bi ≤ f i) → (∀ i, i < bi → f bi < f i) →
      argminFrom f (List.range' s m) bi (f bi) < s + m ∧
      (∀ i, i < s + m → f (argminFrom f (List.range' s m) bi (f bi)) ≤ f i) ∧
      (∀ i, i < argminFrom f (List.range' s m) bi (f bi) →
        f (argminFrom f (List.range' s m) bi (f bi)) < f i) := by
  intro m
  induction m with
  | zero => intro s bi h1 h2 h3; simp [argminFrom]; exact ⟨by omega, h2, h3⟩
  | succ m ih =>
    intro s bi h1 h2 h3
    simp only [List.range'_succ, argminFrom]
    split
    · rename_i hlt
      have := ih (s + 1) s (by omega)
        (fun i hi => by
          by_cases his : i = s
          · subst his; exact Int.le_refl _
          · have := h2 i (by omega); omega)
        (fun i hi => by have := h2 i hi; omega)
      exact ⟨by omega, fun i hi => this.2.1 i (by omega), this.2.2⟩
    · rename_i hnlt
      have := ih (s + 1) bi (by omega)
        (fun i hi => by
          by_cases his : i = s
          · subst his; omega
          · exact h2 i (by omega))
        h3
      exact ⟨by omega, fun i hi => this.2.1 i (by omega), this.2.2⟩

theorem argminIdx_spec (f : Nat → Int) (n : Nat) (hn : 1 ≤ n) :
    ∃ k, argminIdx f n = .ok k ∧ k < n ∧ (∀ i, i < n → f k ≤ f i) ∧ (∀ i, i < k → f k < f i) := by
  have := argminFrom_spec f (n - 1) 1 0 (by omega)
    (fun i hi => by have : i = 0 := by omega
                    subst this; exact Int.le_refl _) (fun i hi => by omega)
  refine ⟨_, by simp [argminIdx, show n ≠ 0 by omega]; rfl, by omega,
    fun i hi => this.2.1 i (by omega), this.2.2⟩

theorem nodup_set : ∀ (l : List Nat) (k x : Nat), l.Nodup → x ∉ l → (l.set k x).Nodup := by
  intro l
  induction l with
  | nil => intro k x _ _; simp
  | cons a l ih =>
    intro k x hn hx
    rw [List.nodup_cons] at hn
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.nodup_cons]
      exact ⟨fun h => hx (by simp [h]), hn.2⟩
    | succ k =>
      simp only [List.set_cons_succ, List.nodup_cons]
      refine ⟨fun h => ?_, ih k x hn.2 (fun h => hx (by simp [h]))⟩
      rcases List.mem_or_eq_of_mem_set h with h | h
      · exact hn.1 h
      · exact hx (by simp [h])

theorem mem_set_cases {l : List Nat} {k x y : Nat} (h : y ∈ l.set k x) : y ∈ l ∨ y = x :=
  List.mem_or_eq_of_mem_set h

/-- Identity invariant: members are distinct, previously allocated objects. -/
def Inv (st : St) : Prop := st.members.Nodup ∧ ∀ x ∈ st.members, x < st.next

theorem replaceOldest_inv (skip : Bool) (st st' : St) (baby : Nat) (acc : Bool)
    (hi : Inv st) (hb : baby ∉ st.members) (hbn : baby < st.next)
    (h : replaceOldest skip st baby acc = .ok st') : Inv st' := by
  unfold replaceOldest at h
  split at h
  · cases hk : argminIdx (fun i => st.birth (st.members.getD i 0)) st.members.length with
    | error e => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h; cases h
      refine ⟨nodup_set _ _ _ hi.1 hb, fun x hx => ?_⟩
      rcases mem_set_cases hx with hx | hx
      · exact hi.2 x hx
      · subst hx; exact hbn
  · cases h; exact hi

theorem replaceTwo_inv (st st' : St) (b1 b2 : Nat) (hi : Inv st) (h1 : b1 ∉ st.members)
    (h2 : b2 ∉ st.members) (h12 : b1 ≠ b2) (hn1 : b1 < st.next) (hn2 : b2 < st.next)
    (h : replaceTwo st b1 b2 = .ok st') : Inv st' := by
  unfold replaceTwo at h
  cases hk : argminIdx (fun i => st.birth (st.members.getD i 0)) st.members.length with
  | error e => simp only [hk, bind, Except.bind] at h; cases h
  | ok k1 =>
    simp only [hk, bind, Except.bind] at h
    cases hk2 : argminIdx (fun i => if i = k1 then typemaxInt else st.birth (st.members.getD i 0))
        st.members.length with
    | error e => rw [hk2] at h; cases h
    | ok k2 =>
      rw [hk2] at h; cases h
      have hn1' := nodup_set _ k1 b1 hi.1 h1
      have hb2 : b2 ∉ st.members.set k1 b1 := by
        intro hm
        rcases mem_set_cases hm with hm | hm
        · exact h2 hm
        · exact h12 hm.symm
      refine ⟨nodup_set _ _ _ hn1' hb2, fun x hx => ?_⟩
      rcases mem_set_cases hx with hx | hx
      · rcases mem_set_cases hx with hx | hx
        · exact hi.2 x hx
        · subst hx; exact hn1
      · subst hx; exact hn2

theorem runGen_members (st : St) (p : Nat) (g : Gen) : (runGen st p g).1.members = st.members := by
  cases g <;> rfl

theorem runGen_next (st : St) (p : Nat) (g : Gen) : st.next ≤ (runGen st p g).1.next := by
  cases g <;> simp [runGen]

theorem runGen_fields (st : St) (p : Nat) (g : Gen) :
    (runGen st p g).1.results = st.results ∧ (runGen st p g).1.copies = st.copies ∧
    (runGen st p g).1.evals = st.evals ∧ (runGen st p g).2.2.2 = g.evals := by
  cases g <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem stepCallRec_fields (st : St) (p : Nat) (g : Gen) :
    (stepCallRec st p g).members = st.members ∧ (stepCallRec st p g).evals = st.evals ∧
    (stepCallRec st p g).results =
      st.results ++ [((runGen st p g).2.1, (runGen st p g).2.2.1, st.results.length + 1, g.evals)] ∧
    (stepCallRec st p g).copies = st.copies ++ [(runGen st p g).1.next] ∧
    st.next ≤ (runGen st p g).1.next ∧ (stepCallRec st p g).next = (runGen st p g).1.next + 1 := by
  obtain ⟨hr, hc, he, hev⟩ := runGen_fields st p g
  refine ⟨runGen_members st p g, he, ?_, ?_, runGen_next st p g, rfl⟩
  · simp only [stepCallRec, hr, hev]
  · simp only [stepCallRec, hc]

theorem runAttempts_basic : ∀ (as : List Attempt) (st : St),
    (runAttempts st as).members = st.members ∧ (runAttempts st as).evals = st.evals ∧
    st.next ≤ (runAttempts st as).next ∧
    (runAttempts st as).results.length = st.results.length + as.length ∧
    (runAttempts st as).copies.length = st.copies.length + as.length ∧
    (runAttempts st as).results.map (·.2.2.2) = st.results.map (·.2.2.2) ++ as.map (·.gen.evals) := by
  intro as
  induction as with
  | nil => intro st; simp [runAttempts]
  | cons a as ih =>
    intro st
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := stepCallRec_fields st a.parent a.gen
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (stepCallRec st a.parent a.gen)
    simp only [runAttempts]
    rw [f1] at i1; rw [f2] at i2; rw [f3] at i4 i6; rw [f4] at i5
    refine ⟨i1, i2, by omega, by rw [i4]; simp; omega, by rw [i5]; simp; omega, by rw [i6]; simp⟩

theorem runAttempts_prefix : ∀ (as : List Attempt) (st : St) (k : Nat), k < st.results.length →
    (runAttempts st as).results[k]? = st.results[k]? := by
  intro as
  induction as with
  | nil => intro st k _; rfl
  | cons a as ih =>
    intro st k hk
    obtain ⟨-, -, f3, -⟩ := stepCallRec_fields st a.parent a.gen
    simp only [runAttempts]
    rw [ih _ k (by rw [f3]; simp; omega), f3, List.getElem?_append_left hk]

theorem runAttempts_ids : ∀ (as : List Attempt) (st : St) (j : Nat), j < as.length →
    ((runAttempts st as).results[st.results.length + j]?).map (·.2.2.1) =
      some (st.results.length + j + 1) := by
  intro as
  induction as with
  | nil => intro st j hj; simp at hj
  | cons a as ih =>
    intro st j hj
    obtain ⟨-, -, f3, -⟩ := stepCallRec_fields st a.parent a.gen
    simp only [runAttempts]
    cases j with
    | zero =>
      rw [runAttempts_prefix as _ _ (by rw [f3]; simp), f3]
      simp
    | succ j =>
      have := ih (stepCallRec st a.parent a.gen) j (by simp at hj; omega)
      rw [f3] at this
      simp only [List.length_append, List.length_singleton] at this
      rw [show st.results.length + (j + 1) = st.results.length + 1 + j by omega, this]

theorem runAttempts_copies : ∀ (as : List Attempt) (st : St),
    (∀ c ∈ st.copies, c < st.next) → st.copies.Nodup →
    (runAttempts st as).copies.Nodup ∧
    ∀ c ∈ (runAttempts st as).copies, c ∈ st.copies ∨ (st.next ≤ c ∧ c < (runAttempts st as).next) := by
  intro as
  induction as with
  | nil => intro st _ hnd; exact ⟨hnd, fun c hc => Or.inl hc⟩
  | cons a as ih =>
    intro st hcs hnd
    obtain ⟨-, -, -, f4, f5, f6⟩ := stepCallRec_fields st a.parent a.gen
    simp only [runAttempts]
    have hnd' : (stepCallRec st a.parent a.gen).copies.Nodup := by
      rw [f4, List.nodup_append]
      refine ⟨hnd, by simp, fun x hx y hy => ?_⟩
      simp at hy; subst hy
      have := hcs x hx; omega
    have hcs' : ∀ c ∈ (stepCallRec st a.parent a.gen).copies, c < (stepCallRec st a.parent a.gen).next := by
      intro c hc'
      rw [f4] at hc'; rw [f6]
      simp at hc'
      rcases hc' with hc' | hc'
      · have := hcs c hc'; omega
      · omega
    obtain ⟨j1, j2⟩ := ih _ hcs' hnd'
    refine ⟨j1, fun c hc' => ?_⟩
    rcases j2 c hc' with h | h
    · rw [f4] at h
      simp at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by have := (runAttempts_basic as (stepCallRec st a.parent a.gen)).2.2.1; omega⟩
    · exact Or.inr ⟨by omega, h.2⟩

theorem argminIdx_ok (f : Nat → Int) (n k : Nat) (h : argminIdx f n = .ok k) :
    k < n ∧ (∀ i, i < n → f k ≤ f i) ∧ (∀ i, i < k → f k < f i) := by
  by_cases hn : n = 0
  · subst hn; simp only [argminIdx, if_true] at h; cases h
  · obtain ⟨k', hk', h1, h2, h3⟩ := argminIdx_spec f n (by omega)
    rw [hk'] at h; cases h; exact ⟨h1, h2, h3⟩

theorem argminIdx_err (f : Nat → Int) (n : Nat) (e : JlError) (h : argminIdx f n = .error e) :
    e = .argumentError "argmin over an empty collection" := by
  unfold argminIdx at h
  split at h
  · cases h; rfl
  · cases h

theorem dedup_fields (st : St) (a1 a2 : Nat) :
    (dedupParents st a1 a2).1.members = st.members ∧ (dedupParents st a1 a2).1.evals = st.evals ∧
    st.next ≤ (dedupParents st a1 a2).1.next ∧
    ∀ x, x < st.next → (dedupParents st a1 a2).1.birth x = st.birth x := by
  unfold dedupParents
  split
  · exact ⟨rfl, rfl, by simp, fun x hx => by simp [upd, show x ≠ st.next by omega]⟩
  · exact ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem replaceOldest_spec (skip : Bool) (st st' : St) (baby : Nat) (acc : Bool)
    (h : replaceOldest skip st baby acc = .ok st') :
    st'.birth = st.birth ∧ st'.next = st.next ∧ st'.evals = st.evals ∧
    ((acc || !skip) = false → st'.members = st.members) ∧
    ((acc || !skip) = true → ∃ k, k < st.members.length ∧ st'.members = st.members.set k baby ∧
      (∀ i, i < st.members.length → st.birth (st.members.getD k 0) ≤ st.birth (st.members.getD i 0)) ∧
      (∀ i, i < k → st.birth (st.members.getD k 0) < st.birth (st.members.getD i 0))) := by
  unfold replaceOldest at h
  split at h
  · rename_i hc
    cases hk : argminIdx (fun i => st.birth (st.members.getD i 0)) st.members.length with
    | error e => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h; cases h
      obtain ⟨h1, h2, h3⟩ := argminIdx_ok _ _ _ hk
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · intro hf; rw [hc] at hf; cases hf
      · intro _; exact ⟨k, h1, rfl, h2, h3⟩
  · rename_i hc
    cases h
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun ht => by simp_all⟩

theorem replaceOldest_err (skip : Bool) (st : St) (baby : Nat) (acc : Bool) (e : JlError)
    (h : replaceOldest skip st baby acc = .error e) :
    e = .argumentError "argmin over an empty collection" := by
  unfold replaceOldest at h
  split at h
  · cases hk : argminIdx (fun i => st.birth (st.members.getD i 0)) st.members.length with
    | error e' => rw [hk] at h; cases h; exact argminIdx_err _ _ _ hk
    | ok k => rw [hk] at h; cases h
  · cases h

theorem replaceTwo_spec (st st' : St) (b1 b2 : Nat) (h : replaceTwo st b1 b2 = .ok st') :
    st'.birth = st.birth ∧ st'.next = st.next ∧ st'.evals = st.evals ∧
    ∃ k1 k2, k1 < st.members.length ∧ k2 < st.members.length ∧
      st'.members = (st.members.set k1 b1).set k2 b2 ∧
      (∀ i, i < st.members.length → st.birth (st.members.getD k1 0) ≤ st.birth (st.members.getD i 0)) ∧
      (∀ i, i < k1 → st.birth (st.members.getD k1 0) < st.birth (st.members.getD i 0)) ∧
      (∀ i, i < st.members.length →
        (if k2 = k1 then typemaxInt else st.birth (st.members.getD k2 0)) ≤
        (if i = k1 then typemaxInt else st.birth (st.members.getD i 0))) ∧
      (∀ i, i < k2 →
        (if k2 = k1 then typemaxInt else st.birth (st.members.getD k2 0)) <
        (if i = k1 then typemaxInt else st.birth (st.members.getD i 0))) := by
  unfold replaceTwo at h
  cases hk : argminIdx (fun i => st.birth (st.members.getD i 0)) st.members.length with
  | error e => simp only [hk, bind, Except.bind] at h; cases h
  | ok k1 =>
    simp only [hk, bind, Except.bind] at h
    cases hk2 : argminIdx (fun i => if i = k1 then typemaxInt else st.birth (st.members.getD i 0))
        st.members.length with
    | error e => rw [hk2] at h; cases h
    | ok k2 =>
      rw [hk2] at h; cases h
      obtain ⟨a1, a2, a3⟩ := argminIdx_ok _ _ _ hk
      obtain ⟨c1, c2, c3⟩ := argminIdx_ok _ _ _ hk2
      exact ⟨rfl, rfl, rfl, k1, k2, a1, c1, rfl, a2, a3, c2, c3⟩

theorem cxChildren_fields (st : St) (b1 b2 : Int) (ev : Rat) :
    (cxChildren st b1 b2 ev).members = st.members ∧ (cxChildren st b1 b2 ev).next = st.next + 2 ∧
    (cxChildren st b1 b2 ev).evals = st.evals + ev ∧
    ∀ x, x < st.next → (cxChildren st b1 b2 ev).birth x = st.birth x := by
  refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
  simp [cxChildren, upd, show x ≠ st.next by omega, show x ≠ st.next + 1 by omega]

theorem copyParents_fields (st : St) (a1 a2 : Nat) (ev : Rat) :
    (copyParents st a1 a2 ev).members = st.members ∧ (copyParents st a1 a2 ev).next = st.next + 2 ∧
    (copyParents st a1 a2 ev).evals = st.evals + ev ∧
    ∀ x, x < st.next → (copyParents st a1 a2 ev).birth x = st.birth x := by
  refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
  simp [copyParents, upd, show x ≠ st.next by omega, show x ≠ st.next + 1 by omega]

theorem replaceTwo_len (st st' : St) (b1 b2 : Nat) (h : replaceTwo st b1 b2 = .ok st') :
    st'.members.length = st.members.length := by
  obtain ⟨-, -, -, k1, k2, -, -, hm, -⟩ := replaceTwo_spec st st' b1 b2 h
  rw [hm]; simp

theorem replaceOldest_len (skip : Bool) (st st' : St) (baby : Nat) (acc : Bool)
    (h : replaceOldest skip st baby acc = .ok st') : st'.members.length = st.members.length := by
  obtain ⟨-, -, -, h1, h2⟩ := replaceOldest_spec skip st st' baby acc h
  cases hc : (acc || !skip)
  · rw [h1 hc]
  · obtain ⟨k, -, hk, -⟩ := h2 hc; rw [hk]; simp

theorem iterStep_len (cfg : Cfg) (s s' : St) (it : Iter) (h : iterStep cfg s it = .ok s') :
    s'.members.length = s.members.length := by
  unfold iterStep at h
  split at h
  · unfold iterCrossover at h
    have d1 := (dedup_fields s (s.members.getD it.win1 0) (s.members.getD it.win2 0)).1
    generalize dedupParents s (s.members.getD it.win1 0) (s.members.getD it.win2 0) = d at h d1
    cases hcx : it.cx with
    | accepted b1 b2 ev =>
      rw [hcx] at h; simp only [crossoverWith] at h
      rw [replaceTwo_len _ _ _ _ h, (cxChildren_fields _ _ _ _).1, d1]
    | rejected ev =>
      rw [hcx] at h; simp only [crossoverWith] at h
      split at h
      · cases h; exact congrArg List.length d1
      · rw [replaceTwo_len _ _ _ _ h, (copyParents_fields _ _ _ _).1, d1]
  · unfold iterMutation at h
    split at h
    · unfold mutWrapped at h
      split at h
      · rw [replaceOldest_len _ _ _ _ _ h]
        exact congrArg List.length (runAttempts_basic it.attempts (reset s)).1
      · cases h
    · unfold mutPlain at h
      rw [replaceOldest_len _ _ _ _ _ h]
      exact congrArg List.length (runGen_members (reset s) (s.members.getD it.win1 0) it.gen)

/-! ## Properties -/

/-- Property `regevol-size`: `reg_evol_cycle` keeps the population size constant. -/
def cycle_size : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (its : Nat → Iter),
    regEvolCycle cfg st its = .ok st' → st'.members.length = st.members.length

theorem cycle_size_holds : cycle_size := by
  intro cfg st st' its h
  exact foldlM_pres (fun s => s.members.length = st.members.length) _
    (fun s i s' hs hf => (iterStep_len cfg s s' (its i) hf).trans hs) _ st st' rfl h

/-- Tournament winners are population positions (`pop-tournament-member`). -/
def WinnersInRange (n : Nat) (its : Nat → Iter) : Prop := ∀ i, (its i).win1 < n ∧ (its i).win2 < n

/-- Property `regevol-no-alias`: starting from a population of distinct, allocated objects,
`reg_evol_cycle` never leaves the same object in two population slots (the `best_of_sample`
docstring, `src/Population.jl:172-174`: callers inserting a winner back must copy it), for any
mutation and crossover outcomes. -/
def no_alias : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (its : Nat → Iter),
    1 ≤ cfg.ns → cfg.ns < st.members.length → Inv st → WinnersInRange st.members.length its →
    regEvolCycle cfg st its = .ok st' → st'.members.Nodup

theorem iterStep_inv (cfg : Cfg) (s s' : St) (it : Iter) (hi : Inv s)
    (h : iterStep cfg s it = .ok s') : Inv s' := by
  unfold iterStep at h
  split at h
  · unfold iterCrossover at h
    obtain ⟨d1, d2, d3, d4⟩ := dedup_fields s (s.members.getD it.win1 0) (s.members.getD it.win2 0)
    generalize dedupParents s (s.members.getD it.win1 0) (s.members.getD it.win2 0) = d at h d1 d2 d3 d4
    have hi1 : Inv d.1 := ⟨by rw [d1]; exact hi.1, fun x hx => by rw [d1] at hx; have := hi.2 x hx; omega⟩
    cases hcx : it.cx with
    | accepted b1 b2 ev =>
      rw [hcx] at h; simp only [crossoverWith] at h
      obtain ⟨e1, e2, -, -⟩ := cxChildren_fields d.1 b1 b2 ev
      refine replaceTwo_inv _ _ _ _ ⟨by rw [e1]; exact hi1.1, fun x hx => ?_⟩ (fun hm => ?_)
        (fun hm => ?_) (by omega) (by rw [e2]; omega) (by rw [e2]; omega) h
      · rw [e1] at hx; rw [e2]; have := hi1.2 x hx; omega
      · rw [e1] at hm; have := hi1.2 _ hm; omega
      · rw [e1] at hm; have := hi1.2 _ hm; omega
    | rejected ev =>
      rw [hcx] at h; simp only [crossoverWith] at h
      split at h
      · cases h; exact ⟨hi1.1, hi1.2⟩
      · obtain ⟨e1, e2, -, -⟩ := copyParents_fields d.1 (s.members.getD it.win1 0) d.2 ev
        refine replaceTwo_inv _ _ _ _ ⟨by rw [e1]; exact hi1.1, fun x hx => ?_⟩ (fun hm => ?_)
          (fun hm => ?_) (by omega) (by rw [e2]; omega) (by rw [e2]; omega) h
        · rw [e1] at hx; rw [e2]; have := hi1.2 x hx; omega
        · rw [e1] at hm; have := hi1.2 _ hm; omega
        · rw [e1] at hm; have := hi1.2 _ hm; omega
  · unfold iterMutation at h
    split at h
    · unfold mutWrapped at h
      split at h
      · rename_i hr
        obtain ⟨b1, -, b3, b4, b5, -⟩ := runAttempts_basic it.attempts (reset s)
        obtain ⟨-, c2⟩ := runAttempts_copies it.attempts (reset s) (by simp [reset]) (by simp [reset])
        have hl4 : (runAttempts (reset s) it.attempts).results.length = it.attempts.length := by
          rw [b4]; simp [reset]
        have hl5 : (runAttempts (reset s) it.attempts).copies.length = it.attempts.length := by
          rw [b5]; simp [reset]
        have hmem : (runAttempts (reset s) it.attempts).copies.getD (it.ret.toNat - 1) 0 ∈
            (runAttempts (reset s) it.attempts).copies := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          simp
        have hrn : (reset s).next = s.next := rfl
        have hrc : (reset s).copies = [] := rfl
        have hrm : (reset s).members = s.members := rfl
        rw [hrm] at b1
        rw [hrn] at b3
        rcases c2 _ hmem with hm | hm
        · rw [hrc] at hm; cases hm
        · rw [hrn] at hm
          refine replaceOldest_inv _ _ _ _ _ ⟨by rw [b1]; exact hi.1, fun x hx => ?_⟩ (fun hx => ?_) ?_ h
          · show x < (runAttempts (reset s) it.attempts).next
            rw [b1] at hx; have := hi.2 x hx; omega
          · rw [b1] at hx; have := hi.2 _ hx; omega
          · exact hm.2
      · cases h
    · unfold mutPlain at h
      cases hg : it.gen with
      | child acc b ev =>
        rw [hg] at h
        refine replaceOldest_inv _ _ _ _ _ ?_ ?_ ?_ h
        · refine ⟨by simpa [runGen, reset] using hi.1, fun x hx => ?_⟩
          simp [runGen, reset] at hx ⊢
          have := hi.2 x hx; omega
        · intro hx
          simp [runGen, reset] at hx
          have := hi.2 _ hx; omega
        · simp [runGen, reset]

/-- Property `regevol-no-alias-fresh`: `reg_evol_cycle` keeps the population made of distinct
objects, all allocated before or during the cycle (every `next_generation` call returns a newly
allocated member). -/
def no_alias_fresh : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (its : Nat → Iter),
    Inv st → regEvolCycle cfg st its = .ok st' → Inv st'

theorem no_alias_fresh_holds : no_alias_fresh := by
  intro cfg st st' its hi h
  exact foldlM_pres Inv _ (fun s i s' hs hf => iterStep_inv cfg s s' (its i) hs hf) _ st st' hi h

example : Inv (⟨[0, 1], fun _ => 0, 2, 0, [], [], []⟩ : St) := ⟨by decide, by decide⟩

theorem no_alias_holds : no_alias := by
  intro cfg st st' its _ _ hi _ h
  exact (no_alias_fresh_holds cfg st st' its hi h).1

/-- Property `regevol-replace-oldest`: a mutation pass either leaves the population unchanged
or replaces exactly one slot, the first one holding a member of minimal `birth` (births read
after the mutation). -/
def replace_oldest : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (it : Iter),
    isCrossover cfg.cp it.u = false → iterStep cfg st it = .ok st' →
    st'.members = st.members ∨
    ∃ k b, k < st.members.length ∧ st'.members = st.members.set k b ∧
      (∀ i, i < st.members.length → st'.birth (st.members.getD k 0) ≤ st'.birth (st.members.getD i 0)) ∧
      (∀ i, i < k → st'.birth (st.members.getD k 0) < st'.birth (st.members.getD i 0))

theorem replace_oldest_holds : replace_oldest := by
  intro cfg st st' it hx h
  unfold iterStep at h
  rw [hx] at h
  simp only [Bool.false_eq_true, if_false] at h
  unfold iterMutation at h
  split at h
  · unfold mutWrapped at h
    split at h
    · obtain ⟨r1, r2, r3, r4, r5⟩ := replaceOldest_spec _ _ _ _ _ h
      have hb1 := (runAttempts_basic it.attempts (reset st)).1
      have hrm : (reset st).members = st.members := rfl
      rw [hrm] at hb1
      simp only [hb1] at r4 r5
      cases hc : ((runAttempts (reset st) it.attempts).results.getD (it.ret.toNat - 1) (0, false, 0, 0)).2.1
          || !cfg.skip
      · left; exact r4 hc
      · right
        obtain ⟨k, hk, hm, h1, h2⟩ := r5 hc
        exact ⟨k, _, hk, hm, by rw [r1]; exact h1, by rw [r1]; exact h2⟩
    · cases h
  · unfold mutPlain at h
    obtain ⟨r1, r2, r3, r4, r5⟩ := replaceOldest_spec _ _ _ _ _ h
    have hm0 := runGen_members (reset st) (st.members.getD it.win1 0) it.gen
    have hrm : (reset st).members = st.members := rfl
    rw [hrm] at hm0
    simp only [hm0] at r4 r5
    cases hc : ((runGen (reset st) (st.members.getD it.win1 0) it.gen).2.2.1 || !cfg.skip)
    · left; exact r4 hc
    · right
      obtain ⟨k, hk, hm, h1, h2⟩ := r5 hc
      exact ⟨k, _, hk, hm, by rw [r1]; exact h1, by rw [r1]; exact h2⟩

/-- Property `regevol-crossover-two-oldest`: a crossover pass that inserts children (accepted,
or rejected with `skip_mutation_failures = false`) on a population of at least two distinct
allocated members with births below `typemax(Int)` replaces two different slots: the first slot
of minimal birth, and the first slot of minimal birth among the others, with two distinct newly
allocated objects. -/
def crossover_two_oldest : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (it : Iter),
    2 ≤ st.members.length → Inv st → (∀ x ∈ st.members, st.birth x < typemaxInt) →
    isCrossover cfg.cp it.u = true → ((∃ b1 b2 ev, it.cx = .accepted b1 b2 ev) ∨ cfg.skip = false) →
    iterStep cfg st it = .ok st' →
    ∃ k1 k2 c1 c2, k1 < st.members.length ∧ k2 < st.members.length ∧ k1 ≠ k2 ∧ c1 ≠ c2 ∧
      c1 ∉ st.members ∧ c2 ∉ st.members ∧ st'.members = (st.members.set k1 c1).set k2 c2 ∧
      (∀ i, i < st.members.length → st.birth (st.members.getD k1 0) ≤ st.birth (st.members.getD i 0)) ∧
      (∀ i, i < k1 → st.birth (st.members.getD k1 0) < st.birth (st.members.getD i 0)) ∧
      (∀ i, i < st.members.length → i ≠ k1 →
        st.birth (st.members.getD k2 0) ≤ st.birth (st.members.getD i 0)) ∧
      (∀ i, i < k2 → i ≠ k1 → st.birth (st.members.getD k2 0) < st.birth (st.members.getD i 0))

theorem two_oldest_of_spec (st : St) (bf : Nat → Int) (hbf : ∀ i, bf i = st.birth (st.members.getD i 0))
    (h2 : 2 ≤ st.members.length) (hlt : ∀ x ∈ st.members, st.birth x < typemaxInt)
    (k1 k2 : Nat) (_hk1 : k1 < st.members.length) (_hk2 : k2 < st.members.length)
    (c2 : ∀ i, i < st.members.length →
        (if k2 = k1 then typemaxInt else bf k2) ≤ (if i = k1 then typemaxInt else bf i))
    (c3 : ∀ i, i < k2 → (if k2 = k1 then typemaxInt else bf k2) < (if i = k1 then typemaxInt else bf i)) :
    k1 ≠ k2 ∧ (∀ i, i < st.members.length → i ≠ k1 → bf k2 ≤ bf i) ∧
      (∀ i, i < k2 → i ≠ k1 → bf k2 < bf i) := by
  have hin : ∀ i, i < st.members.length → bf i < typemaxInt := by
    intro i hi
    rw [hbf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hlt _ (List.getElem_mem hi)
  have hne : k1 ≠ k2 := by
    intro he
    obtain ⟨j, hj, hjk⟩ : ∃ j, j < st.members.length ∧ j ≠ k1 := by
      by_cases h0 : k1 = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    have := c2 j hj
    rw [if_pos he.symm, if_neg hjk] at this
    have := hin j hj
    omega
  refine ⟨hne, fun i hi hik => ?_, fun i hi hik => ?_⟩
  · have := c2 i hi; rwa [if_neg (Ne.symm hne), if_neg hik] at this
  · have := c3 i hi; rwa [if_neg (Ne.symm hne), if_neg hik] at this

theorem crossover_two_oldest_holds : crossover_two_oldest := by
  intro cfg st st' it h2 hi hlt hx hcx h
  unfold iterStep at h
  rw [hx] at h
  simp only [if_true] at h
  unfold iterCrossover at h
  obtain ⟨d1, d2, d3, d4⟩ := dedup_fields st (st.members.getD it.win1 0) (st.members.getD it.win2 0)
  generalize dedupParents st (st.members.getD it.win1 0) (st.members.getD it.win2 0) = d at h d1 d2 d3 d4
  have hmem : ∀ i, i < st.members.length → st.members.getD i 0 < st.next := by
    intro i hi'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    exact hi.2 _ (List.getElem_mem hi')
  -- both inserting branches share this conclusion
  have finish : ∀ (s0 : St), s0.members = st.members → s0.next = d.1.next + 2 →
      (∀ x, x < d.1.next → s0.birth x = d.1.birth x) → replaceTwo s0 d.1.next (d.1.next + 1) = .ok st' →
      ∃ k1 k2 c1 c2, k1 < st.members.length ∧ k2 < st.members.length ∧ k1 ≠ k2 ∧ c1 ≠ c2 ∧
      c1 ∉ st.members ∧ c2 ∉ st.members ∧ st'.members = (st.members.set k1 c1).set k2 c2 ∧
      (∀ i, i < st.members.length → st.birth (st.members.getD k1 0) ≤ st.birth (st.members.getD i 0)) ∧
      (∀ i, i < k1 → st.birth (st.members.getD k1 0) < st.birth (st.members.getD i 0)) ∧
      (∀ i, i < st.members.length → i ≠ k1 →
        st.birth (st.members.getD k2 0) ≤ st.birth (st.members.getD i 0)) ∧
      (∀ i, i < k2 → i ≠ k1 → st.birth (st.members.getD k2 0) < st.birth (st.members.getD i 0)) := by
    intro s0 hm0 hn0 hb0 hr
    obtain ⟨-, -, -, k1, k2, hk1, hk2, hm, a2, a3, c2, c3⟩ := replaceTwo_spec _ _ _ _ hr
    rw [hm0] at hk1 hk2 hm a2 a3 c2 c3
    have hb : ∀ i, i < st.members.length → s0.birth (st.members.getD i 0) = st.birth (st.members.getD i 0) := by
      intro i hi'
      have := hmem i hi'
      rw [hb0 _ (by omega), d4 _ this]
    have hlt' : ∀ x ∈ ({ st with birth := s0.birth } : St).members,
        ({ st with birth := s0.birth } : St).birth x < typemaxInt := by
      intro x hx
      have hxn := hi.2 x hx
      show s0.birth x < typemaxInt
      rw [hb0 _ (by omega), d4 _ hxn]
      exact hlt x hx
    obtain ⟨hne, e2, e3⟩ := two_oldest_of_spec { st with birth := s0.birth }
      (fun j => s0.birth (st.members.getD j 0)) (fun _ => rfl) h2 hlt' k1 k2 hk1 hk2 c2 c3
    refine ⟨k1, k2, d.1.next, d.1.next + 1, hk1, hk2, hne, by omega, fun hc => ?_, fun hc => ?_, hm,
      fun i hi' => ?_, fun i hi' => ?_, fun i hi' hik => ?_, fun i hi' hik => ?_⟩
    · have := hi.2 _ hc; omega
    · have := hi.2 _ hc; omega
    · rw [← hb k1 hk1, ← hb i hi']; exact a2 i hi'
    · rw [← hb k1 hk1, ← hb i (by omega)]; exact a3 i hi'
    · rw [← hb k2 hk2, ← hb i hi']; exact e2 i hi' hik
    · rw [← hb k2 hk2, ← hb i (by omega)]; exact e3 i hi' hik
  cases hc : it.cx with
  | accepted b1 b2 ev =>
    rw [hc] at h; simp only [crossoverWith] at h
    obtain ⟨e1, e2, -, e4⟩ := cxChildren_fields d.1 b1 b2 ev
    exact finish _ (by rw [e1, d1]) e2 e4 h
  | rejected ev =>
    rw [hc] at h
    have hs : cfg.skip = false := by
      rcases hcx with ⟨_, _, _, he⟩ | hs
      · rw [hc] at he; cases he
      · exact hs
    simp only [crossoverWith, hs, Bool.false_eq_true, if_false] at h
    obtain ⟨e1, e2, -, e4⟩ := copyParents_fields d.1 (st.members.getD it.win1 0) d.2 ev
    exact finish _ (by rw [e1, d1]) e2 e4 h

/-- Property `regevol-skip-failures`: with `skip_mutation_failures = true`, a pass whose
mutation is rejected (no middleware) or whose crossover is rejected leaves the population
unchanged. -/
def skip_failures : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (it : Iter), cfg.skip = true →
    ((isCrossover cfg.cp it.u = false ∧ cfg.wrappers = false ∧ it.gen.accepted = false) ∨
     (isCrossover cfg.cp it.u = true ∧ ∃ ev, it.cx = .rejected ev)) →
    iterStep cfg st it = .ok st' → st'.members = st.members

theorem runGen_accepted (st : St) (p : Nat) (g : Gen) : (runGen st p g).2.2.1 = g.accepted := by
  cases g <;> rfl

theorem skip_failures_holds : skip_failures := by
  intro cfg st st' it hs hc h
  unfold iterStep at h
  rcases hc with ⟨hx, hw, ha⟩ | ⟨hx, ev, he⟩
  · rw [hx] at h
    simp only [Bool.false_eq_true, if_false] at h
    unfold iterMutation at h
    rw [hw] at h
    simp only [Bool.false_eq_true, if_false] at h
    unfold mutPlain at h
    obtain ⟨-, -, -, r4, -⟩ := replaceOldest_spec _ _ _ _ _ h
    rw [r4 (by rw [runGen_accepted, ha, hs]; rfl)]
    exact runGen_members (reset st) (st.members.getD it.win1 0) it.gen
  · rw [hx] at h
    simp only [if_true] at h
    unfold iterCrossover at h
    rw [he] at h
    simp only [crossoverWith, hs, if_true] at h
    cases h
    exact (dedup_fields _ _ _).1

/-- Property `regevol-pass-evals`: each pass adds to `num_evals` exactly the evaluations of the
work it did: the crossover's, the single `next_generation` call's without middleware, and with
middleware the sum over every `next_step` call the middleware made (also those whose result it
discarded). -/
def pass_evals : Prop :=
  ∀ (cfg : Cfg) (st st' : St) (it : Iter), iterStep cfg st it = .ok st' →
    st'.evals = st.evals + (if isCrossover cfg.cp it.u then it.cx.evals
      else if cfg.wrappers then rsum (it.attempts.map (·.gen.evals)) else it.gen.evals)

theorem pass_evals_holds : pass_evals := by
  intro cfg st st' it h
  unfold iterStep at h
  split at h
  · rename_i hx
    rw [if_pos hx]
    unfold iterCrossover at h
    have d2 := (dedup_fields st (st.members.getD it.win1 0) (st.members.getD it.win2 0)).2.1
    generalize dedupParents st (st.members.getD it.win1 0) (st.members.getD it.win2 0) = d at h d2
    cases hc : it.cx with
    | accepted b1 b2 ev =>
      rw [hc] at h; simp only [crossoverWith] at h
      rw [(replaceTwo_spec _ _ _ _ h).2.2.1, (cxChildren_fields _ _ _ _).2.2.1, d2]; rfl
    | rejected ev =>
      rw [hc] at h; simp only [crossoverWith] at h
      split at h
      · cases h; rw [d2]; rfl
      · rw [(replaceTwo_spec _ _ _ _ h).2.2.1, (copyParents_fields _ _ _ _).2.2.1, d2]; rfl
  · rename_i hx
    rw [if_neg hx]
    unfold iterMutation at h
    split at h
    · rename_i hw
      rw [if_pos hw]
      unfold mutWrapped at h
      split at h
      · rw [(replaceOldest_spec _ _ _ _ _ h).2.2.1]
        obtain ⟨-, b2, -, -, -, b6⟩ := runAttempts_basic it.attempts (reset st)
        have hre : (reset st).evals = st.evals := rfl
        have hrr : (reset st).results = [] := rfl
        rw [hre] at b2
        rw [hrr] at b6
        simp only [b2, b6, List.map_nil, List.nil_append]
      · cases h
    · rename_i hw
      rw [if_neg hw]
      unfold mutPlain at h
      rw [(replaceOldest_spec _ _ _ _ _ h).2.2.1]
      simp only [(runGen_fields _ _ _).2.2.1, (runGen_fields _ _ _).2.2.2]
      rfl

/-- The middleware error of `src/RegularizedEvolution.jl:139-143`. -/
def middlewareError : JlError :=
  .argumentError "Mutation middleware must return a result from `next_step`."

/-- Property `regevol-middleware-check`: in a mutation pass with middleware, `reg_evol_cycle`
throws the "must return a result from `next_step`" `ArgumentError` exactly when the returned
`attempt_id` is not the id of one of this pass's recorded `next_step` calls. -/
def middleware_check : Prop :=
  ∀ (cfg : Cfg) (st : St) (it : Iter), isCrossover cfg.cp it.u = false → cfg.wrappers = true →
    ((it.ret < 1 ∨ (it.attempts.length : Int) < it.ret) ↔ iterStep cfg st it = .error middlewareError)

theorem middleware_check_holds : middleware_check := by
  intro cfg st it hx hw
  have hlen : (runAttempts (reset st) it.attempts).results.length = it.attempts.length := by
    rw [(runAttempts_basic it.attempts (reset st)).2.2.2.1]; simp [reset]
  unfold iterStep
  rw [hx]
  simp only [Bool.false_eq_true, if_false]
  unfold iterMutation
  rw [hw]
  simp only [if_true]
  unfold mutWrapped
  constructor
  · intro hr
    rw [if_neg (by omega)]
    rfl
  · intro he
    split at he
    · cases hro : replaceOldest cfg.skip _ _ _ with
      | ok s => rw [hro] at he; cases he
      | error e =>
        rw [hro] at he; cases he
        have := replaceOldest_err _ _ _ _ _ hro
        simp [middlewareError] at this
    · omega

/-- Property `regevol-step-attempts`: `reset!` empties both `MutationStep` buffers, and after
it the `k` `next_step` calls of a pass are recorded in order with `attempt_id`s `1..k` and with
`k` distinct, newly allocated copies of their members; the population is untouched. -/
def step_attempts : Prop :=
  ∀ (st : St) (as : List Attempt),
    (reset st).results = [] ∧ (reset st).copies = [] ∧
    (runAttempts (reset st) as).results.length = as.length ∧
    (runAttempts (reset st) as).copies.length = as.length ∧
    (∀ j, j < as.length → ((runAttempts (reset st) as).results[j]?).map (·.2.2.1) = some (j + 1)) ∧
    (runAttempts (reset st) as).copies.Nodup ∧
    (∀ c ∈ (runAttempts (reset st) as).copies, st.next ≤ c ∧ c < (runAttempts (reset st) as).next) ∧
    (runAttempts (reset st) as).members = st.members

theorem step_attempts_holds : step_attempts := by
  intro st as
  obtain ⟨b1, -, -, b4, b5, -⟩ := runAttempts_basic as (reset st)
  obtain ⟨c1, c2⟩ := runAttempts_copies as (reset st) (by simp [reset]) (by simp [reset])
  have hid := runAttempts_ids as (reset st)
  simp only [reset, List.length_nil, Nat.zero_add] at b4 b5 hid
  refine ⟨rfl, rfl, b4, b5, hid, c1, fun c hc => ?_, b1⟩
  rcases c2 c hc with h | h
  · simp [reset] at h
  · exact h

/-- Property `regevol-crossover-prob`: a pass is a crossover exactly when the `rand()` draw
`u ∈ [0, 1)` is below `crossover_probability`, so crossover happens with probability
`crossover_probability` (never when it is 0). -/
def crossover_prob : Prop :=
  ∀ (cp u : Rat), 0 ≤ u → u < 1 → (isCrossover cp u = true ↔ u < cp)

theorem crossover_prob_refuted : ¬ crossover_prob := by
  intro h
  have := (h 0 0 (by decide) (by decide)).1 (by decide)
  exact absurd this (by decide)

/-! ## Satisfiable preconditions -/

/-- A two-member population with distinct allocated identities and finite births. -/
def exSt : St := ⟨[0, 1], fun x => (x : Int), 2, 0, [], [], []⟩

/-- A mutation pass whose `next_generation` returns a fresh, accepted child. -/
def exMut : Iter := ⟨1, 1, 0, .child true 5 1, [], 0, .rejected 0⟩

/-- A crossover pass with an accepted crossover. -/
def exCx : Iter := ⟨0, 0, 1, .child true 5 1, [], 0, .accepted 6 7 2⟩

/-- No middleware, `skip_mutation_failures = true`, `tournament_selection_n = 1`,
`crossover_probability = 0`. -/
def exCfg : Cfg := ⟨0, true, 1, false⟩

example : Inv exSt ∧
    (match regEvolCycle exCfg exSt (fun _ => exMut) with | .ok _ => true | .error _ => false) = true :=
  ⟨⟨by decide, by decide⟩, by decide⟩

example : isCrossover exCfg.cp exMut.u = false ∧
    (match iterStep exCfg exSt exMut with | .ok _ => true | .error _ => false) = true :=
  ⟨by decide, by decide⟩

example : 2 ≤ exSt.members.length ∧ Inv exSt ∧ (∀ x ∈ exSt.members, exSt.birth x < typemaxInt) ∧
    isCrossover exCfg.cp exCx.u = true ∧ (∃ b1 b2 ev, exCx.cx = .accepted b1 b2 ev) ∧
    (match iterStep exCfg exSt exCx with | .ok _ => true | .error _ => false) = true :=
  ⟨by decide, ⟨by decide, by decide⟩, by decide, by decide, ⟨6, 7, 2, rfl⟩, by decide⟩

example : exCfg.skip = true ∧
    (isCrossover exCfg.cp exCx.u = true ∧ ∃ ev, (⟨0, 0, 1, .child true 5 1, [], 0, .rejected 3⟩ : Iter).cx = .rejected ev) ∧
    (match iterStep exCfg exSt ⟨0, 0, 1, .child true 5 1, [], 0, .rejected 3⟩ with
      | .ok _ => true | .error _ => false) = true :=
  ⟨rfl, ⟨by decide, 3, rfl⟩, by decide⟩

example : isCrossover exCfg.cp exMut.u = false ∧ ({ exCfg with wrappers := true } : Cfg).wrappers = true :=
  ⟨by decide, rfl⟩

end SymReg.Population
