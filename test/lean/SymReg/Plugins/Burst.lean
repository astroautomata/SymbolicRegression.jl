import SymReg.Plugins.Dispatch

/-!
`src/plugins/MutationBurst.jl`. The mutation result is the existing population
model's (member, accepted, attempt_id, num_evals) tuple. Arbitrary next-step and
random-draw callbacks thread the entire mutable worker state, including the
shared RNG. Calls are recorded even when a rejected compound result is discarded.
-/
namespace SymReg.Plugins
open DynExpr

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-- `src/plugins/MutationBurst.jl:32-50`. -/
structure BurstConfig where
  retries : Nat := 4
  probability : Rat := 1 / 4
  steps : Nat := 2
  deriving DecidableEq, Repr

def ValidBurst (p : BurstConfig) : Prop :=
  1 ≤ p.retries ∧ 0 ≤ p.probability ∧ p.probability ≤ 1 ∧ 1 ≤ p.steps
instance (p : BurstConfig) : Decidable (ValidBurst p) := inferInstanceAs (Decidable (_ ∧ _))

private def retryError := JlError.argumentError "`retry_attempts` must be at least 1."
private def probabilityError := JlError.argumentError "`compound_probability` must be between 0 and 1."
private def stepsError := JlError.argumentError "`compound_max_steps` must be at least 1."

private def probabilityCheck {P W : Type} (lower upper : P → W → Jl Bool × W)
    (p : P) (w : W) : Jl Bool × W :=
  match lower p w with
  | (.ok true, w') => upper p w'
  | result => result

/- Source: src/plugins/MutationBurst.jl:36-49
function MutationBurstPlugin(;
    retry_attempts::Integer=4,
    compound_probability::Real=0.25,
    compound_max_steps::Integer=2,
)
    retry_attempts >= 1 || throw(ArgumentError("`retry_attempts` must be at least 1."))
    0 <= compound_probability <= 1 ||
        throw(ArgumentError("`compound_probability` must be between 0 and 1."))
    compound_max_steps >= 1 ||
        throw(ArgumentError("`compound_max_steps` must be at least 1."))
    return new(
        Int(retry_attempts), Float64(compound_probability), Int(compound_max_steps)
    )
end
-/
def makeBurst {R P S W : Type} (retries : R) (probability : P) (steps : S)
    (checkRetries : R → W → Jl Bool × W) (lower upper : P → W → Jl Bool × W)
    (checkSteps : S → W → Jl Bool × W) (castRetries : R → W → Jl Int64 × W)
    (castProb : P → W → Jl JF × W) (castSteps : S → W → Jl Int64 × W)
    (w : W) : Jl (Int64 × JF × Int64) × W :=
  match checkRetries retries w with
  | (.error e, w') => (.error e, w')
  | (.ok false, w') => (.error retryError, w')
  | (.ok true, w') =>
    match probabilityCheck lower upper probability w' with
    | (.error e, w'') => (.error e, w'')
    | (.ok false, w'') => (.error probabilityError, w'')
    | (.ok true, w'') =>
      match checkSteps steps w'' with
      | (.error e, after) => (.error e, after)
      | (.ok false, after) => (.error stepsError, after)
      | (.ok true, after) =>
        match castRetries retries after with
        | (.error e, after') => (.error e, after')
        | (.ok nr, after') =>
          match castProb probability after' with
          | (.error e, after'') => (.error e, after'')
          | (.ok p, after'') =>
            let (last, state) := castSteps steps after''
            (last.map (fun ns => (nr, p, ns)), state)

/-- Existing `MutationStepResult` representation, `src/Plugin.jl:486-491`. -/
abbrev StepResult := Nat × Bool × Nat × Rat

def StepResult.accepted (r : StepResult) : Bool := r.2.1

def StepResult.member (r : StepResult) : Nat := r.1

structure BurstRun (S : Type) where
  result : StepResult
  state : S
  calls : List (Nat × StepResult)

/-- Retry loop, `src/plugins/MutationBurst.jl:56-59`. Each retry uses the
original parent, with the latest worker state. -/
def retryBurst {S : Type} (next : Nat → S → StepResult × S) (parent : Nat) :
    Nat → StepResult → S → BurstRun S
  | 0, result, state => ⟨result, state, []⟩
  | fuel + 1, result, state =>
    if result.accepted then ⟨result, state, []⟩ else
    let attempted := next parent state
    let tail := retryBurst next parent fuel attempted.1 attempted.2
    { tail with calls := (parent, attempted.1) :: tail.calls }

/-- Compound loop, `src/plugins/MutationBurst.jl:61-67`. A rejected next step
keeps the previous accepted result, while retaining all effects of that attempt. -/
def compoundBurst {S : Type} (next : Nat → S → StepResult × S)
    (draw : S → Rat × S) (probability : Rat) : Nat → StepResult → S → BurstRun S
  | 0, result, state => ⟨result, state, []⟩
  | fuel + 1, result, state =>
    let random := draw state
    if random.1 < probability then
      let attempted := next result.member random.2
      if !attempted.1.accepted then
        ⟨result, attempted.2, [(result.member, attempted.1)]⟩
      else
        let tail := compoundBurst next draw probability fuel attempted.1 attempted.2
        { tail with calls := (result.member, attempted.1) :: tail.calls }
    else ⟨result, random.2, []⟩

/-- Callable plugin, `src/plugins/MutationBurst.jl:54-69`. -/
def runBurst {S : Type} (p : BurstConfig) (next : Nat → S → StepResult × S)
    (draw : S → Rat × S) (parent : Nat) (state : S) : BurstRun S :=
  let first := next parent state
  let retried := retryBurst next parent (p.retries - 1) first.1 first.2
  if !retried.result.accepted then
    { retried with calls := (parent, first.1) :: retried.calls }
  else
    let compounded := compoundBurst next draw p.probability (p.steps - 1)
      retried.result retried.state
    { compounded with calls := (parent, first.1) :: (retried.calls ++ compounded.calls) }

/-- `src/plugins/MutationBurst.jl:52`: state-independent middleware factory. -/
def wrapBurst {S : Type} (_state : S) (p : BurstConfig) : BurstConfig := p

private theorem retry_spec {S : Type} (next : Nat → S → StepResult × S) (parent : Nat) :
    ∀ fuel r state,
    let out := retryBurst next parent fuel r state
    out.calls.length ≤ fuel ∧ (out.result = r ∨ (parent, out.result) ∈ out.calls) ∧
    ∀ call ∈ out.calls, call.1 = parent := by
  intro fuel
  induction fuel with
  | zero => intro r state; simp [retryBurst]
  | succ fuel ih =>
    intro r state
    simp only [retryBurst]
    split
    · simp
    · obtain ⟨hb, hr, hp⟩ := ih (next parent state).1 (next parent state).2
      refine ⟨by simpa using Nat.succ_le_succ hb, ?_, ?_⟩
      · right
        rcases hr with hr | hr
        · simp [hr]
        · simp [hr]
      · intro call hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · rfl
        · exact hp call hc

private theorem compound_spec {S : Type} (next : Nat → S → StepResult × S)
    (draw : S → Rat × S) (probability : Rat) : ∀ fuel r state,
    let out := compoundBurst next draw probability fuel r state
    out.calls.length ≤ fuel ∧
    (out.result = r ∨ ∃ call ∈ out.calls, call.2 = out.result) ∧
    (r.accepted = true → out.result.accepted = true) := by
  intro fuel
  induction fuel with
  | zero => intro r state; simp [compoundBurst]
  | succ fuel ih =>
    intro r state
    simp only [compoundBurst]
    split
    · split
      · simp
      · rename_i hacc
        obtain ⟨hb, hr, ha⟩ := ih (next r.member (draw state).2).1 (next r.member (draw state).2).2
        refine ⟨by simpa using Nat.succ_le_succ hb, ?_, ?_⟩
        · right
          rcases hr with hr | ⟨call, hc, he⟩
          · exact ⟨(r.member, (next r.member (draw state).2).1), by simp, hr.symm⟩
          · exact ⟨call, by simp [hc], he⟩
        · intro _
          exact ha (by simpa using hacc)
    · simp

def burst_constructor : Prop := ∀ (R P S W : Type) (r : R) (p : P) (s : S)
    checkRetries lower upper checkSteps castRetries castProb castSteps (w : W),
  let out := makeBurst r p s checkRetries lower upper checkSteps castRetries castProb castSteps w
  (∀ e a, checkRetries r w = (.error e, a) → out = (.error e, a)) ∧
  (∀ a, checkRetries r w = (.ok false, a) → out = (.error retryError, a)) ∧
  ∀ a, checkRetries r w = (.ok true, a) →
    (∀ e b, lower p a = (.error e, b) → out = (.error e, b)) ∧
    (∀ b, lower p a = (.ok false, b) → out = (.error probabilityError, b)) ∧
    ∀ b, lower p a = (.ok true, b) →
      (∀ e c, upper p b = (.error e, c) → out = (.error e, c)) ∧
      (∀ c, upper p b = (.ok false, c) → out = (.error probabilityError, c)) ∧
      ∀ c, upper p b = (.ok true, c) →
        (∀ e d, checkSteps s c = (.error e, d) → out = (.error e, d)) ∧
        (∀ d, checkSteps s c = (.ok false, d) → out = (.error stepsError, d)) ∧
        ∀ d, checkSteps s c = (.ok true, d) →
          (∀ e f, castRetries r d = (.error e, f) → out = (.error e, f)) ∧
          ∀ nr f, castRetries r d = (.ok nr, f) →
            (∀ e g, castProb p f = (.error e, g) → out = (.error e, g)) ∧
            ∀ pp g, castProb p f = (.ok pp, g) →
              (∀ e h, castSteps s g = (.error e, h) → out = (.error e, h)) ∧
              (∀ ns h, castSteps s g = (.ok ns, h) → out = (.ok (nr, pp, ns), h))

theorem burst_constructor_holds : burst_constructor := by
  intro R P S W r p s checks lo hi maxCheck retryConvert probConvert stepConvert w
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro e a ha; simp [makeBurst, ha]
  · intro a ha; simp [makeBurst, ha]
  intro a ha
  refine ⟨?_, ?_, ?_⟩
  · intro e b hb; simp [makeBurst, ha, probabilityCheck, hb]
  · intro b hb; simp [makeBurst, ha, probabilityCheck, hb]
  intro b hb
  refine ⟨?_, ?_, ?_⟩
  · intro e c hc; simp [makeBurst, ha, probabilityCheck, hb, hc]
  · intro c hc; simp [makeBurst, ha, probabilityCheck, hb, hc]
  intro c hc
  refine ⟨?_, ?_, ?_⟩
  · intro e d hd; simp [makeBurst, ha, probabilityCheck, hb, hc, hd]
  · intro d hd; simp [makeBurst, ha, probabilityCheck, hb, hc, hd]
  intro d hd
  refine ⟨?_, ?_⟩
  · intro e f hf; simp [makeBurst, ha, probabilityCheck, hb, hc, hd, hf]
  intro nr f hf
  refine ⟨?_, ?_⟩
  · intro e g hg; simp [makeBurst, ha, probabilityCheck, hb, hc, hd, hf, hg]
  intro pp g hg
  constructor
  · intro e h hh; simp [makeBurst, ha, probabilityCheck, hb, hc, hd, hf, hg, hh, Except.map]
  · intro ns h hh; simp [makeBurst, ha, probabilityCheck, hb, hc, hd, hf, hg, hh, Except.map]

def burst_retry_original : Prop := ∀ (S : Type) (next : Nat → S → StepResult × S)
    parent fuel r (state : S),
  let out := retryBurst next parent fuel r state
  (∀ call ∈ out.calls, call.1 = parent) ∧
  (r.accepted = true → out = ⟨r, state, []⟩) ∧
  (∀ i call, out.calls[i]? = some call → call.2.accepted = true →
    i + 1 = out.calls.length ∧ out.result = call.2) ∧
  (out.result.accepted = false → out.calls.length = fuel)

theorem burst_retry_original_holds : burst_retry_original := by
  intro S next parent fuel r state
  refine ⟨(retry_spec next parent fuel r state).2.2, ?_⟩
  induction fuel generalizing r state with
  | zero => simp [retryBurst]
  | succ fuel ih =>
    by_cases ha : r.accepted = true
    · simp [retryBurst, ha]
    · cases hn : next parent state with
      | mk first nextState =>
       rw [retryBurst, if_neg ha, hn]
       dsimp only
       have htail := ih first nextState
       refine ⟨fun h => False.elim (ha h), ?_, ?_⟩
       · intro i call hi hc
         cases i with
         | zero =>
           have hfirst : (parent, first) = call := Option.some.inj hi
           subst call
           obtain ⟨h, _⟩ := htail
           rw [h hc]
           exact ⟨rfl, rfl⟩
         | succ i =>
           obtain ⟨_, h, _⟩ := htail
           obtain ⟨hlen, hres⟩ := h i call hi hc
           exact ⟨by simp only [List.length_cons]; omega, hres⟩
       · intro hr
         exact congrArg Nat.succ (htail.2.2 hr)

def burst_returns_observed : Prop := ∀ (S : Type) (p : BurstConfig)
    (next : Nat → S → StepResult × S) (draw : S → Rat × S) parent state,
  ∃ call ∈ (runBurst (wrapBurst state p) next draw parent state).calls,
    call.2 = (runBurst (wrapBurst state p) next draw parent state).result

theorem burst_returns_observed_holds : burst_returns_observed := by
  intro S p next draw parent state
  have hr := (retry_spec next parent (p.retries - 1) (next parent state).1 (next parent state).2).2.1
  simp only [wrapBurst, runBurst]
  by_cases ha : (!(retryBurst next parent (p.retries - 1) (next parent state).1
    (next parent state).2).result.accepted) = true <;>
    simp only [ha, ite_true]
  · rcases hr with hr | hr
    · exact ⟨(parent, (next parent state).1), by simp, hr.symm⟩
    · exact ⟨(parent, _), by simp [hr], rfl⟩
  · have hc := (compound_spec next draw p.probability (p.steps - 1)
      (retryBurst next parent (p.retries - 1) (next parent state).1 (next parent state).2).result
      (retryBurst next parent (p.retries - 1) (next parent state).1 (next parent state).2).state).2.1
    rcases hc with hc | ⟨call, hm, he⟩
    · rcases hr with hr | hr
      · exact ⟨(parent, (next parent state).1), by simp, (hc.trans hr).symm⟩
      · exact ⟨(parent, _), by simp [hr], hc.symm⟩
    · exact ⟨call, by simp [hm], he⟩

def burst_call_bound : Prop := ∀ (S : Type) (p : BurstConfig)
    (next : Nat → S → StepResult × S) (draw : S → Rat × S) parent state,
  ValidBurst p →
  1 ≤ (runBurst p next draw parent state).calls.length ∧
  (runBurst p next draw parent state).calls.length ≤ p.retries + p.steps - 1

theorem burst_call_bound_holds : burst_call_bound := by
  intro S p next draw parent state hp
  have hr := (retry_spec next parent (p.retries - 1) (next parent state).1 (next parent state).2).1
  have hc := (compound_spec next draw p.probability (p.steps - 1)
    (retryBurst next parent (p.retries - 1) (next parent state).1 (next parent state).2).result
    (retryBurst next parent (p.retries - 1) (next parent state).1 (next parent state).2).state).1
  simp only [runBurst]
  split <;> simp only [List.length_cons, List.length_append] <;> obtain ⟨h1, _, _, h2⟩ := hp <;> omega

def burst_compound_keeps_acceptance : Prop := ∀ (S : Type)
    (next : Nat → S → StepResult × S) (draw : S → Rat × S) probability fuel r (state : S),
  r.accepted = true → (compoundBurst next draw probability fuel r state).result.accepted = true

theorem burst_compound_keeps_acceptance_holds : burst_compound_keeps_acceptance := by
  intro S next draw probability fuel r state
  exact (compound_spec next draw probability fuel r state).2.2

private theorem compound_disabled {S : Type} (next : Nat → S → StepResult × S)
    (draw : S → Rat × S) (hd : ∀ state, 0 ≤ (draw state).1) (fuel : Nat) r state :
    (compoundBurst next draw 0 fuel r state).result = r ∧
    (compoundBurst next draw 0 fuel r state).calls = [] ∧
    (compoundBurst next draw 0 fuel r state).state =
      (if fuel = 0 then state else (draw state).2) := by
  cases fuel with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ fuel =>
    simp [compoundBurst, Rat.not_lt.mpr (hd state)]

def burst_single_step : Prop := ∀ (S : Type) (next : Nat → S → StepResult × S)
    (draw : S → Rat × S) probability parent state,
  (let out := runBurst (wrapBurst state ⟨1, probability, 1⟩) next draw parent state
   out.result = (next parent state).1 ∧ out.state = (next parent state).2 ∧
     out.calls = [(parent, (next parent state).1)]) ∧
  ∀ steps, (∀ state, 0 ≤ (draw state).1) →
    let out := runBurst ⟨1, 0, steps⟩ next draw parent state
    out.result = (next parent state).1 ∧ out.calls = [(parent, (next parent state).1)] ∧
    out.state = if (next parent state).1.accepted && 1 < steps
      then (draw (next parent state).2).2 else (next parent state).2

theorem burst_single_step_holds : burst_single_step := by
  intro S next draw probability parent state
  constructor
  · simp only [wrapBurst, runBurst, Nat.sub_self, retryBurst]
    split <;> simp [compoundBurst]
  · intro steps hd
    simp only [runBurst, Nat.sub_self, retryBurst]
    cases steps with
    | zero => split <;> simp [compoundBurst]
    | succ steps =>
      cases steps with
      | zero => split <;> simp [compoundBurst]
      | succ steps =>
        cases ha : (next parent state).1.accepted <;>
          simp [ha, compoundBurst, Rat.not_lt.mpr (hd (next parent state).2)]

example : ValidBurst {} := by decide
example : ValidBurst ⟨1, 0, 1⟩ := by decide
example : ∀ state : Nat, (0 : Rat) ≤ ((0 : Rat), state).1 := by
  intro state
  change (0 : Rat) ≤ 0
  decide

end SymReg.Plugins
