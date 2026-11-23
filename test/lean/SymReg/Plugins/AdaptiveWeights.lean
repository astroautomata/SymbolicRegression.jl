import SymReg.Plugins.Dispatch
import SymReg.Loss.Core

/-!
`src/plugins/AdaptiveMutationWeights.jl`. Independent parallel vectors are
represented as a list of rows. The event arithmetic rounds each Float64
operation. Mutation events and weight pairs reuse the mutation-engine model.
-/
namespace SymReg.Plugins
open DynExpr SymReg.MutateGen

attribute [local semireducible] Rat.add Rat.mul Rat.inv Rat.sub

inductive Reward where
  | cost | loss | other (name : String)
  deriving DecidableEq, Repr

/-- `src/plugins/AdaptiveMutationWeights.jl:47-72`. -/
structure AdaptiveConfig where
  smoothing : Rat := 1 / 50
  floor : Rat := 1 / 20
  reward : Reward := .cost
  strength : Rat := 1 / 2
  deriving DecidableEq, Repr

def ValidAdaptive (p : AdaptiveConfig) : Prop :=
  0 ≤ p.smoothing ∧ p.smoothing ≤ 1 ∧ 0 < p.floor ∧ p.floor ≤ 1 ∧
  (p.reward = .cost ∨ p.reward = .loss) ∧ 0 ≤ p.strength ∧ p.strength ≤ 1
instance (p : AdaptiveConfig) : Decidable (ValidAdaptive p) := inferInstanceAs (Decidable (_ ∧ _))

structure ConvertedAdaptive where
  smoothing : JF := .fin (1 / 50)
  floor : JF := .fin (1 / 20)
  reward : Reward := .cost
  strength : JF := .fin (1 / 2)


private def inAdaptiveRange (strict : Bool) : JF → Bool
  | .fin x => decide ((if strict then 0 < x else 0 ≤ x) ∧ x ≤ 1)
  | _ => false
/- Source: src/plugins/AdaptiveMutationWeights.jl:52-71
function AdaptiveMutationWeightsPlugin(;
    smoothing::Real=0.02,
    floor::Real=0.05,
    reward::Symbol=:cost,
    adaptation_strength::Real=0.5,
)
    converted_smoothing = Float64(smoothing)
    converted_floor = Float64(floor)
    converted_adaptation_strength = Float64(adaptation_strength)
    0 <= converted_smoothing <= 1 ||
        throw(ArgumentError("`smoothing` must be between 0 and 1."))
    0 < converted_floor <= 1 || throw(ArgumentError("`floor` must be in (0, 1]."))
    reward in (:cost, :loss) ||
        throw(ArgumentError("`reward` must be either `:cost` or `:loss`."))
    0 <= converted_adaptation_strength <= 1 ||
        throw(ArgumentError("`adaptation_strength` must be between 0 and 1."))
    return new(
        converted_smoothing, converted_floor, reward, converted_adaptation_strength
    )
end
-/
def makeAdaptive {W : Type} (smoothing floor strength : ExceptT JlError (StateM W) JF)
    (reward : Reward) : ExceptT JlError (StateM W) ConvertedAdaptive := do
  let s ← smoothing
  let f ← floor
  let a ← strength
  if !(inAdaptiveRange false s) then throw (.argumentError "`smoothing` must be between 0 and 1.")
  else if !(inAdaptiveRange true f) then throw (.argumentError "`floor` must be in (0, 1].")
  else if ¬ (reward = .cost ∨ reward = .loss) then
    throw (.argumentError "`reward` must be either `:cost` or `:loss`.")
  else if !(inAdaptiveRange false a) then
    throw (.argumentError "`adaptation_strength` must be between 0 and 1.")
  else pure ⟨s, f, reward, a⟩

-- Source: src/plugins/AdaptiveMutationWeights.jl:76
def defaultAdaptive : Jl ConvertedAdaptive :=
  ((makeAdaptive (W := Unit) (pure (.fin (5764607523034235 / 288230376151711744)))
    (pure (.fin (3602879701896397 / 72057594037927936))) (pure (.fin (1 / 2))) .cost).run ()).1

/-- `src/plugins/AdaptiveMutationWeights.jl:92-94`. -/
def skipAdaptive : Kind → Bool
  | .simplify | .doNothing => true
  | _ => false

/-- `src/plugins/AdaptiveMutationWeights.jl:102-107`, vectors zipped by index. -/
structure AdaptiveSlot where
  attempts : JF := .fin 0
  successes : JF := .fin 0
  multiplier : JF := .fin 1
  active : Bool := true
  deriving DecidableEq, Repr

private def roundAdaptive := SymReg.Loss.LossPrecision.float64.round

private def addAdaptive (x y : JF) : JF := roundAdaptive (x + y)
private def divAdaptive (x y : JF) : JF := roundAdaptive (x / y)

/- Source: src/plugins/AdaptiveMutationWeights.jl:109-113
function init_plugin_state(::AdaptiveMutationWeightsPlugin, options, dataset)
    n = length(options.mutations)
    active = [!skip_in_adaptive_weights(mutation) for (mutation, _) in options.mutations]
    return AdaptiveMutationWeightsState(zeros(n), zeros(n), ones(n), active)
end
-/
structure AdaptiveInitialization where
  attempts : List JF
  successes : List JF
  multipliers : List JF
  active : List (Option Bool)
  deriving DecidableEq

-- Julia Base v1.12.0, base/array.jl:783-801,823-861,901:
-- `collect(::Generator)`, `collect_to!`, and the live bounds check of `iterate(::Array)`.
-- The destination's shape is captured before iteration. An early end leaves
-- its unfilled Bool slots unspecified. An out-of-range unchecked store is UB.
private def adaptiveCollectOverflow : JlError := .undefinedBehavior "adaptive mask collection"

private def collectAdaptive {M W : Type} (contents : W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool) :
    Nat → Nat → W → Jl (List (Option Bool)) × W
  | fuel, i, w =>
    match (contents w)[i]? with
    | none => (.ok (List.replicate fuel none), w)
    | some none => (.error .undefRefError, w)
    | some (some m) =>
      match (skip m).run w with
      | (.error e, after) => (.error e, after)
      | (.ok b, after) =>
        match fuel with
        | 0 => (.error adaptiveCollectOverflow, after)
        | fuel + 1 =>
          let (out, final) := collectAdaptive contents skip fuel (i + 1) after
          (out.map (some (!b) :: ·), final)

/-- Each access to `options.mutations` may dispatch. After the second access,
the captured vector is read live, including writes through other references. -/
def initAdaptive {M W V : Type} (getVector : ExceptT JlError (StateM W) V)
    (contents : V → W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool) (w : W) : Jl AdaptiveInitialization × W :=
  match getVector.run w with
  | (.error e, after) => (.error e, after)
  | (.ok v, counted) =>
    let n := (contents v counted).length
    match getVector.run counted with
    | (.error e, after) => (.error e, after)
    | (.ok live, start) =>
      let (result, after) := collectAdaptive (contents live) skip (contents live start).length 0 start
      (result.map (fun mask =>
        ⟨List.replicate n (.fin 0), List.replicate n (.fin 0), List.replicate n (.fin 1), mask⟩), after)

/-- One vector-element update at a zero-based index. -/
def changeAt {A : Type} (f : A → A) : List A → Nat → List A
  | [], _ => []
  | x :: xs, 0 => f x :: xs
  | x :: xs, i + 1 => x :: changeAt f xs i

/-- `src/plugins/AdaptiveMutationWeights.jl:126-133`, with strict IEEE comparison. -/
def improves (p : AdaptiveConfig) (e : Event) : Bool :=
  let before := if p.reward = .cost then e.beforeCost else e.beforeLoss
  let after := if p.reward = .cost then e.afterCost else e.afterLoss
  e.accepted && after.any (fun value => SymReg.Population.flt value before)

def countAttempt (success : Bool) (s : AdaptiveSlot) : AdaptiveSlot :=
  { s with
    attempts := addAdaptive s.attempts (.fin 1)
    successes := if success then addAdaptive s.successes (.fin 1) else s.successes }

def activeSlots (s : List AdaptiveSlot) : List AdaptiveSlot := s.filter (·.active)

/-- Target clamp, `src/plugins/AdaptiveMutationWeights.jl:144-147`. -/
def clampTarget (floor ratio : JF) : JF :=
  let upper := divAdaptive (.fin 1) floor
  if SymReg.Population.flt ratio floor then floor
  else if SymReg.Population.flt upper ratio then upper else ratio

/-- EMA, `src/plugins/AdaptiveMutationWeights.jl:148`. -/
def ema (smoothing old target : JF) : JF :=
  addAdaptive (roundAdaptive (roundAdaptive (JF.fin 1 - smoothing) * old))
    (roundAdaptive (smoothing * target))

def rescaleActive (s : List AdaptiveSlot) (mean : JF) : List AdaptiveSlot :=
  s.map (fun x => if x.active then { x with multiplier := divAdaptive x.multiplier mean } else x)

/-- Active-mean normalization, `src/plugins/AdaptiveMutationWeights.jl:150-159`. -/
def normalizeActive (s : List AdaptiveSlot) (n : Nat) : List AdaptiveSlot :=
  let sum := s.foldl (fun acc x => if x.active then addAdaptive acc x.multiplier else acc) (.fin 0)
  rescaleActive s (divAdaptive sum (roundAdaptive (.fin (n : Rat))))

/-- `src/plugins/AdaptiveMutationWeights.jl:115-161`; caller passes Event.idx
in Julia's one-based numbering. Inactive kinds return before any accounting. -/
def adaptMutation (s : List AdaptiveSlot) (p : AdaptiveConfig) (e : Event) :
    Jl (List AdaptiveSlot) :=
  match (if 0 < e.idx then s[e.idx - 1]? else none) with
  | none => throw .boundsError
  | some selected =>
    if !selected.active then pure s else
    let counted := changeAt (countAttempt (improves p e)) s (e.idx - 1)
    let active := activeSlots counted
    let n := active.length
    let meanRate := divAdaptive
      (addAdaptive (active.foldl (fun acc x => addAdaptive acc x.successes) (.fin 0))
        (roundAdaptive (.fin (n : Rat))))
      (addAdaptive (active.foldl (fun acc x => addAdaptive acc x.attempts) (.fin 0))
        (roundAdaptive (.fin (2 * (n : Rat)))))
    let row := countAttempt (improves p e) selected
    let rate := divAdaptive (addAdaptive row.successes (.fin 1)) (addAdaptive row.attempts (.fin 2))
    let target := clampTarget (.fin p.floor) (divAdaptive rate meanRate)
    let learned := changeAt (fun x => { x with multiplier := ema (.fin p.smoothing) x.multiplier target })
      counted (e.idx - 1)
    pure (normalizeActive learned n)

/-- sqrt/power and multiplication in `src/plugins/AdaptiveMutationWeights.jl:177-179`.
The sqrt service is used exactly at exponent .5; exponent 0 avoids both. -/
structure WeightServices where
  sqrt : JF → JF
  power : JF → Rat → JF
  mul : JF → JF → JF := JF.mul

/-- `src/plugins/AdaptiveMutationWeights.jl:163-182`. -/
def conditionAdaptive {W : Type} (rt : WeightServices) (s : List AdaptiveSlot) (p : AdaptiveConfig)
    (readMutations : W → Jl Nat × W) (weights : Weights) (world : W) : Jl Weights × W :=
  let (read, afterRead) := readMutations world
  let out := do
    let n ← read
    if p.strength = 0 then return weights
    if n > weights.length ∨ n > s.length then
      throw (.undefinedBehavior "parallel mutation weights")
    else
      return ((weights.take n).zip s).map (fun (w, slot) =>
        let effective := if p.strength = 1 / 2 then rt.sqrt slot.multiplier
          else rt.power slot.multiplier p.strength
        (w.1, rt.mul w.2 effective)) ++ weights.drop n
  (out, afterRead)

def adaptive_constructor : Prop := ∀ (W : Type)
    (smoothing floor strength : ExceptT JlError (StateM W) JF) reward w,
  let out := (makeAdaptive smoothing floor strength reward).run w
  (∀ e w', smoothing.run w = (.error e, w') → out = (.error e, w')) ∧
  (∀ s w' e w'', smoothing.run w = (.ok s, w') → floor.run w' = (.error e, w'') →
    out = (.error e, w'')) ∧
  (∀ s w' f w'' e w''', smoothing.run w = (.ok s, w') → floor.run w' = (.ok f, w'') →
    strength.run w'' = (.error e, w''') → out = (.error e, w''')) ∧
  (∀ s w' f w'' a w''', smoothing.run w = (.ok s, w') → floor.run w' = (.ok f, w'') →
    strength.run w'' = (.ok a, w''') →
    let checks := [
      (inAdaptiveRange false s, "`smoothing` must be between 0 and 1."),
      (inAdaptiveRange true f, "`floor` must be in (0, 1]."),
      (decide (reward = .cost ∨ reward = .loss), "`reward` must be either `:cost` or `:loss`."),
      (inAdaptiveRange false a, "`adaptation_strength` must be between 0 and 1.")]
    match checks.find? (fun check => !check.1) with
    | some (_, msg) => out = (.error (.argumentError msg), w''')
    | none => out = (.ok ⟨s, f, reward, a⟩, w''')) ∧
  defaultAdaptive = .ok ⟨.fin (5764607523034235 / 288230376151711744),
    .fin (3602879701896397 / 72057594037927936), .cost, .fin (1 / 2)⟩

private theorem adaptive_bind_run {W A B : Type} (x : ExceptT JlError (StateM W) A)
    (f : A → ExceptT JlError (StateM W) B) (w : W) :
    (x >>= f).run w = match x.run w with
      | (.error e, w') => (.error e, w')
      | (.ok a, w') => (f a).run w' := by
  rcases h : x.run w with ⟨r, s⟩
  change x w = (r, s) at h
  cases r <;> simp [Bind.bind, ExceptT.bind, StateT.bind, h, ExceptT.bindCont] <;> rfl

theorem adaptive_constructor_holds : adaptive_constructor := by
  intro W smoothing floor strength reward w
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e w' hs
    simp only [makeAdaptive, adaptive_bind_run, hs]
  · intro s w' e w'' hs hf
    simp only [makeAdaptive, adaptive_bind_run, hs, hf]
  · intro s w' f w'' e w''' hs hf ha
    simp only [makeAdaptive, adaptive_bind_run, hs, hf, ha]
  · intro s w' f w'' a w''' hs hf ha
    simp only [makeAdaptive, adaptive_bind_run, hs, hf, ha, List.find?_cons]
    cases h₁ : inAdaptiveRange false s <;> cases h₂ : inAdaptiveRange true f <;>
      by_cases hr : reward = .cost ∨ reward = .loss <;> cases h₃ : inAdaptiveRange false a <;>
      simp [h₁, h₂, hr, h₃, throw, throwThe, MonadExceptOf.throw,
        pure, ExceptT.pure, StateT.pure, ExceptT.run, StateT.run] <;> rfl
  · have hs : inAdaptiveRange false (.fin (5764607523034235 / 288230376151711744)) = true := by decide +kernel
    have hf : inAdaptiveRange true (.fin (3602879701896397 / 72057594037927936)) = true := by decide +kernel
    have ha : inAdaptiveRange false (.fin (1 / 2)) = true := by decide +kernel
    unfold defaultAdaptive
    simp only [makeAdaptive, adaptive_bind_run, show ∀ x : JF, ∀ w : Unit,
      (pure x : ExceptT JlError (StateM Unit) JF).run w = (.ok x, w) from fun _ _ => rfl,
      hs, hf, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, not_true_eq_false, or_true, true_or]
    rfl

/-- Calls successfully collected before the traversal stopped. Slot reads use
the world left by the previous call, so replacing a later slot is observable. -/
inductive SkipPrefix {M W : Type} (contents : W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool) :
    Nat → W → List Bool → W → Prop where
  | nil (i w) : SkipPrefix contents skip i w [] w
  | cons {i m w mid bs final} (b : Bool) (read : (contents w)[i]? = some (some m))
      (head : (skip m).run w = (.ok b, mid))
      (tail : SkipPrefix contents skip (i + 1) mid bs final) :
      SkipPrefix contents skip i w (b :: bs) final

private def SkipError {M W : Type} (contents : W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool)
    (i : Nat) (full : Prop) (before : W) (e : JlError) (after : W) : Prop :=
  ((contents before)[i]? = some none ∧ e = .undefRefError ∧ after = before) ∨
  ∃ m, (contents before)[i]? = some (some m) ∧
    ((skip m).run before = (.error e, after) ∨
     (full ∧ e = adaptiveCollectOverflow ∧ ∃ b, (skip m).run before = (.ok b, after)))

private def AdaptiveResult {M W : Type} (contents : W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool) (n i : Nat) (w : W)
    (out : Jl (List (Option Bool)) × W) : Prop :=
  match out with
  | (.ok mask, after) =>
    ∃ bs, SkipPrefix contents skip i w bs after ∧ bs.length ≤ n ∧
      (contents after)[i + bs.length]? = none ∧
      mask = bs.map (fun b => some (!b)) ++ List.replicate (n - bs.length) none
  | (.error e, after) =>
    ∃ bs mid, SkipPrefix contents skip i w bs mid ∧ bs.length ≤ n ∧
      SkipError contents skip (i + bs.length) (bs.length = n) mid e after

private theorem collectAdaptive_holds {M W : Type} (contents : W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool) (n i : Nat) (w : W) :
    AdaptiveResult contents skip n i w (collectAdaptive contents skip n i w) := by
  induction n generalizing i w with
  | zero =>
    rw [collectAdaptive]
    cases h : (contents w)[i]? with
    | none => exact ⟨[], .nil i w, Nat.le_refl _, by simpa using h, rfl⟩
    | some slot =>
      cases slot with
      | none => exact ⟨[], w, .nil i w, Nat.le_refl _, Or.inl ⟨by simpa using h, rfl, rfl⟩⟩
      | some m =>
        rcases hs : (skip m).run w with ⟨r, after⟩
        dsimp only
        rw [hs]
        cases r with
        | error e => exact ⟨[], w, .nil i w, Nat.le_refl _, Or.inr ⟨m, by simpa using h, Or.inl hs⟩⟩
        | ok b => exact ⟨[], w, .nil i w, Nat.le_refl _, Or.inr ⟨m, by simpa using h,
            Or.inr ⟨rfl, rfl, b, hs⟩⟩⟩
  | succ n ih =>
    rw [collectAdaptive]
    cases h : (contents w)[i]? with
    | none => exact ⟨[], .nil i w, Nat.zero_le _, by simpa using h, rfl⟩
    | some slot =>
      cases slot with
      | none => exact ⟨[], w, .nil i w, Nat.zero_le _, Or.inl ⟨by simpa using h, rfl, rfl⟩⟩
      | some m =>
        rcases hs : (skip m).run w with ⟨r, mid⟩
        dsimp only
        rw [hs]
        cases r with
        | error e => exact ⟨[], w, .nil i w, Nat.zero_le _, Or.inr ⟨m, by simpa using h, Or.inl hs⟩⟩
        | ok b =>
          have tail := ih (i + 1) mid
          rcases ht : collectAdaptive contents skip n (i + 1) mid with ⟨r, after⟩
          rw [ht] at tail
          dsimp only
          rw [ht]
          cases r with
          | error e =>
            obtain ⟨bs, prev, trace, hlen, hfail⟩ := tail
            refine ⟨b :: bs, prev, .cons b h hs trace, by simp; omega, ?_⟩
            simpa [Nat.add_assoc, Nat.add_comm 1] using hfail
          | ok mask =>
            obtain ⟨bs, trace, hlen, hd, hm⟩ := tail
            refine ⟨b :: bs, .cons b h hs trace, by simp; omega, ?_, ?_⟩
            · simpa [Nat.add_assoc, Nat.add_comm 1] using hd
            · simp [hm]

def adaptive_initial_state : Prop := ∀ (M W V : Type)
    (getVector : ExceptT JlError (StateM W) V) (contents : V → W → List (Option M))
    (skip : M → ExceptT JlError (StateM W) Bool) (w : W),
  let out := initAdaptive getVector contents skip w
  (∀ e after, getVector.run w = (.error e, after) → out = (.error e, after)) ∧
  ∀ v counted, getVector.run w = (.ok v, counted) →
    (∀ e after, getVector.run counted = (.error e, after) → out = (.error e, after)) ∧
    ∀ live start, getVector.run counted = (.ok live, start) →
      let n := (contents v counted).length
      let capacity := (contents live start).length
      match out with
      | (.ok init, after) =>
        init.attempts = List.replicate n (.fin 0) ∧ init.successes = List.replicate n (.fin 0) ∧
          init.multipliers = List.replicate n (.fin 1) ∧
          AdaptiveResult (contents live) skip capacity 0 start (.ok init.active, after)
      | (.error e, after) => AdaptiveResult (contents live) skip capacity 0 start (.error e, after)

theorem adaptive_initial_state_holds : adaptive_initial_state := by
  intro M W V getVector contents skip w
  refine ⟨?_, ?_⟩
  · intro e after h
    simp only [initAdaptive, h]
  · intro v counted h
    refine ⟨?_, ?_⟩
    · intro e after he
      simp only [initAdaptive, h, he]
    · intro live start hs
      simp only [initAdaptive, h, hs]
      have hrun := collectAdaptive_holds (contents live) skip (contents live start).length 0 start
      rcases hr : collectAdaptive (contents live) skip (contents live start).length 0 start with ⟨r, after⟩
      rw [hr] at hrun
      cases r with
      | ok mask => exact ⟨rfl, rfl, rfl, hrun⟩
      | error e => exact hrun

example :
    let skip (m : Bool) : ExceptT JlError (StateM (List (Option Bool))) Bool :=
      fun w => (.ok m, w.set 1 (some true))
    (initAdaptive (pure ()) (fun _ => id) skip [some false, some false]).1.map
      AdaptiveInitialization.active = .ok [some true, some false] := rfl

def adaptive_skip_dispatch : Prop := ∀ m,
  skipAdaptive m = true ↔ m = .simplify ∨ m = .doNothing

theorem adaptive_skip_dispatch_holds : adaptive_skip_dispatch := by
  intro m
  cases m <;> simp [skipAdaptive]

def inactive_accounting : Prop := ∀ (s : List AdaptiveSlot) p e selected,
  (if 0 < e.idx then s[e.idx - 1]? else none) = some selected → selected.active = false →
  adaptMutation s p e = .ok s

theorem inactive_accounting_holds : inactive_accounting := by
  intro s p e selected hs ha
  simp [adaptMutation, hs, ha]
  rfl

def strict_improvement_accounting : Prop := ∀ (s : List AdaptiveSlot) (p : AdaptiveConfig) (e : Event) (row : AdaptiveSlot),
  (if 0 < e.idx then s[e.idx - 1]? else none) = some row → row.active = true →
  let before := if p.reward = .cost then e.beforeCost else e.beforeLoss
  let after := if p.reward = .cost then e.afterCost else e.afterLoss
  let countSuccess := e.accepted && after.any (fun value => SymReg.Population.flt value before)
  ∀ out, adaptMutation s p e = .ok out →
    out.length = s.length ∧
    (∀ (i : Nat) (next : AdaptiveSlot), out[i]? = some next → i ≠ e.idx - 1 →
      ∃ old : AdaptiveSlot, s[i]? = some old ∧ next.attempts = old.attempts ∧ next.successes = old.successes) ∧
    ∃ next : AdaptiveSlot, out[e.idx - 1]? = some next ∧
      next.attempts = roundAdaptive (row.attempts + .fin 1) ∧
      next.successes = if countSuccess then roundAdaptive (row.successes + .fin 1) else row.successes

def target_and_ema_positive : Prop := ∀ floor ratio smoothing old,
  let upper := roundAdaptive (JF.fin 1 / floor)
  let target := clampTarget floor ratio
  (SymReg.Population.flt ratio floor = true → target = floor) ∧
  (SymReg.Population.flt ratio floor = false → SymReg.Population.flt upper ratio = true →
    target = upper) ∧
  (SymReg.Population.flt ratio floor = false → SymReg.Population.flt upper ratio = false →
    target = ratio) ∧
  ema smoothing old target =
    roundAdaptive (roundAdaptive (roundAdaptive (.fin 1 - smoothing) * old) +
      roundAdaptive (smoothing * target))

def adaptive_strength_zero : Prop := ∀ (W : Type) rt s p (read : W → Jl Nat × W) weights w,
  p.strength = 0 →
  (∀ e w', read w = (.error e, w') →
    conditionAdaptive rt s p read weights w = (.error e, w')) ∧
  (∀ n w', read w = (.ok n, w') →
    conditionAdaptive rt s p read weights w = (.ok weights, w'))

theorem adaptive_strength_zero_holds : adaptive_strength_zero := by
  intro W rt s p read weights w h
  constructor
  · intro e w' he; simp [conditionAdaptive, he, bind, Except.bind]
  · intro n w' hn; simp [conditionAdaptive, hn, h, bind, Except.bind, pure, Except.pure]

def adaptive_state_normalization : Prop := ∀ (s : List AdaptiveSlot) (n : Nat),
  let sum := (s.filter (·.active)).foldl (fun acc row => roundAdaptive (acc + row.multiplier)) (.fin 0)
  let mean := roundAdaptive (sum / roundAdaptive (.fin (n : Rat)))
  let out := normalizeActive s n
  out.length = s.length ∧
    ∀ (i : Nat) row, s[i]? = some row →
      ∃ next : AdaptiveSlot, out[i]? = some next ∧
        (row.active = false → next = row) ∧
        (row.active = true → next.multiplier = roundAdaptive (row.multiplier / mean))

private theorem adaptive_active_sum (s : List AdaptiveSlot) (acc : JF) :
    s.foldl (fun acc x => if x.active then addAdaptive acc x.multiplier else acc) acc =
    (s.filter (·.active)).foldl (fun acc x => addAdaptive acc x.multiplier) acc := by
  induction s generalizing acc with
  | nil => rfl
  | cons x xs ih => cases h : x.active <;> simp [h, ih]

theorem adaptive_state_normalization_holds : adaptive_state_normalization := by
  intro s n
  dsimp only
  unfold normalizeActive
  rw [adaptive_active_sum]
  refine ⟨by simp [rescaleActive], ?_⟩
  intro i row hr
  unfold rescaleActive
  rw [List.getElem?_map, hr]
  refine ⟨_, rfl, ?_, ?_⟩
  · intro hn
    simp [hn]
  · intro hy
    simp [hy, divAdaptive, addAdaptive]

private theorem changeAt_eq_set {A : Type} (f : A → A) (s : List A) (i : Nat) :
    changeAt f s i = match s[i]? with | none => s | some x => s.set i (f x) := by
  induction s generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [changeAt, List.getElem?_cons_succ, ih]
      cases xs[i]? <;> rfl

private theorem changeAt_len {A : Type} (f : A → A) (s : List A) (i : Nat) :
    (changeAt f s i).length = s.length := by
  rw [changeAt_eq_set]
  cases s[i]? <;> simp

private theorem changeAt_at {A : Type} (f : A → A) (s : List A) (i : Nat) :
    (changeAt f s i)[i]? = s[i]?.map f := by
  rw [changeAt_eq_set]
  cases h : s[i]? with
  | none => exact h
  | some x =>
    have hi : i < s.length := List.getElem?_eq_some_iff.mp h |>.1
    rw [List.getElem?_set_self hi]
    rfl

private theorem changeAt_not_at {A : Type} (f : A → A) (s : List A) (i j : Nat) (h : j ≠ i) :
    (changeAt f s i)[j]? = s[j]? := by
  rw [changeAt_eq_set]
  cases s[i]? <;> simp [h.symm]

private def counters (a : AdaptiveSlot) : JF × JF := (a.attempts, a.successes)

private theorem normalize_counters (s : List AdaptiveSlot) (n i : Nat) :
    ((normalizeActive s n)[i]?).map counters = (s[i]?).map counters := by
  simp only [normalizeActive, rescaleActive, List.getElem?_map, Option.map_map]
  cases s[i]? with
  | none => rfl
  | some row => cases h : row.active <;> simp [h, counters]

theorem strict_improvement_accounting_holds : strict_improvement_accounting := by
  intro s p e row hir ha
  dsimp only
  intro out ho
  have hi : 0 < e.idx := by
    by_cases h : 0 < e.idx
    · exact h
    · simp [h] at hir
  simp only [hi, ↓reduceIte] at hir
  let idx := e.idx - 1
  let counted := changeAt (countAttempt (improves p e)) s idx
  have hs : (counted[idx]?) = some (countAttempt (improves p e) row) := by
    simp [counted, idx, changeAt_at, hir]
  unfold adaptMutation at ho
  simp only [hi, ↓reduceIte, hir, ha, Bool.not_true, Bool.false_eq_true, Except.pure, pure,
    Except.ok.injEq] at ho
  subst out
  let after := fun (f : AdaptiveSlot → AdaptiveSlot) n => normalizeActive (changeAt f counted idx) n
  suffices h : ∀ f n, (∀ row, counters (f row) = counters row) →
      (after f n).length = s.length ∧
      (∀ i next, (after f n)[i]? = some next → i ≠ idx →
        ∃ old, s[i]? = some old ∧ next.attempts = old.attempts ∧ next.successes = old.successes) ∧
      ∃ next, (after f n)[idx]? = some next ∧
        next.attempts = (countAttempt (improves p e) row).attempts ∧
        next.successes = (countAttempt (improves p e) row).successes by
    refine h _ _ ?_
    intro x
    rfl
  intro f n hfc
  unfold after
  refine ⟨?_, ?_, ?_⟩
  · simp [normalizeActive, rescaleActive, changeAt_len, counted]
  · intro i next hn hne
    change (normalizeActive (changeAt f counted idx) n)[i]? = some next at hn
    have h := normalize_counters (changeAt f counted idx) n i
    rw [hn, changeAt_not_at _ _ _ _ hne, show counted[i]? = s[i]? from
      changeAt_not_at _ _ _ _ hne] at h
    cases hsi : s[i]? with
    | none => simp [hsi] at h
    | some old =>
      have eq : counters next = counters old := by simpa [hsi] using h
      exact ⟨old, rfl, congrArg Prod.fst eq, congrArg Prod.snd eq⟩
  · have h := normalize_counters (changeAt f counted idx) n idx
    rw [changeAt_at, hs] at h
    cases hn : (normalizeActive (changeAt f counted idx) n)[idx]? with
    | none => simp [hn] at h
    | some next =>
      have eq : counters next = counters (countAttempt (improves p e) row) := by
        simpa only [hn, Option.map_some, Option.some.injEq, hfc] using h
      exact ⟨next, rfl, congrArg Prod.fst eq, congrArg Prod.snd eq⟩

def floatMax64 : Rat :=
  179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368

/-- Float64 finite overflow on multiplication; exact finite products below the
overflow range use the existing JF abstraction. -/
def overflowMultiply (x y : JF) : JF :=
  match x * y with
  | .fin q =>
    let limit := floatMax64 + (2 : Rat)^970
    if limit ≤ q then .posInf else if q ≤ -limit then .negInf else .fin q
  | z => z

/-- Finite nonnegative base weights should remain finite under valid defaults.
The numerical primitive is supplied; the witness uses measured Float64 overflow. -/
def adaptive_weights_finite : Prop := ∀ (rt : WeightServices) (s : List AdaptiveSlot)
    (p : AdaptiveConfig) (weights out : Weights),
  ValidAdaptive p → (∀ slot ∈ s, ∃ q, slot.multiplier = .fin q ∧ 0 < q) →
  (∀ w ∈ weights, ∃ q, w.2 = .fin q ∧ 0 ≤ q ∧ q ≤ floatMax64) →
  (conditionAdaptive rt s p (fun _ : Unit => (.ok weights.length, ())) weights ()).1 = .ok out →
  ∀ w ∈ out, JF.valid w.2 = true

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 2048 in
theorem adaptive_weights_finite_refuted : ¬ adaptive_weights_finite := by
  intro hp
  let rt : WeightServices := {
    sqrt := id, power := fun x _ => x, mul := overflowMultiply }
  let p : AdaptiveConfig := { strength := 1 }
  let s : List AdaptiveSlot := [
    { attempts := .fin 1, successes := .fin 1, multiplier := .fin (902 / 901) },
    { multiplier := .fin (900 / 901) }]
  let weights : Weights := [(.constant, .fin floatMax64), (.operator, .fin 1)]
  let out : Weights := [(.constant, .posInf), (.operator, .fin (900 / 901))]
  have positive : ∀ slot ∈ s, ∃ q, slot.multiplier = .fin q ∧ 0 < q := by
    intro slot hs
    simp [s] at hs
    rcases hs with rfl | rfl
    · exact ⟨902 / 901, rfl, by decide⟩
    · exact ⟨900 / 901, rfl, by decide⟩
  have h := hp rt s p weights out (by decide) positive
    (by
      intro w hw
      simp [weights] at hw
      rcases hw with rfl | rfl
      · exact ⟨floatMax64, rfl, by decide, by decide⟩
      · exact ⟨1, rfl, by decide, by decide⟩)
    (by decide) (.constant, .posInf) (by simp [out])
  contradiction

example : ValidAdaptive {} := by decide
example : (if 0 < (1 : Nat) then ([{ active := false }] : List AdaptiveSlot)[0]? else none) =
    some { active := false } := by decide
example : ({ strength := 0 } : AdaptiveConfig).strength = 0 := rfl
example : (if 0 < (1 : Nat) then ([{}] : List AdaptiveSlot)[0]? else none) =
    some ({} : AdaptiveSlot) ∧
    ({} : AdaptiveSlot).active = true := by decide

end SymReg.Plugins
