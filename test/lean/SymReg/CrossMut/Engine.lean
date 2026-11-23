import SymReg.HofMig.Core
import SymReg.MutateGen.Sample
import DynExpr.ParamStruct.Mirror

namespace SymReg.CrossMut
open DynExpr
open SymReg.HofMig (Member)
open DynExpr.Expressions.Sampling (RNG)

/-- `src/Crossovers.jl:30-43`: concrete dispatch identities, including extension types. -/
inductive CrossKind where
  | subtree
  | custom (id : Nat)
  deriving DecidableEq, Repr

/-- `src/Crossover.jl:35-44`: trees are opaque identities in the shared member model.
The counter is exact Rat, as in MutateGen; Float64 rounding is excluded. -/
structure CrossResult where
  child1 : Nat
  child2 : Nat
  numEvals : Rat := 0
  deriving DecidableEq, Repr

/-- `src/Crossover.jl:81-96`: extension dispatch, fallback error, subtree wrapper.
Subtree swapping itself belongs to the existing Crossover slices. -/
def crossover (swap : Nat → Nat → Nat × Nat)
    (custom : Nat → Nat → Nat → Jl CrossResult) (a b : Nat) : CrossKind → Jl CrossResult
  | .subtree => let children := swap a b; pure ⟨children.1, children.2, 0⟩
  | .custom id => custom id a b

/-- `src/Crossover.jl:120-139`: singleton bypasses every weight check and RNG draw;
otherwise reuse MutateGen's actual sampler (one-based result). -/
def selectCrossover (xs : List (CrossKind × JF)) (rng : RNG) : Jl CrossKind × RNG :=
  match xs with
  | [(k, _)] => (.ok k, rng)
  | _ =>
    let (idx, rng') := SymReg.MutateGen.sampleMutationR xs rng
    (idx.bind (fun i => match xs[i - 1]? with
      | some p => .ok p.1 | none => .error .boundsError), rng')

-- Source: src/Crossover.jl:98-106. Both branches pass the original arguments.
def dispatchCross {Args Result : Type} (builtin : Args → Result)
    (custom : Nat → Args → Result) (kind : CrossKind) (args : Args) : Result :=
  match kind with
  | .subtree => builtin args
  | .custom id => custom id args

-- Source: src/Crossover.jl:120-139.
def selectAndDispatchCross {Args Result W : Type} (xs : List (CrossKind × JF)) (rng : RNG)
    (builtin : Args → RNG → W → Jl Result × RNG × W)
    (custom : Nat → Args → RNG → W → Jl Result × RNG × W) (args : Args) (world : W) :
    (Jl Result × RNG × W) × List CrossKind :=
  let (choice, next) := selectCrossover xs rng
  match choice with
  | .ok kind => (dispatchCross builtin custom kind args next world, [kind])
  | .error err => ((.error err, next, world), [])

inductive CrossCall where
  | breed (attempt : Nat) (evals : Rat)
  | complexity (tree : Nat)
  | check (tree : Nat) (size : Int)
  | score (tree : Nat) (size : Int)
  | construct (parents : Nat × Nat) (tree : Nat) (parentRef : Int)
  | accept
  | reject
  deriving DecidableEq, Repr

/-- Only reported crossover work contributes before final scoring,
`src/Crossover.jl:178`; failed attempts contribute too. -/
def loggedEvals : List CrossCall → Rat
  | [] => 0
  | .breed _ n :: calls => n + loggedEvals calls
  | _ :: calls => loggedEvals calls

@[simp] theorem loggedEvals_append (xs ys : List CrossCall) :
    loggedEvals (xs ++ ys) = loggedEvals xs + loggedEvals ys := by
  induction xs with
  | nil => simp [loggedEvals, Rat.zero_add]
  | cons c cs ih => cases c <;> simp [loggedEvals, ih, Rat.add_assoc]

structure CrossServices (H : Type) where
  breed : Nat → H → Jl (CrossResult × H)
  complexity : Nat → H → Jl (Int × H)
  check : Nat → Int → H → Jl (Bool × H)
  score : Nat → Int → H → Jl (JF × JF × H)

structure Candidate where
  result : CrossResult
  size1 : Int
  size2 : Int
  deriving DecidableEq, Repr

structure Trial (H : Type) where
  candidate : Option Candidate
  evals : Rat
  state : H
  log : List CrossCall
  attempts : Nat

/-- `src/Crossover.jl:165-193`: retry the same parents/kind; compute both sizes,
short circuit the second constraint, count each attempted crossover, stop after ten.
All callbacks can throw and can mutate a shared heap/context in H. -/
def tryCross {H : Type} (svc : CrossServices H) : Nat → Nat → Rat → H → Jl (Trial H)
  | 0, _, total, h => pure ⟨none, total, h, [.reject], 0⟩
  | remaining + 1, attempt, total, h => do
    let (r, h) ← svc.breed attempt h
    let (n1, h) ← svc.complexity r.child1 h
    let (n2, h) ← svc.complexity r.child2 h
    let (ok1, h) ← svc.check r.child1 n1 h
    let (ok2, h) ← if ok1 then svc.check r.child2 n2 h else pure (false, h)
    let calls := [.breed attempt r.numEvals, .complexity r.child1, .complexity r.child2,
      .check r.child1 n1] ++ (if ok1 then [.check r.child2 n2] else [])
    if ok1 && ok2 then
      pure ⟨some ⟨r, n1, n2⟩, total + r.numEvals, h, calls, 1⟩
    else
      let tail ← tryCross svc remaining (attempt + 1) (total + r.numEvals) h
      pure { tail with log := calls ++ tail.log, attempts := tail.attempts + 1 }

structure Supply where
  objectId : Nat
  birth : Int
  reference : Int

/-- Default tuple-parent `create_child`, `src/PopMember.jl:239-258`, called by
`src/Crossover.jl:202-219`. Plugin-specific member construction is outside this
PopMember branch. Expression identity is retained; births/references are supplied
independently, as in HofMig.initHof. No reference-uniqueness assumption is made. -/
def childMember (tree : Nat) (cost loss : JF) (size : Int) (parent : Int)
    (supply : Supply) : Member :=
  { cost, loss, complexity := size, tree, objectId := supply.objectId, treeId := tree,
    birth := supply.birth, reference := supply.reference, parent }

structure CrossOutcome (H : Type) where
  first : Member
  second : Member
  accepted : Bool
  evals : Rat
  state : H
  log : List CrossCall

/-- `src/Crossover.jl:194-224`: score in order, charge two dataset fractions,
construct both fresh members with their respective parent's reference. -/
def finishCross {H : Type} (svc : CrossServices H) (a b : Member)
    (s1 s2 : Supply) (fraction : Rat) (t : Trial H) : Jl (CrossOutcome H) := do
  match t.candidate with
  | none => pure ⟨a, b, false, t.evals, t.state, t.log⟩
  | some c =>
    let (cost1, loss1, h) ← svc.score c.result.child1 c.size1 t.state
    let (cost2, loss2, h) ← svc.score c.result.child2 c.size2 h
    pure ⟨childMember c.result.child1 cost1 loss1 c.size1 a.reference s1,
      childMember c.result.child2 cost2 loss2 c.size2 b.reference s2,
      true, t.evals + 2 * fraction, h,
      t.log ++ [.score c.result.child1 c.size1, .score c.result.child2 c.size2,
        .construct (a.objectId, b.objectId) c.result.child1 a.reference,
        .construct (a.objectId, b.objectId) c.result.child2 b.reference, .accept]⟩

/-- Public engine has precisely the fixed ten-attempt limit. -/
def crossoverGeneration {H : Type} (svc : CrossServices H) (a b : Member)
    (s1 s2 : Supply) (fraction : Rat) (h : H) : Jl (CrossOutcome H) := do
  let t ← tryCross svc 10 1 0 h
  finishCross svc a b s1 s2 fraction t

def subtreeDispatch : Prop := ∀ swap custom a b,
  crossover swap custom a b .subtree = .ok ⟨(swap a b).1, (swap a b).2, 0⟩
theorem subtreeDispatch_holds : subtreeDispatch := by intro swap custom a b; rfl

def dispatchIdentity : Prop :=
  ∀ (Args Result W : Type) (builtin : Args → RNG → W → Jl Result × RNG × W)
    (custom : Nat → Args → RNG → W → Jl Result × RNG × W)
    (args : Args) (world : W) xs rng next,
    (selectCrossover xs rng = (.ok .subtree, next) →
      selectAndDispatchCross xs rng builtin custom args world = (builtin args next world, [.subtree])) ∧
    (∀ id, selectCrossover xs rng = (.ok (.custom id), next) →
      selectAndDispatchCross xs rng builtin custom args world = (custom id args next world, [.custom id])) ∧
    (∀ err, selectCrossover xs rng = (.error err, next) →
      selectAndDispatchCross xs rng builtin custom args world = ((.error err, next, world), []))

theorem dispatchIdentity_holds : dispatchIdentity := by
  intro Args Result W builtin custom args world xs rng next
  refine ⟨fun h => ?_, fun id h => ?_, fun err h => ?_⟩ <;>
    simp [selectAndDispatchCross, h, dispatchCross]

def singletonNoDraw : Prop := ∀ k weight rng,
  selectCrossover [(k, weight)] rng = (.ok k, rng)
theorem singletonNoDraw_holds : singletonNoDraw := by intro k weight rng; rfl

def retryBound : Prop := ∀ (H : Type) (svc : CrossServices H) fuel attempt total h t,
  tryCross svc fuel attempt total h = .ok t →
  t.attempts ≤ fuel ∧ (t.candidate = none → t.attempts = fuel) ∧
    t.evals = total + loggedEvals t.log

theorem retryBound_holds : retryBound := by
  intro H svc fuel
  induction fuel with
  | zero =>
    intro attempt total h t he
    simp [tryCross] at he
    subst t
    simp [loggedEvals, Rat.add_zero]
  | succ fuel ih =>
    intro attempt total h t he
    cases hb : svc.breed attempt h with
    | error e => simp [tryCross, hb] at he
    | ok p =>
      rcases p with ⟨r, h0⟩
      cases hn1 : svc.complexity r.child1 h0 with
      | error e => simp [tryCross, hb, hn1] at he
      | ok p =>
        rcases p with ⟨n1, h1⟩
        cases hn2 : svc.complexity r.child2 h1 with
        | error e => simp [tryCross, hb, hn1, hn2] at he
        | ok p =>
          rcases p with ⟨n2, h2⟩
          cases hk1 : svc.check r.child1 n1 h2 with
          | error e => simp [tryCross, hb, hn1, hn2, hk1] at he
          | ok p =>
            rcases p with ⟨ok1, h3⟩
            cases ok1 with
            | false =>
              cases ht : tryCross svc fuel (attempt + 1) (total + r.numEvals) h3 with
              | error e => simp [tryCross, hb, hn1, hn2, hk1, ht] at he
              | ok tail =>
                simp [tryCross, hb, hn1, hn2, hk1, ht] at he
                subst t
                have hh := ih _ _ _ tail ht
                refine ⟨by simpa using Nat.succ_le_succ hh.1, ?_, ?_⟩
                · intro hn
                  have hh' := hh.2.1 hn
                  simp only
                  omega
                · simpa [loggedEvals, Rat.add_zero, Rat.add_assoc] using hh.2.2
            | true =>
              cases hk2 : svc.check r.child2 n2 h3 with
              | error e => simp [tryCross, hb, hn1, hn2, hk1, hk2] at he
              | ok p =>
                rcases p with ⟨ok2, h4⟩
                cases ok2 with
                | false =>
                  cases ht : tryCross svc fuel (attempt + 1) (total + r.numEvals) h4 with
                  | error e => simp [tryCross, hb, hn1, hn2, hk1, hk2, ht] at he
                  | ok tail =>
                    simp [tryCross, hb, hn1, hn2, hk1, hk2, ht] at he
                    subst t
                    have hh := ih _ _ _ tail ht
                    refine ⟨by simpa using Nat.succ_le_succ hh.1, ?_, ?_⟩
                    · intro hn
                      have hh' := hh.2.1 hn
                      simp only
                      omega
                    · simpa [loggedEvals, Rat.add_zero, Rat.add_assoc] using hh.2.2
                | true =>
                  simp [tryCross, hb, hn1, hn2, hk1, hk2] at he
                  subst t
                  simp [loggedEvals, Rat.add_zero]

/-- Each accepted pair has passed both checks with its computed sizes. Callbacks
can mutate H, so the certificate records actual intermediate states. -/
def acceptedChecks : Prop := ∀ (H : Type) (svc : CrossServices H) fuel attempt total h t c,
  tryCross svc fuel attempt total h = .ok t → t.candidate = some c →
  ∃ h0 h1 h2 h3,
    svc.complexity c.result.child1 h0 = .ok (c.size1, h1) ∧
    svc.complexity c.result.child2 h1 = .ok (c.size2, h2) ∧
    svc.check c.result.child1 c.size1 h2 = .ok (true, h3) ∧
    ∃ h4, svc.check c.result.child2 c.size2 h3 = .ok (true, h4)

theorem acceptedChecks_holds : acceptedChecks := by
  intro H svc fuel
  induction fuel with
  | zero => intro attempt total h t c he hc; simp [tryCross] at he; subst t; contradiction
  | succ fuel ih =>
    intro attempt total h t c he hc
    cases hb : svc.breed attempt h with
    | error e => simp [tryCross, hb] at he
    | ok p =>
      rcases p with ⟨r, h0⟩
      cases hn1 : svc.complexity r.child1 h0 with
      | error e => simp [tryCross, hb, hn1] at he
      | ok p =>
        rcases p with ⟨n1, h1⟩
        cases hn2 : svc.complexity r.child2 h1 with
        | error e => simp [tryCross, hb, hn1, hn2] at he
        | ok p =>
          rcases p with ⟨n2, h2⟩
          cases hk1 : svc.check r.child1 n1 h2 with
          | error e => simp [tryCross, hb, hn1, hn2, hk1] at he
          | ok p =>
            rcases p with ⟨ok1, h3⟩
            cases ok1 with
            | false =>
              cases ht : tryCross svc fuel (attempt + 1) (total + r.numEvals) h3 with
              | error e => simp [tryCross, hb, hn1, hn2, hk1, ht] at he
              | ok tail =>
                simp [tryCross, hb, hn1, hn2, hk1, ht] at he
                subst t
                exact ih _ _ _ tail c ht hc
            | true =>
              cases hk2 : svc.check r.child2 n2 h3 with
              | error e => simp [tryCross, hb, hn1, hn2, hk1, hk2] at he
              | ok p =>
                rcases p with ⟨ok2, h4⟩
                cases ok2 with
                | false =>
                  cases ht : tryCross svc fuel (attempt + 1) (total + r.numEvals) h4 with
                  | error e => simp [tryCross, hb, hn1, hn2, hk1, hk2, ht] at he
                  | ok tail =>
                    simp [tryCross, hb, hn1, hn2, hk1, hk2, ht] at he
                    subst t
                    exact ih _ _ _ tail c ht hc
                | true =>
                  simp [tryCross, hb, hn1, hn2, hk1, hk2] at he
                  subst t
                  simp only [Option.some.injEq] at hc
                  subst c
                  exact ⟨h0, h1, h2, h3, hn1, hn2, hk1, h4, hk2⟩

example : tryCross (⟨fun _ h => .ok (⟨0, 1, 0⟩, h),
    fun _ h => .ok (1, h), fun _ _ h => .ok (true, h),
    fun _ _ h => .ok (.fin 0, .fin 0, h)⟩ : CrossServices Unit) 1 1 0 () =
    .ok ⟨some ⟨⟨0, 1, 0⟩, 1, 1⟩, 0, (),
      [.breed 1 0, .complexity 0, .complexity 1, .check 0 1, .check 1 1], 1⟩ := by
  simp [tryCross, Rat.zero_add]

def failedParents : Prop := ∀ (H : Type) svc a b s1 s2 fraction (t : Trial H),
  t.candidate = none →
  finishCross svc a b s1 s2 fraction t = .ok ⟨a, b, false, t.evals, t.state, t.log⟩
theorem failedParents_holds : failedParents := by
  intro H svc a b s1 s2 fraction t hn; simp [finishCross, hn]
example : (none : Option Candidate) = none := rfl

def childFields : Prop := ∀ tree cost loss size parent s,
  let child := childMember tree cost loss size parent s
  child.tree = tree ∧ child.treeId = tree ∧ child.cost = cost ∧ child.loss = loss ∧
  child.complexity = size ∧ child.parent = parent ∧ child.birth = s.birth ∧
  child.reference = s.reference ∧ child.objectId = s.objectId

theorem childFields_holds : childFields := by
  intro tree cost loss size parent s
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def acceptedAccounting : Prop := ∀ (H : Type) svc a b s1 s2 fraction (t : Trial H) c out,
  t.candidate = some c → finishCross svc a b s1 s2 fraction t = .ok out →
  out.accepted = true ∧ out.evals = t.evals + 2 * fraction ∧
  out.first.parent = a.reference ∧ out.second.parent = b.reference ∧
  out.first.birth = s1.birth ∧ out.second.birth = s2.birth ∧
  out.first.tree = c.result.child1 ∧ out.second.tree = c.result.child2

theorem acceptedAccounting_holds : acceptedAccounting := by
  intro H svc a b s1 s2 fraction t c out hc he
  cases h1 : svc.score c.result.child1 c.size1 t.state with
  | error e => simp [finishCross, hc, h1] at he
  | ok p =>
    rcases p with ⟨cost1, loss1, h⟩
    cases h2 : svc.score c.result.child2 c.size2 h with
    | error e => simp [finishCross, hc, h1, h2] at he
    | ok p =>
      rcases p with ⟨cost2, loss2, h'⟩
      simp [finishCross, hc, h1, h2] at he
      subst out
      exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

example : ∃ (svc : CrossServices Unit) (a b : Member) (s1 s2 : Supply)
    (t : Trial Unit) (c : Candidate) (out : CrossOutcome Unit),
    t.candidate = some c ∧ finishCross svc a b s1 s2 1 t = .ok out := by
  let svc : CrossServices Unit :=
    ⟨fun _ h => .ok (⟨0, 1, 0⟩, h), fun _ h => .ok (1, h),
      fun _ _ h => .ok (true, h), fun _ _ h => .ok (.fin 0, .fin 0, h)⟩
  let a : Member := {
    cost := .fin 0, loss := .fin 0, complexity := 1, tree := 0
    objectId := 0, treeId := 0, birth := 1, reference := 1 }
  let supply : Supply := ⟨2, 2, 2⟩
  let c : Candidate := ⟨⟨0, 1, 0⟩, 1, 1⟩
  let t : Trial Unit := ⟨some c, 0, (), [], 1⟩
  cases hs : finishCross svc a a supply supply 1 t with
  | error e => simp [finishCross, svc, t, c] at hs
  | ok out => exact ⟨svc, a, a, supply, supply, t, c, out, rfl, hs⟩

end SymReg.CrossMut
