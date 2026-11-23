import SymReg.MutateGen.Engine

/-!
Lemmas about the engine model: call-log bookkeeping, store invariants, and the
characterisation of the retry loop of `_next_generation`.
-/

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw)

variable {E : Type}

/-! ## Views of the call log -/

/-- `num_evals` reported by a `mutate!` call. -/
def evalsOf : Call E → Option JF
  | .mutate _ v _ _ => some v
  | _ => none

/-- Sum of the `num_evals` of every `mutate!` call. -/
def sumEvals (L : List (Call E)) (initial : JF) : JF :=
  (L.filterMap evalsOf).foldl weightAdd initial

/-- An `eval_cost` call by the engine. -/
def isEval : Call E → Bool
  | .eval _ => true
  | _ => false

/-- A `check_constraints` call that returned false. -/
def isFailedCheck : Call E → Bool
  | .constraints _ false => true
  | _ => false

/-- The attempt number of a `mutate!` call. -/
def attemptOf : Call E → Option Nat
  | .mutate a _ _ _ => some a
  | _ => none

/-- A `mutate!` call whose result had `return_immediately` and `success`. -/
def isImmOk : Call E → Bool
  | .mutate _ _ true true => true
  | _ => false

/-- An `on_mutation_end!` call. -/
def onEndOf : Call E → Option (Nat × Kind × Event)
  | .onEnd i k ev => some (i, k, ev)
  | _ => none

/-- The sampled mutation. -/
def chooseOf : Call E → Option (Kind × Nat)
  | .choose k i => some (k, i)
  | _ => none

/-- Calls the retry loop makes. -/
def isLoopCall : Call E → Bool
  | .mutate .. => true
  | .constraints .. => true
  | _ => false

theorem sumEvals_append (a b : List (Call E)) (initial : JF) :
    sumEvals (a ++ b) initial = sumEvals b (sumEvals a initial) := by
  simp [sumEvals, List.foldl_append]

/-! ## Store bookkeeping -/

theorem createChild_facts (s : St E) (t : E) (c l : JF) (pr : Nat) (cx : Int) :
    let r := createChild s t c l pr cx
    r.1 = s.next ∧ r.2.next = s.next + 1 ∧ r.2.log = s.log ∧ r.2.rng = s.rng ∧
    r.2.scratch = s.scratch ∧ r.2.objs s.next = some ⟨t, c, l, s.next, s.next, pr, cx⟩ ∧
    (∀ o, o ≠ s.next → r.2.objs o = s.objs o) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [createChild, St.write], ?_⟩
  intro o ho
  simp [createChild, St.write, ho]

theorem createChild_inv (s : St E) (t : E) (c l : JF) (pr : Nat) (cx : Int) (h : s.Inv) :
    (createChild s t c l pr cx).2.Inv := by
  intro o m hm
  obtain ⟨_, hn, _, _, _, _, hother⟩ := createChild_facts s t c l pr cx
  rw [hn]
  by_cases ho : o = s.next
  · omega
  · rw [hother o ho] at hm; have := h o m hm; omega

theorem materialise_facts (s : St E) (po pr : Nat) (cx : E → Int) (ho : HOut E) :
    let r := materialise s po pr cx ho
    r.2.log = s.log ∧ r.2.rng = s.rng ∧ r.2.scratch = s.scratch ∧ s.next ≤ r.2.next ∧
    (s.Inv → r.2.Inv) ∧ (∀ o, s.objs o ≠ none → r.2.objs o ≠ none) ∧
    (s.objs po ≠ none → ∀ o, r.1 = .member o → r.2.objs o ≠ none) ∧
    (∀ t, r.1 = .tree t ↔ ho = .tree t) := by
  cases ho with
  | tree t => simp [materialise]
  | child t c l =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := createChild_facts s t c l pr (cx t)
    refine ⟨h3, h4, h5, by simp [materialise, h2], fun hi => createChild_inv s t c l pr (cx t) hi, ?_, ?_, ?_⟩
    · intro o hne
      by_cases ho : o = s.next
      · subst ho; simp [materialise, h6]
      · simp only [materialise]; rw [h7 o ho]; exact hne
    · intro _ o hmo
      simp only [materialise, Out.member.injEq] at hmo
      subst hmo; simp only [materialise]; rw [← h1, h6] at *; simp
    · intro t'; simp [materialise]
  | optimized t c l upd =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := createChild_facts s t c l pr (cx t)
    cases upd with
    | none =>
      refine ⟨h3, h4, h5, by simp [materialise, h2], fun hi => createChild_inv s t c l pr (cx t) hi, ?_, ?_, ?_⟩
      · intro o hne
        by_cases ho : o = s.next
        · subst ho; simp [materialise, h6]
        · simp only [materialise]; rw [h7 o ho]; exact hne
      · intro _ o hmo
        simp only [materialise, Out.member.injEq] at hmo
        subst hmo; simp only [materialise]; rw [← h1, h6] at *; simp
      · intro t'; simp [materialise]
    | some v =>
      obtain ⟨t', c', l'⟩ := v
      have hn : (materialise s po pr cx (.optimized t c l (some (t', c', l')))).2.next = s.next + 2 := rfl
      have hr : (materialise s po pr cx (.optimized t c l (some (t', c', l')))).1 = .member s.next := rfl
      have hobj : ∀ x, (materialise s po pr cx (.optimized t c l (some (t', c', l')))).2.objs x =
          if x = s.next then some ⟨t', c', l', s.next + 1, s.next, pr, cx t⟩ else s.objs x := by
        intro x
        simp only [materialise, createChild, St.write]
        by_cases hx : x = s.next <;> simp [hx]
      dsimp only
      refine ⟨rfl, rfl, rfl, by rw [hn]; omega, ?_, ?_, ?_, ?_⟩
      · intro hi o m' hm'
        rw [hobj] at hm'
        rw [hn]
        by_cases ho : o = s.next
        · omega
        · simp only [ho, ↓reduceIte] at hm'; have := hi o m' hm'; omega
      · intro o hne
        rw [hobj]
        by_cases ho : o = s.next
        · simp [ho]
        · simp only [ho, ↓reduceIte]; exact hne
      · intro _ o hmo
        rw [hr] at hmo
        simp only [Out.member.injEq] at hmo; subst hmo; rw [hobj]; simp
      · intro t''; rw [hr]; simp
  | parent upd =>
    cases upd with
    | none =>
      refine ⟨rfl, rfl, rfl, Nat.le_refl _, fun h => h, fun _ h => h, ?_, ?_⟩
      · intro hp o hmo; simp only [materialise, Out.member.injEq] at hmo; subst hmo; exact hp
      · intro t'; simp [materialise]
    | some v =>
      obtain ⟨t, c, l⟩ := v
      cases hpo : s.objs po with
      | none =>
        simp [materialise, hpo]
      | some m =>
        simp only [materialise, hpo]
        refine ⟨rfl, rfl, rfl, by simp, ?_, ?_, ?_, ?_⟩
        · intro hi o m' hm'
          simp only [St.write] at hm'
          by_cases ho : o = po
          · subst ho; have := hi o m hpo; simp; omega
          · simp [ho] at hm'; have := hi o m' hm'; simp; omega
        · intro o hne
          simp only [St.write]
          by_cases ho : o = po
          · simp [ho]
          · simp [ho]; exact hne
        · intro _ o hmo
          simp only [Out.member.injEq] at hmo; subst hmo; simp [St.write]
        · intro t'; simp

/-! ## The retry loop -/

/-- What the retry loop guarantees about its calls, its result and the store. -/
def RetryOK (cfg : Cfg E) (po : Nat) (curmaxsize : Int) (fuel attempts : Nat) (ev : JF)
    (s : St E) (e : LoopEnd E) (ev' : JF) (s' : St E) : Prop :=
  ∃ L, s'.log = s.log ++ L ∧ L.all isLoopCall = true ∧ ev' = sumEvals L ev ∧
    L.filterMap attemptOf = List.range' (attempts + 1) (L.filterMap attemptOf).length ∧
    (L.filterMap attemptOf).length ≤ fuel ∧
    (0 < fuel → 0 < (L.filterMap attemptOf).length) ∧
    (L.filterMap attemptOf).length ≤ (L.filter isFailedCheck).length + 1 ∧
    ((∃ o, e = .immediate o) ↔ L.any isImmOk = true) ∧
    (∀ t, e = .finished true t → cfg.constraints t curmaxsize = true ∧ Call.constraints t true ∈ L) ∧
    s'.rng.draws = s.rng.draws ∧ s'.scratch = s.scratch ∧ s.next ≤ s'.next ∧
    (s.Inv → s'.Inv) ∧ (∀ o, s.objs o ≠ none → s'.objs o ≠ none) ∧
    (s.objs po ≠ none → ∀ o, e = .immediate o → s'.objs o ≠ none)

theorem bsLoop_draws (b : BS E) (pc : JF) : ∀ (n : Nat) (t : E) (setup : Option Nat) (ev : JF)
    (rng : RNG), (bsLoop b pc n t setup ev rng).2.draws = rng.draws := by
  intro n
  induction n with
  | zero => intro t setup ev rng; rfl
  | succ n ih =>
    intro t setup ev rng
    simp only [bsLoop]
    repeat' split
    all_goals simp_all [adv]

theorem mutateH_draws (mf : MF E) (k : Kind) (scale : JF) (m : Member E) (t : E) (a : Nat)
    (rng : RNG) (r : HRes E) (rng' : RNG) (h : mutateH mf k scale m t a rng = .ok (r, rng')) :
    rng'.draws = rng.draws := by
  cases k <;> simp only [mutateH, treeStep, backsolveH, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals (try simp only [adv, draw, Except.ok.injEq, Prod.mk.injEq] at h)
  all_goals (first
    | (obtain ⟨_, rfl⟩ := h; rfl)
    | (have h2 := congrArg Prod.snd h; simp only at h2; rw [← h2, bsLoop_draws])
    | (cases h)
    | (simp [throw, throwThe, MonadExceptOf.throw, Except.instMonad] at h))

end SymReg.MutateGen

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw)
variable {E : Type}

attribute [local simp] List.filterMap_cons List.filter_cons attemptOf evalsOf isFailedCheck isImmOk
  isLoopCall

private theorem sumEvals_single (a : Nat) (v initial : JF) (i o : Bool) :
    sumEvals [(Call.mutate a v i o : Call E)] initial = weightAdd initial v := rfl

theorem retry_ok (cfg : Cfg E) (k : Kind) (scale : JF) (po : Nat) (m : Member E) (pr : Nat)
    (cms : Int) : ∀ (fuel attempts : Nat) (ev : JF) (s : St E) (e : LoopEnd E) (ev' : JF) (s' : St E),
    retry cfg k scale po m pr cms fuel attempts ev s = .ok ((e, ev'), s') →
    RetryOK cfg po cms fuel attempts ev s e ev' s' := by
  intro fuel
  induction fuel with
  | zero =>
    intro attempts ev s e ev' s' h
    simp only [retry, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨[], by simp, rfl, rfl, by simp, by simp, by simp,
      by simp, by simp, ?_, rfl, rfl, Nat.le_refl _, id, fun _ h => h, ?_⟩
    · intro t ht; cases ht
    · intro _ o ho; cases ho
  | succ fuel ih =>
    intro attempts ev s e ev' s' h
    simp only [retry] at h
    split at h
    · cases h
    · rename_i r rng hm
      have hdr := mutateH_draws _ _ _ _ _ _ _ _ _ hm
      generalize hs1 : ({ s with rng := rng, log := s.log ++ [Call.mutate (attempts + 1) r.evals r.imm r.success] } : St E) = s1 at h
      have hf := materialise_facts s1 po pr cfg.complexity r.out
      generalize hmat : materialise s1 po pr cfg.complexity r.out = q at h hf
      obtain ⟨out, s2⟩ := q
      obtain ⟨hlog, hrng, hsc, hnext, hinv, hkeep, hmem, htree⟩ := hf
      simp only at hlog hrng hsc hnext hinv hkeep hmem htree h
      have h1log : s1.log = s.log ++ [Call.mutate (attempts + 1) r.evals r.imm r.success] := by rw [← hs1]
      have h1rng : s1.rng = rng := by rw [← hs1]
      have h1sc : s1.scratch = s.scratch := by rw [← hs1]
      have h1next : s1.next = s.next := by rw [← hs1]
      have h1objs : s1.objs = s.objs := by rw [← hs1]
      have h1inv : s.Inv → s1.Inv := by intro hi; rw [← hs1]; exact hi
      cases hi : r.imm <;> cases hsu : r.success <;> simp only [hi, hsu, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] at h
      · -- not immediate, failure
        cases out with
        | member o => cases h
        | tree t =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          refine ⟨[Call.mutate (attempts + 1) r.evals false false], by rw [hlog, h1log, hi, hsu],
            rfl, by rw [sumEvals_single], by simp [attemptOf], by simp [attemptOf], by simp [attemptOf],
            by simp [attemptOf], by simp [isImmOk], ?_, by rw [hrng, h1rng, hdr], by rw [hsc, h1sc],
            by rw [← h1next]; exact hnext, fun hs => hinv (h1inv hs), ?_, ?_⟩
          · intro t ht; cases ht
          · intro o ho; apply hkeep; rw [h1objs]; exact ho
          · intro _ o ho; cases ho
      · -- not immediate, success
        cases out with
        | member o => cases h
        | tree t =>
          simp only at h
          cases hc : cfg.constraints t cms <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          · -- constraint failure: retry
            generalize hs3 : ({ s2 with log := s2.log ++ [Call.constraints t false] } : St E) = s3 at h
            obtain ⟨L, hL, hall, hev, hatt, hlen, hpos, hfail, himm, hfin, hdr', hsc', hnext', hinv', hkeep', hmem'⟩ :=
              ih (attempts + 1) (weightAdd ev r.evals) s3 e ev' s' h
            have h3log : s3.log = s.log ++ [Call.mutate (attempts + 1) r.evals false true, Call.constraints t false] := by
              rw [← hs3]; simp [hlog, h1log, hi, hsu]
            refine ⟨[Call.mutate (attempts + 1) r.evals false true, Call.constraints t false] ++ L, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hL, h3log, List.append_assoc]
            · simp [isLoopCall, hall]
            · simpa [sumEvals_append, sumEvals, evalsOf] using hev
            · simp only [List.filterMap_append, List.filterMap_cons, attemptOf, List.filterMap_nil,
                List.nil_append, List.singleton_append, List.length_cons]
              rw [hatt, List.range'_succ]
              simp
            · simp at hlen ⊢; omega
            · intro _; simp [attemptOf]
            · simp at hfail ⊢; omega
            · rw [himm]; simp [isImmOk]
            · intro t' ht'; obtain ⟨a, b⟩ := hfin t' ht'; exact ⟨a, by simp [b]⟩
            · rw [hdr', ← hs3]; simp only; rw [hrng, h1rng, hdr]
            · rw [hsc', ← hs3]; simp only; rw [hsc, h1sc]
            · have : s3.next = s2.next := by rw [← hs3]
              omega
            · intro hsi; apply hinv'; rw [← hs3]; exact hinv (h1inv hsi)
            · intro o ho; apply hkeep'; rw [← hs3]; apply hkeep; rw [h1objs]; exact ho
            · intro hp o ho; apply hmem' _ o ho; rw [← hs3]; apply hkeep; rw [h1objs]; exact hp
          · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            refine ⟨[Call.mutate (attempts + 1) r.evals false true, Call.constraints t true], ?_,
              by simp [isLoopCall], ?_, by simp [attemptOf], by simp [attemptOf], by simp [attemptOf],
              by simp [attemptOf], by simp [isImmOk], ?_, by simp only; rw [hrng, h1rng, hdr],
              by simp only; rw [hsc, h1sc], by simp only; omega,
              fun hs => by exact hinv (h1inv hs), ?_, ?_⟩
            · simp [hlog, h1log, hi, hsu]
            · rfl
            · intro t' ht'; cases ht'; exact ⟨hc, by simp⟩
            · intro o ho; apply hkeep; rw [h1objs]; exact ho
            · intro _ o ho; cases ho
      · -- immediate, failure
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine ⟨[Call.mutate (attempts + 1) r.evals true false], by rw [hlog, h1log, hi, hsu],
          rfl, by rw [sumEvals_single], by simp [attemptOf], by simp [attemptOf], by simp [attemptOf],
          by simp [attemptOf], by simp [isImmOk], ?_, by rw [hrng, h1rng, hdr], by rw [hsc, h1sc],
          by rw [← h1next]; exact hnext, fun hs => hinv (h1inv hs), ?_, ?_⟩
        · intro t ht; cases ht
        · intro o ho; apply hkeep; rw [h1objs]; exact ho
        · intro _ o ho; cases ho
      · -- immediate, success
        cases out with
        | tree t => cases h
        | member o =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          refine ⟨[Call.mutate (attempts + 1) r.evals true true], by rw [hlog, h1log, hi, hsu],
            rfl, by rw [sumEvals_single], by simp [attemptOf], by simp [attemptOf], by simp [attemptOf],
            by simp [attemptOf], by simp [isImmOk], ?_, by rw [hrng, h1rng, hdr], by rw [hsc, h1sc],
            by rw [← h1next]; exact hnext, fun hs => hinv (h1inv hs), ?_, ?_⟩
          · intro t ht; cases ht
          · intro o' ho; apply hkeep; rw [h1objs]; exact ho
          · intro hp o' ho
            cases ho
            exact hmem (by rw [h1objs]; exact hp) o rfl

/-! ## Fresh results -/

/-- An abstract `mutate!` method never returns the `parent_member` object itself, as the
simplify handler, whose result is a `create_child` member (`src/Mutate.jl:918-927`), does not. -/
def NoParentOut (h : Handler E) : Prop := ∀ m t a rng u, (h m t a rng).1.out ≠ .parent u

/-- The simplify handler and every user `mutate!` method satisfy `NoParentOut`. -/
def MF.Fresh (mf : MF E) : Prop := NoParentOut mf.simplify ∧ ∀ n h, mf.custom n = some h → NoParentOut h

theorem bsLoop_not_parent (b : BS E) (pc : JF) : ∀ (n : Nat) (t : E) (setup : Option Nat) (ev : JF)
    (rng : RNG) (u : Option (E × JF × JF)), (bsLoop b pc n t setup ev rng).1.out ≠ .parent u := by
  intro n
  induction n with
  | zero => intro t setup ev rng u; simp [bsLoop]
  | succ n ih =>
    intro t setup ev rng u
    simp only [bsLoop]
    repeat' split
    all_goals simp_all

theorem mutateH_not_parent (mf : MF E) (hf : mf.Fresh) (k : Kind) (scale : JF) (m : Member E)
    (t : E) (a : Nat) (rng : RNG) (r : HRes E) (rng' : RNG)
    (h : mutateH mf k scale m t a rng = .ok (r, rng')) (u : Option (E × JF × JF)) :
    r.out ≠ .parent u := by
  cases k
  case simplify =>
    simp only [mutateH, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hf.1 _ _ _ _ u
  case custom n =>
    simp only [mutateH] at h
    cases hc : mf.custom n with
    | none => rw [hc] at h; cases h
    | some hd =>
      rw [hc] at h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hf.2 n hd hc _ _ _ _ u
  case backsolve =>
    simp only [mutateH, pure, Except.pure, Except.ok.injEq] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    subst h1
    unfold backsolveH
    split
    · simp
    · exact bsLoop_not_parent _ _ _ _ _ _ _ u
  case addNode =>
    simp only [mutateH, draw] at h
    by_cases hu : rng.draws rng.cursor < 1 / 2 <;>
      simp only [hu, ↓reduceIte, treeStep, pure, Except.pure] at h <;> (cases h; simp)
  all_goals simp only [mutateH, treeStep, draw, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; simp)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp)

theorem materialise_fresh (s : St E) (po pr : Nat) (cx : E → Int) (ho : HOut E) (hn : ∀ u, ho ≠ .parent u) :
    (∀ o, (materialise s po pr cx ho).1 = .member o → s.next ≤ o) ∧
    ∀ x, x < s.next → (materialise s po pr cx ho).2.objs x = s.objs x := by
  cases ho with
  | tree t => simp [materialise]
  | child t c l =>
    refine ⟨fun o h => ?_, fun x hx => ?_⟩
    · simp [materialise, createChild] at h; omega
    · have hx' : x ≠ s.next := by omega
      simp [materialise, createChild, St.write, hx']
  | optimized t c l upd =>
    cases upd with
    | none =>
      refine ⟨fun o h => ?_, fun x hx => ?_⟩
      · simp [materialise, createChild] at h; omega
      · have hx' : x ≠ s.next := by omega
        simp [materialise, createChild, St.write, hx']
    | some v =>
      obtain ⟨t', c', l'⟩ := v
      refine ⟨fun o h => ?_, fun x hx => ?_⟩
      · simp [materialise, createChild] at h; omega
      · have hx' : x ≠ s.next := by omega
        simp [materialise, createChild, St.write, hx']
  | parent u => exact absurd rfl (hn u)

/-- When no abstract handler returns the parent, an immediate result of the retry loop is a
newly allocated object and no object allocated before the loop changes. -/
theorem retry_fresh (cfg : Cfg E) (hf : cfg.mf.Fresh) (k : Kind) (scale : JF) (po : Nat)
    (m : Member E) (pr : Nat) (cms : Int) :
    ∀ (fuel attempts : Nat) (ev : JF) (s : St E) (e : LoopEnd E) (ev' : JF) (s' : St E),
    retry cfg k scale po m pr cms fuel attempts ev s = .ok ((e, ev'), s') →
    (∀ o, e = .immediate o → s.next ≤ o) ∧ ∀ x, x < s.next → s'.objs x = s.objs x := by
  intro fuel
  induction fuel with
  | zero =>
    intro attempts ev s e ev' s' h
    simp only [retry, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨fun o ho => (by cases ho), fun _ _ => rfl⟩
  | succ fuel ih =>
    intro attempts ev s e ev' s' h
    simp only [retry] at h
    split at h
    · cases h
    · rename_i r rng hm
      have hnp := mutateH_not_parent cfg.mf hf _ _ _ _ _ _ _ _ hm
      generalize hs1 : ({ s with rng := rng, log := s.log ++ [Call.mutate (attempts + 1) r.evals r.imm r.success] } : St E) = s1 at h
      have hfr := materialise_fresh s1 po pr cfg.complexity r.out hnp
      have hfa := materialise_facts s1 po pr cfg.complexity r.out
      generalize hmat : materialise s1 po pr cfg.complexity r.out = q at h hfr hfa
      obtain ⟨out, s2⟩ := q
      obtain ⟨hmem, hobj⟩ := hfr
      obtain ⟨-, -, -, hnext, -⟩ := hfa
      simp only at hmem hobj hnext h
      have h1next : s1.next = s.next := by rw [← hs1]
      have h1objs : s1.objs = s.objs := by rw [← hs1]
      have hkeep : ∀ x, x < s.next → s2.objs x = s.objs x := by
        intro x hx; rw [hobj x (by omega), h1objs]
      cases hi : r.imm <;> cases hsu : r.success <;> simp only [hi, hsu, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte] at h
      · cases out with
        | member o => cases h
        | tree t =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨fun o ho => (by cases ho), hkeep⟩
      · cases out with
        | member o => cases h
        | tree t =>
          simp only at h
          cases hc : cfg.constraints t cms <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          · obtain ⟨hfi, hob⟩ := ih (attempts + 1) (weightAdd ev r.evals) _ e ev' s' h
            refine ⟨fun o ho => ?_, fun x hx => ?_⟩
            · have := hfi o ho; simp only at this; omega
            · rw [hob x (by simp only; omega)]; exact hkeep x hx
          · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            exact ⟨fun o ho => (by cases ho), hkeep⟩
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨fun o ho => (by cases ho), hkeep⟩
      · cases out with
        | tree t => cases h
        | member o =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          refine ⟨fun o' ho' => ?_, hkeep⟩
          cases ho'
          have := hmem o rfl
          omega

end SymReg.MutateGen
