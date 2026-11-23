import SymReg.MutateGen.EngineLemmas

/-!
Case analysis of `nextGenCore` and `nextGeneration`: every successful call ends in exactly
one of the four exits of `src/Mutate.jl:438,475,503,536,561`.
-/

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw)

variable {E : Type}

/-- The `on_mutation_end!` calls `_fire_on_mutation_end!` makes for one event. -/
def endsOf (cfg : Cfg E) (k : Kind) (ev : Event) : List (Call E) :=
  (List.range cfg.plugins.length).map (fun i => Call.onEnd i k ev)

/-- `copy_into!(node_storage, member.tree)` on the current parent object. -/
def curTreeOf (po : Nat) (m : Member E) (s : St E) : E := ((s.objs po).map Member.tree).getD m.tree

/-- The final store after `create_child`: object `o = s.next` holds `r`, others unchanged. -/
def ChildStore (s s' : St E) (o : Nat) (r : Member E) : Prop :=
  o = s.next ∧ s'.objs o = some r ∧ (∀ o', o' ≠ o → s'.objs o' = s.objs o') ∧ s'.next = s.next + 1

/-- The four exits of `_next_generation`. `s2` is the store after the retry loop. -/
def Outcome (cfg : Cfg E) (k : Kind) (idx po : Nat) (m : Member E) (e : LoopEnd E) (evr : JF)
    (s2 : St E) (o : Nat) (acc : Bool) (ev : JF) (s' : St E) : Prop :=
  s'.rng.draws = s2.rng.draws ∧ s'.scratch = s2.scratch ∧
  ∃ evt pre, s'.log = s2.log ++ pre ++ endsOf cfg k evt ∧ evt.accepted = acc ∧ evt.idx = idx ∧
  ((e = .immediate o ∧ acc = true ∧ ev = evr ∧ pre = [] ∧ s'.objs = s2.objs ∧ s'.next = s2.next) ∨
   ((∃ t, e = .finished false t) ∧ acc = false ∧ ev = evr ∧ pre = [] ∧
     ChildStore s2 s' o ⟨curTreeOf po m s2, m.cost, m.loss, o, o, m.ref, cfg.complexity (curTreeOf po m s2)⟩) ∨
   (∃ t, e = .finished true t ∧ (cfg.evalCost t).1 = .nan ∧ acc = false ∧ ev = weightAdd evr cfg.frac ∧
     pre = [.eval t] ∧ ChildStore s2 s' o ⟨curTreeOf po m s2, m.cost, m.loss, o, o, m.ref,
       cfg.complexity (curTreeOf po m s2)⟩) ∨
   (∃ t c l, e = .finished true t ∧ cfg.evalCost t = (c, l) ∧ c ≠ .nan ∧ ev = weightAdd evr cfg.frac ∧
     pre = [.eval t] ∧
     acc = !jlt (prodJF (cfg.plugins.map fun pl => pl.accept m t m.cost c))
       (.fin (s2.rng.draws s2.rng.cursor)) ∧
     (acc = true → ChildStore s2 s' o ⟨t, c, l, o, o, m.ref, cfg.complexity t⟩) ∧
     (acc = false → ChildStore s2 s' o ⟨curTreeOf po m s2, m.cost, m.loss, o, o, m.ref,
       cfg.complexity (curTreeOf po m s2)⟩)))

theorem core_outcome (cfg : Cfg E) (k : Kind) (idx po : Nat) (m : Member E) (cms : Int)
    (s s' : St E) (o : Nat) (acc : Bool) (ev : JF)
    (h : nextGenCore cfg k idx po m cms s = .ok ((o, acc, ev), s')) :
    ∃ scale e evr s2, retry cfg k scale po m m.ref cms 10 0 (.fin 0) s = .ok ((e, evr), s2) ∧
      Outcome cfg k idx po m e evr s2 o acc ev s' := by
  unfold nextGenCore at h
  generalize (if k = .constant then _ else _ : JF) = scale at h
  refine ⟨scale, ?_⟩
  dsimp only at h
  split at h
  · cases h
  · rename_i o' evr s2 hr
    split at h
    · rename_i r hr2
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, _, _, hr, rfl, rfl, ⟨true, m.cost, some r.cost, m.loss, some r.loss, idx⟩, [],
        by simp [fireEnd, endsOf], rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · cases h
  · rename_i t evr s2 hr
    simp only [createChild, St.write, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    refine ⟨_, _, _, hr, rfl, rfl, ⟨false, m.cost, none, m.loss, none, idx⟩, [],
      by simp [fireEnd, endsOf], rfl, rfl,
      Or.inr (Or.inl ⟨⟨t, rfl⟩, rfl, rfl, rfl, ?_⟩)⟩
    refine ⟨rfl, by simp [fireEnd, curTreeOf], ?_, rfl⟩
    intro o' ho'; simp [fireEnd]; try (intro h; exact absurd h ho')
  · rename_i t evr s2 hr
    try dsimp only at h
    split at h
    · rename_i hnan
      simp only [createChild, St.write, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, _, _, hr, rfl, rfl, ⟨false, m.cost, none, m.loss, none, idx⟩, [.eval t],
        by simp [fireEnd, endsOf], rfl, rfl,
        Or.inr (Or.inr (Or.inl ⟨t, rfl, hnan, rfl, rfl, rfl, ?_⟩))⟩
      refine ⟨rfl, by simp [fireEnd, curTreeOf], ?_, rfl⟩
      intro o' ho'; simp [fireEnd]; try (intro h; exact absurd h ho')
    · rename_i hnan
      split at h
      · rename_i hj
        simp only [createChild, St.write, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        refine ⟨_, _, _, hr, rfl, rfl, ⟨false, m.cost, some (cfg.evalCost t).1, m.loss,
          some (cfg.evalCost t).2, idx⟩, [.eval t], by simp [fireEnd, endsOf], rfl, rfl,
          Or.inr (Or.inr (Or.inr ⟨t, (cfg.evalCost t).1, (cfg.evalCost t).2, rfl, rfl, hnan, rfl, rfl,
            by simpa [draw] using hj, fun hf => Bool.noConfusion hf, fun _ => ?_⟩))⟩
        refine ⟨rfl, by simp [fireEnd, curTreeOf], ?_, rfl⟩
        intro o' ho'; simp [fireEnd]; try (intro h; exact absurd h ho')
      · rename_i hj
        simp only [createChild, St.write, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        refine ⟨_, _, _, hr, rfl, rfl, ⟨true, m.cost, some (cfg.evalCost t).1, m.loss,
          some (cfg.evalCost t).2, idx⟩, [.eval t], by simp [fireEnd, endsOf], rfl, rfl,
          Or.inr (Or.inr (Or.inr ⟨t, (cfg.evalCost t).1, (cfg.evalCost t).2, rfl, rfl, hnan, rfl, rfl,
            by simpa [draw] using hj, fun _ => ?_, fun hf => Bool.noConfusion hf⟩))⟩
        refine ⟨rfl, by simp [fireEnd], ?_, rfl⟩
        intro o' ho'; simp [fireEnd]; try (intro h; exact absurd h ho')

theorem scratch_ok {α : Type} (prior : List (Option α)) (muts : List α) :
    mutationWeightsScratch prior muts = .ok (muts.map some) := by
  have hl : (List.take muts.length prior ++ List.replicate (muts.length - prior.length) none).length =
      muts.length := by simp; omega
  simp only [mutationWeightsScratch, copyTo, resizeScratch, hl, Nat.le_refl, ↓reduceIte,
    List.drop_eq_nil_of_le (Nat.le_of_eq hl), List.append_nil]
  rfl

theorem readAll_map {α : Type} (xs : List α) : readAll (xs.map some) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [readAll, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]; rfl

theorem ng_unfold (cfg : Cfg E) (po : Nat) (cms : Int) (s s' : St E) (o : Nat) (acc : Bool)
    (ev : JF) (h : nextGeneration cfg po cms s = .ok ((o, acc, ev), s')) :
    ∃ m idx k w rng, s.objs po = some m ∧
      sampleMutationR (conditionedWeights cfg m cms cfg.mutations) s.rng = (.ok idx, rng) ∧
      (conditionedWeights cfg m cms cfg.mutations)[idx - 1]? = some (k, w) ∧
      nextGenCore cfg k idx po (conditionParent cfg m) cms
        { s.write po (conditionParent cfg m) with
          scratch := (conditionedWeights cfg m cms cfg.mutations).map some, rng := rng,
                 log := s.log ++ [.choose k idx] } = .ok ((o, acc, ev), s') := by
  unfold nextGeneration at h
  split at h
  · cases h
  · rename_i m hm
    rw [scratch_ok] at h
    simp only [readAll_map] at h
    split at h
    · cases h
    · rename_i idx rng hs
      split at h
      · cases h
      · rename_i k w hk
        exact ⟨m, idx, k, w, rng, hm, hs, hk, h⟩

end SymReg.MutateGen
