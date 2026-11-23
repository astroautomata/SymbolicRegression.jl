import SymReg.HofMig.Core

namespace SymReg.HofMig
open DynExpr

def member_copy_payload : Prop := ∀ (m : Member) (fresh : Nat),
  payload (copyMember m fresh).1 = payload m

theorem member_copy_payload_holds : member_copy_payload := by
  intro m fresh
  rfl

def member_copy_fresh : Prop := ∀ (m : Member) (fresh : Nat), Below fresh m →
  (copyMember m fresh).1.objectId ≠ m.objectId ∧
  (copyMember m fresh).1.treeId ≠ m.treeId ∧
  (copyMember m fresh).2 = fresh + 2

theorem member_copy_fresh_holds : member_copy_fresh := by
  intro m fresh h
  change fresh ≠ m.objectId ∧ fresh + 1 ≠ m.treeId ∧ fresh + 2 = fresh + 2
  unfold Below at h
  omega

example : Below 2 (specimen (.fin 0) (.fin 1)) := by simp [Below, specimen]

def constructor_empty : Prop := ∀ (n : Int) (tree fresh : Nat) (signals : Nat → Int × Int),
  (initHof n tree fresh signals).1.slots.length = n.toNat ∧
  ∀ s ∈ (initHof n tree fresh signals).1.slots, s.exists = false ∧
    s.member.cost = .fin 0 ∧ s.member.loss = .posInf ∧ s.member.complexity = 1

theorem constructor_empty_holds : constructor_empty := by
  intro n tree fresh signals
  constructor
  · simp [initHof]
  · intro s hs
    simp only [initHof, List.mem_map] at hs
    obtain ⟨i, _, rfl⟩ := hs
    simp

def eltype_paths : Prop := ∀ (h : Hof) (onType : Bool), memberEltype h onType = Member

theorem eltype_paths_holds : eltype_paths := by intro h onType; rfl

theorem copyMembers_length (ms : List Member) (fresh : Nat) :
    (copyMembers ms fresh).1.length = ms.length := by
  induction ms generalizing fresh with
  | nil => rfl
  | cons m ms ih => simpa [copyMembers, copyMember] using ih (fresh + 2)

theorem copyMembers_payload (ms : List Member) (fresh : Nat) :
    (copyMembers ms fresh).1.map payload = ms.map payload := by
  induction ms generalizing fresh with
  | nil => rfl
  | cons m ms ih => simp [copyMembers, copyMember, payload, ih]

theorem copyMembers_supply (ms : List Member) (fresh : Nat) :
    (copyMembers ms fresh).2 = fresh + 2 * ms.length := by
  induction ms generalizing fresh with
  | nil => simp [copyMembers]
  | cons m ms ih =>
    simp only [copyMembers, copyMember, ih, List.length_cons]
    omega

private theorem map_zip_right {α β : Type} (as : List α) (bs : List β)
    (h : as.length = bs.length) : (as.zip bs).map Prod.snd = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih => cases bs <;> simp_all

private theorem map_zip_left {α β : Type} (as : List α) (bs : List β)
    (h : as.length = bs.length) : (as.zip bs).map Prod.fst = as := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih => cases bs <;> simp_all

def hall_copy_values : Prop := ∀ (h : Hof) (fresh : Nat),
  ((copyHof h fresh).1.slots.map Slot.exists) = h.slots.map Slot.exists ∧
  ((copyHof h fresh).1.slots.map (payload ∘ Slot.member)) =
    h.slots.map (payload ∘ Slot.member) ∧
  (copyHof h fresh).2 = fresh + 2 * h.slots.length

theorem hall_copy_values_holds : hall_copy_values := by
  intro h fresh
  have hl : (copyMembers (h.slots.map Slot.member) fresh).1.length =
      (h.slots.map Slot.exists).length := by simp [copyMembers_length]
  constructor
  · simpa [copyHof, List.map_map, Function.comp_def] using map_zip_right _ _ hl
  constructor
  · have hh := congrArg (List.map payload) (map_zip_left
      (copyMembers (h.slots.map Slot.member) fresh).1 (h.slots.map Slot.exists) hl)
    simpa [copyHof, List.map_map, Function.comp_def, copyMembers_payload] using hh
  · simp [copyHof, copyMembers_supply]

def cached_complexity : Prop := ∀ (m : Member) (compute : Nat → Int),
  (resolveComplexity compute m).2 =
    (if m.complexity = -1 then compute m.tree else m.complexity) ∧
  (resolveComplexity compute m).1.complexity = (resolveComplexity compute m).2 ∧
  (resolveComplexity compute m).1.cost = m.cost ∧
  (resolveComplexity compute m).1.treeId = m.treeId

theorem cached_complexity_holds : cached_complexity := by
  intro m compute
  by_cases hc : m.complexity = -1 <;> simp [resolveComplexity, recomputeComplexity, hc]

def update_range : Prop := ∀ (h : Hof) (m : Member) (size : Int) (fresh : Nat),
  ¬ (0 < size ∧ size ≤ (h.slots.length : Int)) →
    updateUnchecked h m size fresh = (h, fresh)

theorem update_range_holds : update_range := by
  intro h m size fresh hn
  simp [updateUnchecked, hn]

example : ¬ (0 < (0 : Int) ∧ 0 ≤ (1 : Int)) := by decide


theorem less_self (x : JF) : less x x = false := by
  cases x <;> simp [less, DynExpr.Expressions.Sampling.greater]


def nan_recovery : Prop := ∀ (incumbent challenger : Member) (fresh : Nat),
  incumbent.cost = .nan → challenger.cost ≠ .nan →
  (((updateUnchecked ⟨[⟨incumbent, true⟩]⟩ challenger 1 fresh).1.slots[0]?).map
    (fun s => s.member.cost)) = some challenger.cost

theorem nan_recovery_refuted : ¬ nan_recovery := by
  intro hp
  have hh := hp (specimen .nan (.fin 1)) (specimen (.fin 1) (.fin 1)) 2 rfl (by decide)
  simp [updateUnchecked, specimen, less, DynExpr.Expressions.Sampling.greater] at hh

def checked_size_reject : Prop :=
  ∀ (h : Hof) (m : Member) (maxsize : Int) (fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  ¬ (0 < (resolveComplexity compute m).2 ∧ (resolveComplexity compute m).2 ≤ maxsize) →
  updateChecked h m maxsize fresh compute check = .ok (h, (resolveComplexity compute m).1, fresh)

theorem checked_size_reject_holds : checked_size_reject := by
  intro h m maxsize fresh compute check hn
  simp [updateChecked, hn]
  rfl

example : ¬ (0 < (resolveComplexity (fun _ => 2) (specimen (.fin 0) (.fin 1) 2)).2 ∧
    (resolveComplexity (fun _ => 2) (specimen (.fin 0) (.fin 1) 2)).2 ≤ 1) := by decide

def checked_constraints_reject : Prop :=
  ∀ (h : Hof) (m : Member) (maxsize : Int) (fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  check (resolveComplexity compute m).1 maxsize (resolveComplexity compute m).2 = .ok false →
  updateChecked h m maxsize fresh compute check = .ok (h, (resolveComplexity compute m).1, fresh)

theorem checked_constraints_reject_holds : checked_constraints_reject := by
  intro h m maxsize fresh compute check hc
  cases hr : resolveComplexity compute m with
  | mk m' size =>
    simp only [hr] at hc ⊢
    by_cases hi : 0 < size ∧ size ≤ maxsize
    · simp [updateChecked, hr, hi, hc]
      rfl
    · simp [updateChecked, hr, hi]
      rfl

example : (fun (_ : Member) (_ _ : Int) => (Except.ok false : Jl Bool))
    (specimen (.fin 0) (.fin 1)) 1 1 = .ok false := rfl

def cache_effects : Prop := ∀ (s : UpdateServices) (m : Member) (h : Hof) (fresh : Nat)
    (sharing : Bool),
  let st : UpdateState := { hall := h, fresh }
  (m.complexity ≠ -1 → runComplexity s m st sharing = (.ok m.complexity, st)) ∧
  ∀ force : Bool, (force = true ∨ m.complexity = -1) →
    (∀ e stop, s.tree m st = (.error e, stop) →
      runComplexity s m st sharing force = (.error e, stop)) ∧
    ∀ tree next, s.tree m st = (.ok tree, next) →
    let called := next.record (.compute tree s.options sharing)
    (∀ e stop, s.compute tree s.options sharing called = (.error e, stop) →
      runComplexity s m st sharing force = (.error e, stop)) ∧
    (∀ n result, s.compute tree s.options sharing called = (.ok n, result) →
      runComplexity s m st sharing force =
        (.ok n, { (result.record (.cache m.objectId n)) with
          caches := (m.objectId, n) :: result.caches }))

theorem cache_effects_holds : cache_effects := by
  intro s m h f sharing
  constructor
  · intro hn
    simp [runComplexity, UpdateState.readMember, hn]
  · intro force hf
    have hg : (force || m.complexity == -1) = true := by
      rcases hf with rfl | hc <;> simp [*]
    refine ⟨?_, ?_⟩
    · intro e stop ht
      simp [runComplexity, UpdateState.readMember, hg, ht]
    · intro tree next ht
      refine ⟨?_, ?_⟩
      · intro e stop hc
        simp [runComplexity, UpdateState.readMember, hg, ht, hc]
      · intro n result hc
        simp [runComplexity, UpdateState.readMember, hg, ht, hc]

def ReplacementEffects (s : UpdateServices) (m : Member) (size : Int)
    (accepted : UpdateState) (actual : Jl Unit × UpdateState) : Prop :=
  let copying := accepted.record (.copy m.objectId)
  (∀ e next, s.copy (accepted.readMember m) copying = (.error e, next) →
    actual = (.error e, next)) ∧
  (∀ copied next, s.copy (accepted.readMember m) copying = (.ok copied, next) →
    let assigning := next.record (.store size)
    (∀ e stop, s.store size copied assigning = (.error e, stop) →
      actual = (.error e, stop)) ∧
    (∀ stored stop, s.store size copied assigning = (.ok stored, stop) →
      actual.1 = .ok () ∧
      actual.2.hall.slots = stop.hall.slots.set (size.toNat - 1) ⟨stored, true⟩ ∧
      actual.2.events = stop.events ++ [.mark size]))

def update_rule : Prop := ∀ (s : UpdateServices) m size st slot,
  0 < size → size ≤ (st.hall.slots.length : Int) →
  st.hall.slots[size.toNat - 1]? = some slot →
  let actual := runUnchecked s m size st
  (slot.exists = false → ReplacementEffects s m size st actual) ∧
  (slot.exists = true →
    let first := s.cost (st.readMember m) st
    (∀ e next, first = (.error e, next) → actual = (.error e, next)) ∧
    (∀ a next, first = (.ok a, next) →
      (next.hall.slots[size.toNat - 1]? = none → actual = (.error .boundsError, next)) ∧
      ∀ incumbent, next.hall.slots[size.toNat - 1]? = some incumbent →
      let second := s.cost (next.readMember incumbent.member) next
      (∀ e stop, second = (.error e, stop) → actual = (.error e, stop)) ∧
      ∀ b tested, second = (.ok b, tested) →
      let compared := s.compare a b (tested.record (.compare size))
      (∀ e stop, compared = (.error e, stop) → actual = (.error e, stop)) ∧
      (∀ stop, compared = (.ok false, stop) → actual = (.ok (), stop)) ∧
      (∀ accepted, compared = (.ok true, accepted) →
        ReplacementEffects s m size accepted actual)))

private theorem replacement_effects (s : UpdateServices) (m : Member) (size : Int)
    (st : UpdateState) (slot : Slot) (hp : 0 < size) (hn : size ≤ (st.hall.slots.length : Int))
    (hs : st.hall.slots[size.toNat - 1]? = some slot)
    (accepted : UpdateState)
    (h : (if slot.exists then compareCosts s m size st else (.ok true, st)) =
      (.ok true, accepted)) : ReplacementEffects s m size accepted (runUnchecked s m size st) := by
  have step : runUnchecked s m size st =
      (match s.copy (accepted.readMember m) (accepted.record (.copy m.objectId)) with
       | (.error e, stopped) => (.error e, stopped)
       | (.ok copied, next) =>
         match s.store size copied (next.record (.store size)) with
         | (.error e, stopped) => (.error e, stopped)
         | (.ok stored, stop) => (.ok (), { (stop.record (.mark size)) with
             hall := ⟨stop.hall.slots.set (size.toNat - 1) ⟨stored, true⟩⟩ })) := by
    have hi : 0 < size ∧ size ≤ (st.hall.slots.length : Int) := ⟨hp, hn⟩
    simp only [runUnchecked, if_pos hi, hs, h] <;> rfl
  unfold ReplacementEffects
  rw [step]
  refine ⟨?_, ?_⟩
  · intro e next hc
    simp only [hc]
  · intro copied next hc
    simp only [hc]
    exact ⟨fun e stop hw => by simp only [hw],
      fun stored stop hw => by simp only [hw] <;> simp [UpdateState.record]⟩

theorem update_rule_holds : update_rule := by
  intro s m size st slot hp hn hs
  refine ⟨?_, ?_⟩
  · intro he
    exact replacement_effects s m size st slot hp hn hs st (by simp [he])
  · intro he
    refine ⟨?_, ?_⟩
    · intro e next hc
      simp [runUnchecked, compareCosts, hp, hn, hs, he, hc]
    · intro a next hc
      refine ⟨?_, ?_⟩
      · intro hi
        simp [runUnchecked, compareCosts, hp, hn, hs, he, hc, hi]
      · intro incumbent hi
        refine ⟨?_, ?_⟩
        · intro e stop ht
          simp [runUnchecked, compareCosts, hp, hn, hs, he, hc, hi, ht]
        · intro b tested ht
          refine ⟨?_, ?_, ?_⟩
          · intro e stop hr
            simp [runUnchecked, compareCosts, hp, hn, hs, he, hc, hi, ht, hr]
          · intro stop hr
            simp [runUnchecked, compareCosts, hp, hn, hs, he, hc, hi, ht, hr]
          · intro accepted hr
            exact replacement_effects s m size st slot hp hn hs accepted
              (by simp [compareCosts, he, hc, hi, ht, hr])

example : (0 < (1 : Int) ∧ 1 ≤ (1 : Int)) ∧
    ([⟨specimen (.fin 0) (.fin 1), false⟩] : List Slot)[0]? =
      some ⟨specimen (.fin 0) (.fin 1), false⟩ := by decide

private def stockCost (s : UpdateServices) : UpdateServices :=
  { s with
    cost := fun m st => (.ok m.cost, st)
    compare := fun a b st => (.ok (less a b), st) }

def update_tie : Prop := ∀ (s : UpdateServices) m size st slot,
  0 < size → size ≤ (st.hall.slots.length : Int) →
  st.hall.slots[size.toNat - 1]? = some slot → slot.exists = true →
  let s := stockCost s
  let actual := runUnchecked s m size st
  let a := (st.readMember m).cost
  let b := (st.readMember slot.member).cost
  (a = b → actual = (.ok (), st.record (.compare size))) ∧
  (less a b = true → ReplacementEffects s m size (st.record (.compare size)) actual)

theorem update_tie_holds : update_tie := by
  intro s m size st slot hp hn hs he
  refine ⟨?_, ?_⟩
  · intro hc
    simp [runUnchecked, compareCosts, stockCost, hp, hn, hs, he, hc, less_self]
  · intro hc
    exact replacement_effects (stockCost s) m size st slot hp hn hs _
      (by simp [compareCosts, stockCost, hs, he, hc])

def nan_incumbent_frozen : Prop := ∀ (s : UpdateServices) m size st slot,
  0 < size → size ≤ (st.hall.slots.length : Int) →
  st.hall.slots[size.toNat - 1]? = some slot →
  (st.readMember slot.member).cost = .nan →
  let s := stockCost s
  let actual := runUnchecked s m size st
  (slot.exists = true → actual = (.ok (), st.record (.compare size))) ∧
  (slot.exists = false → ReplacementEffects s m size st actual)

theorem nan_incumbent_frozen_holds : nan_incumbent_frozen := by
  intro s m size st slot hp hn hs hc
  refine ⟨?_, (update_rule_holds (stockCost s) m size st slot hp hn hs).1⟩
  intro he
  simp [runUnchecked, compareCosts, stockCost, hp, hn, hs, he, hc, less,
    DynExpr.Expressions.Sampling.greater]

example : let m := specimen .nan (.fin 1)
    let s : Slot := ⟨m, true⟩
    ([s] : List Slot)[0]? = some s ∧ s.exists = true ∧ m.cost = s.member.cost ∧
      s.member.cost = .nan := by decide

def update_range_effects : Prop := ∀ (s : UpdateServices) m size st,
  (¬ (0 < size ∧ size ≤ (st.hall.slots.length : Int)) →
    runUnchecked s m size st = (.ok (), st)) ∧
  (∀ slot, 0 < size → size ≤ (st.hall.slots.length : Int) →
    st.hall.slots[size.toNat - 1]? = some slot → slot.exists = false →
    ReplacementEffects s m size st (runUnchecked s m size st))

theorem update_range_effects_holds : update_range_effects := by
  intro s m size st
  exact ⟨fun hn => by simp [runUnchecked, hn],
    fun slot hp hn hs => (update_rule_holds s m size st slot hp hn hs).1⟩

def checked_size_effects : Prop := ∀ (s : UpdateServices) m st,
  (∀ e next, runComplexity s m st = (.error e, next) →
    runChecked s m st = (.error e, next)) ∧
  ∀ size next, runComplexity s m st = (.ok size, next) →
  (size ≤ 0 → runChecked s m st = (.ok (), next)) ∧
  (0 < size →
    (∀ e stop, s.maxsize next = (.error e, stop) → runChecked s m st = (.error e, stop)) ∧
    (∀ limit tested, s.maxsize next = (.ok limit, tested) → limit < size →
      runChecked s m st = (.ok (), tested)))

theorem checked_size_effects_holds : checked_size_effects := by
  intro s m st
  refine ⟨fun e next hr => by simp [runChecked, hr], ?_⟩
  intro size next hr
  refine ⟨fun hn => by simp [runChecked, hr, hn], ?_⟩
  intro hp
  refine ⟨fun e stop hm => by simp [runChecked, hr, Int.not_le.mpr hp, hm],
    fun limit tested hm hn => by simp [runChecked, hr, Int.not_le.mpr hp, hm, hn]⟩

def checked_constraint_effects : Prop := ∀ (s : UpdateServices) m st size next limit tested,
  runComplexity s m st = (.ok size, next) → 0 < size →
  s.maxsize next = (.ok limit, tested) → size ≤ limit →
  let getTree := s.tree (tested.readMember m) tested
  (∀ e stop, getTree = (.error e, stop) → runChecked s m st = (.error e, stop)) ∧
  ∀ tree live, getTree = (.ok tree, live) →
  (∀ e stop, s.maxsize live = (.error e, stop) → runChecked s m st = (.error e, stop)) ∧
  ∀ current called, s.maxsize live = (.ok current, called) →
  let result := s.check tree s.options current size (called.record (.check tree s.options current size))
  (∀ stop, result = (.ok false, stop) → runChecked s m st = (.ok (), stop)) ∧
  (∀ e stop, result = (.error e, stop) → runChecked s m st = (.error e, stop)) ∧
  (∀ accepted, result = (.ok true, accepted) →
    runChecked s m st = runUnchecked s m size accepted)

theorem checked_constraint_effects_holds : checked_constraint_effects := by
  intro s m st size next limit tested hr hp hm hn
  have hp' : ¬ size ≤ 0 := Int.not_le.mpr hp
  have hn' : ¬ limit < size := Int.not_lt.mpr hn
  refine ⟨fun e stop ht => by simp [runChecked, hr, hp', hm, hn', ht], ?_⟩
  intro tree live ht
  refine ⟨fun e stop hl => by simp [runChecked, hr, hp', hm, hn', ht, hl], ?_⟩
  intro current called hl
  refine ⟨fun stop hc => by simp [runChecked, hr, hp', hm, hn', ht, hl, hc],
    fun e stop hc => by simp [runChecked, hr, hp', hm, hn', ht, hl, hc],
    fun accepted hc => by simp [runChecked, hr, hp', hm, hn', ht, hl, hc]⟩

def checked_step_effects : Prop := ∀ (s : UpdateServices) m st size next limit tested tree live
    current called accepted slot,
  runComplexity s m st = (.ok size, next) → 0 < size →
  s.maxsize next = (.ok limit, tested) → size ≤ limit →
  s.tree (tested.readMember m) tested = (.ok tree, live) →
  s.maxsize live = (.ok current, called) →
  s.check tree s.options current size (called.record (.check tree s.options current size)) =
    (.ok true, accepted) →
  size ≤ (accepted.hall.slots.length : Int) →
  accepted.hall.slots[size.toNat - 1]? = some slot → slot.exists = false →
  ReplacementEffects s m size accepted (runChecked s m st)

theorem checked_step_effects_holds : checked_step_effects := by
  intro s m st size next limit tested tree live current called accepted slot hr hp hm hn ht hl hc
    hs hi he
  have step := checked_constraint_effects_holds s m st size next limit tested hr hp hm hn
  rw [(step.2 tree live ht |>.2 current called hl |>.2.2 accepted hc)]
  exact (update_range_effects_holds s m size accepted).2 slot hp hs hi he

example :
    let m := specimen (.fin 1) (.fin 2) (-1)
    let s : UpdateServices := {
      options := 7
      maxsize := fun st => (.ok 1, st)
      compute := fun _ _ _ st => (.ok 1, st)
      check := fun _ _ _ _ st => (.ok true, st.writeMember { m with complexity := -1 }) }
    let st : UpdateState := { hall := ⟨[⟨m, false⟩]⟩, fresh := 10 }
    let (result, next) := runChecked s m st
    result = .ok () ∧
      next.hall.slots[0]?.map (fun slot => (slot.member.complexity, slot.exists)) = some (-1, true) :=
  by decide

end SymReg.HofMig
