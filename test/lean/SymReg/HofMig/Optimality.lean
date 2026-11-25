import SymReg.HofMig.Hall

namespace SymReg.HofMig
open DynExpr

abbrev Payload := JF × JF × Int × Nat × Int × Int × Int

/-- Optional payload of the existing member at a complexity slot. -/
def slotPayload (h : Hof) (k : Nat) : Option Payload :=
  (h.slots[k]?).bind (fun s => if s.exists then some (payload s.member) else none)

/-- Independent sequential best-seen specification: NaN challengers are skipped,
incumbent ties are kept, and non-NaN challengers compare via `isless`. -/
def choosePayload (old : Option Payload) (candidate : Payload) : Option Payload :=
  if candidate.1 = .nan then old
  else match old with
    | none => some candidate
    | some incumbent => if isless candidate.1 incumbent.1 then some candidate else old

/-- Reference per-complexity reduction of an arbitrary population stream. -/
def bestSeen (k : Nat) (compute : Nat → Int) : Option Payload → List Member → Option Payload
  | old, [] => old
  | old, m :: ms =>
    let (resolved, size) := resolveComplexity compute m
    bestSeen k compute
      (if size = ((k + 1 : Nat) : Int) then choosePayload old (payload resolved) else old) ms

theorem update_length (h : Hof) (m : Member) (size : Int) (fresh : Nat) :
    (updateUnchecked h m size fresh).1.slots.length = h.slots.length := by
  unfold updateUnchecked
  split
  · split
    · rfl
    · split
      · rfl
      · split <;> simp [copyMember]
  · rfl

theorem update_observation (h : Hof) (m : Member) (size : Int) (fresh k : Nat)
    (hk : k < h.slots.length) :
    slotPayload (updateUnchecked h m size fresh).1 k =
      if size = ((k + 1 : Nat) : Int) then choosePayload (slotPayload h k) (payload m)
      else slotPayload h k := by
  by_cases he : size = ((k + 1 : Nat) : Int)
  · subst size
    have hle : (k : Int) + 1 ≤ (h.slots.length : Int) := by omega
    by_cases hnan : m.cost = .nan
    · simp [updateUnchecked, hle, hnan, choosePayload, payload]
    · cases hp : h.slots[k].exists <;> cases hc : isless m.cost h.slots[k].member.cost <;>
        simp [updateUnchecked, hle, hnan, hp, hc, slotPayload, choosePayload, payload, copyMember, hk]
  · have he' : size ≠ (k : Int) + 1 := by omega
    by_cases hi : 0 < size ∧ size ≤ (h.slots.length : Int)
    · by_cases hnan : m.cost = .nan
      · simp [updateUnchecked, hi, hnan, he']
      · have hn : size.toNat - 1 ≠ k := by omega
        cases hs : h.slots[size.toNat - 1]? with
        | none => simp [updateUnchecked, hi, hnan, hs, he']
        | some s =>
          cases hc : (!s.exists || isless m.cost s.member.cost) <;>
            simp [updateUnchecked, hi, hnan, hs, hc, slotPayload, List.getElem?_set_ne hn, he', copyMember]
    · simp [updateUnchecked, hi, he']

def all_slots_best_seen : Prop :=
  ∀ (h : Hof) (ms : List Member) (fresh k : Nat) (compute : Nat → Int),
  k < h.slots.length →
  slotPayload (updateManyUnchecked h ms fresh compute).1 k =
    bestSeen k compute (slotPayload h k) ms

theorem all_slots_best_seen_holds : all_slots_best_seen := by
  intro h ms fresh k compute hk
  induction ms generalizing h fresh with
  | nil => rfl
  | cons m ms ih =>
    simp only [updateManyUnchecked, bestSeen]
    have hl := update_length h (resolveComplexity compute m).1 (resolveComplexity compute m).2 fresh
    have hh := ih (updateUnchecked h (resolveComplexity compute m).1
      (resolveComplexity compute m).2 fresh).1
      (updateUnchecked h (resolveComplexity compute m).1
        (resolveComplexity compute m).2 fresh).2 (by omega)
    rw [hh, update_observation h _ _ _ _ hk]

example : 0 < (⟨[⟨specimen (.fin 0) (.fin 1), false⟩]⟩ : Hof).slots.length := by decide

def update_frame : Prop := ∀ (h : Hof) (m : Member) (size : Int) (fresh k : Nat),
  size.toNat - 1 ≠ k → (updateUnchecked h m size fresh).1.slots[k]? = h.slots[k]?

theorem update_frame_holds : update_frame := by
  intro h m size fresh k hn
  unfold updateUnchecked
  split
  · split
    · rfl
    · split
      · rfl
      · split <;> simp [copyMember, List.getElem?_set_ne hn]
  · rfl

example : (1 : Nat) ≠ 0 := by decide

def update_copies : Prop := ∀ (h : Hof) (m : Member) (size : Int) (fresh : Nat) (s : Slot),
  (0 < size ∧ size ≤ (h.slots.length : Int)) →
  m.cost ≠ .nan →
  h.slots[size.toNat - 1]? = some s →
  (!s.exists || isless m.cost s.member.cost) = true → Below fresh m →
  ∃ stored, (updateUnchecked h m size fresh).1.slots[size.toNat - 1]? = some ⟨stored, true⟩ ∧
    payload stored = payload m ∧ stored.objectId ≠ m.objectId ∧ stored.treeId ≠ m.treeId

theorem update_copies_holds : update_copies := by
  intro h m size fresh s hi hnan hs hc hf
  refine ⟨(copyMember m fresh).1, ?_, rfl, ?_⟩
  · have hb : size.toNat - 1 < h.slots.length := by omega
    simp [updateUnchecked, hi, hnan, hs, hc, List.getElem?_set_self hb, copyMember]
  · exact ⟨(member_copy_fresh_holds m fresh hf).1,
      (member_copy_fresh_holds m fresh hf).2.1⟩

example : let m := specimen (.fin 0) (.fin 1)
    let s : Slot := ⟨m, false⟩
    (0 < (1 : Int) ∧ 1 ≤ (1 : Int)) ∧ m.cost ≠ .nan ∧ ([s] : List Slot)[0]? = some s ∧
    (!s.exists || isless m.cost s.member.cost) = true ∧ Below 2 m := by
  simp [specimen, Below]

def checked_scalar_step : Prop :=
  ∀ (h : Hof) (m : Member) (maxsize : Int) (fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  (0 < (resolveComplexity compute m).2 ∧ (resolveComplexity compute m).2 ≤ maxsize) →
  check (resolveComplexity compute m).1 maxsize (resolveComplexity compute m).2 = .ok true →
  updateChecked h m maxsize fresh compute check =
    .ok ((updateUnchecked h (resolveComplexity compute m).1 (resolveComplexity compute m).2 fresh).1,
      (resolveComplexity compute m).1,
      (updateUnchecked h (resolveComplexity compute m).1 (resolveComplexity compute m).2 fresh).2)

theorem checked_scalar_step_holds : checked_scalar_step := by
  intro h m maxsize fresh compute check hi hc
  cases hr : resolveComplexity compute m with
  | mk resolved size =>
    simp only [hr] at hi hc ⊢
    simp [updateChecked, hr, hi, hc]
    cases updateUnchecked h resolved size fresh
    rfl

example : let m := specimen (.fin 0) (.fin 1)
    let compute := fun (_ : Nat) => (1 : Int)
    (0 < (resolveComplexity compute m).2 ∧ (resolveComplexity compute m).2 ≤ 1) ∧
      (fun (_ : Member) (_ _ : Int) => (Except.ok true : Jl Bool))
        (resolveComplexity compute m).1 1 (resolveComplexity compute m).2 = .ok true := by decide

def checked_many_append : Prop :=
  ∀ (h : Hof) (left right : List Member) (maxsize : Int) (fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  updateManyChecked h (left ++ right) maxsize fresh compute check =
    (do let (h', left', f') ← updateManyChecked h left maxsize fresh compute check
        let (h'', right', f'') ← updateManyChecked h' right maxsize f' compute check
        pure (h'', left' ++ right', f''))

theorem checked_many_append_holds : checked_many_append := by
  intro h left right maxsize fresh compute check
  induction left generalizing h fresh with
  | nil =>
    simp [updateManyChecked, pure, Except.pure, bind, Except.bind]
    cases updateManyChecked h right maxsize fresh compute check <;> rfl
  | cons m ms ih =>
    cases hs : updateChecked h m maxsize fresh compute check with
    | error e => simp [updateManyChecked, hs, bind, Except.bind]
    | ok step =>
      rcases step with ⟨h', m', f'⟩
      simp only [List.cons_append, updateManyChecked, hs, bind, Except.bind]
      rw [ih]
      cases hm : updateManyChecked h' ms maxsize f' compute check with
      | error e => simp [bind, Except.bind]
      | ok middle =>
        rcases middle with ⟨h'', ms', f''⟩
        cases hr : updateManyChecked h'' right maxsize f'' compute check <;>
          simp [hr, pure, Except.pure, bind, Except.bind]

private theorem runCheckedSources_append (s : UpdateServices) (left right : List UpdateSource)
    (st : UpdateState) :
    runCheckedSources s (left ++ right) st =
      (match runCheckedSources s left st with
       | (.error e, stopped) => (.error e, stopped)
       | (.ok (), next) => runCheckedSources s right next) := by
  induction left generalizing st with
  | nil => rfl
  | cons src rest ih =>
    simp only [List.cons_append, runCheckedSources]
    split
    · rfl
    · split
      · rfl
      · exact ih _

def checked_population_order : Prop :=
  (∀ s left right st, runCheckedSources s (left ++ right) st =
    (match runCheckedSources s left st with
     | (.error e, stopped) => (.error e, stopped)
     | (.ok (), next) => runCheckedSources s right next)) ∧
  let first := { (specimen (.fin 2) (.fin 2) (-1)) with treeId := 11, tree := 11, objectId := 1 }
  let second := { (specimen (.fin 1) (.fin 1) (-1)) with treeId := 22, tree := 22, objectId := 2 }
  let third := { second with tree := 33, objectId := 3 }
  let e := DynExpr.JlError.errorException "constraint failed"
  let svc : UpdateServices := {
    options := 9, maxsize := fun st => (.ok 1, st), compute := fun _ _ _ st => (.ok 1, st),
    check := fun tree _ _ _ st => if tree = 22 then (.error e, st) else (.ok true, st) }
  let (result, stopped) := runManyChecked svc [first, second, third]
    { hall := ⟨[⟨third, false⟩]⟩, fresh := 10 }
  result = .error e ∧ stopped.fresh = 12 ∧
    stopped.caches = [(2, 1), (1, 1)] ∧
    stopped.hall.slots = [⟨{ first with complexity := 1, objectId := 10, treeId := 11 }, true⟩] ∧
    stopped.events = [.visit 1, .compute 11 9 false, .cache 1 1, .check 11 9 1 1,
      .copy 1, .store 1, .mark 1, .visit 2, .compute 22 9 false, .cache 2 1, .check 22 9 1 1] ∧
  let aliased := { first with complexity := 2 }
  let svc := { svc with maxsize := fun st => (.ok 2, st), check := fun _ _ _ _ st => (.ok true, st) }
  let (out, live) := runCheckedAliased svc
    { hall := ⟨[⟨aliased, true⟩, ⟨third, false⟩]⟩, fresh := 10 }
  out = .ok () ∧ live.events =
    [.visit 1, .check 11 9 2 2, .copy 1, .store 2, .mark 2, .visit 10, .check 11 9 2 2, .compare 2]

theorem checked_population_order_holds : checked_population_order := by
  exact ⟨runCheckedSources_append, by decide⟩

/-- Per-slot best-seen specification after rejecting out-of-range or
constraint-failing members; constraint exceptions stop this reduction too. -/
def bestChecked (k : Nat) (maxsize : Int) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool) (old : Option Payload) : List Member → Jl (Option Payload)
  | [] => pure old
  | m :: ms => do
    let (resolved, size) := resolveComplexity compute m
    if ¬ (0 < size ∧ size ≤ maxsize) then
      return ← bestChecked k maxsize compute check old ms
    if !(← check resolved maxsize size) then
      return ← bestChecked k maxsize compute check old ms
    bestChecked k maxsize compute check
      (if size = ((k + 1 : Nat) : Int) then choosePayload old (payload resolved) else old) ms

def checked_all_slots_best_seen : Prop :=
  ∀ (h : Hof) (ms : List Member) (maxsize : Int) (fresh k : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
  k < h.slots.length →
  (updateManyChecked h ms maxsize fresh compute check).map (fun result => slotPayload result.1 k) =
    bestChecked k maxsize compute check (slotPayload h k) ms

theorem checked_all_slots_best_seen_holds : checked_all_slots_best_seen := by
  intro h ms maxsize fresh k compute check hk
  induction ms generalizing h fresh with
  | nil => rfl
  | cons m ms ih =>
    cases hr : resolveComplexity compute m with
    | mk resolved size =>
      by_cases hi : 0 < size ∧ size ≤ maxsize
      · cases hc : check resolved maxsize size with
        | error e =>
          simp [updateManyChecked, updateChecked, bestChecked, hr, hi, hc,
            Except.map, bind, Except.bind]
        | ok pass =>
          cases pass with
          | false =>
            have hh := ih h fresh hk
            cases hm : updateManyChecked h ms maxsize fresh compute check <;>
              simpa [updateManyChecked, updateChecked, bestChecked, hr, hi, hc, hm,
                Except.map, pure, Except.pure, bind, Except.bind] using hh
          | true =>
            let step := updateUnchecked h resolved size fresh
            have hlen : k < step.1.slots.length := by
              dsimp [step]
              rw [update_length]
              exact hk
            have hh := ih step.1 step.2 hlen
            have hob := update_observation h resolved size fresh k hk
            change slotPayload step.1 k = _ at hob
            rw [hob] at hh
            cases hm : updateManyChecked step.1 ms maxsize step.2 compute check <;>
              simpa [updateManyChecked, updateChecked, bestChecked, hr, hi, hc,
                step, hm, Except.map, pure, Except.pure, bind, Except.bind] using hh
      · have hh := ih h fresh hk
        cases hm : updateManyChecked h ms maxsize fresh compute check <;>
          simpa [updateManyChecked, updateChecked, bestChecked, hr, hi, hm,
            Except.map, pure, Except.pure, bind, Except.bind] using hh

example : 0 < (⟨[⟨specimen (.fin 0) (.fin 1), false⟩]⟩ : Hof).slots.length := by decide

end SymReg.HofMig
