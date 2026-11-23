import SymReg.HofMig.Hall
import Init.Data.Rat.Lemmas

namespace SymReg.HofMig
open DynExpr

/-- Original slots annotated with all preceding slots, an independent selection specification. -/
def withPrefixes (earlier : List Slot) : List Slot → List (List Slot × Slot)
  | [] => []
  | s :: ss => (earlier, s) :: withPrefixes (earlier ++ [s]) ss

/-- Mathematical front membership: a non-NaN loss, with the code's IEEE rejection comparison. -/
def frontSpec (earlier slots : List Slot) : List Member :=
  ((withPrefixes earlier slots).filter (fun (before, s) =>
    s.exists && s.member.loss != .nan &&
      before.all (fun p => !p.exists || !greaterEqual s.member.loss p.member.loss))).map
    (fun pair => pair.2.member)


theorem dominates_all (m : Member) (earlier : List Slot) :
    dominatesEarlier m earlier =
      earlier.all (fun p => !p.exists || !greaterEqual m.loss p.member.loss) := by
  induction earlier with
  | nil => rfl
  | cons s ss ih =>
    change Bool.not ((s.exists && greaterEqual m.loss s.member.loss) ||
        ss.any (fun p => p.exists && greaterEqual m.loss p.member.loss)) =
      ((!s.exists || !greaterEqual m.loss s.member.loss) &&
        ss.all (fun p => !p.exists || !greaterEqual m.loss p.member.loss))
    rw [← ih]
    simp only [dominatesEarlier]
    cases s.exists <;> cases greaterEqual m.loss s.member.loss <;>
      cases ss.any (fun p => p.exists && greaterEqual m.loss p.member.loss) <;> rfl

theorem dominates_iff (m : Member) (earlier : List Slot) :
    dominatesEarlier m earlier = true ↔
      ∀ p ∈ earlier, p.exists = true → greaterEqual m.loss p.member.loss = false := by
  rw [dominates_all]
  simp only [List.all_eq_true]
  constructor
  · intro h p hp he
    simpa [he] using h p hp
  · intro h p hp
    cases he : p.exists
    · simp
    · simp [h p hp he]

theorem frontRaw_spec (earlier slots : List Slot) : frontRaw earlier slots = frontSpec earlier slots := by
  induction slots generalizing earlier with
  | nil => rfl
  | cons s ss ih =>
    have ht := ih (earlier ++ [s])
    by_cases hc : (s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier) = true
    · have hc' : (s.exists && s.member.loss != .nan &&
        earlier.all (fun p => !p.exists || !greaterEqual s.member.loss p.member.loss)) = true := by
        simpa only [dominates_all] using hc
      simpa only [frontRaw, frontSpec, withPrefixes, List.filter_cons, hc, hc',
        Bool.false_eq_true, ↓reduceIte, List.map_cons] using congrArg (List.cons s.member) ht
    · have hc' : ¬ (s.exists && s.member.loss != .nan &&
        earlier.all (fun p => !p.exists || !greaterEqual s.member.loss p.member.loss)) = true := by
        simpa only [dominates_all] using hc
      simpa only [frontRaw, frontSpec, withPrefixes, List.filter_cons, hc, hc',
        Bool.false_eq_true, ↓reduceIte] using ht

theorem frontRaw_sublist (earlier slots : List Slot) :
    (frontRaw earlier slots).Sublist ((slots.filter Slot.exists).map Slot.member) := by
  induction slots generalizing earlier with
  | nil => exact .slnil
  | cons s ss ih =>
    have ht := ih (earlier ++ [s])
    by_cases hc : (s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier) = true
    · have he : s.exists = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
      simp only [frontRaw, hc, ↓reduceIte]
      simpa [he] using List.Sublist.cons₂ s.member ht
    · simp only [frontRaw, hc, Bool.false_eq_true, ↓reduceIte]
      cases he : s.exists
      · simpa [he] using ht
      · simpa [he] using List.Sublist.cons s.member ht

theorem frontRaw_prior (earlier slots : List Slot) (p : Slot)
    (hp : p ∈ earlier) (he : p.exists = true) (m : Member)
    (hm : m ∈ frontRaw earlier slots) : greaterEqual m.loss p.member.loss = false := by
  induction slots generalizing earlier with
  | nil => simp [frontRaw] at hm
  | cons s ss ih =>
    have hp' : p ∈ earlier ++ [s] := List.mem_append_left _ hp
    by_cases hc : (s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier) = true
    · simp only [frontRaw, hc, ↓reduceIte, List.mem_cons] at hm
      rcases hm with rfl | hm
      · have hdom : dominatesEarlier s.member earlier = true := (Bool.and_eq_true_iff.mp hc).2
        exact (dominates_iff s.member earlier).mp hdom p hp he
      · exact ih (earlier ++ [s]) hp' hm
    · simp only [frontRaw, hc, Bool.false_eq_true, ↓reduceIte] at hm
      exact ih (earlier ++ [s]) hp' hm

theorem frontRaw_pairwise (earlier slots : List Slot) :
    (frontRaw earlier slots).Pairwise
      (fun a b => greaterEqual b.loss a.loss = false) := by
  induction slots generalizing earlier with
  | nil => simp [frontRaw]
  | cons s ss ih =>
    by_cases hc : (s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier) = true
    · simp only [frontRaw, hc, ↓reduceIte, List.pairwise_cons]
      constructor
      · intro m hm
        exact frontRaw_prior (earlier ++ [s]) ss s (by simp)
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1 m hm
      · exact ih _
    · simp only [frontRaw, hc, Bool.false_eq_true, ↓reduceIte]
      exact ih _

theorem frontRaw_nonnan (earlier slots : List Slot) :
    ∀ m ∈ frontRaw earlier slots, m.loss ≠ .nan := by
  induction slots generalizing earlier with
  | nil => simp [frontRaw]
  | cons s ss ih =>
    intro m hm
    by_cases hc : (s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier) = true
    · simp only [frontRaw, hc, ↓reduceIte, List.mem_cons] at hm
      rcases hm with rfl | hm
      · have hn := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
        simpa using hn
      · exact ih _ m hm
    · simp only [frontRaw, hc, Bool.false_eq_true, ↓reduceIte] at hm
      exact ih _ m hm

theorem nonnan_ge_false_lt (a b : JF) (ha : a ≠ .nan) (hb : b ≠ .nan)
    (hc : greaterEqual a b = false) : less a b = true := by
  cases a <;> cases b <;>
    simp_all [greaterEqual, less, DynExpr.Expressions.Sampling.greater]
  exact Rat.lt_of_le_of_ne (Rat.not_lt.mp hc.1) hc.2

private theorem pairwise_strict (ms : List Member)
    (hw : ms.Pairwise (fun a b => greaterEqual b.loss a.loss = false))
    (hn : ∀ m ∈ ms, m.loss ≠ .nan) :
    ms.Pairwise (fun a b => less b.loss a.loss = true) := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    rw [List.pairwise_cons] at hw ⊢
    constructor
    · intro b hb
      exact nonnan_ge_false_lt b.loss m.loss (hn b (by simp [hb])) (hn m (by simp)) (hw.1 b hb)
    · exact ih hw.2 (fun a ha => hn a (List.mem_cons_of_mem _ ha))

def frontier_exact : Prop := ∀ (h : Hof) (fresh : Nat),
  (calculatePareto h fresh).1.map payload = (frontSpec [] h.slots).map payload ∧
  (calculatePareto h fresh).2 = fresh + 2 * (frontSpec [] h.slots).length

theorem frontier_exact_holds : frontier_exact := by
  intro h fresh
  simp [calculatePareto, copyMembers_payload, copyMembers_supply, frontRaw_spec]

def frontier_increasing : Prop := ∀ (h : Hof),
  ((h.slots.filter Slot.exists).map Slot.member).Pairwise
    (fun a b => a.complexity < b.complexity) →
  (frontRaw [] h.slots).Pairwise (fun a b => a.complexity < b.complexity)

theorem frontier_increasing_holds : frontier_increasing := by
  intro h hi
  exact List.Pairwise.sublist (frontRaw_sublist [] h.slots) hi

example : (([⟨specimen (.fin 1) (.fin 2) 1, true⟩,
    ⟨specimen (.fin 0) (.fin 1) 2, true⟩] : List Slot).filter Slot.exists |>.map Slot.member).Pairwise
    (fun a b => a.complexity < b.complexity) := by decide

def frontier_strict_non_nan : Prop := ∀ (h : Hof),
  (∀ s ∈ h.slots, s.exists = true → s.member.loss ≠ .nan) →
  (frontRaw [] h.slots).Pairwise (fun a b => less b.loss a.loss = true)

theorem frontier_strict_non_nan_holds : frontier_strict_non_nan := by
  intro h hn
  apply pairwise_strict _ (frontRaw_pairwise [] h.slots)
  intro m hm
  have hs := (frontRaw_sublist [] h.slots).subset hm
  obtain ⟨s, hsFiltered, hmEq⟩ := List.mem_map.mp hs
  have hh := List.mem_filter.mp hsFiltered
  simpa [hmEq] using hn s hh.1 hh.2

example : ∀ s ∈ ([⟨specimen (.fin 0) (.fin 1), true⟩] : List Slot),
    s.exists = true → s.member.loss ≠ .nan := by
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst s
  decide

def frontier_strict_all : Prop := ∀ (h : Hof),
  (frontRaw [] h.slots).Pairwise (fun a b => less b.loss a.loss = true)

theorem frontier_strict_all_holds : frontier_strict_all := by
  intro h
  exact pairwise_strict _ (frontRaw_pairwise [] h.slots) (frontRaw_nonnan [] h.slots)

theorem copyMembers_fresh (ms : List Member) (fresh : Nat) :
    ∀ m ∈ (copyMembers ms fresh).1, fresh ≤ m.objectId ∧ fresh < m.treeId := by
  induction ms generalizing fresh with
  | nil => simp [copyMembers]
  | cons x xs ih =>
    intro m hm
    simp only [copyMembers, copyMember, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp
    · have hh := ih (fresh + 2) m hm
      omega

def frontier_copies : Prop := ∀ (h : Hof) (fresh : Nat) (source : Member),
  Below fresh source → ∀ m ∈ (calculatePareto h fresh).1,
    m.objectId ≠ source.objectId ∧ m.treeId ≠ source.treeId

theorem frontier_copies_holds : frontier_copies := by
  intro h fresh source hs m hm
  have hh := copyMembers_fresh (frontRaw [] h.slots) fresh m hm
  unfold Below at hs
  omega

example : Below 2 (specimen (.fin 1) (.fin 1)) := by simp [Below, specimen]

private theorem scan_stock (earlier slots : List Slot) (fresh : Nat) :
    let expected := copyMembers (frontRaw earlier slots) fresh
    let actual := scanFrontier stockFrontierCopy earlier slots fresh ()
    actual.1 = .ok expected.1 ∧ actual.2.1 = expected.2 ∧
      actual.2.2.2.filterMap (fun e => match e with | .copy id => some id | _ => none) =
        (frontRaw earlier slots).map Member.objectId := by
  induction slots generalizing earlier fresh with
  | nil => simp [scanFrontier, frontRaw, copyMembers]
  | cons s ss ih =>
    by_cases hs : (s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier) = true
    · have ht := ih (earlier ++ [s]) (fresh + 2)
      rcases he : scanFrontier stockFrontierCopy (earlier ++ [s]) ss (fresh + 2) ()
        with ⟨result, supply, world, events⟩
      simp only [he] at ht
      simp [scanFrontier, frontRaw, copyMembers, stockFrontierCopy, copyMember, hs, he, ht.1, ht.2.1, ht.2.2,
        Except.map]
    · have ht := ih (earlier ++ [s]) fresh
      rcases he : scanFrontier stockFrontierCopy (earlier ++ [s]) ss fresh ()
        with ⟨result, supply, world, events⟩
      simp only [he] at ht
      simp [scanFrontier, frontRaw, hs, he, ht.1, ht.2.1, ht.2.2]


private theorem scan_append_error {W : Type} (copy : FrontierCopy W)
    (earlier before after : List Slot) (fresh next final : Nat) (world live stopped : W)
    (done : List Member) (calls suffix : List FrontierEvent) (e : JlError)
    (hp : scanFrontier copy earlier before fresh world = (.ok done, next, live, calls))
    (he : scanFrontier copy (earlier ++ before) after next live = (.error e, final, stopped, suffix)) :
    scanFrontier copy earlier (before ++ after) fresh world =
      (.error e, final, stopped, calls ++ suffix) := by
  induction before generalizing earlier fresh world done calls with
  | nil =>
    simp [scanFrontier] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    simpa using he
  | cons slot before ih =>
    have ha : earlier ++ slot :: before = (earlier ++ [slot]) ++ before := by
      simp [List.append_assoc]
    rw [ha] at he
    by_cases hs : (slot.exists && slot.member.loss != .nan && dominatesEarlier slot.member earlier) = true
    · rcases hc : copy slot.member fresh world with ⟨result, supply, state⟩
      cases result with
      | error err => simp [scanFrontier, hs, hc] at hp
      | ok copied =>
        rcases ht : scanFrontier copy (earlier ++ [slot]) before supply state with
          ⟨result, supply', state', events⟩
        cases result with
        | error err => simp [scanFrontier, hs, hc, ht, Except.map] at hp
        | ok rest =>
          simp [scanFrontier, hs, hc, ht, Except.map] at hp
          obtain ⟨_, rfl, rfl, rfl⟩ := hp
          have hp' := ih (earlier ++ [slot]) supply state rest events ht he
          simp [scanFrontier, hs, hc, hp', Except.map]
    · rcases ht : scanFrontier copy (earlier ++ [slot]) before fresh world with
        ⟨result, supply', state', events⟩
      cases result with
      | error err => simp [scanFrontier, hs, ht] at hp
      | ok rest =>
        simp [scanFrontier, hs, ht] at hp
        obtain ⟨_, rfl, rfl, rfl⟩ := hp
        have hp' := ih (earlier ++ [slot]) fresh world rest events ht he
        simp [scanFrontier, hs, hp']

private theorem copyMembers_ids (source : List Member) (fresh : Nat) :
    ((copyMembers source fresh).1.flatMap (fun m => [m.objectId, m.treeId])).Nodup := by
  induction source generalizing fresh with
  | nil => simp [copyMembers]
  | cons m ms ih =>
    change (fresh :: (fresh + 1) ::
      (copyMembers ms (fresh + 2)).1.flatMap (fun m => [m.objectId, m.treeId])).Nodup
    have outside : ∀ n ∈ (copyMembers ms (fresh + 2)).1.flatMap
        (fun m => [m.objectId, m.treeId]), fresh + 2 ≤ n := by
      intro n hn
      obtain ⟨m, hm, h⟩ := List.mem_flatMap.mp hn
      have hf := copyMembers_fresh ms (fresh + 2) m hm
      simp at h
      omega
    simp only [List.nodup_cons, List.mem_cons]
    exact ⟨fun h => h.elim (by omega) (fun hm => by have := outside _ hm; omega),
      fun hm => by have := outside _ hm; omega, ih _⟩

def frontier_trace_exact : Prop :=
  (∀ h fresh, (∀ slot ∈ h.slots, Below fresh slot.member) →
    let actual := runFrontier stockFrontierCopy h fresh ()
    ∃ out, actual.1 = .ok out ∧
      out.map payload = (frontSpec [] h.slots).map payload ∧
      out.map Member.lossNegativeZero = (frontSpec [] h.slots).map Member.lossNegativeZero ∧
      (∀ m ∈ out, ∀ slot ∈ h.slots, m.objectId ≠ slot.member.objectId ∧ m.treeId ≠ slot.member.treeId) ∧
      (out.flatMap (fun m => [m.objectId, m.treeId])).Nodup ∧
      actual.2.2.2.filterMap (fun e => match e with | .copy id => some id | _ => none) =
        (frontSpec [] h.slots).map Member.objectId) ∧
  (∀ (W : Type) (copy : FrontierCopy W) before slot after fresh next final
      (world live stopped : W) done calls e,
    scanFrontier copy [] before fresh world = (.ok done, next, live, calls) →
    slot.exists = true → slot.member.loss ≠ .nan → dominatesEarlier slot.member before = true →
    copy slot.member next live = (.error e, final, stopped) →
    runFrontier copy ⟨before ++ slot :: after⟩ fresh world =
      (.error e, final, stopped, calls ++ [.visit before.length, .copy slot.member.objectId]))

theorem frontier_trace_exact_holds : frontier_trace_exact := by
  constructor
  · intro h fresh hinput
    have ht := scan_stock [] h.slots fresh
    have hzero : ∀ (source : List Member) supply,
        (copyMembers source supply).1.map Member.lossNegativeZero =
          source.map Member.lossNegativeZero := by
      intro source
      induction source with
      | nil => intro supply; rfl
      | cons m ms ih =>
        intro supply
        simp [copyMembers, copyMember, ih]
    refine ⟨_, ht.1, by simp [copyMembers_payload, frontRaw_spec],
      by simp [hzero, frontRaw_spec], ?_, copyMembers_ids _ _,
      by simpa [runFrontier, frontRaw_spec] using ht.2.2⟩
    intro m hm slot hs
    have h1 := copyMembers_fresh (frontRaw [] h.slots) fresh m hm
    have h2 := hinput slot hs
    unfold Below at h2
    omega
  · intro W copy before slot after fresh next final world live stopped done calls e hp he hn hd hc
    exact scan_append_error copy [] before (slot :: after) fresh next final world live stopped
      done calls _ e hp (by simp [scanFrontier, he, hn, hd, hc])

private theorem scan_projection {W A : Type} (copy : FrontierCopy W) (project : Member → A)
    (preserves : ∀ m f w copied next live, copy m f w = (.ok copied, next, live) →
      project copied = project m)
    (earlier slots : List Slot) (fresh : Nat) (world : W) (out : List Member)
    (success : (scanFrontier copy earlier slots fresh world).1 = .ok out) :
    out.map project = (frontRaw earlier slots).map project := by
  induction slots generalizing earlier fresh world out with
  | nil =>
    have h : out = [] := by simpa [scanFrontier] using success.symm
    subst out
    rfl
  | cons slot slots ih =>
    by_cases h : (slot.exists && slot.member.loss != .nan && dominatesEarlier slot.member earlier) = true
    · rcases hc : copy slot.member fresh world with ⟨result, next, live⟩
      cases result with
      | error e => simp [scanFrontier, h, hc] at success
      | ok copied =>
        rcases ht : scanFrontier copy (earlier ++ [slot]) slots next live with
          ⟨result, final, stopped, events⟩
        cases result with
        | error e => simp [scanFrontier, h, hc, ht, Except.map] at success
        | ok tail =>
          have htail := ih (earlier ++ [slot]) next live tail (by simp [ht])
          simp [scanFrontier, h, hc, ht, Except.map] at success
          subst out
          simp [frontRaw, h, preserves _ _ _ _ _ _ hc, htail]
    · have ht : (scanFrontier copy (earlier ++ [slot]) slots fresh world).1 = .ok out := by
        revert success
        simp [scanFrontier, h]
      simp [frontRaw, h, ih _ _ _ _ ht]

def copied_complexities_increase : Prop := ∀ (W : Type) (copy : FrontierCopy W) h fresh world out,
  (∀ m f w copied next live, copy m f w = (.ok copied, next, live) →
    copied.complexity = m.complexity) →
  ((h.slots.filter Slot.exists).map Slot.member).Pairwise (fun a b => a.complexity < b.complexity) →
  (runFrontier copy h fresh world).1 = .ok out →
  out.map Member.complexity = (frontSpec [] h.slots).map Member.complexity ∧
    (out.map Member.complexity).Pairwise (· < ·)

theorem copied_complexities_increase_holds : copied_complexities_increase := by
  intro W copy h fresh world out preserves hi success
  have eq := scan_projection copy Member.complexity preserves [] h.slots fresh world out success
  exact ⟨eq.trans (congrArg (List.map Member.complexity) (frontRaw_spec [] h.slots)),
    by rw [eq]; exact List.pairwise_map.mpr (frontier_increasing_holds h hi)⟩

private theorem frontRaw_first (earlier before : List Slot) (slot : Slot) (after : List Slot)
    (prior : ∀ p ∈ earlier ++ before, p.exists = false ∨ p.member.loss = .nan)
    (present : slot.exists = true) (nonNan : slot.member.loss ≠ .nan) :
    (frontRaw earlier (before ++ slot :: after)).head? = some slot.member := by
  induction before generalizing earlier with
  | nil =>
    have hdom : dominatesEarlier slot.member earlier = true := by
      refine (dominates_iff _ _).mpr ?_
      intro p hp he
      have h := prior p (by simpa using hp)
      rcases h with hf | hn
      · simp [he] at hf
      · cases hm : slot.member.loss <;> simp [greaterEqual, hm, hn]
    simp [frontRaw, present, nonNan, hdom]
  | cons p rest ih =>
    have h := prior p (by simp)
    have ht := ih (earlier ++ [p]) (fun b hb => prior b (by simpa [List.append_assoc] using hb))
    rcases h with hf | hn
    · simpa [frontRaw, hf] using ht
    · simpa [frontRaw, hn] using ht

def copied_losses_decrease : Prop := ∀ (W : Type) (copy : FrontierCopy W) h fresh world out,
  (∀ m f w copied next live, copy m f w = (.ok copied, next, live) → copied.loss = m.loss) →
  (runFrontier copy h fresh world).1 = .ok out →
  out.map Member.loss = (frontSpec [] h.slots).map Member.loss ∧
  (∀ loss ∈ out.map Member.loss, loss ≠ .nan) ∧
  (out.map Member.loss).Pairwise (fun earlier later => less later earlier = true) ∧
  (∀ before first after, h.slots = before ++ first :: after →
    (∀ p ∈ before, p.exists = false ∨ p.member.loss = .nan) →
    first.exists = true → first.member.loss ≠ .nan →
    (out.map Member.loss).head? = some first.member.loss)

theorem copied_losses_decrease_holds : copied_losses_decrease := by
  intro W copy h fresh world out preserves success
  have eq := scan_projection copy Member.loss preserves [] h.slots fresh world out success
  refine ⟨eq.trans (congrArg (List.map Member.loss) (frontRaw_spec [] h.slots)), ?_⟩
  rw [eq]
  refine ⟨?_, List.pairwise_map.mpr (frontier_strict_all_holds h), ?_⟩
  · intro loss hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    exact frontRaw_nonnan [] h.slots m hm
  · intro before first after hs hb he hn
    have hm := frontRaw_first [] before first after (by simpa using hb) he hn
    simpa [hs] using congrArg (Option.map Member.loss) hm

end SymReg.HofMig
