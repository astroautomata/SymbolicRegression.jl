import SymReg.HofMig.Migration

namespace SymReg.HofMig
open DynExpr
open DynExpr.Expressions.Sampling (RNG)

def migration_clamps : Prop := ∀ (sampled : Int) (candidates population : Nat),
  0 ≤ sampled → 0 ≤ clampCount sampled candidates population ∧
  clampCount sampled candidates population ≤ sampled ∧
  clampCount sampled candidates population ≤ (candidates : Int) ∧
  clampCount sampled candidates population ≤ (population : Int)

theorem migration_clamps_holds : migration_clamps := by
  intro sampled candidates population hs
  unfold clampCount
  omega

example : 0 ≤ (3 : Int) := by decide

def migration_zero_fraction : Prop := ∀ (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (fuel fresh birthCursor : Nat) (rng : RNG),
  migrate rt candidates population (.fin 0) fuel fresh birthCursor rng =
    .ok (population, fresh, birthCursor, rng)

theorem migration_zero_fraction_holds : migration_zero_fraction := by
  intro rt candidates population fuel fresh birthCursor rng
  simp [migrate, poissonSample, migrateSampled, migrateSampledState, Except.map, pure, Except.pure, bind, Except.bind]

def migration_empty_candidates : Prop := ∀ (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (sampled : Int) (fresh birthCursor : Nat) (rng : RNG),
  population ≠ [] → gatherCandidates candidates = [] → 0 ≤ sampled →
  (sampled = 0 → migrateSampledState rt candidates population sampled fresh birthCursor rng =
    (.ok (), population, fresh, birthCursor, rng)) ∧
  (0 < sampled → migrateSampledState rt candidates population sampled fresh birthCursor rng =
    (.error (.argumentError "collection must be non-empty"), population, fresh, birthCursor, rng))

theorem migration_empty_candidates_holds : migration_empty_candidates := by
  intro rt candidates population sampled fresh birthCursor rng _ hc hs
  have hzero : clampCount sampled 0 population.length = 0 := by unfold clampCount; omega
  constructor
  · intro hz
    simp [migrateSampledState, hz]
  · intro hp
    have hn : sampled ≠ 0 := by omega
    simp [migrateSampledState, hn, hc, hzero, drawLocations, drawMigrants,
      pure, Except.pure, throw, MonadExcept.throw]
    rfl

example (m : Member) : [m] ≠ [] ∧ gatherCandidates (.populations [[], []]) = [] := by simp [gatherCandidates]

-- Source: src/Options.jl:1317,1366; src/Population.jl:253-258;
-- src/SymbolicRegression.jl:1153,1191-1205. The current subpopulation is
-- written before inter-population migration; the other two sources are guarded.
theorem defaultBestPool_nonempty (before ranked after : List (List Member)) (current : List Member)
    (hcurrent : current ≠ []) (hcount : ranked.flatten.length = current.length) :
    gatherCandidates (.populations (before ++ ranked.flatten.take 12 :: after)) ≠ [] := by
  cases hr : ranked.flatten with
  | nil =>
    cases current with
    | nil => contradiction
    | cons m ms => simp [hr] at hcount
  | cons m ms =>
    simp [gatherCandidates, hr]

def migration_empty_destination : Prop := ∀ (rt : MigrationRuntime) (candidates : Candidates)
    (frac : Rat) (fuel fresh birthCursor : Nat) (rng : RNG),
  migrate rt candidates [] (.fin frac) fuel fresh birthCursor rng =
    .ok ([], fresh, birthCursor, rng)

theorem migration_empty_destination_holds : migration_empty_destination := by
  intro rt candidates frac fuel fresh birthCursor rng
  simp [migrate, poissonSample, migrateSampled, migrateSampledState, Except.map, pure, Except.pure, bind, Except.bind]

def migration_gather_order : Prop := ∀ (populations : List (List Member)),
  gatherCandidates (.populations populations) = populations.flatten

theorem migration_gather_order_holds : migration_gather_order := by intro populations; rfl

def location_draws : Prop := ∀ (population count : Nat) (rng : RNG),
  0 < population → ∃ locations rng', drawLocations population count rng = .ok (locations, rng') ∧
    locations.length = count ∧ rng'.cursor = rng.cursor + count ∧
    (∀ j, j < count → locations[j]? =
      some (rng.indexDraws (population - 1) (rng.cursor + j)).val) ∧
    ∀ i ∈ locations, i < population

theorem location_draws_holds : location_draws := by
  intro population count rng hp
  by_cases hc : count = 0
  · subst count
    refine ⟨[], rng, rfl, rfl, by omega, ?_⟩
    simp
  · have hn : population ≠ 0 := by omega
    refine ⟨(List.range count).map (fun i =>
      (rng.indexDraws (population - 1) (rng.cursor + i)).val),
      { rng with cursor := rng.cursor + count }, ?_, ?_, rfl, ?_⟩
    · simp [drawLocations, hc, hn]
      rfl
    · simp
    · constructor
      · intro j hj
        simp [List.getElem?_range hj]
      · intro i hi
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
        have hb := (rng.indexDraws (population - 1) (rng.cursor + j)).isLt
        omega

example : 0 < (2 : Nat) := by decide

def migrant_draws : Prop := ∀ (m : Member) (ms : List Member) (count : Nat) (rng : RNG),
  ∃ selected rng', drawMigrants (m :: ms) count rng = .ok (selected, rng') ∧
    selected.length = count ∧ rng'.cursor = rng.cursor + count ∧
    (∀ j, j < count → selected[j]? = (m :: ms)[(rng.indexDraws ms.length (rng.cursor + j)).val]?) ∧
    ∀ x ∈ selected, x ∈ m :: ms

theorem migrant_draws_holds : migrant_draws := by
  intro m ms count rng
  by_cases hc : count = 0
  · subst count
    refine ⟨[], rng, rfl, rfl, by omega, ?_⟩
    simp
  · refine ⟨(List.range count).map (fun i =>
      ((m :: ms)[(rng.indexDraws ms.length (rng.cursor + i)).val]?).getD m),
      { rng with cursor := rng.cursor + count }, ?_, ?_, rfl, ?_⟩
    · simp [drawMigrants, hc]
      rfl
    · simp
    · constructor
      · intro j hj
        have hb := (rng.indexDraws ms.length (rng.cursor + j)).isLt
        have hi : (rng.indexDraws ms.length (rng.cursor + j)).val < (m :: ms).length := by
          simpa using hb
        simp [List.getElem?_range hj, List.getElem?_eq_getElem hi]
      · intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        cases hg : (m :: ms)[(rng.indexDraws ms.length (rng.cursor + i)).val]? with
        | none => simp
        | some v => simpa [hg] using List.mem_of_getElem? hg

def migration_frame : Prop := ∀ (rt : MigrationRuntime) (locations : List Nat) (migrants population : List Member)
    (fresh birthCursor i : Nat), i ∉ locations →
  (applyMigration rt locations migrants population fresh birthCursor).1[i]? = population[i]?

theorem migration_frame_holds : migration_frame := by
  intro rt locations
  induction locations with
  | nil => intro migrants population fresh birthCursor i hi; rfl
  | cons j js ih =>
    intro migrants population fresh birthCursor i hi
    cases migrants with
    | nil => rfl
    | cons m ms =>
      have hne : j ≠ i := by intro he; subst j; exact hi (by simp)
      have htail : i ∉ js := fun hm => hi (List.mem_cons_of_mem _ hm)
      simp only [applyMigration, copyMember]
      rw [ih ms _ _ _ i htail, List.getElem?_set_ne hne]

example : 1 ∉ ([0] : List Nat) := by decide

def migration_length : Prop := ∀ (rt : MigrationRuntime) (locations : List Nat) (migrants population : List Member)
    (fresh birthCursor : Nat),
  (applyMigration rt locations migrants population fresh birthCursor).1.length = population.length

theorem migration_length_holds : migration_length := by
  intro rt locations
  induction locations with
  | nil => intro migrants population fresh birthCursor; rfl
  | cons j js ih =>
    intro migrants population fresh birthCursor
    cases migrants with
    | nil => rfl
    | cons m ms =>
      simpa [applyMigration, copyMember] using
        (ih ms (population.set j { (copyMember m fresh).1 with birth := rt.births birthCursor })
          (fresh + 2) (birthCursor + 1))

theorem migration_identity_origin (rt : MigrationRuntime) (locations : List Nat) :
    ∀ (migrants population : List Member) (fresh birthCursor i : Nat) (m : Member),
    (applyMigration rt locations migrants population fresh birthCursor).1[i]? = some m →
    population[i]? = some m ∨ (fresh ≤ m.objectId ∧ fresh < m.treeId) := by
  induction locations with
  | nil => intro migrants population fresh birthCursor i m hh; exact Or.inl hh
  | cons j js ih =>
    intro migrants population fresh birthCursor i m hh
    cases migrants with
    | nil => exact Or.inl hh
    | cons candidate candidates =>
      simp only [applyMigration, copyMember] at hh
      obtain hp | hf := ih candidates _ (fresh + 2) (birthCursor + 1) i m hh
      · rw [List.getElem?_set] at hp
        by_cases he : j = i
        · subst j
          by_cases hb : i < population.length
          · simp [hb] at hp
            subst m
            exact Or.inr (by simp)
          · simp [hb] at hp
        · exact Or.inl (by simpa [he] using hp)
      · exact Or.inr (by omega)

def migration_no_new_alias : Prop := ∀ (rt : MigrationRuntime) (locations : List Nat)
    (migrants population : List Member) (fresh birthCursor i : Nat) (out source : Member),
  Below fresh source →
  (applyMigration rt locations migrants population fresh birthCursor).1[i]? = some out →
  population[i]? = some out ∨ (out.objectId ≠ source.objectId ∧ out.treeId ≠ source.treeId)

theorem migration_no_new_alias_holds : migration_no_new_alias := by
  intro rt locations migrants population fresh birthCursor i out source hs hh
  obtain hp | hf := migration_identity_origin rt locations migrants population fresh birthCursor i out hh
  · exact Or.inl hp
  · right
    unfold Below at hs
    omega

example : Below 2 (specimen (.fin 0) (.fin 1)) := by simp [Below, specimen]

def migration_duplicate_migrant_copies : Prop := ∀ (rt : MigrationRuntime) (population : List Member)
    (migrant : Member) (fresh birthCursor : Nat), 2 ≤ population.length →
  ((applyMigration rt [0, 1] [migrant, migrant] population fresh birthCursor).1[0]?).map Member.objectId = some fresh ∧
  ((applyMigration rt [0, 1] [migrant, migrant] population fresh birthCursor).1[1]?).map Member.objectId = some (fresh + 2) ∧
  (applyMigration rt [0, 1] [migrant, migrant] population fresh birthCursor).2.1 = fresh + 4

theorem migration_duplicate_migrant_copies_holds : migration_duplicate_migrant_copies := by
  intro rt population migrant fresh birthCursor hp
  have h0 : 0 < population.length := by omega
  have h1 : 1 < population.length := by omega
  simp [applyMigration, copyMember, h0, h1]

example : 2 ≤ ([specimen (.fin 0) (.fin 1), specimen (.fin 0) (.fin 1)] : List Member).length := by decide

def migration_last_write : Prop := ∀ (rt : MigrationRuntime) (population : List Member)
    (first last : Member) (fresh birthCursor i : Nat), i < population.length →
  (applyMigration rt [i, i] [first, last] population fresh birthCursor).1[i]? =
    some { (copyMember last (fresh + 2)).1 with birth := rt.births (birthCursor + 1) }

theorem migration_last_write_holds : migration_last_write := by
  intro rt population first last fresh birthCursor i hi
  simp [applyMigration, copyMember, hi]

example : 0 < ([specimen (.fin 0) (.fin 1)] : List Member).length := by decide

def migration_poisson_dispatch : Prop := ∀ (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (frac : JF) (fuel fresh birthCursor : Nat) (rng rng' : RNG) (sampled : Int),
  poissonSample rt (.fin (population.length : Rat) * frac) fuel rng = .ok (sampled, rng') →
  migrate rt candidates population frac fuel fresh birthCursor rng =
    migrateSampled rt candidates population sampled fresh birthCursor rng'

theorem migration_poisson_dispatch_holds : migration_poisson_dispatch := by
  intro rt candidates population frac fuel fresh birthCursor rng rng' sampled hh
  simp [migrate, hh, bind, Except.bind]

example : let rt : MigrationRuntime := ⟨fun _ => .ok (.fin 1), fun _ => 0⟩
    let rng : RNG := ⟨fun _ => 0, 0, fun n _ => ⟨0, Nat.zero_lt_succ n⟩⟩
    poissonSample rt (.fin 0) 0 rng = .ok (0, rng) := rfl

private theorem applyMigration_births (rt : MigrationRuntime) (locations : List Nat) :
    ∀ migrants population fresh birthCursor,
      (applyMigration rt locations migrants population fresh birthCursor).2.2 =
        birthCursor + min locations.length migrants.length := by
  induction locations with
  | nil => intro migrants population fresh birthCursor; simp [applyMigration]
  | cons i rest ih =>
    intro migrants population fresh birthCursor
    cases migrants with
    | nil => simp [applyMigration]
    | cons m ms =>
      simp only [applyMigration, List.length_cons]
      rw [ih]
      omega

def migration_candidate_cap : Prop := ∀ (rt : MigrationRuntime) (candidates : Candidates)
    (population : List Member) (sampled : Int) (fresh birthCursor : Nat) (rng : RNG),
  0 ≤ sampled → (sampled = 0 ∨ gatherCandidates candidates ≠ []) →
  ∃ out f b rng', migrateSampled rt candidates population sampled fresh birthCursor rng =
    .ok (out, f, b, rng') ∧ out.length = population.length ∧
    b = birthCursor + min (min sampled.toNat (gatherCandidates candidates).length) population.length

theorem migration_candidate_cap_holds : migration_candidate_cap := by
  intro rt candidates population sampled fresh birthCursor rng hs hnempty
  by_cases hz : sampled = 0
  · subst sampled; exact ⟨_, _, _, _, rfl, rfl, by simp⟩
  let migrants := gatherCandidates candidates
  let count := clampCount sampled migrants.length population.length
  obtain ⟨h0, _, hm, hp⟩ := migration_clamps_holds sampled migrants.length population.length hs
  have hcount : count.toNat = min (min sampled.toNat migrants.length) population.length := by
    change (min (min sampled (migrants.length : Int)) (population.length : Int)).toNat = _
    omega
  have hloc : ∃ locations rng', drawLocations population.length count.toNat rng = .ok (locations, rng') ∧
      locations.length = count.toNat := by
    by_cases hp0 : population.length = 0
    · have hc : count.toNat = 0 := by simp [hcount, hp0]
      exact ⟨[], rng, by simp [drawLocations, hc, pure, Except.pure], by simp [hc]⟩
    · obtain ⟨xs, r, hr, hlen, _, _⟩ := location_draws_holds population.length count.toNat rng (by omega)
      exact ⟨xs, r, hr, hlen⟩
  obtain ⟨locations, rng', hl, hll⟩ := hloc
  have hdraw : ∃ selected rng'', drawMigrants migrants count.toNat rng' = .ok (selected, rng'') ∧
      selected.length = count.toNat := by
    cases hms : migrants with
    | nil => exact False.elim ((hnempty.resolve_left hz) hms)
    | cons m ms =>
      obtain ⟨selected, r, he, hn, _, _⟩ := migrant_draws_holds m ms count.toNat rng'
      exact ⟨selected, r, he, hn⟩
  obtain ⟨selected, rng'', hd, hdl⟩ := hdraw
  let result := applyMigration rt locations selected population fresh birthCursor
  refine ⟨result.1, result.2.1, result.2.2, rng'', ?_,
    migration_length_holds rt locations selected population fresh birthCursor, ?_⟩
  · change (migrateSampled rt candidates population sampled fresh birthCursor rng) = _
    have hn : ¬ count < 0 := Int.not_lt.mpr h0
    simp only [migrateSampled, migrateSampledState, hz, ↓reduceIte,
      show ¬ clampCount sampled (gatherCandidates candidates).length population.length < 0 from hn]
    rw [show drawLocations population.length count.toNat rng = .ok (locations, rng') from hl]
    simp only
    rw [show drawMigrants (gatherCandidates candidates) count.toNat rng' = .ok (selected, rng'') from hd]
    simp only
    change _ = Except.ok ((applyMigration rt locations selected population fresh birthCursor).1,
      (applyMigration rt locations selected population fresh birthCursor).2.1,
      (applyMigration rt locations selected population fresh birthCursor).2.2, rng'')
    cases applyMigration rt locations selected population fresh birthCursor with
    | mk p fb => cases fb; rfl
  · change (applyMigration rt locations selected population fresh birthCursor).2.2 =
      birthCursor + min (min sampled.toNat migrants.length) population.length
    rw [applyMigration_births, hll, hdl]
    simp [hcount]

example : (0 : Int) ≤ 2 := by decide

end SymReg.HofMig
