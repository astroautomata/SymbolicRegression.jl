import SymReg.Search.StateProofs
import SymReg.Search.Extras
import SymReg.Search.UtilityProofs
import SymReg.Options.Struct
import DynExpr.Registry.Types

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

private theorem step_bind_ok {α β : Type} {x : Jl α} {f : α → Jl β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => cases h

/-- The head checks all stopping conditions after consuming a visit. Even an idle visit
can stop the entire search, with no further observations needed. -/
def stop_at_checkpoint : Prop :=
  ∀ (cfg : SearchConfig) (state : HeadState) (order : List (Nat × Nat))
    (observation : Observation) (rest : List Observation) (step : Nat)
    (work : Nat → Nat → Nat → Reply) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool) (key : Nat × Nat) (next : HeadState),
    state.stopped = false → 0 < (state.outputs.map OutputState.remaining).sum →
    taskAt order step = .ok key → headStep cfg state key observation work compute check = .ok next →
    (observation.userQuit = true ∨ observation.externalStop = true ∨
      (checkTimeout cfg.startTime (fun _ => observation.now) cfg.timeout).1 = true ∨
      checkLoss next.halls cfg.earlyStop (fun m => (resolveComplexity compute m).2) = true ∨
      checkMaxEvals (next.outputs.map fun out =>
        (List.range cfg.populations).map (fun i => (out.cells i).evaluations)) cfg.maxEvals = true) →
    mainSearchLoop cfg order (observation :: rest) step state work compute check = .ok next

theorem stop_at_checkpoint_holds : stop_at_checkpoint := by
  intro cfg state order observation rest step work compute check key next h0 h1 hk hn ht
  have hsum : (state.outputs.map OutputState.remaining).sum ≠ 0 := Nat.ne_of_gt h1
  have hstop : next.stopped = true := by
    simp only [headStep, h0, hsum, decide_false, Bool.false_or] at hn
    obtain ⟨_, _, hn⟩ := step_bind_ok hn
    obtain ⟨_, _, hn⟩ := step_bind_ok hn
    split at hn
    · obtain ⟨⟨h, _, fresh⟩, _, hn⟩ := step_bind_ok hn
      simp only [runStopChecks, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hn
      subst next
      apply (stop_disjunction_holds _ _ _ _ _).mpr
      rcases ht with h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · simp only [runStopChecks, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hn
      subst next
      apply (stop_disjunction_holds _ _ _ _ _).mpr
      rcases ht with h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have hdone := global_stop_persistent_holds cfg next order rest (step + 1) work compute check hstop
  simpa [mainSearchLoop, h0, hsum, hk, hn, bind, Except.bind] using hdone

example : let out := startOutput 1 1 (fun _ => []) unitReply
    (⟨[out], [⟨[]⟩], false, 0⟩ : HeadState).stopped = false ∧ 0 < out.remaining := by decide

/-- A visit for one output cannot change another output's hall, including its saved losses. -/
def visit_preserves_other_halls : Prop :=
  ∀ (cfg : SearchConfig) (state next : HeadState) (key : Nat × Nat)
    (observation : Observation) (work : Nat → Nat → Nat → Reply) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool) (j : Nat),
    j ≠ key.1 → headStep cfg state key observation work compute check = .ok next →
    next.halls[j]? = state.halls[j]?

theorem visit_preserves_other_halls_holds : visit_preserves_other_halls := by
  intro cfg state next key observation work compute check j hj hn
  unfold headStep at hn
  split at hn
  · cases hn
    rfl
  · obtain ⟨_, _, hn⟩ := step_bind_ok hn
    obtain ⟨_, _, hn⟩ := step_bind_ok hn
    dsimp only at hn
    split at hn
    · obtain ⟨⟨h, _, fresh⟩, _, hn⟩ := step_bind_ok hn
      simp only [runStopChecks, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hn
      subst next
      exact List.getElem?_set_ne (Ne.symm hj)
    · simp only [runStopChecks, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hn
      subst next
      rfl

example : (1 : Nat) ≠ (0, 0).1 := by decide

/-- The saved-state loader can retrieve every population and hall emitted by a
compatible output bank; the retrieved members keep the equation payloads. -/
def returned_state_reloadable : Prop :=
  ∀ (pops : List (List (List Member))) (halls : List Hof) (dimOut out pop fresh : Nat)
    (saved : SavedState) (row : List (List Member)) (members : List Member),
    formatOutput pops halls dimOut true = .ok (.state saved) →
    pops[out]? = some row → row[pop]? = some members →
    ∃ copies supply loaded,
      loadHalls (some saved) fresh = some (copies, supply) ∧
      copies.map (observeHall ∘ HallCopy.hall) = halls.map observeHall ∧
      (∀ copy ∈ copies, freshHall fresh copy) ∧
      loadPopulation (some saved) out pop supply = .ok (some loaded) ∧
      copiedPopulation members supply loaded

theorem returned_state_reloadable_holds : returned_state_reloadable := by
  intro pops halls dimOut out pop fresh saved row members hs hout hpop
  have reload (output : HallOutput)
      (he : output.asList = halls) :
      ∃ copies supply loaded,
        loadHalls (some ⟨.vectors pops, output⟩) fresh = some (copies, supply) ∧
        copies.map (observeHall ∘ HallCopy.hall) = halls.map observeHall ∧
        (∀ copy ∈ copies, freshHall fresh copy) ∧
        loadPopulation (some ⟨.vectors pops, output⟩) out pop supply = .ok (some loaded) ∧
        copiedPopulation members supply loaded := by
    obtain ⟨copies, supply, hload, hpayload, hfresh⟩ :=
      state_hall_roundtrip_holds (.vectors pops) output fresh
    rw [he] at hpayload
    obtain ⟨loaded, hpopload, hcopy⟩ :=
      state_population_roundtrip_holds pops output out pop supply row members hout hpop
    exact ⟨copies, supply, loaded, hload, hpayload, hfresh, hpopload, hcopy⟩
  by_cases hd : dimOut = 1
  · cases halls with
    | nil => simp [formatOutput, hd, bind, Except.bind] at hs
    | cons h rest =>
      cases rest with
      | nil =>
        have he := (state_format_holds pops h).1
        rw [hd, he] at hs
        cases hs
        exact reload (.scalar h) rfl
      | cons h' rest => simp [formatOutput, hd, bind, Except.bind] at hs
  · have he : formatOutput pops halls dimOut true =
        .ok (.state ⟨.vectors pops, .vector halls⟩) := by
      simp [formatOutput, hd, bind, Except.bind, pure, Except.pure]
    rw [he] at hs
    cases hs
    exact reload (.vector halls) rfl

example : let m := specimen (.fin 0) (.fin 0)
    formatOutput [[[m]]] [⟨[]⟩] 1 true = .ok (.state ⟨.vectors [[[m]]], .scalar ⟨[]⟩⟩) ∧
      ([[[m]]] : List (List (List Member)))[0]? = some [[m]] ∧
      ([[m]] : List (List Member))[0]? = some [m] := by decide

private theorem mapM_payload {α β γ : Type} (xs : List α) (f : α → Jl β)
    (g : β → γ) (project : α → γ)
    (h : ∀ x y, f x = .ok y → g y = project x) (ys : List β)
    (hy : xs.mapM f = .ok ys) : ys.map g = xs.map project := by
  induction xs generalizing ys with
  | nil => cases hy; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons] at hy
    obtain ⟨y, hx, ht⟩ := step_bind_ok hy
    obtain ⟨tail, hs, ht⟩ := step_bind_ok ht
    simp only [pure, Except.pure, Except.ok.injEq] at ht
    subst ys
    simp only [List.map_cons, h x y hx, ih tail hs]

/-- Successful construction keeps exactly one data object per target row, in
matrix row order, regardless of optional weight, name or unit configuration. -/
def output_target_rows : Prop :=
  ∀ (x y : List (List JF)) (w : Option (List (List JF))) (names display : Option (List String))
    (yn : TargetNames) (xu : Option (List String)) (yu : TargetUnits) (extra : Nat)
    (datasets : List SearchDataset),
    constructDatasets x y w names display yn xu yu extra = .ok datasets →
    datasets.map (fun d => (d.data.columns, d.data.y)) = y.map (fun row => (x, some row))

theorem output_target_rows_holds : output_target_rows := by
  intro x y w names display yn xu yu extra datasets hs
  unfold constructDatasets at hs
  have h := mapM_payload _ _ (fun d : SearchDataset => (d.data.columns, d.data.y))
    (fun (p : List JF × Nat) => (x, some p.1)) (by
      rintro ⟨row, j⟩ d h
      cases w <;> dsimp only at h <;>
        obtain ⟨_, _, h⟩ := step_bind_ok h <;>
        obtain ⟨_, _, h⟩ := step_bind_ok h <;>
        obtain ⟨_, _, h⟩ := step_bind_ok h <;>
        cases h <;> rfl) datasets hs
  have hzip (rows : List (List JF)) (start : Nat) :
      (rows.zipIdx start).map (fun p => (x, some p.1)) = rows.map (fun row => (x, some row)) := by
    induction rows generalizing start with
    | nil => rfl
    | cons r rows ih => simp [List.zipIdx_cons, ih]
  exact h.trans (hzip y 0)

/-- A restored member is rescored against the target row at its own output index.
The loss implementation is supplied by `eval_cost` and may differ across datasets. -/
def restored_output_loss : Prop :=
  ∀ (datasets : List SearchDataset) (saved : List Hof) (j k : Nat)
    (dataset : SearchDataset) (old : Hof) (slot : Slot) (options : Nat)
    (strip : Hof → Nat → SearchDataset → Hof)
    (score : SearchDataset → Member → Nat → JF × JF),
    saved.length = datasets.length → datasets[j]? = some dataset → saved[j]? = some old →
    (strip old options dataset).slots[k]? = some slot → slot.exists = true →
    (initializeHalls (m := Jl) (some saved) datasets options (fun _ _ => .ok ⟨[]⟩)
      (fun h o d => .ok (strip h o d)) (fun d m o => .ok (score d m o))).map
      (fun halls => halls[j]?.bind fun hall => hall.slots[k]?.map fun s => s.member.loss) =
      .ok (some (score dataset slot.member options).2)

theorem restored_output_loss_holds : restored_output_loss := by
  intro datasets saved j k dataset old slot options strip score hl hd hh hk he
  let scoreSlot := fun (d : SearchDataset) (s : Slot) =>
    let v := score d s.member options
    if s.exists then
      let member := { s.member with cost := v.1, loss := v.2 }
      { s with member }
    else s
  have hslots (d : SearchDataset) (slots : List Slot) :
      (slots.mapM (m := Jl) fun s => do
        if s.exists then
          let (cost, loss) ← .ok (score d s.member options)
          pure { s with member := { s.member with cost := cost, loss := loss } }
        else pure s) = .ok (slots.map (scoreSlot d)) := by
    apply SymReg.Constraints.mapM_ok
    intro s _
    cases hx : s.exists <;> cases hy : score d s.member options <;>
      simp [hx, hy, scoreSlot, Pure.pure, Except.pure, Bind.bind, Except.bind]
  have hhalls :
      initializeHalls (m := Jl) (some saved) datasets options (fun _ _ => .ok ⟨[]⟩)
        (fun h o d => .ok (strip h o d)) (fun d m o => .ok (score d m o)) =
      .ok ((saved.zip datasets).map fun (h, d) =>
        { strip h options d with slots := (strip h options d).slots.map (scoreSlot d) }) := by
    have hz : ¬ saved.length ≠ datasets.length := fun hn => hn hl
    simp only [initializeHalls, ite_eq_right hz]
    apply SymReg.Constraints.mapM_ok
    rintro ⟨h, d⟩ _
    specialize hslots d (strip h options d).slots
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hslots ⊢
    rw [hslots]
  rw [hhalls]
  have hzip : (saved.zip datasets)[j]? = some (old, dataset) :=
    List.getElem?_zip_eq_some.mpr ⟨hh, hd⟩
  simp [List.getElem?_map, hzip, hk, he, Except.map, scoreSlot]

/-- A warm start should not return an equation above the new `maxsize` after a
change that `check_warm_start_compatibility` identifies as incompatible. The shape of
saved halls still matches the data. The initialization and finalization projections
omit payload-preserving expression metadata operations. -/
def warm_start_incompatible : Prop :=
  ∀ (cfg : SearchConfig) (saved : SavedState) (score : Nat → Member → JF × JF)
    (fresh : Nat) (comps : List Hof) (result : Hof) (equal : String → Bool),
    cfg.dimOut = 1 → cfg.returnState = false → cfg.iterations = 0 → cfg.populations = 1 →
    SymReg.Options.checkWarmStart true equal = .error ⟨["maxsize"]⟩ →
    initializeHalls (m := Jl) ((loadHalls (some saved) fresh).map (List.map HallCopy.hall ∘ Prod.fst)) [0] ()
      (fun _ _ => .ok ⟨[]⟩) (fun h _ _ => .ok h) (fun i m _ => .ok (score i m)) = .ok comps →
    equationSearch cfg [fun _ => []] comps [(0, 0)] [] (fun _ => unitReply)
      (fun _ => 0) (fun _ _ _ => .ok true) = .ok (.halls (.scalar result)) →
    ∀ k, cfg.maxsize ≤ k → slotPayload result k = none

private def warmCfg : SearchConfig :=
  { populations := 1, iterations := 0, dimOut := 1, returnState := false,
    maxsize := 4, startTime := .fin 0 }

private def warmHall : Hof :=
  let m := specimen (.fin 0) (.fin 0)
  ⟨List.replicate 4 ⟨m, false⟩ ++ [⟨m, true⟩]⟩

private def warmSaved : SavedState := ⟨.vectors [[[]]], .scalar warmHall⟩

private def warmScored : Hof := ⟨(copyHof warmHall 12).1.slots.map fun s =>
  if s.exists then ⟨{ s.member with cost := .fin 0, loss := .fin 0 }, true⟩ else s⟩

theorem warm_start_incompatible_refuted : ¬ warm_start_incompatible := by
  intro h
  have hc := h warmCfg warmSaved (fun _ _ => (.fin 0, .fin 0)) 10 [warmScored]
    warmScored (· != "maxsize") rfl rfl rfl rfl (by decide +kernel) rfl rfl 4 (by decide)
  have hn : slotPayload warmScored 4 ≠ none := by decide +kernel
  exact hn hc

open DynExpr.Registry in
def driverEntries : List Entry := [
  { id := "search-stop-checkpoint", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"],
    statement := "At a successful head checkpoint any triggered stopping condition returns the current result without consuming another visit.",
    preconditions := "Active search and a successfully processed visit.", status := .todo,
    prop := ``stop_at_checkpoint
    notes := "Needs the ordered effectful checks after migration, hooks, relaunch and logging." },
  { id := "search-output-hall-isolation", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_main_search_loop!"],
    statement := "Processing one output's search visit leaves all other output halls and saved losses untouched.",
    preconditions := "Successful visit.", status := .todo,
    prop := ``visit_preserves_other_halls
    notes := "Needs separate direct merge writes, hook effects and cross-output complexity cache writes." },
  { id := "search-state-reload", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["equation_search", "_format_output"],
    statement := "The saved-state loader retrieves each returned population with its equation payloads and all returned output halls.",
    preconditions := "Successful return_state formatting and valid output and population indexes.", status := .todo,
    prop := ``returned_state_reloadable
    notes := "Reload now checks ordered payloads, occupancy and fresh allocation ranges for scalar and vector halls. Bind fallible member copies and prove disjointness of the mutable backing vectors." },
  { id := "search-output-target-rows", juliaFile := "src/SearchUtils.jl", juliaFns := ["construct_datasets"],
    statement := "Successful dataset construction yields one data object per target row in input order, with the shared input matrix and its own target row.",
    preconditions := "Successful dataset construction.", status := .todo,
    prop := ``output_target_rows
    notes := "Needs original matrix identity and independent target slice identities." },
  { id := "search-restored-output-loss", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["_initialize_search!"],
    statement := "An occupied slot of a restored output hall has the loss computed on that output's own target row.",
    preconditions := "Matching target and saved hall counts; an occupied saved slot.", status := .todo,
    prop := ``restored_output_loss
    notes := "The scorer now receives the full SearchDataset, member and options. Prove earlier hall and slot effects persist and later scores are skipped when the first evaluation throws." },
  { id := "search-warm-start-incompatible", juliaFile := "src/SymbolicRegression.jl", juliaFns := ["equation_search", "_initialize_search!"],
    statement := "A warm start after an incompatible maxsize change cannot return an equation beyond the new limit.",
    preconditions := "Matching output and population shape, zero-iteration inspection.", status := .refuted,
    prop := ``warm_start_incompatible, thm := some ``warm_start_incompatible_refuted }
]

end SymReg.Search
