import SymReg.Search.Accounting
import SymReg.ConstraintsProofs

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

 def weighted_dataset_rows : Prop := ∀ (columns targets weights : List (List JF))
    (variables display : Option (List String)) (names : TargetNames)
    (xUnits : Option (List String)) (units : TargetUnits) (extra : Nat)
    (weightFor : Nat → List JF) (nameFor : Nat → String) (unitFor : Nat → Option String),
  (∀ y j, (y, j) ∈ targets.zipIdx →
    SymReg.Loss.at1 weights (j + 1) = .ok (weightFor j) ∧
    targetName names variables targets.length j = .ok (nameFor j) ∧
    targetUnit units j = .ok (unitFor j)) →
  constructDatasets columns targets (some weights) variables display names xUnits units extra =
    .ok (targets.zipIdx.map fun (y, j) =>
      { data := { columns := columns, y := some y, weights := some (weightFor j),
                  xUnits := xUnits.isSome, yUnits := (unitFor j).isSome }
        index := j + 1, variableNames := variables, displayNames := display,
        targetName := nameFor j, xUnits := xUnits, yUnits := unitFor j, extra := extra })
 theorem weighted_dataset_rows_holds : weighted_dataset_rows := by
  intro columns targets weights variables display names xUnits units extra weightFor nameFor unitFor h
  unfold constructDatasets
  apply SymReg.Constraints.mapM_ok
  rintro ⟨y, j⟩ hj
  obtain ⟨hw, hn, hu⟩ := h y j hj
  simp [hw, hn, hu, bind, Except.bind, pure, Except.pure, Except.map]
example : ∀ y j, (y, j) ∈ ([[JF.fin 2]] : List (List JF)).zipIdx →
    SymReg.Loss.at1 [[JF.fin 1]] (j + 1) = .ok [JF.fin 1] ∧
    targetName (.scalar "z") none 1 j = .ok "z" ∧
    targetUnit (.scalar none) j = .ok none := by
  intro y j hj
  simp at hj
  obtain ⟨rfl, rfl⟩ := hj
  decide

def observeHall (hall : Hof) : List Payload × List Bool :=
  (hall.slots.map (payload ∘ Slot.member), hall.slots.map Slot.exists)

theorem copyHalls_observation (halls : List Hof) (fresh : Nat) :
    (copyHalls halls fresh).1.map (observeHall ∘ HallCopy.hall) = halls.map observeHall := by
  induction halls generalizing fresh with
  | nil => rfl
  | cons h hs ih =>
    simp only [copyHalls, List.map_cons, Function.comp_apply]
    rw [ih]
    congr 1
    have he := hall_copy_values_holds h (fresh + 2)
    exact Prod.ext he.2.1 he.1

def freshHall (start : Nat) (copy : HallCopy) : Prop :=
  start ≤ copy.membersId ∧ copy.membersId < copy.occupancyId ∧
    ∀ slot ∈ copy.hall.slots,
      copy.occupancyId < slot.member.objectId ∧ copy.occupancyId < slot.member.treeId

private theorem copyHof_fresh (h : Hof) (fresh : Nat) :
    ∀ slot ∈ (copyHof h (fresh + 2)).1.slots,
      fresh + 1 < slot.member.objectId ∧ fresh + 1 < slot.member.treeId := by
  intro slot hs
  simp only [copyHof, List.mem_map] at hs
  obtain ⟨⟨m, flag⟩, hm, rfl⟩ := hs
  have hf := copyMembers_fresh _ _ m (List.of_mem_zip hm).1
  change fresh + 1 < m.objectId ∧ fresh + 1 < m.treeId
  exact ⟨by omega, by omega⟩

theorem copyHalls_fresh (halls : List Hof) (fresh : Nat) :
    ∀ copy ∈ (copyHalls halls fresh).1, freshHall fresh copy := by
  induction halls generalizing fresh with
  | nil => simp [copyHalls]
  | cons h hs ih =>
    intro copy hm
    simp only [copyHalls, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨Nat.le_refl _, Nat.lt_succ_self _, copyHof_fresh h fresh⟩
    · obtain ⟨h1, h2, h3⟩ := ih _ copy hm
      rw [(hall_copy_values_holds h (fresh + 2)).2.2] at h1
      exact ⟨by omega, h2, h3⟩

def state_hall_roundtrip : Prop := ∀ (pops : PopulationStorage) (halls : HallOutput) (fresh : Nat),
  let expected := halls.asList
  ∃ copies next, loadHalls (some ⟨pops, halls⟩) fresh = some (copies, next) ∧
    copies.map (observeHall ∘ HallCopy.hall) = expected.map observeHall ∧
    ∀ copy ∈ copies, freshHall fresh copy

theorem state_hall_roundtrip_holds : state_hall_roundtrip := by
  intro pops halls fresh
  cases halls with
  | scalar h => exact ⟨_, _, rfl, copyHalls_observation [h] fresh, copyHalls_fresh [h] fresh⟩
  | vector hs => exact ⟨_, _, rfl, copyHalls_observation hs fresh, copyHalls_fresh hs fresh⟩

 def returned_population_sizes : Prop := ∀ (iterations populations size : Nat)
    (initial : Nat → List Member) (work : Nat → Nat → Reply)
    (visits : List (Nat × Bool × Bool)),
  (∀ i g, (work i g).population.length = size) →
  let result := runVisits (startOutput iterations populations initial work) visits work
  result.remaining = 0 → ∀ i, i < populations → (result.cells i).lastPopulation.length = size
 theorem returned_population_sizes_refuted : ¬ returned_population_sizes := by
  intro h
  let m := specimen (.fin 0) (.fin 1)
  let work := fun (_ _ : Nat) => (⟨[m, m, m, m], ⟨[]⟩, 0, .fin 1, 0⟩ : Reply)
  have hh := h 1 2 4 (fun _ => [m]) work [(0, true, false), (0, true, false)]
    (by intros; rfl) (by decide) 1 (by decide)
  change 1 = 4 at hh
  omega

/-- Two identical CSV writes, `src/SearchUtils.jl:945-959`. -/
def saveWrites (outputs j : Nat) (csv : String) : List (String × String) :=
  (saveFileNames outputs j).map (fun name => (name, csv))

 def file_backups : Prop := ∀ (outputs j : Nat) (csv : String),
  (saveWrites outputs j csv).length = 2 ∧
    ∀ write ∈ saveWrites outputs j csv, write.2 = csv
 theorem file_backups_holds : file_backups := by
  intro outputs j csv
  simp [saveWrites, saveFileNames]

/-- `generate_run_id`, `src/SearchUtils.jl:269-273`; date/RNG calls are inputs. -/
def generateRunId (formattedDate : String) (randomCharacters : List Char) : String :=
  formattedDate ++ "_" ++ String.ofList randomCharacters

 def run_id_prefix : Prop := ∀ (date : String) (characters : List Char),
  (generateRunId date characters).startsWith (date ++ "_") = true
 theorem run_id_prefix_holds : run_id_prefix := by
  intro date characters
  simp [generateRunId]

 def frontier_changes : Prop := ∀ (cache : FrontierCache)
    (entries : List (Nat × JF × JF × Int)), cache.entries ≠ entries →
  (saveFrontier cache entries).1 = true
 theorem frontier_changes_holds : frontier_changes := by
  intro cache entries hn
  simp [saveFrontier, hn]
example : (⟨[], true⟩ : FrontierCache).entries ≠ [(0, .fin 0, .fin 0, 1)] := by decide

 def template_guess_guard : Prop := ∀ (detected : List Bool),
  templateGuessAllowed detected = .ok () ↔ ∀ b ∈ detected, b = false
 theorem template_guess_guard_holds : template_guess_guard := by
  intro detected
  simp [templateGuessAllowed, List.any_eq_true]

 theorem batch_count (slots : List Slot) (base : Rat) :
  slots.foldl (fun (n : JF) slot => if slot.exists then n + JF.fin 1 else n) (JF.fin base) =
    JF.fin (base + ((slots.filter Slot.exists).length : Rat)) := by
  induction slots generalizing base with
  | nil => simp <;> grind
  | cons slot slots ih =>
    cases hs : slot.exists <;>
      simp [hs, ih, Rat.natCast_add] <;> grind

 def dispatch_batched : Prop := ∀ (evolution optimize : Rat) (best : Hof) (maxsize : Nat),
  dispatchEvaluations (.fin evolution) (.fin optimize) true best maxsize =
    .fin (evolution + optimize +
      (((best.slots.take maxsize).filter Slot.exists).length : Rat))
 theorem dispatch_batched_holds : dispatch_batched := by
  intro evolution optimize best maxsize
  have hz : (0 : Rat) + evolution + optimize = evolution + optimize := by grind
  simpa [dispatchEvaluations, JF.add, hz] using
    batch_count (best.slots.take maxsize) (evolution + optimize)

inductive RuntimeField where
  | mode (value : Parallelism) | dimension (value : Nat) | flag (value : Bool)
  deriving DecidableEq, Repr

/-- Specialized `getproperty`, `src/SearchUtils.jl:125-140`.
Unprojected fields are read directly from their corresponding runtime fields. -/
def runtimeGetProperty (runtime : Runtime) (name : String) : Option RuntimeField :=
  if name = "parallelism" then some (.mode runtime.mode)
  else if name = "dim_out" then some (.dimension runtime.dimOut)
  else if name = "return_state" then some (.flag runtime.returnState)
  else none

def runtimePropertyNames (_runtime : Runtime) : List String :=
  ["niterations", "numprocs", "init_procs", "addprocs_function", "worker_timeout",
   "exeflags", "worker_imports", "runtests", "verbosity", "progress", "logger",
   "external_stop", "parallelism", "dim_out", "return_state", "run_id",
   "parallelism", "dim_out", "return_state"]

 def runtime_projection : Prop := ∀ (runtime : Runtime),
  runtimeGetProperty runtime "parallelism" = some (.mode runtime.mode) ∧
    runtimeGetProperty runtime "dim_out" = some (.dimension runtime.dimOut) ∧
    runtimeGetProperty runtime "return_state" = some (.flag runtime.returnState)
 theorem runtime_projection_holds : runtime_projection := by intro runtime; exact ⟨rfl, rfl, rfl⟩

 def hall_output_frame : Prop := ∀ (halls : List Hof) (out other : Nat) (merged : Hof),
  out ≠ other → (halls.set out merged)[other]? = halls[other]?
 theorem hall_output_frame_holds : hall_output_frame := by
  intro halls out other merged hn
  exact List.getElem?_set_ne hn
example : (0 : Nat) ≠ 1 := by decide

end SymReg.Search
