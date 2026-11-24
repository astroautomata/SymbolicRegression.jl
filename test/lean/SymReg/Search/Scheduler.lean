import SymReg.HofMig.Optimality
import SymReg.Loss.Core

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

/-- `src/SearchUtils.jl:165-185,364-382`. Thread and process latency is an input. -/
inductive Parallelism where
  | serial | multithreading | multiprocessing
  deriving DecidableEq, Repr

/-- `src/SearchUtils.jl:304,905-912`; population evolution is supplied by the caller. -/
structure Reply where
  population : List Member
  bestSeen : Hof
  trace : Nat
  evaluations : JF
  pluginState : Nat
  deriving DecidableEq, Repr

/-- `src/SearchUtils.jl:364-382`. -/
def workerOutputType (mode : Parallelism) : Type :=
  if mode = .serial then Reply else Nat × Reply

def extractWorker (mode : Parallelism) : workerOutputType mode → Reply :=
  if h : mode = .serial then by subst mode; exact id
  else by simp only [workerOutputType, h, if_false]; exact Prod.snd

/-- One population's channel, generation number, returned population and evaluation counter;
`src/SymbolicRegression.jl:800,833-839,1033-1060,1135-1155,1229-1260`. -/
structure Cell where
  running : Bool
  collected : Nat
  launched : Nat
  pending : Reply
  pendingId : Nat
  lastPopulation : List Member
  evaluations : JF

/-- Scheduler projection of `SearchState`, `src/SearchUtils.jl:873-903`.
Indices are zero based; `receipts` stores (population, generation) in reverse order. -/
structure OutputState where
  remaining : Nat
  cells : Nat → Cell
  receipts : List (Nat × Nat)
  launches : Nat

/-- `_create_workers`, `_warmup_search!`, `src/SymbolicRegression.jl:843-844,1016-1060`.
The initialization tasks precede these evolution jobs and their evaluation reports are discarded. -/
def startOutput (iterations populations : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) : OutputState :=
  let active := iterations * populations > 0
  { remaining := iterations * populations
    cells := fun i =>
      { running := decide (i < populations) && decide active
        collected := 0
        launched := if i < populations ∧ active then 1 else 0
        pending := work i 0
        pendingId := 0
        lastPopulation := initial i
        evaluations := .fin 0 }
    receipts := []
    launches := if active then populations else 0 }

/-- One ready-result branch, `src/SymbolicRegression.jl:1133-1155,1210-1260`.
Stopping is checked after this branch, so a final extra job can already have been launched. -/
def collect (s : OutputState) (population : Nat) (ready externalStop : Bool)
    (work : Nat → Nat → Reply) : OutputState :=
  let c := s.cells population
  if ready && c.running && decide (s.remaining > 0) then
    let relaunch := decide (s.remaining > 1) && !externalStop
    let c' : Cell :=
      { running := relaunch
        collected := c.collected + 1
        launched := c.launched + if relaunch then 1 else 0
        pending := if relaunch then work population (c.collected + 1) else c.pending
        pendingId := if relaunch then c.launched else c.pendingId
        lastPopulation := c.pending.population
        evaluations := c.evaluations + c.pending.evaluations }
    { remaining := s.remaining - 1
      cells := fun i => if i = population then c' else s.cells i
      receipts := (population, c.pendingId) :: s.receipts
      launches := s.launches + if relaunch then 1 else 0 }
  else s

/-- Arbitrary task-order visits and arbitrary channel readiness, including idle spins;
`src/SymbolicRegression.jl:1107-1134`. -/
def runVisits (s : OutputState) (visits : List (Nat × Bool × Bool))
    (work : Nat → Nat → Reply) : OutputState :=
  visits.foldl (fun st (i, ready, external) => collect st i ready external work) s

/-- `src/SymbolicRegression.jl:1356-1378`: waiting never ingests a result. -/
def tearDown (s : OutputState) : OutputState := s

/-- Counter conservation independent of worker reports and timing. -/
def Budget (total : Nat) (s : OutputState) : Prop :=
  s.remaining + s.receipts.length = total

/-- Each launch has either one receipt or one pending channel result. -/
def CellBalance (c : Cell) : Prop :=
  c.launched = c.collected + if c.running then 1 else 0

/-- Receipt generations precede the current generation, preventing a second collection. -/
def ReceiptInvariant (s : OutputState) : Prop :=
  s.receipts.Nodup ∧ (∀ p g, (p, g) ∈ s.receipts → g < (s.cells p).collected) ∧
    ∀ p, (s.cells p).running = true →
      (s.cells p).pendingId = (s.cells p).collected ∧ (s.cells p).launched = (s.cells p).collected + 1

 theorem collect_budget (s : OutputState) (p : Nat) (r e : Bool)
    (work : Nat → Nat → Reply) (total : Nat) (h : Budget total s) :
    Budget total (collect s p r e work) := by
  unfold collect
  dsimp only
  split
  · simp only [Budget, List.length_cons]
    have hp : s.remaining > 0 := by simp_all
    unfold Budget at h
    omega
  · exact h

 theorem visits_budget (s : OutputState) (visits : List (Nat × Bool × Bool))
    (work : Nat → Nat → Reply) (total : Nat) (h : Budget total s) :
    Budget total (runVisits s visits work) := by
  induction visits generalizing s with
  | nil => exact h
  | cons v vs ih => exact ih _ (collect_budget _ _ _ _ _ _ h)

 theorem collect_cell_balance (s : OutputState) (p i : Nat) (r e : Bool)
    (work : Nat → Nat → Reply) (h : CellBalance (s.cells i)) :
    CellBalance ((collect s p r e work).cells i) := by
  unfold collect
  dsimp only
  split
  · by_cases hi : i = p
    · subst i
      dsimp only
      unfold CellBalance at h ⊢
      have ha : (s.cells p).running = true := by simp_all
      cases hr : (decide (s.remaining > 1) && !e) <;> simp_all <;> omega
    · simpa [hi] using h
  · exact h

 theorem collect_receipts (s : OutputState) (p : Nat) (r e : Bool)
    (work : Nat → Nat → Reply) (h : ReceiptInvariant s) :
    ReceiptInvariant (collect s p r e work) := by
  unfold collect
  dsimp only
  split
  · have hr : (s.cells p).running = true := by simp_all
    have hp := h.2.2 p hr
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, h.1⟩
      intro hm
      have := h.2.1 p (s.cells p).pendingId hm
      omega
    · intro q g hm
      simp only [List.mem_cons] at hm
      rcases hm with he | hm
      · cases he
        simp [hp.1]
      · have hh := h.2.1 q g hm
        by_cases hq : q = p <;> simp_all <;> omega
    · intro q hq
      by_cases he : q = p
      · subst q
        have ha : (decide (s.remaining > 1) && !e) = true := by simpa using hq
        simp [ha, hp.2]
      · simpa [he] using h.2.2 q (by simpa [he] using hq)
  · exact h

 theorem visits_receipts (s : OutputState) (visits : List (Nat × Bool × Bool))
    (work : Nat → Nat → Reply) (h : ReceiptInvariant s) :
    ReceiptInvariant (runVisits s visits work) := by
  induction visits generalizing s with
  | nil => exact h
  | cons v vs ih => exact ih _ (collect_receipts _ _ _ _ _ h)

 def cycle_budget : Prop := ∀ (n p : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool × Bool)),
  let result := runVisits (startOutput n p initial work) visits work
  result.remaining = 0 → result.receipts.length = n * p

 theorem cycle_budget_holds : cycle_budget := by
  intro n p initial work visits
  have h := visits_budget (startOutput n p initial work) visits work (n * p) (by rfl)
  dsimp only
  intro hz
  simpa [Budget, hz] using h

example : (1 : Nat) * 2 > 0 := by decide

 def no_duplicate_collection : Prop := ∀ (n p : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool × Bool)),
  (runVisits (startOutput n p initial work) visits work).receipts.Nodup

 theorem no_duplicate_collection_holds : no_duplicate_collection := by
  intro n p initial work visits
  exact (visits_receipts _ visits work (by
    simp [ReceiptInvariant, startOutput]
    intro q hq hpos
    exact ⟨hq, by omega⟩)).1

 theorem visits_cell_balance (s : OutputState) (visits : List (Nat × Bool × Bool))
    (work : Nat → Nat → Reply) (i : Nat) (h : CellBalance (s.cells i)) :
    CellBalance ((runVisits s visits work).cells i) := by
  induction visits generalizing s with
  | nil => exact h
  | cons v vs ih => exact ih _ (collect_cell_balance _ _ _ _ _ _ h)

 def population_one_inflight : Prop := ∀ (n p i : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool × Bool)),
  CellBalance ((runVisits (startOutput n p initial work) visits work).cells i)

 theorem population_one_inflight_holds : population_one_inflight := by
  intro n p i initial work visits
  have hb : CellBalance ((startOutput n p initial work).cells i) := by
    by_cases hi : i < p <;> by_cases hz : n * p > 0 <;>
      simp [CellBalance, startOutput, hi, hz]
  exact visits_cell_balance _ visits work i hb

 def idle_preserves : Prop := ∀ (s : OutputState) (p : Nat) (e : Bool)
    (work : Nat → Nat → Reply), collect s p false e work = s

 theorem idle_preserves_holds : idle_preserves := by
  intro s p e work
  simp [collect]

 def finished_preserves : Prop := ∀ (s : OutputState) (p : Nat) (r e : Bool)
    (work : Nat → Nat → Reply), s.remaining = 0 → collect s p r e work = s

 theorem finished_preserves_holds : finished_preserves := by
  intro s p r e work hz
  simp [collect, hz]

example : (startOutput 0 2 (fun _ => []) (fun _ _ => ⟨[], ⟨[]⟩, 0, .fin 0, 0⟩)).remaining = 0 := rfl

 def collected_evaluations : Prop := ∀ (s : OutputState) (p : Nat) (e : Bool)
    (work : Nat → Nat → Reply), (s.cells p).running = true → s.remaining > 0 →
  ((collect s p true e work).cells p).evaluations =
    (s.cells p).evaluations + (s.cells p).pending.evaluations

 theorem collected_evaluations_holds : collected_evaluations := by
  intro s p e work ha hr
  simp [collect, ha, hr]

example : let work := fun (_ _ : Nat) => (⟨[], ⟨[]⟩, 0, .fin 1, 0⟩ : Reply)
  ((startOutput 1 1 (fun _ => []) work).cells 0).running = true ∧
  (startOutput 1 1 (fun _ => []) work).remaining > 0 := by decide

 def output_isolation : Prop := ∀ (s : OutputState) (p q : Nat) (r e : Bool)
    (work : Nat → Nat → Reply), p ≠ q →
  (collect s p r e work).cells q = s.cells q

 theorem output_isolation_holds : output_isolation := by
  intro s p q r e work hn
  unfold collect
  dsimp only
  split <;> simp_all [Ne.symm hn]

example : (0 : Nat) ≠ 1 := by decide

 def teardown_no_collection : Prop := ∀ (s : OutputState),
  (tearDown s).receipts = s.receipts ∧ (tearDown s).cells = s.cells

 theorem teardown_no_collection_holds : teardown_no_collection := by intro s; exact ⟨rfl, rfl⟩

/-- Concrete arbitrary worker values for the quantified counterexamples. -/
def unitReply (_ _ : Nat) : Reply := ⟨[], ⟨[]⟩, 0, .fin 1, 0⟩

 def exact_launched_cycles : Prop := ∀ (n p : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool × Bool)),
  0 < n → 0 < p →
  let result := runVisits (startOutput n p initial work) visits work
  result.remaining = 0 → result.launches = n * p

 theorem exact_launched_cycles_refuted : ¬ exact_launched_cycles := by
  intro h
  have hh := h 1 2 (fun _ => []) unitReply [(0, true, false), (1, true, false)]
    (by decide) (by decide) (by decide)
  contradiction

 def every_launch_collected : Prop := ∀ (n p : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) (visits : List (Nat × Bool × Bool)),
  let result := runVisits (startOutput n p initial work) visits work
  result.remaining = 0 → (tearDown result).receipts.length = result.launches

 theorem every_launch_collected_refuted : ¬ every_launch_collected := by
  intro h
  have hh := h 1 2 (fun _ => []) unitReply [(0, true, false), (1, true, false)] (by decide)
  contradiction

/-! ## Event-driven `done_ch` completion channel and single-copy population handoff -/

/-- Event-driven head-loop state (`src/SymbolicRegression.jl:1092-1296`):
extends `OutputState` with a completion channel `doneCh` carrying `(population, taskOk)`
events posted by async listener tasks, and a per-population `posted` flag tracking whether
the currently running listener has already posted its event. -/
structure EventState where
  sched : OutputState
  doneCh : List (Nat × Bool)
  posted : Nat → Bool

/-- Channel capacity and listener invariant: every queued event belongs to a distinct
population in `0..populations-1` whose `posted` flag is set, and `posted` is set only for
running populations in `0..populations-1`. -/
def EventInvariant (populations : Nat) (es : EventState) : Prop :=
  (es.doneCh.map Prod.fst).Nodup ∧
  (∀ p, es.posted p = true → p < populations ∧ (es.sched.cells p).running = true) ∧
  (∀ p, es.posted p = true ↔ p ∈ es.doneCh.map Prod.fst)

def startEvents (iterations populations : Nat) (initial : Nat → List Member)
    (work : Nat → Nat → Reply) : EventState :=
  { sched := startOutput iterations populations initial work
    doneCh := []
    posted := fun _ => false }

/-- Listener task finishes for population `p` and pushes `(p, taskOk)` to `done_ch`. -/
def postDone (es : EventState) (p : Nat) (taskOk : Bool) : EventState :=
  if (es.sched.cells p).running && !es.posted p then
    { es with
      doneCh := es.doneCh ++ [(p, taskOk)]
      posted := fun i => if i = p then true else es.posted i }
  else es

/-- Head loop consumes one event from `done_ch` (`src/SymbolicRegression.jl:1134-1148`).
`none` represents propagating a failed task (`!task_ok || istaskfailed`). -/
def consumeDone (es : EventState) (externalStop : Bool) (work : Nat → Nat → Reply) :
    Option EventState :=
  match es.doneCh with
  | [] => some es
  | (_, false) :: _ => none
  | (p, true) :: rest =>
    let sched' := collect es.sched p true externalStop work
    some { sched := sched'
           doneCh := rest
           posted := fun i => if i = p then false else es.posted i }

/-- Bounded length of any duplicate-free list of naturals strictly below `n`. -/
private theorem nodup_lt_length_le :
    ∀ (xs : List Nat) (n : Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  intro xs n hnd hlt
  have hsub : ∀ x ∈ xs, x ∈ List.range n := fun x hx => List.mem_range.mpr (hlt x hx)
  have hlen : (List.range n).length = n := List.length_range
  rw [← hlen]
  exact nodup_length_le_of_subset xs (List.range n) hnd hsub
where
  nodup_length_le_of_subset :
      ∀ (m l : List Nat), m.Nodup → (∀ x ∈ m, x ∈ l) → m.length ≤ l.length
    | [], _, _, _ => Nat.zero_le _
    | a :: m, l, hn, hs => by
      rw [List.nodup_cons] at hn
      have ha : a ∈ l := hs a (by simp)
      have hsub : ∀ x ∈ m, x ∈ l.erase a := by
        intro x hx
        have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
        exact (List.mem_erase_of_ne hxa).2 (hs x (by simp [hx]))
      have hih := nodup_length_le_of_subset m (l.erase a) hn.2 hsub
      rw [List.length_erase_of_mem ha] at hih
      have hpos : 0 < l.length := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

theorem eventInvariant_bounded (populations : Nat) (es : EventState)
    (h : EventInvariant populations es) : es.doneCh.length ≤ populations := by
  have hlen : (es.doneCh.map Prod.fst).length = es.doneCh.length := List.length_map _
  rw [← hlen]
  apply nodup_lt_length_le _ populations h.1
  intro p hp
  exact (h.2.1 p ((h.2.2 p).mpr hp)).1

theorem postDone_preserves (populations : Nat) (es : EventState) (p : Nat) (taskOk : Bool)
    (hp : p < populations) (h : EventInvariant populations es) :
    EventInvariant populations (postDone es p taskOk) ∧
    (postDone es p taskOk).sched = es.sched := by
  unfold postDone
  split
  · rename_i hc
    have hrun : (es.sched.cells p).running = true := by simp_all
    have hnp : es.posted p = false := by simp_all
    have hnotmem : p ∉ es.doneCh.map Prod.fst := by
      intro hm
      have := (h.2.2 p).mpr hm
      rw [hnp] at this
      cases this
    refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨h.1, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hnotmem ha
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; exact ⟨hp, hrun⟩
      · simp only [hqp, ↓reduceIte] at hq
        exact h.2.1 q hq
    · intro q
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
      by_cases hqp : q = p
      · subst hqp; simp
      · simp only [hqp, ↓reduceIte, or_false]
        exact h.2.2 q
  · exact ⟨h, rfl⟩

theorem consumeDone_preserves (populations total : Nat) (es : EventState)
    (externalStop : Bool) (work : Nat → Nat → Reply)
    (hinv : EventInvariant populations es)
    (hbud : Budget total es.sched)
    (hrec : ReceiptInvariant es.sched)
    (hbal : ∀ i, CellBalance (es.sched.cells i)) :
    match consumeDone es externalStop work with
    | none => ∃ p rest, es.doneCh = (p, false) :: rest
    | some es' =>
      EventInvariant populations es' ∧
      es'.doneCh.length ≤ populations ∧
      Budget total es'.sched ∧
      ReceiptInvariant es'.sched ∧
      (∀ i, CellBalance (es'.sched.cells i)) := by
  unfold consumeDone
  cases hch : es.doneCh with
  | nil =>
    exact ⟨hinv, eventInvariant_bounded populations es hinv, hbud, hrec, hbal⟩
  | cons ev rest =>
    rcases ev with ⟨p, ok⟩
    cases ok with
    | false => exact ⟨p, rest, rfl⟩
    | true =>
      dsimp only
      have hnd_cons : (p :: rest.map Prod.fst).Nodup := by
        simpa [hch] using hinv.1
      rw [List.nodup_cons] at hnd_cons
      have hinv' : EventInvariant populations
          { sched := collect es.sched p true externalStop work
            doneCh := rest
            posted := fun i => if i = p then false else es.posted i } := by
        refine ⟨hnd_cons.2, ?_, ?_⟩
        · intro q hq
          by_cases hqp : q = p
          · subst hqp; simp at hq
          · simp only [hqp, ↓reduceIte] at hq
            have hq0 := hinv.2.1 q hq
            have hcell := output_isolation_holds es.sched p q true externalStop work (Ne.symm hqp)
            exact ⟨hq0.1, by rw [hcell]; exact hq0.2⟩
        · intro q
          by_cases hqp : q = p
          · subst hqp
            simp [hnd_cons.1]
          · simp only [hqp, ↓reduceIte]
            have hiff := hinv.2.2 q
            simp only [hch, List.map_cons, List.mem_cons, hqp, false_or] at hiff
            exact hiff
      refine ⟨hinv', eventInvariant_bounded populations _ hinv',
        collect_budget _ _ _ _ _ _ hbud,
        collect_receipts _ _ _ _ _ hrec,
        fun i => collect_cell_balance _ _ _ _ _ _ (hbal i)⟩

/-- Property `search-event-channel`: `done_ch` starts empty with `EventInvariant`, stays
bounded by `populations` (never filling capacity `populations + 1`), preserves `Budget`,
`ReceiptInvariant`, and `CellBalance` across every post/consume step, and signals `none`
on failed-task notifications instead of ignoring them. -/
def event_channel_sound : Prop :=
  (∀ iterations populations initial work,
    EventInvariant populations (startEvents iterations populations initial work)) ∧
  (∀ populations es p taskOk, p < populations → EventInvariant populations es →
    EventInvariant populations (postDone es p taskOk) ∧
    (postDone es p taskOk).doneCh.length ≤ populations ∧
    (postDone es p taskOk).sched = es.sched) ∧
  (∀ populations total es externalStop work,
    EventInvariant populations es → Budget total es.sched →
    ReceiptInvariant es.sched → (∀ i, CellBalance (es.sched.cells i)) →
    match consumeDone es externalStop work with
    | none => ∃ p rest, es.doneCh = (p, false) :: rest
    | some es' =>
      EventInvariant populations es' ∧
      es'.doneCh.length ≤ populations ∧
      Budget total es'.sched ∧
      ReceiptInvariant es'.sched ∧
      (∀ i, CellBalance (es'.sched.cells i)))

theorem event_channel_sound_holds : event_channel_sound := by
  refine ⟨?_, ?_, ?_⟩
  · intro iterations populations initial work
    refine ⟨List.nodup_nil, ?_, ?_⟩
    · intro p hp; simp [startEvents] at hp
    · intro p; simp [startEvents]
  · intro populations es p taskOk hp hinv
    have ⟨h1, h2⟩ := postDone_preserves populations es p taskOk hp hinv
    exact ⟨h1, eventInvariant_bounded populations _ h1, h2⟩
  · intro populations total es externalStop work hinv hbud hrec hbal
    exact consumeDone_preserves populations total es externalStop work hinv hbud hrec hbal

/-- Single-copy population handoff (`src/SymbolicRegression.jl:1175-1245`):
`saved_pop = copy(cur_pop)` allocates fresh member IDs disjoint from `cur_pop`;
`best_sub_pop(saved_pop)` selects a subset of `saved_pop`'s member IDs;
reusing `in_pop = cur_pop` for the next worker shares zero member IDs with either
`state.last_pops[j][i]` or `state.best_sub_pops[j][i]`. -/
def single_copy_handoff : Prop :=
  ∀ (curIds savedIds bestIds : List Nat),
    (∀ id ∈ savedIds, id ∉ curIds) →
    (∀ id ∈ bestIds, id ∈ savedIds) →
    (∀ id ∈ curIds, id ∉ savedIds ∧ id ∉ bestIds)

theorem single_copy_handoff_holds : single_copy_handoff := by
  intro curIds savedIds bestIds hdisj hsub id hid
  refine ⟨fun hs => hdisj id hs hid, fun hb => hdisj id (hsub id hb) hid⟩

end SymReg.Search
