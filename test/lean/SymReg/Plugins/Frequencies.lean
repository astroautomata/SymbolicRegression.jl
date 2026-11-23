import SymReg.Plugins.Dispatch
import SymReg.Loss.Core

/-!
`src/plugins/AdaptiveParsimony.jl:31-103,145-164,206-220`.
The two fields reference mutable Float64 vectors. Arithmetic uses the shared
IEEE rounding model, which identifies signed zeros and NaN payloads.
-/
namespace SymReg.Plugins
open DynExpr

attribute [local semireducible] Rat.add Rat.mul Rat.inv Rat.sub

theorem ratDivSelf (a : Rat) (ha : a ≠ 0) : a / a = 1 := by
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel a ha

theorem ratZeroDiv (a : Rat) : 0 / a = 0 := by
  rw [Rat.div_def, Rat.zero_mul]

theorem ratLeDiv {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h
    apply Rat.not_lt.mp
    intro hn
    exact (Rat.not_lt.mpr h) ((Rat.div_lt_iff hc).mpr hn)
  · intro h
    apply Rat.not_lt.mp
    intro hn
    exact (Rat.not_lt.mpr h) ((Rat.div_lt_iff hc).mp hn)

theorem ratDivLe {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  constructor
  · intro h
    apply Rat.not_lt.mp
    intro hn
    exact (Rat.not_lt.mpr h) ((Rat.lt_div_iff hc).mpr hn)
  · intro h
    apply Rat.not_lt.mp
    intro hn
    exact (Rat.not_lt.mpr h) ((Rat.lt_div_iff hc).mp hn)

theorem ratDivMono {a b c : Rat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  simp only [Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr hc))

theorem ratAddPos {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  have h : b ≤ a + b := by
    simpa [Rat.zero_add] using (Rat.add_le_add_right (c := b)).mpr ha
  exact Std.lt_of_lt_of_le hb h

theorem ratDivByQuotient (a b : Rat) (ha : a ≠ 0) : a / (a / b) = b := by
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
  rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc, Rat.mul_inv_cancel a ha, Rat.mul_one]

abbrev FrequencyHeap := Heap (List JF)

-- Source: src/plugins/AdaptiveParsimony.jl:31-35
-- struct RunningSearchStatistics
--     window_size::Int
--     frequencies::Vector{Float64}
--     normalized_frequencies::Vector{Float64}  # Stores `frequencies`, but normalized (updated once in a while)
-- end
structure Statistics where
  window : Int
  frequencies : Addr
  normalized : Addr
  deriving DecidableEq, Repr

def round64 : JF → JF := Loss.LossPrecision.round .float64
def fdiv64 (a b : JF) : JF := round64 (a / b)
def fsum64 : List JF → JF := Loss.pairwiseSum .float64

def floatLT : JF → JF → Bool
  | .nan, _ | _, .nan => false
  | .negInf, .negInf | .posInf, .posInf => false
  | .negInf, _ | _, .posInf => true
  | .fin x, .fin y => decide (x < y)
  | _, _ => false

def floatMin (a b : JF) : JF :=
  if a = .nan ∨ b = .nan then .nan else if floatLT b a then b else a

def writeFrequency (h : FrequencyHeap) (a : Addr) (xs : List JF) : Jl Unit × FrequencyHeap :=
  match h.write a xs with
  | .error e => (.error e, h)
  | .ok next => (.ok (), next)

def normalizeBins (src : List JF) (n : Nat) : Jl (List JF) :=
  let q := fsum64 src
  if src.length = n then .ok (src.map (fun x => fdiv64 x q))
  else match src with
  | [x] => .ok (List.replicate n (fdiv64 x q))
  | _ => .error (.dimensionMismatch "arrays could not be broadcast to a common size")

-- Source: src/plugins/AdaptiveParsimony.jl:100-104
-- function normalize_frequencies!(running_search_statistics::RunningSearchStatistics)
--     running_search_statistics.normalized_frequencies .=
--         running_search_statistics.frequencies ./ sum(running_search_statistics.frequencies)
--     return nothing
-- end
def normalize (h : FrequencyHeap) (s : Statistics) : Jl Unit × FrequencyHeap :=
  match (do
    let raw ← h.read s.frequencies
    let dest ← h.read s.normalized
    normalizeBins raw dest.length) with
  | .error e => (.error e, h)
  | .ok xs => writeFrequency h s.normalized xs

-- Source: src/plugins/AdaptiveParsimony.jl:37-43
-- function RunningSearchStatistics(; options::AbstractOptions, window_size::Int=100000)
--     init_frequencies = ones(Float64, options.maxsize)
--
--     return RunningSearchStatistics(
--         window_size, init_frequencies, copy(init_frequencies) / sum(init_frequencies)
--     )
-- end
def initStatistics (h : FrequencyHeap) (maxsize : Int) (window : Int := 100000) :
    Jl (Statistics × FrequencyHeap) :=
  if maxsize < 0 then .error (.argumentError "invalid Array dimensions") else
  let raw := List.replicate maxsize.toNat (.fin 1)
  let (a, h₁) := h.alloc raw
  let q := fsum64 raw
  let (b, h₂) := h₁.alloc (raw.map (fun x => fdiv64 x q))
  .ok (⟨window, a, b⟩, h₂)

/-- Non-integer inputs use their Julia dispatch for the chained comparisons
and, if reached, conversion to a Vector index. -/
inductive FrequencySize where
  | integer (value : Int)
  | nothing
  | dispatched (positive : FrequencyHeap → Jl Bool × FrequencyHeap)
      (within : Nat → FrequencyHeap → Jl Bool × FrequencyHeap)
      (index : FrequencyHeap → Jl Nat × FrequencyHeap)

private def bumpFrequency (h : FrequencyHeap) (s : Statistics) (i : Nat) :
    Jl Unit × FrequencyHeap :=
  match h.read s.frequencies with
  | .error e => (.error e, h)
  | .ok raw =>
    match raw[i]? with
    | none => (.error .boundsError, h)
    | some x => writeFrequency h s.frequencies (raw.set i (round64 (x + JF.fin 1)))

-- Source: src/plugins/AdaptiveParsimony.jl:51-58
-- @inline function update_frequencies!(
--     running_search_statistics::RunningSearchStatistics; size=nothing
-- )
--     if 0 < size <= length(running_search_statistics.frequencies)
--         running_search_statistics.frequencies[size] += 1
--     end
--     return nothing
-- end
def updateFrequency (h : FrequencyHeap) (s : Statistics) (size : FrequencySize := .nothing) :
    Jl Unit × FrequencyHeap :=
  match size with
  | .nothing => (.error (.methodError "isless"), h)
  | .integer i =>
    if 0 < i then
      match h.read s.frequencies with
      | .error e => (.error e, h)
      | .ok raw =>
        if i ≤ (raw.length : Int) then bumpFrequency h s (i.toNat - 1) else (.ok (), h)
    else (.ok (), h)
  | .dispatched positive within index =>
    match positive h with
    | (.error e, h') => (.error e, h')
    | (.ok false, h') => (.ok (), h')
    | (.ok true, h') =>
      match h'.read s.frequencies with
      | .error e => (.error e, h')
      | .ok raw =>
        match within raw.length h' with
        | (.error e, h'') => (.error e, h'')
        | (.ok false, h'') => (.ok (), h'')
        | (.ok true, h'') =>
          match index h'' with
          | (.error e, out) => (.error e, out)
          | (.ok 0, out) => (.error .boundsError, out)
          | (.ok (i + 1), out) => bumpFrequency out s i

def updateMembers (s : Statistics) (h : FrequencyHeap) :
    List (FrequencyHeap → Jl Int × FrequencyHeap) → Jl Unit × FrequencyHeap
  | [] => (.ok (), h)
  | getSize :: rest =>
    match getSize h with
    | (.error e, next) => (.error e, next)
    | (.ok size, afterSize) =>
      match updateFrequency afterSize s (.integer size) with
      | (.ok (), next) => updateMembers s next rest
      | (.error e, next) => (.error e, next)

-- Source: src/plugins/AdaptiveParsimony.jl:80-95
-- while difference_in_size > 0
--     indices_to_subtract = findall(frequencies .> smallest_frequency_allowed)
--     num_remaining = size(indices_to_subtract, 1)
--     amount_to_subtract = min(
--         difference_in_size / num_remaining,
--         min(frequencies[indices_to_subtract]...) - smallest_frequency_allowed,
--     )
--     frequencies[indices_to_subtract] .-= amount_to_subtract
--     total_amount_to_subtract = amount_to_subtract * num_remaining
--     difference_in_size -= total_amount_to_subtract
--     num_loops += 1
--     if num_loops > max_loops || total_amount_to_subtract < 1e-6
--         # Sometimes, total_amount_to_subtract can be a very very small number.
--         break
--     end
-- end
def windowLoop : Nat → JF → List JF → Jl Unit × List JF
  | 0, _, fs => (.ok (), fs)
  | fuel + 1, difference, fs =>
    if floatLT (.fin 0) difference then
      let selected := fs.filter (floatLT (.fin 1))
      match selected with
      | [] => (.error (.methodError "min()"), fs)
      | x :: rest =>
        let n := Loss.floatCount .float64 selected.length
        let amount := floatMin (fdiv64 difference n)
          (round64 (rest.foldl floatMin x - .fin 1))
        let fs' := fs.map (fun y => if floatLT (.fin 1) y then round64 (y - amount) else y)
        let removed := round64 (amount * n)
        let difference' := round64 (difference - removed)
        if floatLT removed (round64 (.fin (1 / 1000000))) then (.ok (), fs')
        else windowLoop fuel difference' fs'
    else (.ok (), fs)

-- Source: src/plugins/AdaptiveParsimony.jl:66-80,96-98
-- function move_window!(running_search_statistics::RunningSearchStatistics)
--     smallest_frequency_allowed = 1
--     max_loops = 1000
--
--     frequencies = running_search_statistics.frequencies
--     window_size = running_search_statistics.window_size
--
--     cur_size_frequency_complexities = sum(frequencies)
--     if cur_size_frequency_complexities > window_size
--         difference_in_size = cur_size_frequency_complexities - window_size
--         # We need frequencyComplexities to be positive, but also sum to a number.
--         num_loops = 0
--         # TODO: Clean this code up. Should not have to have
--         # loop catching.
--         while difference_in_size > 0
def moveWindow (h : FrequencyHeap) (s : Statistics) : Jl Unit × FrequencyHeap :=
  match h.read s.frequencies with
  | .error e => (.error e, h)
  | .ok raw =>
    let sum := fsum64 raw
    if floatLT (.fin (s.window : Rat)) sum then
      let (result, xs) := windowLoop 1001 (round64 (sum - round64 (.fin (s.window : Rat)))) raw
      (result, (writeFrequency h s.frequencies xs).2)
    else (.ok (), h)

-- Source: src/plugins/AdaptiveParsimony.jl:215-220
-- for member in returned_pop.members
--     sz = compute_complexity(member, options)
--     update_frequencies!(s.rss; size=sz)
-- end
-- move_window!(s.rss)
-- return nothing
def onGeneration (h : FrequencyHeap) (s : Statistics)
    (members : List (FrequencyHeap → Jl Int × FrequencyHeap)) : Jl Unit × FrequencyHeap :=
  match updateMembers s h members with
  | (.error e, next) => (.error e, next)
  | (.ok (), next) => moveWindow next s

-- Source: src/plugins/AdaptiveParsimony.jl:149-155
-- function fork_plugin_state(
--     head_state::AdaptiveParsimonyState, ::AdaptiveParsimonyPlugin, dataset
-- )
--     snapshot = deepcopy(head_state.rss)::RunningSearchStatistics
--     normalize_frequencies!(snapshot)
--     return AdaptiveParsimonyState(snapshot)
-- end
def forkParsimony (h : FrequencyHeap) (head : Statistics) : Jl Statistics × FrequencyHeap :=
  match (do
    let raw ← h.read head.frequencies
    let cached ← h.read head.normalized
    pure (raw, cached)) with
  | .error e => (.error e, h)
  | .ok (raw, cached) =>
    let (a, first) := h.alloc raw
    let (b, next) := if head.normalized = head.frequencies then (a, first) else first.alloc cached
    let child := ⟨head.window, a, b⟩
    let (r, out) := normalize next child
    (r.map (fun _ => child), out)

-- Source: src/plugins/AdaptiveParsimony.jl:157-164
-- function refresh_worker_plugin_state(
--     worker_state::AdaptiveParsimonyState,
--     latest_head_state::AdaptiveParsimonyState,
--     plugin::AdaptiveParsimonyPlugin,
--     dataset,
-- )
--     return fork_plugin_state(latest_head_state, plugin, dataset)
-- end
def refreshParsimony (h : FrequencyHeap) (_worker head : Statistics) :
    Jl Statistics × FrequencyHeap := forkParsimony h head

private theorem writeFrequency_read_other (h : FrequencyHeap) (a b : Addr)
    (xs : List JF) (hne : b ≠ a) :
    (writeFrequency h a xs).2.read b = h.read b := by
  unfold writeFrequency
  split
  · rfl
  · rename_i h' hw
    exact Heap.read_write_other _ _ _ _ _ hw hne

def stale_probability_preserved : Prop := ∀ h s (size : Int) raw,
  h.read s.frequencies = .ok raw →
  let (r, out) := updateFrequency h s (.integer size)
  (s.normalized ≠ s.frequencies → out.read s.normalized = h.read s.normalized) ∧
  (s.normalized = s.frequencies → out.read s.normalized = out.read s.frequencies) ∧
  (∀ e, r = .error e → out.read s.normalized = h.read s.normalized) ∧
  (updateFrequency h s).1 = .error (.methodError "isless") ∧
  (updateFrequency h s).2.read s.normalized = h.read s.normalized

theorem stale_probability_preserved_holds : stale_probability_preserved := by
  intro h s size raw hr
  simp only [updateFrequency, hr]
  refine ⟨?_, fun he => by rw [he], ?_, trivial, trivial⟩
  · intro hn
    split
    · split
      · simp only [bumpFrequency, hr]
        split
        · rfl
        · exact writeFrequency_read_other _ _ _ _ hn
      · rfl
    · rfl
  · split
    · split
      · simp only [bumpFrequency, hr]
        split
        · intros; rfl
        · unfold writeFrequency
          split <;> simp
      · simp
    · simp

def frequency_update_shape : Prop := ∀ h s raw size,
  h.read s.frequencies = .ok raw →
  let (r, out) := updateFrequency h s (.integer size)
  r = .ok () ∧
  ∃ after, out.read s.frequencies = .ok after ∧ after.length = raw.length ∧
    ∀ j, after[j]? =
      if size = ((j + 1 : Nat) : Int) then (raw[j]?).map (fun x => round64 (x + .fin 1))
      else raw[j]?

private theorem writeFrequency_ok (h : FrequencyHeap) (a : Addr) (old xs : List JF)
    (hr : h.read a = .ok old) :
    (writeFrequency h a xs).1 = .ok () ∧ (writeFrequency h a xs).2.read a = .ok xs := by
  have hn : h.cells a ≠ none := by
    intro he
    simp [Heap.read, he] at hr
  simp [writeFrequency, Heap.write, hn, Heap.read]

theorem frequency_update_shape_holds : frequency_update_shape := by
  intro h s raw size hr
  dsimp only
  simp only [updateFrequency, hr]
  by_cases hsize : 0 < size ∧ size ≤ (raw.length : Int)
  · have hi : size.toNat - 1 < raw.length := by omega
    let i := size.toNat - 1
    obtain ⟨x, hx⟩ : ∃ x, raw[i]? = some x := ⟨raw[i], List.getElem?_eq_getElem hi⟩
    simp only [if_pos hsize.1, if_pos hsize.2, bumpFrequency, hr, ← show i = size.toNat - 1 from rfl, hx]
    have hw := writeFrequency_ok h s.frequencies raw (raw.set i (round64 (x + .fin 1))) hr
    refine ⟨hw.1, _, hw.2, List.length_set, ?_⟩
    intro j
    have hidx : i = j ↔ size = ((j + 1 : Nat) : Int) := by dsimp [i]; omega
    by_cases he : i = j
    · subst j
      rw [List.getElem?_set_self hi, if_pos (hidx.mp rfl), hx]
      rfl
    · rw [List.getElem?_set_ne he, if_neg (mt hidx.mpr he)]
  · have hRun : (if 0 < size then
        if size ≤ (raw.length : Int) then bumpFrequency h s (size.toNat - 1) else (.ok (), h)
        else (.ok (), h)) = (.ok (), h) := by
      split
      · split <;> simp_all
      · rfl
    rw [hRun]
    refine ⟨rfl, raw, hr, rfl, ?_⟩
    intro j
    split
    · have hj : raw.length ≤ j := by omega
      rw [List.getElem?_eq_none hj]
      rfl
    · rfl

def normalization_shape : Prop := ∀ h s raw cached,
  h.read s.frequencies = .ok raw → h.read s.normalized = .ok cached →
  let (r, out) := normalize h s
  if raw.length = cached.length ∨ raw.length = 1 then
    r = .ok () ∧ (∃ xs, out.read s.normalized = .ok xs ∧ xs.length = cached.length) ∧
    (s.frequencies ≠ s.normalized → out.read s.frequencies = .ok raw ∧
      ∀ a, (normalize out s).2.read a = out.read a)
  else r = .error (.dimensionMismatch "arrays could not be broadcast to a common size") ∧
    ∀ a, out.read a = h.read a

private theorem normalizeBins_shape (raw : List JF) (n : Nat) :
    if raw.length = n ∨ raw.length = 1 then
      ∃ xs, normalizeBins raw n = .ok xs ∧ xs.length = n
    else normalizeBins raw n = .error (.dimensionMismatch "arrays could not be broadcast to a common size") := by
  by_cases he : raw.length = n
  · simp [normalizeBins, he]
  · cases raw with
    | nil =>
      have hne : (0 : Nat) ≠ n := he
      simp [normalizeBins, hne]
    | cons x xs => cases xs <;> simp_all [normalizeBins]

theorem normalization_shape_holds : normalization_shape := by
  intro h s raw cached hr hc
  have hs := normalizeBins_shape raw cached.length
  by_cases he : raw.length = cached.length ∨ raw.length = 1
  · simp only [he, if_true] at hs ⊢
    obtain ⟨xs, hx, hlen⟩ := hs
    have hn : normalize h s = writeFrequency h s.normalized xs := by
      simp [normalize, hr, hc, hx, bind, Except.bind]
    rw [hn]
    have hw := writeFrequency_ok h s.normalized cached xs hc
    refine ⟨hw.1, ⟨xs, hw.2, hlen⟩, ?_⟩
    intro hd
    let out := (writeFrequency h s.normalized xs).2
    have hout : out.read s.frequencies = .ok raw :=
      (writeFrequency_read_other h s.normalized s.frequencies xs hd).trans hr
    refine ⟨hout, ?_⟩
    intro a
    have hnorm : normalize out s = writeFrequency out s.normalized xs := by
      have hc' : out.read s.normalized = .ok xs := hw.2
      simp [normalize, hout, hc', hlen, hx, bind, Except.bind]
    change (normalize out s).2.read a = out.read a
    rw [hnorm]
    by_cases ha : a = s.normalized
    · subst a
      exact (writeFrequency_ok out s.normalized xs xs hw.2).2.trans hw.2.symm
    · exact writeFrequency_read_other _ _ _ _ ha
  · simp only [he, if_false] at hs ⊢
    simp [normalize, hr, hc, hs, bind, Except.bind]

def init_frequency_counts : Prop := ∀ h n window,
  if n < 0 then initStatistics h n window = .error (.argumentError "invalid Array dimensions") else
  ∃ s out, initStatistics h n window = .ok (s, out) ∧
    s.window = window ∧ s.frequencies ≠ s.normalized ∧
    h.cells s.frequencies = none ∧ h.cells s.normalized = none ∧
    out.read s.frequencies = .ok (List.replicate n.toNat (.fin 1)) ∧
    out.read s.normalized = .ok (List.replicate n.toNat (fdiv64 (.fin 1)
      (fsum64 (List.replicate n.toNat (.fin 1)))))

theorem init_frequency_counts_holds : init_frequency_counts := by
  intro h n window
  unfold initStatistics
  split
  · rfl
  · refine ⟨_, _, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · change h.next ≠ h.next + 1
      omega
    · exact h.fresh h.next (Nat.le_refl _)
    · exact h.fresh (h.next + 1) (by omega)
    · simp [Heap.alloc, Heap.read, show h.next ≠ h.next + 1 by omega]
    · simp [Heap.alloc, Heap.read, List.map_replicate]

/-- Initial counts are one; each generation only adds one or subtracts from bins
above one. This arithmetic envelope includes Float64 rounding of the updates. -/
def SearchCountRange (raw : List JF) : Prop :=
  raw ≠ [] ∧ raw.length ≤ 2^63 - 1 ∧
    ∀ x ∈ raw, ∃ q : Rat, x = .fin q ∧ 0 < q ∧ q ≤ 2^53

def normalization_probability : Prop := ∀ h s raw cached,
  h.read s.frequencies = .ok raw → h.read s.normalized = .ok cached →
  raw.length = cached.length → SearchCountRange raw →
  ∃ xs q mass, (normalize h s).2.read s.normalized = .ok xs ∧
    fsum64 raw = .fin q ∧ 0 < q ∧
    (∀ (i : Nat) x, raw[i]? = some x → xs[i]? = some (fdiv64 x (.fin q))) ∧
    fsum64 xs = .fin mass ∧ max (mass - 1) (1 - mass) ≤ (raw.length : Rat) / 2^51

def window_probability_preserved : Prop := ∀ h s
    (members : List (FrequencyHeap → Jl Int × FrequencyHeap)),
  (s.normalized ≠ s.frequencies →
    (moveWindow h s).2.read s.normalized = h.read s.normalized ∧
    ((∀ run ∈ members, ∀ state, (run state).2.read s.normalized = state.read s.normalized) →
      (onGeneration h s members).2.read s.normalized = h.read s.normalized)) ∧
  (s.normalized = s.frequencies → ∀ raw,
    h.read s.normalized = .ok raw →
    (∃ xs, (moveWindow h s).2.read s.normalized = .ok xs ∧ xs.length = raw.length ∧
      ∀ (j : Nat) q, raw[j]? = some (.fin q) →
        (q ≤ 1 → xs[j]? = some (.fin q)) ∧
        (1 < q → ∃ t : Rat, xs[j]? = some (.fin t) ∧ 0 ≤ t ∧ t ≤ q)) ∧
    ∀ (sizes : List Int) e,
      let priorCalls := sizes.map (fun size (state : FrequencyHeap) => (.ok size, state))
      let fail := fun state : FrequencyHeap => (.error e, state)
      let (result, out) := onGeneration h s (priorCalls ++ fail :: members)
      result = .error e ∧
      ∃ xs, out.read s.normalized = .ok xs ∧ xs.length = raw.length ∧
        ∀ (j : Nat) x, raw[j]? = some x →
          xs[j]? = some (sizes.foldl (fun value size =>
            if size = ((j + 1 : Nat) : Int) then round64 (value + .fin 1) else value) x))

private def bumpBin (j : Nat) (value : JF) (size : Int) : JF :=
  if size = ((j + 1 : Nat) : Int) then round64 (value + .fin 1) else value

def frequency_exact_counts : Prop := ∀ h s raw (sizes : List Int) j x,
  h.read s.frequencies = .ok raw → raw[j]? = some x →
  let (r, out) := updateMembers s h (sizes.map (fun size state => (.ok size, state)))
  r = .ok () ∧ ∃ xs, out.read s.frequencies = .ok xs ∧
    xs[j]? = some (sizes.foldl (bumpBin j) x)

theorem frequency_exact_counts_holds : frequency_exact_counts := by
  intro h s raw sizes j x hr hx
  induction sizes generalizing h raw x with
  | nil => exact ⟨rfl, raw, hr, hx⟩
  | cons z zs ih =>
    obtain ⟨hs, mid, hm, -, hbin⟩ := frequency_update_shape_holds h s raw z hr
    let run := updateFrequency h s (.integer z)
    change run.1 = .ok () at hs
    change run.2.read s.frequencies = .ok mid at hm
    have hnext : updateFrequency h s (.integer z) = (.ok (), run.2) := by
      change (run.1, run.2) = (.ok (), run.2)
      rw [hs]
    have hz : mid[j]? = some (bumpBin j x z) := by
      rw [hbin, hx]
      unfold bumpBin
      split <;> rfl
    simpa only [List.map_cons, updateMembers, hnext, List.foldl_cons] using
      ih run.2 mid _ hm hz


private def forkExpectedCache (raw : List JF) (n : Nat) : Jl (List JF) :=
  let total := Loss.pairwiseSum .float64 raw
  if raw.length = n then .ok (raw.map fun x => Loss.LossPrecision.float64.round (x / total))
  else match raw with
    | [x] => .ok (List.replicate n (Loss.LossPrecision.float64.round (x / total)))
    | _ => .error (.dimensionMismatch "arrays could not be broadcast to a common size")

private theorem normalizeBins_fork (raw : List JF) (n : Nat) :
    normalizeBins raw n = forkExpectedCache raw n := by
  unfold normalizeBins forkExpectedCache
  by_cases h : raw.length = n
  · simp only [h, ↓reduceIte, fsum64, fdiv64, round64]
  · simp only [h, ↓reduceIte, fsum64, fdiv64, round64]

def fork_refresh_snapshot : Prop := ∀ h head worker raw cached,
  h.read head.frequencies = .ok raw → h.read head.normalized = .ok cached →
  let (r, out) := forkParsimony h head
  (∀ a, a < h.next → out.read a = h.read a) ∧
  refreshParsimony h worker head = (r, out) ∧
  match forkExpectedCache raw cached.length with
  | .error e => r = .error e
  | .ok xs => ∃ child, r = .ok child ∧ child.window = head.window ∧
      h.next ≤ child.frequencies ∧ h.next ≤ child.normalized ∧
      (child.frequencies = child.normalized ↔ head.frequencies = head.normalized) ∧
      out.read child.normalized = .ok xs ∧
      out.read child.frequencies = .ok (if head.frequencies = head.normalized then xs else raw)

private theorem fork_normalize (h mid : FrequencyHeap) (head child : Statistics) (raw cached : List JF)
    (hr : mid.read child.frequencies = .ok raw) (hc : mid.read child.normalized = .ok cached)
    (hf : ∀ a, a < h.next → mid.read a = h.read a) (hw : child.window = head.window)
    (ha : h.next ≤ child.frequencies) (hb : h.next ≤ child.normalized)
    (hAlias : child.frequencies = child.normalized ↔ head.frequencies = head.normalized) :
    let (r, out) := normalize mid child
    (∀ a, a < h.next → out.read a = h.read a) ∧
    match forkExpectedCache raw cached.length with
    | .error e => r.map (fun _ => child) = .error e
    | .ok xs => ∃ result, r.map (fun _ => child) = .ok result ∧ result.window = head.window ∧
        h.next ≤ result.frequencies ∧ h.next ≤ result.normalized ∧
        (result.frequencies = result.normalized ↔ head.frequencies = head.normalized) ∧
        out.read result.normalized = .ok xs ∧
        out.read result.frequencies = .ok (if head.frequencies = head.normalized then xs else raw) := by
  rw [← normalizeBins_fork]
  unfold normalize
  simp only [hr, hc, bind, Except.bind]
  split
  · exact ⟨hf, rfl⟩
  · rename_i xs hxs
    have hc' := writeFrequency_ok mid child.normalized cached xs hc
    refine ⟨fun a hlt => (writeFrequency_read_other mid child.normalized a xs
      (show a ≠ child.normalized by omega)).trans (hf a hlt),
      child, by rw [hc'.1]; rfl, hw, ha, hb, hAlias, hc'.2, ?_⟩
    by_cases he : head.frequencies = head.normalized
    · rw [if_pos he, hAlias.mpr he]
      exact hc'.2
    · rw [if_neg he, writeFrequency_read_other _ _ _ _ (mt hAlias.mp he), hr]

theorem fork_refresh_snapshot_holds : fork_refresh_snapshot := by
  intro h head worker raw cached hr hc
  have hrefresh : refreshParsimony h worker head = forkParsimony h head := rfl
  simp only [hrefresh]
  unfold forkParsimony
  simp only [hr, hc, bind, Except.bind, pure, Except.pure]
  rw [← normalizeBins_fork]
  by_cases hAlias : head.frequencies = head.normalized
  · have hv : cached = raw := by rw [hAlias, hc] at hr; cases hr; rfl
    subst cached
    simp only [hAlias.symm, ↓reduceIte]
    let first := (h.alloc raw).2
    let child : Statistics := ⟨head.window, h.next, h.next⟩
    have hcr : first.read h.next = .ok raw := Heap.read_alloc_same h raw
    have hoff : ∀ a, a < h.next → first.read a = h.read a :=
      fun a hlt => Heap.read_alloc_other h raw a (show a ≠ h.next by omega)
    obtain ⟨hframe, hresult⟩ := fork_normalize h first head child raw raw hcr hcr hoff rfl
      (Nat.le_refl _) (Nat.le_refl _) (by simp [child, hAlias])
    rw [← normalizeBins_fork] at hresult
    refine ⟨hframe, trivial, ?_⟩
    cases hnorm : normalizeBins raw raw.length <;>
      simpa [hnorm, hAlias, normalize, child, first,
        show (h.alloc raw).1 = h.next from rfl,
        show (h.alloc raw).2.read h.next = .ok raw from hcr, bind, Except.bind] using hresult
  · have hne : head.normalized ≠ head.frequencies := Ne.symm hAlias
    simp only [hne, ↓reduceIte]
    let first := (h.alloc raw).2
    let mid := (first.alloc cached).2
    let child : Statistics := ⟨head.window, h.next, h.next + 1⟩
    have he : first.next = h.next + 1 := rfl
    have hr' : mid.read h.next = .ok raw :=
      (Heap.read_alloc_other first cached h.next (show h.next ≠ first.next by omega)).trans
        (Heap.read_alloc_same h raw)
    have hc' : mid.read (h.next + 1) = .ok cached := Heap.read_alloc_same first cached
    have hf : ∀ a, a < h.next → mid.read a = h.read a := fun a hlt =>
      (Heap.read_alloc_other first cached a (show a ≠ first.next by omega)).trans
        (Heap.read_alloc_other h raw a (show a ≠ h.next by omega))
    obtain ⟨hframe, hresult⟩ := fork_normalize h mid head child raw cached hr' hc' hf rfl
      (Nat.le_refl _) (Nat.le_succ _) (by simp [child, hAlias])
    rw [← normalizeBins_fork] at hresult
    exact ⟨hframe, trivial, hresult⟩

def window_exact_target : Prop := ∀ h s raw,
  h.read s.frequencies = .ok raw →
  (∀ x ∈ raw, ∃ q : Rat, x = .fin q ∧ 1 ≤ q) →
  (raw.length : Int) ≤ s.window →
  floatLT (.fin (s.window : Rat)) (fsum64 raw) = true →
  (moveWindow h s).1 = .ok () →
  ∃ out, (moveWindow h s).2.read s.frequencies = .ok out ∧
    fsum64 out = round64 (.fin (s.window : Rat))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem window_exact_target_refuted : ¬ window_exact_target := by
  intro claim
  let a := round64 (.fin (10000001 / 10000000))
  let raw := [a, .fin 3]
  let h := (Heap.empty.alloc raw).2
  let s : Statistics := ⟨2, 0, 0⟩
  have hr : h.read s.frequencies = .ok raw := by rfl
  have hb : ∀ x ∈ raw, ∃ q : Rat, x = .fin q ∧ 1 ≤ q := by
    intro x hx
    simp [raw] at hx
    rcases hx with rfl | rfl
    · exact ⟨4503600077730459 / 4503599627370496, by decide, by decide⟩
    · exact ⟨3, rfl, by decide⟩
  obtain ⟨out, hout, he⟩ := claim h s raw hr hb (by decide) (by decide) (by decide)
  have hn : (moveWindow h s).2.read s.frequencies = .ok out →
      fsum64 out ≠ round64 (.fin 2) := by
    intro hh
    have hx : (moveWindow h s).2.read s.frequencies =
        .ok [JF.fin 1, round64 (.fin 3 - round64 (a - .fin 1))] := by decide
    rw [hx] at hh
    cases hh
    decide
  exact hn hout he
end SymReg.Plugins
