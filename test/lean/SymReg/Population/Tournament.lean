import DynExpr.Runtime.Value
import DynExpr.Runtime.Errors
import SymReg.Loss.Core

/-!
Model of tournament selection in `src/Population.jl` (SymbolicRegression.jl `upstream/master`
daae84e5): `_sample_indices!`, `get_tournament_selection_weights`, the `StatsBase.sample`
call that draws the tournament place, `bottomk_fast` (`src/Utils.jl:97-131`) and
`_best_of_sample` / `best_of_sample`.

Costs are `Float64` values modelled by DE's `JF` (NaN and infinities matter here). The
selection weights are modelled with exact rational arithmetic (no rounding). Random draws are
abstract streams quantified over in every property.
-/

namespace SymReg.Population
open DynExpr

/-! ## Float comparisons -/

/-- Julia `<` on `Float64` (IEEE): every comparison involving NaN is false. Used by
`src/Population.jl:207` and `src/Utils.jl:117,122`. -/
def flt : JF → JF → Bool
  | .nan, _ => false
  | _, .nan => false
  | .fin a, .fin b => decide (a < b)
  | .negInf, .negInf => false
  | .negInf, _ => true
  | _, .negInf => false
  | .fin _, .posInf => true
  | .posInf, _ => false

/-- Julia `isless` on `Float64`, the default order of `sortperm` (`src/Population.jl:254`):
the IEEE order with NaN after every other value. -/
def isless : JF → JF → Bool
  | .nan, _ => false
  | _, .nan => true
  | a, b => flt a b

/-- `isnan`. -/
def isNaN : JF → Bool
  | .nan => true
  | _ => false

theorem isless_irrefl (a : JF) : isless a a = false := by
  cases a <;> simp [isless, flt]

theorem isless_trans {a b c : JF} (h1 : isless a b = true) (h2 : isless b c = true) :
    isless a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [isless, flt] <;> grind

theorem isless_asymm {a b : JF} (h : isless a b = true) : isless b a = false := by
  cases a <;> cases b <;> simp_all [isless, flt] <;> grind

theorem isless_of_isless_not_isless {a b c : JF} (h1 : isless a b = true)
    (h2 : isless c b = false) : isless a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [isless, flt] <;> grind

theorem not_isless_trans {a b c : JF} (h1 : isless b a = false) (h2 : isless c b = false) :
    isless c a = false := by
  cases a <;> cases b <;> cases c <;> simp_all [isless, flt] <;> grind

theorem isless_of_not_nan {a : JF} (h : isNaN a = false) : isless a .nan = true := by
  cases a <;> simp_all [isless, isNaN]

theorem isless_eq_flt_of_not_nan {a b : JF} (ha : isNaN a = false) (hb : isNaN b = false) :
    isless a b = flt a b := by
  cases a <;> cases b <;> simp_all [isless, isNaN]

/-- One-based checked indexing `xs[i]`; out of range throws a `BoundsError`. -/
def at1 {α : Type} (xs : List α) (i : Nat) : Jl α :=
  match (if 1 ≤ i then xs[i - 1]? else none) with
  | some x => pure x
  | none => throw .boundsError

/-! ## `_sample_indices!` -/

/-- Inner rejection loop of `src/Population.jl:160-163`: `candidate = rand(1:N)`, redrawn
while `candidate in view(idxs, 1:(i - 1))` (`prev`). `draw c` is the `c`-th value of the
`rand(1:N)` stream. The Julia loop is unbounded; `fuel` bounds the draws of one inner loop and
`none` means the fuel ran out. Returns the accepted candidate and the next stream cursor. -/
def drawFresh (draw : Nat → Nat) (prev : List Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, c =>
    if draw c ∈ prev then drawFresh draw prev fuel (c + 1) else some (draw c, c + 1)

/-- Outer loop `for i in 1:n` of `src/Population.jl:159-165`; `acc` is `idxs[1:(i - 1)]`. -/
def sampleLoop (draw : Nat → Nat) (fuel : Nat) : Nat → List Nat → Nat → Option (List Nat × Nat)
  | 0, acc, c => some (acc, c)
  | k + 1, acc, c =>
    match drawFresh draw acc fuel c with
    | none => none
    | some (v, c') => sampleLoop draw fuel k (acc ++ [v]) c'

/-- `_sample_indices!(idxs, N, n)`, `src/Population.jl:157-167`. `resize!(idxs, n)` discards
the scratch buffer's old contents from the reads: only `idxs[1:(i - 1)]`, written by this call,
is read. The range `1:N` enters through the stream contract `RandRange draw N`. Returns the
indices and the stream cursor after the last draw. -/
def sampleIndices (draw : Nat → Nat) (fuel n : Nat) : Option (List Nat × Nat) :=
  sampleLoop draw fuel n [] 0

/-- Contract of `rand(1:N)`: every draw lies in `1:N`. -/
def RandRange (draw : Nat → Nat) (N : Nat) : Prop := ∀ c, 1 ≤ draw c ∧ draw c ≤ N

/-- A stream that keeps producing every value of `1:N` (any reasonable generator does so with
probability one). -/
def Fair (draw : Nat → Nat) (N : Nat) : Prop :=
  ∀ v c, 1 ≤ v → v ≤ N → ∃ c', c ≤ c' ∧ draw c' = v

/-- Property `pop-sample-indices-valid`: whenever `_sample_indices!` returns, it returns `n`
distinct indices, all in `1:N`. -/
def sample_indices_valid : Prop :=
  ∀ (draw : Nat → Nat) (N n fuel : Nat) (idxs : List Nat) (c : Nat),
    RandRange draw N → sampleIndices draw fuel n = some (idxs, c) →
    idxs.length = n ∧ idxs.Nodup ∧ ∀ x ∈ idxs, 1 ≤ x ∧ x ≤ N

/-- A sample consumes a succession of intervals. Each interval ends in its
first unseen value, and the final accepted value ends the read prefix. -/
inductive FirstDistinct (draw : Nat → Nat) : Nat → List Nat → Nat → List Nat → Nat → Prop where
  | done : FirstDistinct draw 0 acc c acc c
  | take (next : Nat) : c ≤ next → draw next ∉ acc →
      (∀ d, c ≤ d → d < next → draw d ∈ acc) →
      FirstDistinct draw n (acc ++ [draw next]) (next + 1) idxs ending →
      FirstDistinct draw (n + 1) acc c idxs ending

/-- Property `pop-sample-indices-terminates`: for `n ≤ N` and a stream that keeps producing
every value of `1:N`, `_sample_indices!` terminates. -/
def sample_indices_terminates : Prop :=
  ∀ (draw : Nat → Nat) (N n : Nat), n ≤ N → RandRange draw N → Fair draw N →
    ∃ fuel idxs c, sampleIndices draw fuel n = some (idxs, c) ∧
      idxs.length = n ∧ idxs.Nodup ∧
      FirstDistinct draw n [] 0 idxs c

theorem drawFresh_spec (draw : Nat → Nat) (prev : List Nat) :
    ∀ fuel c v c', drawFresh draw prev fuel c = some (v, c') → v ∉ prev ∧ ∃ d, draw d = v := by
  intro fuel
  induction fuel with
  | zero => intro c v c' h; simp [drawFresh] at h
  | succ f ih =>
    intro c v c' h
    unfold drawFresh at h
    split at h
    · exact ih _ _ _ h
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hn, c, rfl⟩

theorem sampleLoop_spec (draw : Nat → Nat) (N fuel : Nat) (hr : RandRange draw N) :
    ∀ k acc c r c', sampleLoop draw fuel k acc c = some (r, c') → acc.Nodup →
      (∀ x ∈ acc, 1 ≤ x ∧ x ≤ N) →
      r.length = acc.length + k ∧ r.Nodup ∧ ∀ x ∈ r, 1 ≤ x ∧ x ≤ N := by
  intro k
  induction k with
  | zero =>
    intro acc c r c' h hn hb
    simp only [sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨by simp, hn, hb⟩
  | succ k ih =>
    intro acc c r c' h hn hb
    unfold sampleLoop at h
    split at h
    · simp at h
    · rename_i v c1 hd
      obtain ⟨hv, d, hd'⟩ := drawFresh_spec draw acc fuel c v c1 hd
      have hn' : (acc ++ [v]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hn, by simp, ?_⟩
        intro a ha b hb' hab
        simp at hb'
        subst hb'; subst hab
        exact hv ha
      have hb'' : ∀ x ∈ acc ++ [v], 1 ≤ x ∧ x ≤ N := by
        intro x hx
        simp at hx
        rcases hx with hx | hx
        · exact hb x hx
        · subst hx; rw [← hd']; exact hr d
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ h hn' hb''
      refine ⟨?_, h2, h3⟩
      rw [h1]; simp; omega

theorem sample_indices_valid_holds : sample_indices_valid := by
  intro draw N n fuel idxs c hr h
  obtain ⟨h1, h2, h3⟩ := sampleLoop_spec draw N fuel hr n [] 0 idxs c h (by simp) (by simp)
  exact ⟨by simpa using h1, h2, h3⟩

/-- A duplicate-free list `m` contained in `l` is no longer than `l`. -/
theorem nodup_length_le_of_subset :
    ∀ (m l : List Nat), m.Nodup → (∀ x ∈ m, x ∈ l) → m.length ≤ l.length := by
  intro m
  induction m with
  | nil => intro l _ _; simp
  | cons a m ih =>
    intro l hn hs
    rw [List.nodup_cons] at hn
    have ha : a ∈ l := hs a (by simp)
    have hsub : ∀ x ∈ m, x ∈ l.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hs x (by simp [hx]))
    have := ih (l.erase a) hn.2 hsub
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < l.length := List.length_pos_of_mem ha
    simp; omega

/-- Pigeonhole: fewer than `N` values cannot cover `1:N`. -/
theorem exists_unused (acc : List Nat) (N : Nat) (hl : acc.length < N) :
    ∃ v, 1 ≤ v ∧ v ≤ N ∧ v ∉ acc := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ x ∈ List.range' 1 N, x ∈ acc := by
    intro x hx
    rw [List.mem_range'_1] at hx
    apply Classical.byContradiction
    intro hxa
    exact hno ⟨x, hx.1, by omega, hxa⟩
  have := nodup_length_le_of_subset _ _ (List.nodup_range' (s := 1) (n := N)) hall
  simp at this
  omega

theorem drawFresh_mono (draw : Nat → Nat) (prev : List Nat) :
    ∀ fuel c r, drawFresh draw prev fuel c = some r →
      ∀ fuel', fuel ≤ fuel' → drawFresh draw prev fuel' c = some r := by
  intro fuel
  induction fuel with
  | zero => intro c r h; simp [drawFresh] at h
  | succ f ih =>
    intro c r h fuel' hle
    obtain ⟨g, rfl⟩ : ∃ g, fuel' = g + 1 := ⟨fuel' - 1, by omega⟩
    unfold drawFresh at h ⊢
    split at h
    · rename_i hin
      rw [if_pos hin]
      exact ih _ _ h g (by omega)
    · rename_i hin
      rw [if_neg hin]
      exact h

theorem drawFresh_reach (draw : Nat → Nat) (prev : List Nat) (c' : Nat) (hc' : draw c' ∉ prev) :
    ∀ fuel c, c ≤ c' → c' - c < fuel → ∃ r, drawFresh draw prev fuel c = some r := by
  intro fuel
  induction fuel with
  | zero => intro c _ h; omega
  | succ f ih =>
    intro c hc hlt
    unfold drawFresh
    split
    · rename_i hin
      have hne : c ≠ c' := fun h => hc' (h ▸ hin)
      exact ih (c + 1) (by omega) (by omega)
    · exact ⟨_, rfl⟩

theorem sampleLoop_reach (draw : Nat → Nat) (N : Nat) (hr : RandRange draw N) (hf : Fair draw N) :
    ∀ k acc c, acc.length + k ≤ N → acc.Nodup → (∀ x ∈ acc, 1 ≤ x ∧ x ≤ N) →
      ∃ F, ∀ fuel, F ≤ fuel → ∃ r, sampleLoop draw fuel k acc c = some r := by
  intro k
  induction k with
  | zero => intro acc c _ _ _; exact ⟨0, fun _ _ => ⟨_, rfl⟩⟩
  | succ k ih =>
    intro acc c hl hn hb
    obtain ⟨v, hv1, hv2, hv3⟩ := exists_unused acc N (by omega)
    obtain ⟨c', hcc', hdc'⟩ := hf v c hv1 hv2
    obtain ⟨⟨w, c1⟩, hw⟩ :=
      drawFresh_reach draw acc c' (hdc' ▸ hv3) (c' - c + 1) c hcc' (by omega)
    obtain ⟨hw1, d, hwd⟩ := drawFresh_spec draw acc _ c w c1 hw
    have hn' : (acc ++ [w]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hn, by simp, ?_⟩
      intro a ha b hb' hab
      simp at hb'
      subst hb'; subst hab
      exact hw1 ha
    have hb'' : ∀ x ∈ acc ++ [w], 1 ≤ x ∧ x ≤ N := by
      intro x hx
      simp at hx
      rcases hx with hx | hx
      · exact hb x hx
      · subst hx; rw [← hwd]; exact hr d
    obtain ⟨F, hF⟩ := ih (acc ++ [w]) c1 (by simp; omega) hn' hb''
    refine ⟨max F (c' - c + 1), fun fuel hle => ?_⟩
    have hd := drawFresh_mono draw acc _ c _ hw fuel (by omega)
    obtain ⟨r, hr'⟩ := hF fuel (by omega)
    refine ⟨r, ?_⟩
    unfold sampleLoop
    rw [hd]
    exact hr'

private theorem drawFresh_prefix (draw : Nat → Nat) (prev : List Nat) :
    ∀ fuel c v c', drawFresh draw prev fuel c = some (v, c') →
      c < c' ∧ v = draw (c' - 1) ∧ (∀ d, c ≤ d → d < c' - 1 → draw d ∈ prev) := by
  intro fuel
  induction fuel with
  | zero => intro c v c' h; cases h
  | succ fuel ih =>
    intro c v c' h
    unfold drawFresh at h
    split at h
    · rename_i hmem
      obtain ⟨hlt, hv, hp⟩ := ih _ _ _ h
      exact ⟨by omega, hv, fun d hdc hd =>
        if he : d = c then he.symm ▸ hmem else hp d (by omega) hd⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by simp, fun d h1 h2 => by omega⟩

private theorem sampleLoop_firstDistinct (draw : Nat → Nat) (fuel : Nat) :
    ∀ n acc c idxs ending, sampleLoop draw fuel n acc c = some (idxs, ending) →
      FirstDistinct draw n acc c idxs ending := by
  intro n
  induction n with
  | zero =>
    intro acc c idxs ending h
    simp only [sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .done
  | succ n ih =>
    intro acc c idxs ending h
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i v cursor hd
      obtain ⟨hlt, hv, hskip⟩ := drawFresh_prefix draw acc fuel c v cursor hd
      have hfresh := (drawFresh_spec draw acc fuel c v cursor hd).1
      refine .take (cursor - 1) (by omega) (hv ▸ hfresh) hskip ?_
      have he : cursor - 1 + 1 = cursor := by omega
      rw [he, ← hv]
      exact ih _ _ _ _ h

theorem sample_indices_terminates_holds : sample_indices_terminates := by
  intro draw N n hn hr hf
  obtain ⟨F, hF⟩ := sampleLoop_reach draw N hr hf n [] 0 (by simpa using hn) (by simp) (by simp)
  obtain ⟨r, h⟩ := hF F (Nat.le_refl _)
  obtain ⟨idxs, c⟩ := r
  have hsample : sampleIndices draw F n = some (idxs, c) := h
  obtain ⟨hlen, hnd, _⟩ := sample_indices_valid_holds draw N n F idxs c hr hsample
  exact ⟨F, idxs, c, hsample, hlen, hnd, sampleLoop_firstDistinct draw F n [] 0 idxs c h⟩

example : RandRange (fun c => c % 3 + 1) 3 ∧ Fair (fun c => c % 3 + 1) 3 := by
  refine ⟨fun c => ⟨by dsimp only; omega, by dsimp only; omega⟩, fun v c h1 h2 => ?_⟩
  refine ⟨3 * c + (v - 1), by omega, ?_⟩
  dsimp only
  omega

/-! ## Tournament weights and the place draw -/

/-- `x ^ k` for `k ≥ 0` (Julia `(1 - p) .^ k` with integer `k`), exact. -/
def rpow (x : Rat) : Nat → Rat
  | 0 => 1
  | k + 1 => rpow x k * x

/-- `get_tournament_selection_weights(options)`, `src/Population.jl:224-234`:
`k = collect(0:(n - 1)); prob_each = p * ((1 - p) .^ k)`. The per-task cache
(`get!(CACHED_WEIGHTS[], (n, p))`, line 228) is keyed on exactly the inputs `(n, p)`, so a hit
returns these same weights. Exact arithmetic. -/
def tournamentWeights (n : Nat) (p : Rat) : List Rat :=
  (List.range n).map fun k => p * rpow (1 - p) k

/-- `sum(prob_each)`, the total stored in `StatsBase.Weights(prob_each, sum(prob_each))`. -/
def wsum (w : List Rat) : Rat := w.foldl (· + ·) 0

/-- Property `pop-weights-geometric`: the weights are `p, p(1-p), p(1-p)^2, ...`, `n` of them,
and their total is `1 - (1-p)^n`, so place `k` is drawn with probability
`p(1-p)^(k-1) / (1 - (1-p)^n)`. -/
def weights_geometric : Prop :=
  ∀ (n : Nat) (p : Rat), (tournamentWeights n p).length = n ∧
    (∀ k, k < n → (tournamentWeights n p)[k]? = some (p * rpow (1 - p) k)) ∧
    wsum (tournamentWeights n p) = 1 - rpow (1 - p) n

theorem wsum_range_succ (n : Nat) (p : Rat) :
    wsum (tournamentWeights (n + 1) p) = wsum (tournamentWeights n p) + p * rpow (1 - p) n := by
  simp [wsum, tournamentWeights, List.range_succ, List.foldl_append]

theorem weights_geometric_holds : weights_geometric := by
  intro n p
  refine ⟨by simp [tournamentWeights], ?_, ?_⟩
  · intro k hk
    simp [tournamentWeights, hk]
  · induction n with
    | zero => simp [wsum, tournamentWeights, rpow]; grind
    | succ n ih =>
      rw [wsum_range_succ, ih]
      simp only [rpow]
      grind

/-- Property `pop-weights-valid`: for `0 < p ≤ 1` and `n ≥ 1`, the weights are a valid
(unnormalised) distribution: all nonnegative, the first is `p > 0`, the total is positive and at
most 1; for `0 < p < 1` they are strictly decreasing. -/
def weights_valid : Prop :=
  ∀ (n : Nat) (p : Rat), 1 ≤ n → 0 < p → p ≤ 1 →
    (∀ w ∈ tournamentWeights n p, 0 ≤ w) ∧ (tournamentWeights n p)[0]? = some p ∧
    0 < wsum (tournamentWeights n p) ∧ wsum (tournamentWeights n p) ≤ 1 ∧
    (p < 1 → ∀ k, k + 1 < n →
      (tournamentWeights n p)[k + 1]?.getD 0 < (tournamentWeights n p)[k]?.getD 0)

theorem rpow_nonneg (x : Rat) (hx : 0 ≤ x) : ∀ k, 0 ≤ rpow x k := by
  intro k
  induction k with
  | zero => simp [rpow]; decide
  | succ k ih => exact Rat.mul_nonneg ih hx

theorem rpow_pos (x : Rat) (hx : 0 < x) : ∀ k, 0 < rpow x k := by
  intro k
  induction k with
  | zero => simp [rpow]; decide
  | succ k ih => exact Rat.mul_pos ih hx

theorem rpow_le_one (x : Rat) (hx : 0 ≤ x) (h1 : x ≤ 1) : ∀ k, rpow x k ≤ 1 := by
  intro k
  induction k with
  | zero => simp [rpow]
  | succ k ih =>
    simp only [rpow]
    have h0 := rpow_nonneg x hx k
    have : rpow x k * x ≤ rpow x k * 1 := by
      have := Rat.mul_nonneg h0 (show 0 ≤ 1 - x by grind)
      grind
    grind

theorem weights_valid_holds : weights_valid := by
  intro n p hn hp hp1
  have hq : 0 ≤ 1 - p := by grind
  have hsum := (weights_geometric_holds n p).2.2
  have hpow := rpow_le_one (1 - p) hq (by grind) n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [tournamentWeights, List.mem_map, List.mem_range] at hw
    obtain ⟨k, -, rfl⟩ := hw
    exact Rat.mul_nonneg (Rat.le_of_lt hp) (rpow_nonneg _ hq k)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [tournamentWeights, rpow]
  · rw [hsum]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [rpow]
    have h0 := rpow_nonneg (1 - p) hq m
    have hm := rpow_le_one (1 - p) hq (by grind) m
    have : rpow (1 - p) m * (1 - p) ≤ 1 * (1 - p) := by
      have := Rat.mul_nonneg (show 0 ≤ 1 - rpow (1 - p) m by grind) hq
      grind
    grind
  · rw [hsum]
    have := rpow_nonneg (1 - p) hq n
    grind
  · intro hp2 k hk
    simp only [tournamentWeights, List.getElem?_map, List.getElem?_range hk,
      List.getElem?_range (show k < n by omega), Option.map_some, Option.getD_some, rpow]
    have hpos := rpow_pos (1 - p) (by grind) k
    have : p * rpow (1 - p) k * p > 0 := Rat.mul_pos (Rat.mul_pos hp hpos) hp
    grind

/-- `while cw < t && i < n; i += 1; cw += wv[i]; end` of `StatsBase.sample(rng, wv)`
(StatsBase `src/sampling.jl:586-605`); `rest` is `wv[(i + 1):n]`. -/
def sbLoop (t : Rat) : Nat → Rat → List Rat → Nat × Rat
  | i, cw, [] => (i, cw)
  | i, cw, x :: xs => if cw < t then sbLoop t (i + 1) (cw + x) xs else (i, cw)

/-- Floating-point fallback `while iszero(wv[i]); i -= 1; end` of StatsBase
`src/sampling.jl:600-603`; reaching index 0 throws a `BoundsError`. -/
def sbBackoff (w : List Rat) : Nat → Jl Nat
  | 0 => throw .boundsError
  | i + 1 => if w.getD i 1 = 0 then sbBackoff w i else pure (i + 1)

/-- `StatsBase.sample(wv)` with uniform draw `u = rand()` (StatsBase `src/sampling.jl:586-605`),
the tournament place of `src/Population.jl:200`. `isfinite(wsum)` always holds for exact
weights. -/
def sbSample (w : List Rat) (u : Rat) : Jl Nat :=
  match w with
  | [] => throw .boundsError
  | w1 :: ws =>
    let t := u * wsum w
    let r := sbLoop t 1 w1 ws
    if r.2 < t then sbBackoff w r.1 else pure r.1

/-- Property `pop-place-range`: for `0 < p ≤ 1`, `n ≥ 1` and any draw `u ∈ [0, 1)`, the
tournament place `StatsBase.sample(get_tournament_selection_weights(options))` is in `1:n`. -/
def place_range : Prop :=
  ∀ (n : Nat) (p u : Rat), 1 ≤ n → 0 < p → p ≤ 1 → 0 ≤ u → u < 1 →
    ∃ k, sbSample (tournamentWeights n p) u = .ok k ∧ 1 ≤ k ∧ k ≤ n

theorem sbLoop_bounds (t : Rat) : ∀ (xs : List Rat) i cw,
    i ≤ (sbLoop t i cw xs).1 ∧ (sbLoop t i cw xs).1 ≤ i + xs.length := by
  intro xs
  induction xs with
  | nil => intro i cw; simp [sbLoop]
  | cons x xs ih =>
    intro i cw
    simp only [sbLoop]
    split
    · have := ih (i + 1) (cw + x); simp; omega
    · simp

theorem sbBackoff_ok (w : List Rat) (hw : w.getD 0 1 ≠ 0) :
    ∀ i, 1 ≤ i → ∃ k, sbBackoff w i = .ok k ∧ 1 ≤ k ∧ k ≤ i := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _
    simp only [sbBackoff]
    split
    · rename_i hz
      cases i with
      | zero => exact absurd hz hw
      | succ j =>
        obtain ⟨k, hk, h1, h2⟩ := ih (by omega)
        exact ⟨k, hk, h1, by omega⟩
    · exact ⟨i + 1, rfl, by omega, by omega⟩

theorem place_range_holds : place_range := by
  intro n p u hn hp hp1 _ _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw : tournamentWeights (m + 1) p = p :: (List.range m).map (fun k => p * rpow (1 - p) (k + 1)) := by
    simp [tournamentWeights, List.range_succ_eq_map, rpow]
  have h0 : (tournamentWeights (m + 1) p).getD 0 1 ≠ 0 := by
    rw [hw]; simp; intro h; rw [h] at hp; exact Rat.lt_irrefl hp
  have hb := sbLoop_bounds (u * wsum (tournamentWeights (m + 1) p))
    ((List.range m).map (fun k => p * rpow (1 - p) (k + 1))) 1 p
  simp only [List.length_map, List.length_range] at hb
  generalize hR : sbLoop (u * wsum (tournamentWeights (m + 1) p)) 1 p
    ((List.range m).map (fun k => p * rpow (1 - p) (k + 1))) = R at hb
  have hs : sbSample (tournamentWeights (m + 1) p) u =
      if R.2 < u * wsum (tournamentWeights (m + 1) p)
      then sbBackoff (tournamentWeights (m + 1) p) R.1 else pure R.1 := by
    rw [← hR]
    conv => lhs; rw [hw]
    simp only [sbSample]
    rw [← hw]
  rw [hs]
  split
  · obtain ⟨k, hk, h1, h2⟩ := sbBackoff_ok _ h0 R.1 (by omega)
    exact ⟨k, hk, h1, by omega⟩
  · exact ⟨R.1, rfl, by omega, by omega⟩

/-! ## `bottomk_fast` -/

/-- Initial buffer entry `(typemax(T), 1)` of `src/Utils.jl:120-121`. -/
def dflt : JF × Nat := (.posInf, 1)

/-- The swap pass `for ki in pos:-1:(firstindex(minval) + 1)` with `else break`
(`src/Utils.jl:140-147`), written 0-based: compare position `j + 1` with `j` using `isless`,
stopping as soon as `!isless a.1 b.1`. -/
def bubble (buf : List (JF × Nat)) : Nat → List (JF × Nat)
  | 0 => buf
  | j + 1 =>
    let a := buf.getD (j + 1) dflt
    let b := buf.getD j dflt
    if isless a.1 b.1 then bubble ((buf.set (j + 1) b).set j a) j else buf

/-- Body of `_bottomk!` for element `x[i]`, `src/Utils.jl:128-147`, tracking `(buf, filled)`. -/
def bottomkStep (k : Nat) (st : List (JF × Nat) × Nat) (x : JF) (i : Nat) :
    List (JF × Nat) × Nat :=
  let (buf, filled) := st
  if filled < k then
    (bubble (buf.set filled (x, i)) filled, filled + 1)
  else if isless x (buf.getD (k - 1) dflt).1 then
    (bubble (buf.set (k - 1) (x, i)) (k - 1), filled)
  else
    (buf, filled)

/-- `for i in eachindex(x)` of `src/Utils.jl:128`. -/
def bottomkGo (k : Nat) : List (JF × Nat) × Nat → List JF → Nat → List (JF × Nat) × Nat
  | st, [], _ => st
  | st, x :: xs, i => bottomkGo k (bottomkStep k st x i) xs (i + 1)

/-- `_bottomk_dispatch(x, Val(k))` for `k ≥ 2` (`src/Utils.jl:119-123`), which
`bottomk_fast(x, k)` (`src/Utils.jl:97-104`) calls for every `k ≥ 2`: the `(value, index)`
buffer after scanning `x`. -/
def bottomk (k : Nat) (x : List JF) : List (JF × Nat) :=
  (bottomkGo k (List.replicate k dflt, 0) x 1).1

/-! ## `_best_of_sample` and `best_of_sample` -/

/-- Base `prod` on a tuple of Float32/64 multipliers; the empty tuple returns
the integer identity, which promotes to the loss type for the final multiply. -/
def prodJF (precision : Loss.LossPrecision) : List JF → JF
  | [] => .fin 1
  | x :: xs => xs.foldl (fun a b => precision.round (a * b)) x

private def collectMultipliers {M W : Type} (precision : Loss.LossPrecision) (member : M) :
    List (M → W → Jl JF × W) → W → Jl (List JF) × W
  | [], w => (.ok [], w)
  | hook :: rest, w =>
    match hook member w with
    | (.error e, w') => (.error e, w')
    | (.ok x, w') =>
      let value := precision.round x
      let (tail, w'') := collectMultipliers precision member rest w'
      (tail.map (value :: ·), w'')

-- Source: src/Population.jl:189-195
-- function adjusted_cost(i)
--     member = members[idxs[i]]
--     multipliers = strictmap(options.plugins, plugin_states) do plugin, pstate
--         return L(tournament_cost_multiplier(pstate, plugin, member, options))
--     end
--     L(member.cost) * prod(multipliers)
-- end
def adjusted {M W : Type} (precision : Loss.LossPrecision) (cost : M → W → JF)
    (hooks : List (M → W → Jl JF × W)) (member : M) (w : W) : Jl JF × W :=
  match collectMultipliers precision member hooks w with
  | (.error e, w') => (.error e, w')
  | (.ok mults, w') =>
    let c := precision.round (cost member w')
    (.ok (precision.round (c * prodJF precision mults)), w')

theorem adjusted_one_infinite (precision : Loss.LossPrecision) (before after : Nat) (cost : JF) :
    let neutral := fun (_ : Unit) (w : Unit) => (.ok (JF.fin 1), w)
    let infinite := fun (_ : Unit) (w : Unit) => (.ok JF.posInf, w)
    (adjusted precision (fun _ _ => cost)
      (List.replicate before neutral ++ infinite :: List.replicate after neutral) () ()).1 =
      .ok (precision.round (precision.round cost * .posInf)) := by
  dsimp only
  have h1 : precision.round (.fin 1) = .fin 1 := by cases precision <;> decide +kernel
  let one : Unit → Unit → Jl JF × Unit := fun _ w => (.ok (.fin 1), w)
  let inf : Unit → Unit → Jl JF × Unit := fun _ w => (.ok .posInf, w)
  have collectTail (n : Nat) :
      collectMultipliers precision () (List.replicate n one) () =
        (.ok (List.replicate n (.fin 1)), ()) := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, collectMultipliers, one, ih, h1, Except.map]
  have collectAll (n : Nat) :
      collectMultipliers precision () (List.replicate n one ++ inf :: List.replicate after one) () =
        (.ok (List.replicate n (.fin 1) ++ .posInf :: List.replicate after (.fin 1)), ()) := by
    induction n with
    | zero => simp [collectMultipliers, inf, collectTail, Loss.LossPrecision.round, Except.map]
    | succ n ih => simp [List.replicate_succ, collectMultipliers, one, ih, h1, Except.map]
  have foldTail (n : Nat) :
      (List.replicate n (JF.fin 1)).foldl (fun a b => precision.round (a * b)) .posInf = .posInf := by
    have hi : precision.round (JF.posInf * .fin 1) = .posInf := by cases precision <;> decide +kernel
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.foldl_cons, hi, ih]
  have hstep : precision.round (JF.fin 1 * .fin 1) = .fin 1 := by cases precision <;> decide +kernel
  have hinf : precision.round (JF.fin 1 * .posInf) = .posInf := by cases precision <;> decide +kernel
  have foldBefore (n : Nat) :
      (List.replicate n (JF.fin 1) ++ JF.posInf :: List.replicate after (JF.fin 1)).foldl
        (fun a b => precision.round (a * b)) (.fin 1) = .posInf := by
    induction n with
    | zero => simpa [hinf] using foldTail after
    | succ n ih => simpa [List.replicate_succ, hstep] using ih
  have hprod : prodJF precision
      (List.replicate before (JF.fin 1) ++ .posInf :: List.replicate after (.fin 1)) = .posInf := by
    cases before with
    | zero => exact foldTail after
    | succ n => simpa only [List.replicate_succ, List.cons_append, prodJF] using foldBefore n
  change (adjusted precision _ (List.replicate before one ++ inf :: List.replicate after one)
    () ()).1 = _
  rw [adjusted, collectAll]
  change Except.ok (precision.round (precision.round cost * prodJF precision
    (List.replicate before (JF.fin 1) ++ .posInf :: List.replicate after (.fin 1)))) = _
  rw [hprod]

/-- First-place loop `for i in 2:n; isless(cost, best_cost) && ...` of `src/Population.jl:201-206`. -/
def firstMinGo : List JF → Nat → Nat → JF → Nat
  | [], _, bi, _ => bi
  | c :: cs, i, bi, bc =>
    if isless c bc then firstMinGo cs (i + 1) i c else firstMinGo cs (i + 1) bi bc

/-- Position chosen in the sample by `src/Population.jl:199-211`: for `tournament_winner == 1`
the first-place loop (`adjusted_cost(1)` on an empty sample throws a `BoundsError`), otherwise
`bottomk_fast(costs, tournament_winner)[2][end]`. -/
def chooseIdx (costs : List JF) (winner : Nat) : Jl Nat :=
  if winner = 1 then
    match costs with
    | [] => throw .boundsError
    | c :: cs => pure (firstMinGo cs 2 1 c)
  else pure ((bottomk winner costs).getD (winner - 1) dflt).2

-- Source: src/Population.jl:187-212. Each hook sees the member reached through
-- the live index vector, and the winning position is dereferenced again.
structure TournamentState (M : Type) where
  members : List M
  indices : List Nat

def tournamentLookup {M : Type} (state : TournamentState M) (position : Nat) : Jl M :=
  (at1 state.indices position).bind (at1 state.members)

private def tournamentCosts {M : Type}
    (score : M → TournamentState M → Jl JF × TournamentState M) :
    List Nat → TournamentState M → Jl (List JF) × TournamentState M
  | [], state => (.ok [], state)
  | i :: rest, state =>
    match tournamentLookup state i with
    | .error e => (.error e, state)
    | .ok member =>
      match score member state with
      | (.error e, next) => (.error e, next)
      | (.ok value, next) =>
        let (values, final) := tournamentCosts score rest next
        (values.map (value :: ·), final)

def bestOfSampleLive {M : Type} (state : TournamentState M)
    (score : M → TournamentState M → Jl JF × TournamentState M) (winner : Nat) :
    Jl M × TournamentState M :=
  let (scores, final) := tournamentCosts score (List.range' 1 state.indices.length) state
  (scores.bind fun costs => (chooseIdx costs winner).bind (tournamentLookup final), final)

def tournament_member_live : Prop :=
  ∀ (M : Type) (state : TournamentState M)
    (score : M → TournamentState M → Jl JF × TournamentState M) (place : Nat) (winner : M),
    (bestOfSampleLive state score place).1 = .ok winner →
    ∃ i ∈ state.indices, at1 state.members i = .ok winner

theorem tournament_member_live_refuted : ¬ tournament_member_live := by
  intro law
  obtain ⟨i, hi, h⟩ := law Nat ⟨[11, 22], [1]⟩
    (fun _ s => (.ok (.fin 1), { s with indices := [2] })) 1 22 rfl
  simp only [List.mem_singleton] at hi
  subst i
  cases h

private theorem tournamentCosts_nointerference {M : Type}
    (score : M → TournamentState M → Jl JF × TournamentState M)
    (stable : ∀ member state, (score member state).2 = state) :
    ∀ positions state, (tournamentCosts score positions state).2 = state := by
  intro positions
  induction positions with
  | nil => intro state; rfl
  | cons i rest ih =>
    intro state
    cases hread : tournamentLookup state i with
    | error e => simp [tournamentCosts, hread]
    | ok member =>
      have h := stable member state
      cases hscore : score member state with
      | mk result next =>
        rw [hscore] at h
        dsimp at h
        subst next
        cases result <;> simp [tournamentCosts, hread, hscore, ih]

theorem bestOfSampleLive_member {M : Type} (state : TournamentState M)
    (score : M → TournamentState M → Jl JF × TournamentState M)
    (stable : ∀ member state, (score member state).2 = state)
    (place : Nat) (winner : M) (h : (bestOfSampleLive state score place).1 = .ok winner) :
    ∃ i ∈ state.indices, at1 state.members i = .ok winner := by
  have hframe := tournamentCosts_nointerference score stable
    (List.range' 1 state.indices.length) state
  unfold bestOfSampleLive at h
  cases hc : tournamentCosts score (List.range' 1 state.indices.length) state with
  | mk result final =>
    rw [hc] at hframe
    dsimp at hframe
    subst final
    cases result with
    | error e => simp [hc, bind, Except.bind] at h
    | ok costs =>
      cases hchoose : chooseIdx costs place with
      | error e => simp [hc, hchoose, bind, Except.bind] at h
      | ok position =>
        simp only [hc, hchoose, bind, Except.bind, tournamentLookup] at h
        have indexRead : ∃ i, at1 state.indices position = .ok i ∧ i ∈ state.indices := by
          unfold at1 at h ⊢
          cases hj : (if 1 ≤ position then state.indices[position - 1]? else none) with
          | none => simpa [hj, pure, Except.pure, throw, MonadExcept.throw, throwThe] using h
          | some i =>
            refine ⟨i, rfl, ?_⟩
            split at hj
            · exact List.mem_of_getElem? hj
            · cases hj
        obtain ⟨i, hi, hmem⟩ := indexRead
        exact ⟨i, hmem, by simpa [hi] using h⟩

/-- `_best_of_sample(members, idxs, options; plugin_states)`, `src/Population.jl:184-213`, with
`adj` the adjusted cost of a member. `pIsOne` is `p == 1.0`; `place` is the value
`StatsBase.sample(get_tournament_selection_weights(options))` returns when `p != 1.0`
(line 200). The adjusted costs are pure, so computing them all up front is equivalent to the
lazy calls of the Julia code. -/
def bestOfSampleCore {ι : Type} (members : List ι) (idxs : List Nat) (adj : ι → JF)
    (pIsOne : Bool) (place : Nat) : Jl ι := do
  let smp ← idxs.mapM (at1 members)
  let chosen ← chooseIdx (smp.map adj) (if pIsOne then 1 else place)
  at1 smp chosen

/-- `best_of_sample(pop, options; plugin_states)`, `src/Population.jl:176-183`: sample
`tournament_selection_n` indices of `1:pop.n` (`pop.n = length(pop.members)`), then run the
tournament on them. `none` = the index sampling did not return within `fuel`. -/
def bestOfSample {ι : Type} (draw : Nat → Nat) (fuel : Nat) (members : List ι) (ns : Nat)
    (adj : ι → JF) (pIsOne : Bool) (place : Nat) : Option (Jl ι) :=
  (sampleIndices draw fuel ns).map fun r => bestOfSampleCore members r.1 adj pIsOne place

/-- Property `pop-tournament-member`: whenever the index sampling returns (rand(1:pop.n)
stream, `tournament_selection_n ≥ 1`), `best_of_sample` returns the population's own member at
one of the sampled indices (not a copy), for every place and every cost. -/
def tournament_member : Prop :=
  ∀ (ι : Type) (members : List ι) (draw : Nat → Nat) (fuel ns : Nat) (adj : ι → JF)
    (pIsOne : Bool) (place : Nat) (idxs : List Nat) (c : Nat),
    1 ≤ ns → RandRange draw members.length → sampleIndices draw fuel ns = some (idxs, c) →
    ∃ j, j < idxs.length ∧ ∃ m, members[idxs.getD j 0 - 1]? = some m ∧
      bestOfSample draw fuel members ns adj pIsOne place = some (.ok m)

theorem at1_ok {α : Type} (xs : List α) (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ xs.length) :
    at1 xs i = .ok (xs[i - 1]'(by omega)) := by
  simp [at1, h1, List.getElem?_eq_getElem (show i - 1 < xs.length by omega)]
  rfl

theorem mapM_at1 {α : Type} (xs : List α) :
    ∀ (is : List Nat), (∀ i ∈ is, 1 ≤ i ∧ i ≤ xs.length) →
      ∃ smp, is.mapM (at1 xs) = .ok smp ∧ smp.length = is.length ∧
        ∀ j, j < is.length → smp[j]? = xs[is.getD j 0 - 1]? := by
  intro is
  induction is with
  | nil => intro _; exact ⟨[], rfl, rfl, fun j h => by simp at h⟩
  | cons i is ih =>
    intro h
    obtain ⟨smp, hs, hl, hj⟩ := ih (fun x hx => h x (by simp [hx]))
    have hi := h i (by simp)
    refine ⟨xs[i - 1]'(by omega) :: smp, ?_, by simp [hl], ?_⟩
    · rw [List.mapM_cons, at1_ok xs i hi.1 hi.2, hs]; rfl
    · intro j hj'
      cases j with
      | zero => simp [List.getElem?_eq_getElem (show i - 1 < xs.length by omega)]
      | succ j => simpa using hj j (by simpa using hj')

theorem firstMinGo_range : ∀ (cs : List JF) i bi bc, 1 ≤ bi → bi < i →
    1 ≤ firstMinGo cs i bi bc ∧ firstMinGo cs i bi bc < i + cs.length := by
  intro cs
  induction cs with
  | nil => intro i bi bc h1 h2; simp [firstMinGo]; omega
  | cons c cs ih =>
    intro i bi bc h1 h2
    simp only [firstMinGo]
    split
    · have := ih (i + 1) i c (by omega) (by omega); simp; omega
    · have := ih (i + 1) bi bc h1 (by omega); simp; omega

theorem bubble_mem (P : JF × Nat → Prop) (hd : P dflt) :
    ∀ j (buf : List (JF × Nat)), (∀ e ∈ buf, P e) → ∀ e ∈ bubble buf j, P e := by
  intro j
  induction j with
  | zero => intro buf h; simpa [bubble] using h
  | succ j ih =>
    intro buf h
    simp only [bubble]
    have hget : ∀ i, P (buf.getD i dflt) := by
      intro i
      rw [List.getD_eq_getElem?_getD]
      cases hx : buf[i]? with
      | none => simpa using hd
      | some x => simpa using h x (List.mem_of_getElem? hx)
    split
    · apply ih
      intro e he
      rcases List.mem_or_eq_of_mem_set he with he | he
      · rcases List.mem_or_eq_of_mem_set he with he | he
        · exact h e he
        · rw [he]; exact hget j
      · rw [he]; exact hget (j + 1)
    · exact h

theorem bottomkGo_mem (k n : Nat) : ∀ (xs : List JF) st i, (∀ e ∈ st.1, 1 ≤ e.2 ∧ e.2 ≤ n) →
    1 ≤ i → i + xs.length ≤ n + 1 → ∀ e ∈ (bottomkGo k st xs i).1, 1 ≤ e.2 ∧ e.2 ≤ n := by
  intro xs
  induction xs with
  | nil => intro st i h _ _; simpa [bottomkGo] using h
  | cons x xs ih =>
    intro st i h hi hl
    obtain ⟨buf, filled⟩ := st
    simp only [bottomkGo]
    apply ih _ _ _ (by omega) (by simp at hl; omega)
    simp only [bottomkStep]
    split
    · apply bubble_mem (fun e => 1 ≤ e.2 ∧ e.2 ≤ n) (by simp [dflt]; simp at hl; omega)
      intro e he
      rcases List.mem_or_eq_of_mem_set he with he | he
      · exact h e he
      · rw [he]; simp at hl ⊢; omega
    · split
      · apply bubble_mem (fun e => 1 ≤ e.2 ∧ e.2 ≤ n) (by simp [dflt]; simp at hl; omega)
        intro e he
        rcases List.mem_or_eq_of_mem_set he with he | he
        · exact h e he
        · rw [he]; simp at hl ⊢; omega
      · exact h

theorem bottomk_index (k : Nat) (xs : List JF) (hn : 1 ≤ xs.length) :
    1 ≤ ((bottomk k xs).getD (k - 1) dflt).2 ∧ ((bottomk k xs).getD (k - 1) dflt).2 ≤ xs.length := by
  have hall := bottomkGo_mem k xs.length xs (List.replicate k dflt, 0) 1
    (by intro e he; rw [List.eq_of_mem_replicate he]; simp [dflt]; omega) (by omega) (by omega)
  rw [List.getD_eq_getElem?_getD]
  cases hx : (bottomk k xs)[k - 1]? with
  | none => simp [dflt]; omega
  | some x => simpa using hall x (List.mem_of_getElem? hx)

theorem chooseIdx_range (costs : List JF) (w : Nat) (hn : 1 ≤ costs.length) :
    ∃ ch, chooseIdx costs w = .ok ch ∧ 1 ≤ ch ∧ ch ≤ costs.length := by
  unfold chooseIdx
  split
  · cases costs with
    | nil => simp at hn
    | cons c cs =>
      have := firstMinGo_range cs 2 1 c (by omega) (by omega)
      exact ⟨_, rfl, this.1, by simp; omega⟩
  · have := bottomk_index w costs hn
    exact ⟨_, rfl, this.1, this.2⟩

theorem bestOfSampleCore_member {ι : Type} (members : List ι) (idxs : List Nat) (adj : ι → JF)
    (pIsOne : Bool) (place : Nat) (hne : idxs ≠ [])
    (hb : ∀ i ∈ idxs, 1 ≤ i ∧ i ≤ members.length) :
    ∃ j, j < idxs.length ∧ ∃ m, members[idxs.getD j 0 - 1]? = some m ∧
      bestOfSampleCore members idxs adj pIsOne place = .ok m := by
  obtain ⟨smp, hs, hl, hj⟩ := mapM_at1 members idxs hb
  have hlen : 1 ≤ smp.length := by
    rw [hl]; cases idxs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  obtain ⟨ch, hch, h1, h2⟩ := chooseIdx_range (smp.map adj) (if pIsOne then 1 else place)
    (by simpa using hlen)
  simp only [List.length_map] at h2
  refine ⟨ch - 1, by omega, smp[ch - 1]'(by omega), ?_, ?_⟩
  · rw [← hj (ch - 1) (by omega), List.getElem?_eq_getElem]
  · simp only [bestOfSampleCore, hs, hch, bind, Except.bind]
    exact at1_ok smp ch h1 h2

theorem tournament_member_holds : tournament_member := by
  intro ι members draw fuel ns adj pIsOne place idxs c hns hr hs
  obtain ⟨hl, -, hb⟩ := sample_indices_valid_holds draw members.length ns fuel idxs c hr hs
  have hne : idxs ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
  obtain ⟨j, hj, m, hm, hres⟩ := bestOfSampleCore_member members idxs adj pIsOne place hne hb
  exact ⟨j, hj, m, hm, by simp [bestOfSample, hs, hres]⟩

/-- Invariant of the first-place loop (`src/Population.jl:201-206`) under `isless`: the
running best is `≤` every cost seen (with NaN last) and strictly `<` every cost seen before
its position. -/
theorem firstMinGo_spec : ∀ (cs pre : List JF) (bi : Nat) (bc : JF),
    1 ≤ bi → bi ≤ pre.length → pre[bi - 1]? = some bc →
    (∀ x ∈ pre, isless x bc = false) →
    (∀ t, t < bi - 1 → ∀ x, pre[t]? = some x → isless bc x = true) →
    ∃ bw, (pre ++ cs)[firstMinGo cs (pre.length + 1) bi bc - 1]? = some bw ∧
      1 ≤ firstMinGo cs (pre.length + 1) bi bc ∧
      (∀ x ∈ pre ++ cs, isless x bw = false) ∧
      (∀ t, t < firstMinGo cs (pre.length + 1) bi bc - 1 → ∀ x, (pre ++ cs)[t]? = some x →
        isless bw x = true) := by
  intro cs
  induction cs with
  | nil =>
    intro pre bi bc h1 h2 h3 hA hB
    refine ⟨bc, by simpa [firstMinGo] using h3, by simpa [firstMinGo] using h1, by simpa using hA, ?_⟩
    intro t ht x hx
    simp [firstMinGo] at ht hx
    exact hB t ht x hx
  | cons c cs ih =>
    intro pre bi bc h1 h2 h3 hA hB
    have happ : pre ++ c :: cs = (pre ++ [c]) ++ cs := by simp
    have hlen : (pre ++ [c]).length = pre.length + 1 := by simp
    have hpre : ∀ t, t < pre.length → (pre ++ [c])[t]? = pre[t]? := by
      intro t ht; rw [List.getElem?_append_left ht]
    simp only [firstMinGo]
    rw [happ]
    split
    · rename_i hlt
      have := ih (pre ++ [c]) (pre.length + 1) c (by omega)
        (by simp) (by simp) ?_ ?_
      · rw [hlen] at this; exact this
      · intro x hx
        simp at hx
        rcases hx with hx | rfl
        · cases hfx : isless x c with
          | false => rfl
          | true => have := isless_trans hfx hlt; rw [hA x hx] at this; exact absurd this (by decide)
        · exact isless_irrefl x
      · intro t ht x hx
        rw [hpre t (by omega)] at hx
        by_cases htb : t < bi - 1
        · exact isless_trans hlt (hB t htb x hx)
        · exact isless_of_isless_not_isless hlt (hA x (List.mem_of_getElem? hx))
    · rename_i hnlt
      have := ih (pre ++ [c]) bi bc h1 (by simp; omega)
        (by rw [hpre _ (by omega)]; exact h3) ?_ ?_
      · rw [hlen] at this; exact this
      · intro x hx
        simp at hx
        rcases hx with hx | rfl
        · exact hA x hx
        · simpa using hnlt
      · intro t ht x hx
        rw [hpre t (by omega)] at hx
        exact hB t ht x hx

/-- Property `pop-tournament-nan`: with `p == 1.0`, if some sampled member has a non-NaN
adjusted cost, the winner's adjusted cost is not NaN. -/
def tournament_nan : Prop :=
  ∀ (ι : Type) (members : List ι) (idxs : List Nat) (adj : ι → JF) (m : ι),
    (∀ i ∈ idxs, 1 ≤ i ∧ i ≤ members.length) → idxs.Nodup →
    (∃ i ∈ idxs, ∃ x, members[i - 1]? = some x ∧ isNaN (adj x) = false) →
    bestOfSampleCore members idxs adj true 1 = .ok m → isNaN (adj m) = false

theorem tournament_nan_holds : tournament_nan := by
  intro ι members idxs adj m hb _ ⟨i, hi, x, hx, hxn⟩ hres
  obtain ⟨smp, hs, hl, hj⟩ := mapM_at1 members idxs hb
  obtain ⟨t, ht, hit⟩ := List.getElem_of_mem hi
  have hxmem : adj x ∈ smp.map adj := by
    have hst : smp[t]? = some x := by
      have h1 := hj t (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at h1
      simpa [hit, hx] using h1
    exact List.mem_map.mpr ⟨x, List.mem_of_getElem? hst, rfl⟩
  cases hcs : smp.map adj with
  | nil => rw [hcs] at hxmem; simp at hxmem
  | cons c cs =>
    obtain ⟨bw, hbw, h1, hA, _⟩ := firstMinGo_spec cs [c] 1 c (by omega)
      (by simp) rfl (by simp [isless_irrefl]) (by intro _ h; omega)
    simp only [List.length_singleton, List.singleton_append, Nat.reduceAdd] at hbw h1 hA
    have hch : chooseIdx (smp.map adj) 1 = .ok (firstMinGo cs 2 1 c) := by
      rw [hcs]; rfl
    have hwlt : firstMinGo cs 2 1 c ≤ smp.length := by
      have hlen : (c :: cs).length = smp.length := by rw [← hcs, List.length_map]
      have := (List.getElem?_eq_some_iff.1 hbw).1
      omega
    simp only [bestOfSampleCore, hs, ↓reduceIte, hch, bind, Except.bind,
      at1_ok smp _ h1 hwlt, Except.ok.injEq] at hres
    subst hres
    have hbw' : adj (smp[firstMinGo cs 2 1 c - 1]'(by omega)) = bw := by
      have hmap : (smp.map adj)[firstMinGo cs 2 1 c - 1]? = (smp[firstMinGo cs 2 1 c - 1]?).map adj := by
        simp
      rw [hcs, hbw, List.getElem?_eq_getElem (by omega)] at hmap
      simp at hmap
      exact hmap.symm
    rw [hbw']
    cases hbw_eq : bw with
    | nan =>
      have hlt := isless_of_not_nan hxn
      have hge := hA (adj x) (hcs ▸ hxmem)
      rw [hbw_eq] at hge
      rw [hlt] at hge
      cases hge
    | _ => rfl

/-- Property `pop-tournament-first-min`: when the first place is taken (`p == 1.0`, or the
drawn place is 1) and no sampled adjusted cost is NaN, the winner has the minimal adjusted cost
`L(member.cost) * prod(multipliers)` of the sample, and it is the first sampled position with
that cost (strict `<`). -/
def tournament_first_min : Prop :=
  ∀ (ι : Type) (members : List ι) (idxs : List Nat) (adj : ι → JF) (pIsOne : Bool) (place : Nat),
    (∀ i ∈ idxs, 1 ≤ i ∧ i ≤ members.length) → idxs ≠ [] → (pIsOne = true ∨ place = 1) →
    (∀ i ∈ idxs, ∀ x, members[i - 1]? = some x → isNaN (adj x) = false) →
    ∃ j, j < idxs.length ∧ ∃ m, members[idxs.getD j 0 - 1]? = some m ∧
      bestOfSampleCore members idxs adj pIsOne place = .ok m ∧
      ∀ i, i < idxs.length → ∀ x, members[idxs.getD i 0 - 1]? = some x →
        flt (adj x) (adj m) = false ∧ (i < j → flt (adj m) (adj x) = true)

theorem tournament_first_min_holds : tournament_first_min := by
  intro ι members idxs adj pIsOne place hb hne hw hnan
  obtain ⟨smp, hs, hl, hj⟩ := mapM_at1 members idxs hb
  have hwin : (if pIsOne = true then 1 else place) = 1 := by
    rcases hw with h | h <;> simp [h]
  have hsn : ∀ x ∈ smp.map adj, isNaN x = false := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨t, ht, hxt⟩ := List.getElem_of_mem hx
    have h1 := hj t (by omega)
    rw [List.getElem?_eq_getElem ht, hxt] at h1
    have hmem : idxs.getD t 0 ∈ idxs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    exact hnan _ hmem x h1.symm
  cases hcs : smp.map adj with
  | nil => cases idxs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hl; cases smp with
      | nil => simp at hl
      | cons _ _ => simp at hcs
  | cons c cs =>
    rw [hcs] at hsn
    obtain ⟨bw, hbw, h1, hA, hB⟩ := firstMinGo_spec cs [c] 1 c (by omega)
      (by simp) rfl (by simp [isless_irrefl]) (by intro t ht; omega)
    simp only [List.length_singleton, List.singleton_append] at hbw h1 hA hB
    have hlenc : cs.length + 1 = smp.length := by
      have := congrArg List.length hcs; simp at this; omega
    have hch : chooseIdx (smp.map adj) (if pIsOne = true then 1 else place) =
        .ok (firstMinGo cs 2 1 c) := by
      rw [hwin, hcs]; rfl
    have hwlt : firstMinGo cs 2 1 c ≤ smp.length := by
      have := (List.getElem?_eq_some_iff.1 hbw).1; simp at this; omega
    have hmap : ∀ t, t < smp.length → (smp.map adj)[t]? = (smp[t]?).map adj := by
      intro t _; simp
    have hbwn : isNaN bw = false := hsn bw (List.mem_of_getElem? hbw)
    refine ⟨firstMinGo cs 2 1 c - 1, by omega, smp[firstMinGo cs 2 1 c - 1]'(by omega), ?_, ?_, ?_⟩
    · rw [← hj _ (by omega), List.getElem?_eq_getElem]
    · simp only [bestOfSampleCore, hs, hch, bind, Except.bind]
      exact at1_ok smp _ h1 hwlt
    · have hbw' : adj (smp[firstMinGo cs 2 1 c - 1]'(by omega)) = bw := by
        have := hmap (firstMinGo cs 2 1 c - 1) (by omega)
        rw [hcs, hbw, List.getElem?_eq_getElem (by omega)] at this
        simp at this; exact this.symm
      rw [hbw']
      intro i hi x hx
      rw [← hj i hi] at hx
      have hxi : (c :: cs)[i]? = some (adj x) := by
        rw [← hcs]; simp [hx]
      have hxn : isNaN (adj x) = false := hsn _ (List.mem_of_getElem? hxi)
      refine ⟨?_, fun hij => ?_⟩
      · rw [← isless_eq_flt_of_not_nan hxn hbwn]
        exact hA _ (List.mem_of_getElem? hxi)
      · rw [← isless_eq_flt_of_not_nan hbwn hxn]
        exact hB i hij _ hxi

/-- Number of costs in `l` satisfying `f`. -/
def countIf (l : List JF) (f : JF → Bool) : Nat := (l.filter f).length

/-- Sorted insertion by `isless` on the first component. -/
private def insertSorted (p : JF × Nat) : List (JF × Nat) → List (JF × Nat)
  | [] => [p]
  | q :: qs => if isless p.1 q.1 then p :: q :: qs else q :: insertSorted p qs

private theorem insertSorted_length (p : JF × Nat) :
    ∀ l : List (JF × Nat), (insertSorted p l).length = l.length + 1
  | [] => rfl
  | q :: qs => by
    simp only [insertSorted]
    split <;> simp [insertSorted_length p qs]

private theorem mem_insertSorted (p x : JF × Nat) :
    ∀ l : List (JF × Nat), x ∈ insertSorted p l ↔ x = p ∨ x ∈ l
  | [] => by simp [insertSorted]
  | q :: qs => by
    simp only [insertSorted]
    split
    · simp
    · simp only [List.mem_cons, mem_insertSorted p x qs]
      grind

private theorem insertSorted_append_of_isless (p b : JF × Nat) :
    ∀ pre : List (JF × Nat), isless p.1 b.1 = true →
      insertSorted p (pre ++ [b]) = insertSorted p pre ++ [b]
  | [], h => by simp [insertSorted, h]
  | q :: qs, h => by
    simp only [List.cons_append, insertSorted]
    split
    · rfl
    · simp [insertSorted_append_of_isless p b qs h]

private theorem insertSorted_of_ge (p : JF × Nat) :
    ∀ pre : List (JF × Nat), (∀ q ∈ pre, isless p.1 q.1 = false) →
      insertSorted p pre = pre ++ [p]
  | [], _ => rfl
  | q :: qs, h => by
    simp [insertSorted, h q (by simp),
      insertSorted_of_ge p qs (fun x hx => h x (by simp [hx]))]

private theorem insertSorted_pairwise (p : JF × Nat) :
    ∀ l : List (JF × Nat), l.Pairwise (fun a b => isless b.1 a.1 = false) →
      (insertSorted p l).Pairwise (fun a b => isless b.1 a.1 = false)
  | [], _ => by simp [insertSorted]
  | q :: qs, hs => by
    rw [List.pairwise_cons] at hs
    simp only [insertSorted]
    split
    · rename_i hlt
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr hs⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact isless_asymm hlt
      · exact isless_asymm (isless_of_isless_not_isless hlt (hs.1 x hx))
    · rename_i hnlt
      rw [List.pairwise_cons]
      refine ⟨?_, insertSorted_pairwise p qs hs.2⟩
      intro x hx
      rcases (mem_insertSorted p x qs).mp hx with rfl | hx
      · simpa using hnlt
      · exact hs.1 x hx

private theorem insertSorted_nodup_snd (p : JF × Nat) :
    ∀ l : List (JF × Nat), (l.map Prod.snd).Nodup → p.2 ∉ l.map Prod.snd →
      ((insertSorted p l).map Prod.snd).Nodup
  | [], _, _ => by simp [insertSorted]
  | q :: qs, hn, hf => by
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn hf
    simp only [insertSorted]
    split
    · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨hf, hn⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, insertSorted_nodup_snd p qs hn.2 hf.2⟩
      intro hm
      obtain ⟨x, hx, hxs⟩ := List.mem_map.mp hm
      rcases (mem_insertSorted p x qs).mp hx with rfl | hx
      · exact hf.1 hxs
      · exact hn.1 (List.mem_map.mpr ⟨x, hx, hxs⟩)

private theorem dropLast_append_getLast {α : Type} :
    ∀ (l : List α) (h : l ≠ []), l.dropLast ++ [l.getLast h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: b :: xs, _ => by
    simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b xs), List.cons_append,
      List.getLast_cons (List.cons_ne_nil b xs)]
    congr 1
    exact dropLast_append_getLast (b :: xs) (List.cons_ne_nil b xs)

private theorem set_append_right {α : Type} :
    ∀ (xs ys : List α) (i : Nat) (x : α), xs.length ≤ i →
      (xs ++ ys).set i x = xs ++ ys.set (i - xs.length) x
  | [], ys, i, x, _ => by simp
  | a :: xs, ys, 0, _, h => by simp at h
  | a :: xs, ys, i + 1, x, h => by
    simp only [List.cons_append, List.set_cons_succ, List.length_cons]
    rw [set_append_right xs ys i x (by simp at h; omega)]
    simp [Nat.succ_sub_succ]

private theorem bubble_insertSorted : ∀ (n : Nat) (pre suf : List (JF × Nat)) (p : JF × Nat),
    pre.length = n → pre.Pairwise (fun a b => isless b.1 a.1 = false) →
    bubble (pre ++ p :: suf) n = insertSorted p pre ++ suf := by
  intro n
  induction n with
  | zero =>
    intro pre suf p hlen _
    cases pre with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro pre suf p hlen hsort
    have hne : pre ≠ [] := by intro h; subst h; simp at hlen
    let pre' := pre.dropLast
    let b := pre.getLast hne
    have hsplit : pre = pre' ++ [b] := (dropLast_append_getLast pre hne).symm
    rw [hsplit] at hlen hsort ⊢
    have hlen' : pre'.length = n := by simp at hlen; omega
    have hsort' : pre'.Pairwise (fun a b => isless b.1 a.1 = false) ∧
        ∀ q ∈ pre', isless b.1 q.1 = false := by
      rw [List.pairwise_append] at hsort
      exact ⟨hsort.1, fun q hq => hsort.2.2 q hq b (by simp)⟩
    have hget1 : ((pre' ++ [b]) ++ p :: suf).getD (n + 1) dflt = p := by
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.singleton_append,
        List.getElem?_append_right (by omega)]
      simp [hlen']
    have hget0 : ((pre' ++ [b]) ++ p :: suf).getD n dflt = b := by
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.singleton_append,
        List.getElem?_append_right (by omega)]
      simp [hlen']
    have hswap : (((pre' ++ [b]) ++ p :: suf).set (n + 1) b).set n p =
        pre' ++ p :: b :: suf := by
      rw [List.append_assoc, List.singleton_append,
        set_append_right pre' (b :: p :: suf) (n + 1) b (by omega),
        show n + 1 - pre'.length = 1 by omega]
      simp only [List.set_cons_succ, List.set_cons_zero]
      rw [set_append_right pre' (b :: b :: suf) n p (by omega),
        show n - pre'.length = 0 by omega]
      simp
    simp only [bubble, hget1, hget0]
    split
    · rename_i hlt
      rw [hswap, ih pre' (b :: suf) p hlen' hsort'.1,
        insertSorted_append_of_isless p b pre' hlt]
      simp
    · rename_i hnlt
      have hnlt' : isless p.1 b.1 = false := by simpa using hnlt
      have hall : ∀ q ∈ pre' ++ [b], isless p.1 q.1 = false := by
        intro q hq
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact not_isless_trans (hsort'.2 q hq) hnlt'
        · exact hnlt'
      rw [insertSorted_of_ge p (pre' ++ [b]) hall]
      simp

private structure BottomkInv (k : Nat) (seen : List JF) (buf : List (JF × Nat)) (filled : Nat) :
    Prop where
  hlen : buf.length = k
  hfilled : filled = min k seen.length
  hsort : (buf.take filled).Pairwise (fun a b => isless b.1 a.1 = false)
  hnodup : ((buf.take filled).map Prod.snd).Nodup
  hmem : ∀ p ∈ buf.take filled, 1 ≤ p.2 ∧ p.2 ≤ seen.length ∧ seen[p.2 - 1]? = some p.1
  hfull : filled < k → ∀ j, j < seen.length → j + 1 ∈ (buf.take filled).map Prod.snd
  homit : ∀ j v, j < seen.length → seen[j]? = some v →
    j + 1 ∉ (buf.take filled).map Prod.snd → ∀ p ∈ buf.take filled, isless v p.1 = false

private theorem set_eq_take_cons_drop {α : Type} :
    ∀ (l : List α) (i : Nat) (x : α), i < l.length →
      l.set i x = l.take i ++ x :: l.drop (i + 1)
  | [], _, _, h => by simp at h
  | _ :: xs, 0, x, _ => by simp
  | a :: xs, i + 1, x, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append, List.drop_succ_cons]
    congr 1
    exact set_eq_take_cons_drop xs i x (by simp at h; omega)

private theorem bottomkStep_inv (k : Nat) (hk : 1 ≤ k) (seen : List JF)
    (buf : List (JF × Nat)) (filled : Nat) (x : JF) (inv : BottomkInv k seen buf filled) :
    let st' := bottomkStep k (buf, filled) x (seen.length + 1)
    BottomkInv k (seen ++ [x]) st'.1 st'.2 := by
  have hseen_old : ∀ j, j < seen.length → (seen ++ [x])[j]? = seen[j]? := fun j hj =>
    List.getElem?_append_left hj
  have hseen_new : (seen ++ [x])[seen.length]? = some x := by simp
  have hfresh : seen.length + 1 ∉ (buf.take filled).map Prod.snd := by
    intro hm
    obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hm
    have := (inv.hmem p hp).2.1
    omega
  simp only [bottomkStep]
  by_cases hf : filled < k
  · simp only [hf, ↓reduceIte]
    have hfeq : filled = seen.length := by have := inv.hfilled; omega
    have hflen : (buf.take filled).length = filled := by
      rw [List.length_take, inv.hlen]; omega
    have hsplit : buf.set filled (x, seen.length + 1) =
        buf.take filled ++ (x, seen.length + 1) :: buf.drop (filled + 1) :=
      set_eq_take_cons_drop buf filled (x, seen.length + 1) (by rw [inv.hlen]; exact hf)
    have hbub : bubble (buf.set filled (x, seen.length + 1)) filled =
        insertSorted (x, seen.length + 1) (buf.take filled) ++ buf.drop (filled + 1) := by
      rw [hsplit]
      exact bubble_insertSorted filled (buf.take filled) (buf.drop (filled + 1))
        (x, seen.length + 1) hflen inv.hsort
    have htake : (bubble (buf.set filled (x, seen.length + 1)) filled).take (filled + 1) =
        insertSorted (x, seen.length + 1) (buf.take filled) := by
      rw [hbub, List.take_append_of_le_length (by rw [insertSorted_length, hflen]; omega)]
      exact List.take_of_length_le (by rw [insertSorted_length, hflen]; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbub, List.length_append, insertSorted_length, hflen, List.length_drop, inv.hlen]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [htake]; exact insertSorted_pairwise _ _ inv.hsort
    · rw [htake]; exact insertSorted_nodup_snd _ _ inv.hnodup hfresh
    · rw [htake]
      intro p hp
      rcases (mem_insertSorted _ _ _).mp hp with rfl | hp
      · exact ⟨by omega, by simp, by simp⟩
      · obtain ⟨h1, h2, h3⟩ := inv.hmem p hp
        exact ⟨h1, by simp; omega, by rw [hseen_old _ (by omega)]; exact h3⟩
    · intro _ j hj
      rw [htake]
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hje : j < seen.length
      · obtain ⟨p, hp, hps⟩ := List.mem_map.mp (inv.hfull hf j hje)
        exact List.mem_map.mpr ⟨p, (mem_insertSorted _ _ _).mpr (.inr hp), hps⟩
      · have : j = seen.length := by omega
        subst this
        exact List.mem_map.mpr ⟨(x, seen.length + 1), (mem_insertSorted _ _ _).mpr (.inl rfl), rfl⟩
    · intro j v hj _ hnot
      exfalso
      apply hnot
      rw [htake]
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hje : j < seen.length
      · obtain ⟨p, hp, hps⟩ := List.mem_map.mp (inv.hfull hf j hje)
        exact List.mem_map.mpr ⟨p, (mem_insertSorted _ _ _).mpr (.inr hp), hps⟩
      · have : j = seen.length := by omega
        subst this
        exact List.mem_map.mpr ⟨(x, seen.length + 1), (mem_insertSorted _ _ _).mpr (.inl rfl), rfl⟩
  · simp only [hf, ↓reduceIte]
    have hfeq : filled = k := by have := inv.hfilled; omega
    have hkle : k ≤ seen.length := by have := inv.hfilled; omega
    have htake_eq : buf.take filled = buf := List.take_of_length_le (by rw [inv.hlen, hfeq]; omega)
    have hne : buf ≠ [] := by
      intro h; have hl := inv.hlen; rw [h] at hl; simp at hl; omega
    let pre := buf.dropLast
    let last := buf.getLast hne
    have hsplit : buf = pre ++ [last] := (dropLast_append_getLast buf hne).symm
    have hpre_len : pre.length = k - 1 := by
      have := congrArg List.length hsplit; simp [inv.hlen] at this; omega
    have hlast : buf.getD (k - 1) dflt = last := by
      rw [List.getD_eq_getElem?_getD, hsplit, List.getElem?_append_right (by omega)]
      simp [hpre_len]
    have hsort_buf : (pre ++ [last]).Pairwise (fun a b => isless b.1 a.1 = false) := by
      rw [← hsplit, ← htake_eq]; exact inv.hsort
    rw [List.pairwise_append] at hsort_buf
    have hpre_sort : pre.Pairwise (fun a b => isless b.1 a.1 = false) := hsort_buf.1
    have hlast_ge : ∀ q ∈ pre, isless last.1 q.1 = false := fun q hq => hsort_buf.2.2 q hq last (by simp)
    rw [hlast]
    split
    · rename_i hlt
      have hset : buf.set (k - 1) (x, seen.length + 1) = pre ++ [(x, seen.length + 1)] := by
        conv => lhs; rw [hsplit]
        rw [set_append_right pre [last] (k - 1) _ (by omega), show k - 1 - pre.length = 0 by omega]
        rfl
      have hbub : bubble (buf.set (k - 1) (x, seen.length + 1)) (k - 1) =
          insertSorted (x, seen.length + 1) pre := by
        rw [hset]
        simpa using bubble_insertSorted (k - 1) pre [] (x, seen.length + 1) hpre_len hpre_sort
      have hlen' : (insertSorted (x, seen.length + 1) pre).length = k := by
        rw [insertSorted_length, hpre_len]; omega
      have htake' : (bubble (buf.set (k - 1) (x, seen.length + 1)) (k - 1)).take filled =
          insertSorted (x, seen.length + 1) pre := by
        rw [hbub]; exact List.take_of_length_le (by omega)
      have hnodup_pre : (pre.map Prod.snd).Nodup := by
        have := inv.hnodup
        rw [htake_eq, hsplit, List.map_append, List.nodup_append] at this
        exact this.1
      have hfresh_pre : seen.length + 1 ∉ pre.map Prod.snd := by
        intro hm; apply hfresh
        rw [htake_eq, hsplit, List.map_append]; exact List.mem_append_left _ hm
      refine ⟨by rw [hbub]; exact hlen', by simp; omega,
        by rw [htake']; exact insertSorted_pairwise _ _ hpre_sort,
        by rw [htake']; exact insertSorted_nodup_snd _ _ hnodup_pre hfresh_pre, ?_,
        fun h => absurd h (by omega), ?_⟩
      · rw [htake']
        intro p hp
        rcases (mem_insertSorted _ _ _).mp hp with rfl | hp
        · exact ⟨by omega, by simp, by simp⟩
        · have hpbuf : p ∈ buf.take filled := by
            rw [htake_eq, hsplit]; exact List.mem_append_left _ hp
          obtain ⟨h1, h2, h3⟩ := inv.hmem p hpbuf
          exact ⟨h1, by simp; omega, by rw [hseen_old _ (by omega)]; exact h3⟩
      · rw [htake']
        intro j v hj hsv hnot p hp
        simp only [List.length_append, List.length_singleton] at hj
        have hjne : j ≠ seen.length := by
          intro he; subst he; apply hnot
          exact List.mem_map.mpr ⟨(x, seen.length + 1), (mem_insertSorted _ _ _).mpr (.inl rfl), rfl⟩
        have hjlt : j < seen.length := by omega
        rw [hseen_old j hjlt] at hsv
        have hlast_mem : last ∈ buf.take filled := by
          rw [htake_eq, hsplit]; simp
        by_cases hin : j + 1 ∈ (buf.take filled).map Prod.snd
        · rw [htake_eq, hsplit, List.map_append, List.mem_append] at hin
          rcases hin with hin | hin
          · exfalso; apply hnot
            obtain ⟨q, hq, hqs⟩ := List.mem_map.mp hin
            exact List.mem_map.mpr ⟨q, (mem_insertSorted _ _ _).mpr (.inr hq), hqs⟩
          · simp only [List.map_singleton, List.mem_singleton] at hin
            have hlmem := inv.hmem last hlast_mem
            have hvlast : v = last.1 := by
              have h1 := hlmem.2.2
              rw [← hin, Nat.add_sub_cancel, hsv] at h1
              exact Option.some.inj h1
            subst hvlast
            rcases (mem_insertSorted _ _ _).mp hp with rfl | hp
            · exact isless_asymm hlt
            · exact hlast_ge p hp
        · have hvall := inv.homit j v hjlt hsv hin
          have hvlast : isless v last.1 = false := hvall last hlast_mem
          rcases (mem_insertSorted _ _ _).mp hp with rfl | hp
          · exact isless_asymm (isless_of_isless_not_isless hlt hvlast)
          · exact hvall p (by rw [htake_eq, hsplit]; exact List.mem_append_left _ hp)
    · rename_i hnlt
      have hnlt' : isless x last.1 = false := by simpa using hnlt
      refine ⟨inv.hlen, by simp; omega, inv.hsort, inv.hnodup, ?_,
        fun h => absurd h (by omega), ?_⟩
      · intro p hp
        obtain ⟨h1, h2, h3⟩ := inv.hmem p hp
        exact ⟨h1, by simp; omega, by rw [hseen_old _ (by omega)]; exact h3⟩
      · intro j v hj hsv hnot p hp
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hjlt : j < seen.length
        · rw [hseen_old j hjlt] at hsv
          exact inv.homit j v hjlt hsv hnot p hp
        · have hje : j = seen.length := by omega
          subst hje
          rw [hseen_new] at hsv
          cases hsv
          rw [htake_eq, hsplit, List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact not_isless_trans (hlast_ge p hp) hnlt'
          · exact hnlt'

private theorem bottomkGo_inv (k : Nat) (hk : 1 ≤ k) :
    ∀ (xs seen : List JF) (buf : List (JF × Nat)) (filled : Nat),
      BottomkInv k seen buf filled →
      let st' := bottomkGo k (buf, filled) xs (seen.length + 1)
      BottomkInv k (seen ++ xs) st'.1 st'.2 := by
  intro xs
  induction xs with
  | nil =>
    intro seen buf filled inv
    simpa [bottomkGo] using inv
  | cons x xs ih =>
    intro seen buf filled inv
    have inv1 := bottomkStep_inv k hk seen buf filled x inv
    have hlen : (seen ++ [x]).length = seen.length + 1 := by simp
    have inv2 := ih (seen ++ [x]) _ _ inv1
    simpa [bottomkGo, hlen, List.append_assoc] using inv2

theorem bottomk_spec (k : Nat) (xs : List JF) (hk : 1 ≤ k) (hle : k ≤ xs.length) :
    let out := bottomk k xs
    out.length = k ∧ (out.map Prod.snd).Nodup ∧
      out.Pairwise (fun a b => isless b.1 a.1 = false) ∧
      (∀ p ∈ out, 1 ≤ p.2 ∧ p.2 ≤ xs.length ∧ xs[p.2 - 1]? = some p.1) ∧
      (∀ j v, j < xs.length → xs[j]? = some v → j + 1 ∉ out.map Prod.snd →
        ∀ p ∈ out, isless v p.1 = false) := by
  have init : BottomkInv k [] (List.replicate k dflt) 0 :=
    ⟨List.length_replicate, by simp, by simp, by simp, by simp, by simp, by simp⟩
  have h := bottomkGo_inv k hk xs [] (List.replicate k dflt) 0 init
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h
  have hf : (bottomkGo k (List.replicate k dflt, 0) xs 1).2 = k := by
    rw [h.hfilled]; omega
  have htake : (bottomk k xs).take (bottomkGo k (List.replicate k dflt, 0) xs 1).2 = bottomk k xs := by
    rw [hf]; exact List.take_of_length_le (by rw [bottomk, h.hlen]; omega)
  refine ⟨h.hlen, ?_, ?_, ?_, ?_⟩
  · have hnd := h.hnodup; change ((bottomk k xs).take _).map Prod.snd |>.Nodup at hnd
    rw [htake] at hnd; exact hnd
  · have hs := h.hsort; change ((bottomk k xs).take _).Pairwise _ at hs
    rw [htake] at hs; exact hs
  · have hm := h.hmem; change ∀ p ∈ (bottomk k xs).take _, _ at hm
    rw [htake] at hm; exact hm
  · have ho := h.homit; change ∀ j v, _ → _ → j + 1 ∉ ((bottomk k xs).take _).map Prod.snd →
      ∀ p ∈ (bottomk k xs).take _, _ at ho
    rw [htake] at ho; exact ho

private def idxFilter {α : Type} (l : List α) (f : α → Bool) : List Nat :=
  (List.range l.length).filter fun i => (l[i]?.map f).getD false

private theorem filter_length_eq_idx_filter {α : Type} (l : List α) (f : α → Bool) :
    (l.filter f).length = (idxFilter l f).length := by
  induction l with
  | nil => rfl
  | cons a xs ih =>
    simp only [idxFilter, List.filter_cons, List.length_cons, List.range_succ_eq_map,
      List.getElem?_cons_zero, List.filter_map, Function.comp_def, List.getElem?_cons_succ,
      List.length_map, Option.map_some, Option.getD_some] at ih ⊢
    cases f a <;> simp [ih]

private theorem filter_map_eq_mapM_ok {α : Type} (xs : List α) :
    ∀ (is : List Nat) (smp : List α), (∀ i ∈ is, 1 ≤ i ∧ i ≤ xs.length) →
      is.mapM (at1 xs) = .ok smp →
      (is.filterMap fun i => xs[i - 1]?) = smp := by
  intro is
  induction is with
  | nil => intro smp _ h; cases h; rfl
  | cons i is ih =>
    intro smp hb h
    have hi := hb i (by simp)
    rw [List.mapM_cons, at1_ok xs i hi.1 hi.2] at h
    cases hm : is.mapM (at1 xs) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok rest =>
      simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [List.filterMap_cons, List.getElem?_eq_getElem (show i - 1 < xs.length by omega),
        ih rest (fun x hx => hb x (by simp [hx])) hm]

private theorem nodup_map_of_inj_on {α β : Type} (f : α → β) :
    ∀ l : List α, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: l, hn, hinj => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj_on f l hn.2 (fun x hx y hy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have heq := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    exact hn.1 (heq ▸ hb)

/-- Property `pop-tournament-rank`: when place `k ≥ 2` is drawn, the winner holds the `k`-th
place of the sample in the `isless` order of adjusted costs (ties in any order): fewer than `k`
sampled costs are smaller than the winner's and at least `k` are `<=` it. This is the
selection rule of `tournament_selection_p` ("the next fittest with probability p*(1-p), and so
forth", `src/Options.jl:381-383`). -/
def tournament_rank : Prop :=
  ∀ (ι : Type) (members : List ι) (idxs : List Nat) (adj : ι → JF) (place : Nat) (m : ι),
    (∀ i ∈ idxs, 1 ≤ i ∧ i ≤ members.length) → idxs.Nodup → 2 ≤ place → place ≤ idxs.length →
    bestOfSampleCore members idxs adj false place = .ok m →
    countIf ((idxs.filterMap fun i => members[i - 1]?).map adj) (fun x => isless x (adj m)) < place ∧
    place ≤ countIf ((idxs.filterMap fun i => members[i - 1]?).map adj) (fun x => !isless (adj m) x)

theorem tournament_rank_holds : tournament_rank := by
  intro ι members idxs adj place m hb _ hp hple hres
  obtain ⟨smp, hs, hl, _⟩ := mapM_at1 members idxs hb
  have hfm : (idxs.filterMap fun i => members[i - 1]?) = smp :=
    filter_map_eq_mapM_ok members idxs smp hb hs
  rw [hfm]
  let costs := smp.map adj
  have hclen : costs.length = idxs.length := by simp [costs, hl]
  obtain ⟨hout_len, hout_nd, hout_sort, hout_mem, hout_omit⟩ :=
    bottomk_spec place costs (by omega) (by omega)
  have hne_out : bottomk place costs ≠ [] := by intro h; rw [h] at hout_len; simp at hout_len; omega
  let pre := (bottomk place costs).dropLast
  let last := (bottomk place costs).getLast hne_out
  have hsplit : bottomk place costs = pre ++ [last] :=
    (dropLast_append_getLast (bottomk place costs) hne_out).symm
  have hpre_len : pre.length = place - 1 := by
    have := congrArg List.length hsplit; simp [hout_len] at this; omega
  have hlast_get : (bottomk place costs).getD (place - 1) dflt = last := by
    rw [List.getD_eq_getElem?_getD, hsplit, List.getElem?_append_right (by omega)]
    simp [hpre_len]
  have hch : chooseIdx costs place = .ok last.2 := by
    unfold chooseIdx
    rw [ite_eq_right (by omega), hlast_get]; rfl
  have hlast_mem : last ∈ bottomk place costs := by rw [hsplit]; simp
  obtain ⟨hl1, hl2, hl3⟩ := hout_mem last hlast_mem
  have hl2' : last.2 ≤ smp.length := by simp [costs] at hl2; exact hl2
  simp only [bestOfSampleCore, hs, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at hres
  change (chooseIdx costs place >>= at1 smp) = .ok m at hres
  rw [hch] at hres
  simp only [bind, Except.bind, at1_ok smp last.2 hl1 hl2', Except.ok.injEq] at hres
  subst hres
  have hval : adj (smp[last.2 - 1]'(by omega)) = last.1 := by
    have hmap : costs[last.2 - 1]? = (smp[last.2 - 1]?).map adj := by simp [costs]
    rw [hl3, List.getElem?_eq_getElem (by omega)] at hmap
    simp at hmap
    exact hmap.symm
  rw [hval]
  have hsort_split := hout_sort
  rw [hsplit, List.pairwise_append] at hsort_split
  have hlast_ge : ∀ p ∈ pre, isless last.1 p.1 = false := fun p hp =>
    hsort_split.2.2 p hp last (by simp)
  constructor
  · unfold countIf
    rw [filter_length_eq_idx_filter]
    let ltIdxs := idxFilter costs (fun x => isless x last.1)
    have hnd_lt : (ltIdxs.map (· + 1)).Nodup := by
      have h1 : ltIdxs.Nodup := List.Pairwise.filter _ List.nodup_range
      exact nodup_map_of_inj_on (· + 1) ltIdxs h1 (fun _ _ _ _ h => by omega)
    have hsub : ∀ idx ∈ ltIdxs.map (· + 1), idx ∈ pre.map Prod.snd := by
      intro idx hidx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hidx
      dsimp only [ltIdxs, idxFilter] at hj
      rw [List.mem_filter, List.mem_range] at hj
      obtain ⟨hjlt, hmatch⟩ := hj
      have hcj : costs[j]? = some (costs[j]'hjlt) := List.getElem?_eq_getElem hjlt
      rw [hcj] at hmatch
      simp only [Option.map_some, Option.getD_some] at hmatch
      have hin : j + 1 ∈ (bottomk place costs).map Prod.snd := by
        apply Classical.byContradiction
        intro hnot
        have := hout_omit j (costs[j]'hjlt) hjlt hcj hnot last hlast_mem
        rw [this] at hmatch
        cases hmatch
      rw [hsplit, List.map_append, List.mem_append, List.map_singleton, List.mem_singleton] at hin
      rcases hin with hin | heq
      · exact hin
      · exfalso
        have h1 := hl3
        rw [← heq, Nat.add_sub_cancel, hcj, Option.some.injEq] at h1
        rw [h1, isless_irrefl] at hmatch
        cases hmatch
    have hle_lt := nodup_length_le_of_subset (ltIdxs.map (· + 1)) (pre.map Prod.snd) hnd_lt hsub
    simp only [List.length_map, hpre_len] at hle_lt
    change ltIdxs.length < place
    omega
  · unfold countIf
    rw [filter_length_eq_idx_filter]
    let leIdxs := idxFilter costs (fun x => !isless last.1 x)
    have hnd_out : ((bottomk place costs).map fun p => p.2 - 1).Nodup := by
      have h1 : ((bottomk place costs).map Prod.snd).Nodup := hout_nd
      rw [show ((bottomk place costs).map fun p => p.2 - 1) =
          ((bottomk place costs).map Prod.snd).map (· - 1) by simp [List.map_map, Function.comp_def]]
      apply nodup_map_of_inj_on (· - 1) _ h1
      intro a ha b hb hab
      obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp ha
      obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
      have := (hout_mem pa hpa).1
      have := (hout_mem pb hpb).1
      omega
    have hsub : ∀ j ∈ (bottomk place costs).map (fun p => p.2 - 1), j ∈ leIdxs := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      obtain ⟨hp1, hp2, hp3⟩ := hout_mem p hp
      dsimp only [leIdxs, idxFilter]
      rw [List.mem_filter, List.mem_range]
      refine ⟨by omega, ?_⟩
      rw [hp3]
      simp only [Option.map_some, Option.getD_some]
      rw [hsplit, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · simp [hlast_ge p hp]
      · simp [isless_irrefl]
    have hle_le := nodup_length_le_of_subset _ _ hnd_out hsub
    simp only [List.length_map, hout_len] at hle_le
    change place ≤ leIdxs.length
    exact hle_le

/-! ## Satisfiable preconditions -/

example : RandRange (fun c => c % 3 + 1) 3 ∧
    sampleIndices (fun c => c % 3 + 1) 5 2 = some ([1, 2], 2) := by
  refine ⟨fun c => ⟨by dsimp only; omega, by dsimp only; omega⟩, by decide⟩

example : 1 ≤ 3 ∧ (0 : Rat) < 1 ∧ (1 : Rat) ≤ 1 ∧ (0 : Rat) ≤ 0 ∧ (0 : Rat) < 1 := by
  decide

example : (∀ i ∈ [1, 2], 1 ≤ i ∧ i ≤ [10, 20].length) ∧ [1, 2] ≠ [] ∧ [1, 2].Nodup ∧
    (∀ i ∈ [1, 2], ∀ x, [10, 20][i - 1]? = some x →
      isNaN ((fun m : Nat => if m = 10 then JF.fin 3 else .posInf) x) = false) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i hi x hx
  simp at hi
  rcases hi with rfl | rfl <;> simp at hx <;> subst hx <;> rfl
end SymReg.Population
