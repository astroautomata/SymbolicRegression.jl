import SymReg.Loss.Aggregation

namespace SymReg.Loss
open DynExpr

private def unweighted (p : LossPrecision) (f : JF → JF → Rat) (x y : List JF) : Jl JF :=
  lossArray x y (.supervised (fun pred target => .ok (.fin (f pred target)))) true p

private def weighted (p : LossPrecision) (f : JF → JF → Rat) (x y : List JF)
    (c : Rat) : Jl JF :=
  weightedLoss x y (List.replicate x.length (.fin c))
    (.supervised (fun pred target => .ok (.fin (f pred target)))) true p

/-- Equal finite nonzero weights should preserve the finiteness of a finite unweighted result. -/
def equal_weights : Prop :=
  ∀ (p : LossPrecision) (f : JF → JF → Rat) (x y : List JF) (c mean : Rat),
    x.length = y.length → x ≠ [] → c ≠ 0 → p.round (.fin c) = .fin c →
    unweighted p f x y = .ok (.fin mean) →
    ∃ scaled : Rat, weighted p f x y c = .ok (.fin scaled)

theorem equal_weights_refuted : ¬ equal_weights := by
  intro h
  let f : JF → JF → Rat := fun _ _ => 1
  let x : List JF := [.fin 0, .fin 0]
  let y : List JF := [.fin 1, .fin 1]
  let c := LossPrecision.float64.maxFinite
  have hc : LossPrecision.float64.maxFinite ≠ 0 := by decide +kernel
  have hw : weighted .float64 (fun _ _ => 1) [.fin 0, .fin 0] [.fin 1, .fin 1]
      LossPrecision.float64.maxFinite = .ok .nan := by decide +kernel
  have hu : unweighted .float64 (fun _ _ => 1) [.fin 0, .fin 0] [.fin 1, .fin 1] =
      .ok (.fin 1) := by decide +kernel
  obtain ⟨scaled, hs⟩ := h .float64 f x y c 1 rfl (by simp [x]) hc
    (by decide +kernel) hu
  change weighted .float64 (fun _ _ => 1) [.fin 0, .fin 0] [.fin 1, .fin 1]
    LossPrecision.float64.maxFinite = .ok (.fin scaled) at hs
  rw [hw] at hs
  cases hs

private def epsilon (p : LossPrecision) : Rat :=
  match p with
  | .float16 => 1 / 1024
  | .float32 => 1 / 8388608
  | .float64 => 1 / 4503599627370496

private theorem abs_le_bounds (x b : Rat) : x.abs ≤ b ↔ -b ≤ x ∧ x ≤ b := by
  have h := Rat.abs_nonneg (x := x)
  by_cases hx : 0 ≤ x
  · rw [Rat.abs_of_nonneg hx] at *
    grind
  · have hn : x ≤ 0 := by grind
    rw [Rat.abs_of_nonpos hn] at *
    grind [Rat.neg_le_neg_iff]

/-- Track the exact argument to each rounded addition in a finite reduction.
This is the linear leaf reduction used by `pairwiseSum`. -/
inductive SumRounds (p : LossPrecision) : Rat → List Rat → Rat → List Rat → Prop where
  | nil (a : Rat) : SumRounds p a [] a []
  | cons {a b next result : Rat} {bs bounds : List Rat} :
      p.round (.fin (a + b)) = .fin next →
      SumRounds p next bs result bounds →
      SumRounds p a (b :: bs) result (p.ulp (a + b) / 2 :: bounds)

theorem SumRounds.error {p : LossPrecision} {a result : Rat} {xs bounds : List Rat}
    (h : SumRounds p a xs result bounds) :
    (result - (a + xs.sum)).abs ≤ bounds.sum := by
  induction h with
  | nil a => simp [Rat.add_zero, Rat.sub_self]
  | @cons a b next result bs bounds hr _ ih =>
    have hstep := (abs_le_bounds _ _).mp (p.round_error hr)
    have hrest := (abs_le_bounds _ _).mp ih
    apply (abs_le_bounds _ _).mpr
    simp only [List.sum_cons]
    grind

theorem SumRounds.foldl {p : LossPrecision} {a result : Rat} {xs bounds : List Rat}
    (h : SumRounds p a xs result bounds) :
    (xs.map JF.fin).foldl (fun x y => p.round (x + y)) (.fin a) = .fin result := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    simp only [List.map_cons, List.foldl_cons]
    change List.foldl _ (p.round (.fin (_ + _))) _ = _
    rw [hr, ih]

private theorem finite_rounded_add {p : LossPrecision} {a b : JF} {r : Rat}
    (h : p.round (a + b) = .fin r) :
    ∃ x y : Rat, a = .fin x ∧ b = .fin y ∧ p.round (.fin (x + y)) = .fin r := by
  cases a <;> cases b <;> first | exact ⟨_, _, rfl, rfl, h⟩ | cases h

private theorem SumRounds.of_foldl {p : LossPrecision} {a result : Rat} (xs : List Rat)
    (h : (xs.map JF.fin).foldl (fun x y => p.round (x + y)) (.fin a) = .fin result) :
    ∃ bounds, SumRounds p a xs result bounds := by
  induction xs generalizing a with
  | nil =>
    change JF.fin a = .fin result at h
    cases h
    exact ⟨[], .nil _⟩
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons] at h
    have finite_start (v : JF) (ys : List Rat) (r : Rat)
        (h : (ys.map JF.fin).foldl (fun x y => p.round (x + y)) v = .fin r) :
        ∃ q : Rat, v = .fin q := by
      induction ys generalizing v with
      | nil => exact ⟨r, h⟩
      | cons y ys ih =>
        simp only [List.map_cons, List.foldl_cons] at h
        obtain ⟨next, hn⟩ := ih _ h
        obtain ⟨q, _, hv, _, _⟩ := finite_rounded_add hn
        exact ⟨q, hv⟩
    obtain ⟨next, hn⟩ := finite_start _ bs result h
    rw [hn] at h
    obtain ⟨bounds, hb⟩ := ih h
    exact ⟨_, .cons hn hb⟩

/-- The budget records half-ULPs of the additions performed in every finite
leaf block and at every finite merge of the pairwise reduction. -/
inductive PairwiseRounds (p : LossPrecision) : Nat → List Rat → Rat → List Rat → Prop where
  | empty (fuel : Nat) : PairwiseRounds p fuel [] 0 []
  | leaf {fuel : Nat} {x : Rat} {xs : List Rat} {r : Rat} {bounds : List Rat} :
      (x :: xs).length ≤ 1024 →
      SumRounds p x xs r bounds →
      PairwiseRounds p (fuel + 1) (x :: xs) r bounds
  | merge {fuel : Nat} {xs : List Rat} {l r result : Rat} {lb rb : List Rat} :
      1024 < xs.length →
      PairwiseRounds p fuel (xs.take ((xs.length + 1) / 2)) l lb →
      PairwiseRounds p fuel (xs.drop ((xs.length + 1) / 2)) r rb →
      p.round (.fin (l + r)) = .fin result →
      PairwiseRounds p (fuel + 1) xs result (p.ulp (l + r) / 2 :: (lb ++ rb))

theorem PairwiseRounds.error {p : LossPrecision} {fuel : Nat} {xs bounds : List Rat}
    {result : Rat} (h : PairwiseRounds p fuel xs result bounds) :
    (result - xs.sum).abs ≤ bounds.sum := by
  induction h with
  | empty fuel => simp [Rat.sub_self]
  | leaf _ h => exact h.error
  | @merge fuel xs l r result lb rb _ hl hr hs ihl ihr =>
    have hsum : (xs.take ((xs.length + 1) / 2)).sum +
        (xs.drop ((xs.length + 1) / 2)).sum = xs.sum := by
      rw [← List.sum_append, List.take_append_drop]
    have he := (abs_le_bounds _ _).mp (p.round_error hs)
    have hle := (abs_le_bounds _ _).mp ihl
    have hre := (abs_le_bounds _ _).mp ihr
    apply (abs_le_bounds _ _).mpr
    simp only [List.sum_cons, List.sum_append]
    grind

private theorem PairwiseRounds.of_go {p : LossPrecision} (fuel : Nat) (xs : List Rat)
    (hFuel : xs.length ≤ fuel) {result : Rat}
    (h : pairwiseSum.go p fuel (xs.map JF.fin) = .fin result) :
    ∃ bounds, PairwiseRounds p fuel xs result bounds := by
  induction fuel generalizing xs result with
  | zero =>
    cases xs with
    | nil =>
      change JF.fin 0 = .fin result at h
      cases h
      exact ⟨[], .empty _⟩
    | cons => simp at hFuel
  | succ fuel ih =>
    cases xs with
    | nil =>
      change JF.fin 0 = .fin result at h
      cases h
      exact ⟨[], .empty _⟩
    | cons x xs =>
      simp only [List.map_cons, pairwiseSum.go, List.length_cons, List.length_map] at h
      split at h
      · rename_i hSmall
        obtain ⟨bounds, hr⟩ := SumRounds.of_foldl xs h
        exact ⟨bounds, .leaf (by simpa using hSmall) hr⟩
      · rename_i hLarge
        let samples := x :: xs
        let middle := (samples.length + 1) / 2
        change p.round (pairwiseSum.go p fuel ((samples.map JF.fin).take middle) +
          pairwiseSum.go p fuel ((samples.map JF.fin).drop middle)) = .fin result at h
        rw [← List.map_take, ← List.map_drop] at h
        obtain ⟨l, r, hl, hr, hAdd⟩ := finite_rounded_add h
        have hLen : 1024 < samples.length := by
          change ¬ xs.length + 1 ≤ 1024 at hLarge
          change 1024 < xs.length + 1
          omega
        have hlLen : (samples.take middle).length ≤ fuel := by
          rw [List.length_take]
          dsimp [middle]
          change samples.length ≤ fuel + 1 at hFuel
          omega
        have hrLen : (samples.drop middle).length ≤ fuel := by
          rw [List.length_drop]
          dsimp [middle]
          change samples.length ≤ fuel + 1 at hFuel
          omega
        obtain ⟨lb, hl⟩ := ih _ hlLen hl
        obtain ⟨rb, hr⟩ := ih _ hrLen hr
        exact ⟨_, .merge hLen hl hr hAdd⟩

/-- The modeled pairwise sum's forward error is bounded by the sum of the
half-ULPs at every addition, provided the reduction returned a finite value. -/
theorem pairwiseSum_error {p : LossPrecision} (xs : List Rat) {result : Rat}
    (h : pairwiseSum p (xs.map JF.fin) = .fin result) :
    ∃ bounds, PairwiseRounds p xs.length xs result bounds ∧
      (result - xs.sum).abs ≤ bounds.sum := by
  unfold pairwiseSum at h
  rw [List.length_map] at h
  obtain ⟨bounds, hb⟩ := PairwiseRounds.of_go xs.length xs (Nat.le_refl _) h
  exact ⟨bounds, hb, hb.error⟩

/-- A relative agreement bound for positive normal-range calculations. -/
def equal_weights_rounding : Prop :=
  ∀ (p : LossPrecision) (f : JF → JF → Rat) (x y : List JF)
    (c lo hi : Rat),
    x.length = y.length → x ≠ [] → 0 < c → p.round (.fin c) = .fin c →
    p.minNormal ≤ c → p.minNormal ≤ lo → lo ≤ hi →
    (∀ v ∈ x.zipWith f y, lo ≤ v ∧ v ≤ hi ∧ p.round (.fin v) = .fin v) →
    p.minNormal ≤ c * lo →
    (x.length : Rat) * max (max c hi) (c * hi) ≤ p.maxFinite / 2 →
    16 * (x.length : Rat) * epsilon p ≤ 1 →
    ∃ mean scaled : Rat, unweighted p f x y = .ok (.fin mean) ∧
      weighted p f x y c = .ok (.fin scaled) ∧
      (scaled - mean).abs ≤ 16 * (x.length : Rat) * epsilon p * mean

end SymReg.Loss
