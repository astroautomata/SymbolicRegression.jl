import SymReg.MLJ.Select

namespace SymReg.MLJ
open DynExpr SymReg.HofMig

theorem ok_of_toOption {e : Except ε α} {a : α} (h : e.toOption = some a) : e = .ok a := by
  cases e <;> simp_all [Except.toOption]

theorem get_unique {l : List α} {j : Nat} {a b : α} (ha : l[j]? = some a) (hb : l[j]? = some b) :
    a = b := by rw [ha] at hb; exact Option.some.inj hb

/-- Row `j` passes the 1.5x minimum-loss threshold of src/MLJInterface.jl:726-728. -/
def Eligible (losses : List JF) (m : JF) (j : Nat) : Prop :=
  ∃ l, losses[j]? = some l ∧ lessEq l (.fin (3 / 2) * m) = true

/-- The docstring rule (src/MLJInterface.jl:852-858): among rows within 1.5x the
minimum loss, the selected row has the highest score, and is the first such row. -/
def cb_log_rule : Prop := ∀ (losses scores : List JF) (scale : Option LossScale),
  scale ≠ some .linear → losses ≠ [] → scores.length = losses.length →
  (∀ l ∈ losses, l ≠ .nan ∧ less l (.fin 0) = false) →
  (∀ s ∈ scores, s ≠ .nan ∧ s ≠ .negInf) →
  ∃ r m, chooseBest losses scores scale = .ok r ∧ minimum losses = .ok m ∧
    1 ≤ r ∧ r ≤ losses.length ∧ Eligible losses m (r - 1) ∧
    ∀ (j : Nat) s s', Eligible losses m j → scores[j]? = some s → scores[r - 1]? = some s' →
      less s' s = false ∧ (j < r - 1 → less s s' = true)

example : ∀ l ∈ [JF.fin 2, .fin 1], l ≠ .nan ∧ less l (.fin 0) = false := by decide
example : ∀ s ∈ [JF.fin 0, .fin 1], s ≠ .nan ∧ s ≠ .negInf := by decide

theorem cb_log_rule_holds : cb_log_rule := by
  intro losses scores scale hs hne hlen hl hsc
  cases losses with
  | nil => exact absurd rfl hne
  | cons x xs =>
  have hlnan : ∀ y ∈ x :: xs, y ≠ .nan := fun y hy => (hl y hy).1
  obtain ⟨hmem, hmin⟩ := foldl_jmin xs x hlnan
  generalize hm : xs.foldl jmin x = m at hmem hmin
  have hmin_ok : minimum (x :: xs) = .ok m := by simp [minimum, hm]
  have hmask := maskScores_ok (.fin (3 / 2) * m) (x :: xs) scores (by omega)
  obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨s0, hs0⟩ : ∃ s0, scores[i0]? = some s0 := by
    have := lt_of_get hi0
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hs0n := hsc s0 (List.mem_of_getElem? hs0)
  have hmt := lessEq_threshold m (hlnan m hmem) (hl m hmem).2
  have hM0 := mask_get (.fin (3 / 2) * m) (x :: xs) scores i0 m s0 hi0 hs0
  rw [if_pos hmt] at hM0
  have hMn : ∀ v ∈ mask (.fin (3 / 2) * m) (x :: xs) scores, v ≠ .nan := by
    intro v hv
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
    obtain ⟨l, s, _, hs', rfl⟩ := mask_get_inv _ _ _ j v hj
    split
    · exact (hsc s (List.mem_of_getElem? hs')).1
    · intro h; cases h
  have hMlen : (mask (.fin (3 / 2) * m) (x :: xs) scores).length = (x :: xs).length := by
    simp [mask, List.length_zipWith, hlen]
  cases hM : mask (.fin (3 / 2) * m) (x :: xs) scores with
  | nil => rw [hM] at hM0; simp at hM0
  | cons y ys =>
  rw [hM] at hMn hM0 hMlen
  obtain ⟨v, hv, hk1, hkle, hmax, hfirst⟩ := find_result isLess better_isLess y ys hMn
  generalize hk : (findAux isLess (y, 1) ys 2).2 = k at hv hk1 hkle hmax hfirst
  have hcb : chooseBest (x :: xs) scores scale = .ok k := by
    simp only [chooseBest, if_neg hs, hmin_ok, hmask, hM, bind, Except.bind, argmax, hk]
  rw [← hM] at hv
  obtain ⟨lk, sk, hlk, hsk, hvk⟩ := mask_get_inv _ _ _ _ _ hv
  have helig : lessEq lk (.fin (3 / 2) * m) = true := by
    cases hle : lessEq lk (.fin (3 / 2) * m)
    · simp [hle] at hvk
      have := hmax i0 s0 hM0
      rw [hvk, negInf_isLess hs0n.1 hs0n.2] at this; cases this
    · rfl
  rw [if_pos helig] at hvk
  subst hvk
  have hskn := hsc v (List.mem_of_getElem? hsk)
  refine ⟨k, m, hcb, hmin_ok, hk1, by simpa [hMlen] using hkle, ⟨lk, hlk, helig⟩, ?_⟩
  intro j s s' ⟨lj, hlj, hjel⟩ hsj hs'
  have := get_unique hs' hsk; subst this
  have hMj := mask_get (.fin (3 / 2) * m) (x :: xs) scores j lj s hlj hsj
  rw [if_pos hjel, hM] at hMj
  have hsn := hsc s (List.mem_of_getElem? hsj)
  refine ⟨?_, fun hj => ?_⟩
  · have := hmax j s hMj; rwa [isLess_eq hskn.1 hsn.1] at this
  · have := hfirst j s hj hMj; rwa [isLess_eq hsn.1 hskn.1] at this

/-- `loss_scale = :linear` selects the first minimum-loss row, src/MLJInterface.jl:722-724. -/
def cb_linear_rule : Prop := ∀ (losses scores : List JF),
  losses ≠ [] → (∀ l ∈ losses, l ≠ .nan) →
  ∃ r, chooseBest losses scores (some .linear) = .ok r ∧ 1 ≤ r ∧ r ≤ losses.length ∧
    ∀ (j : Nat) l l', losses[j]? = some l → losses[r - 1]? = some l' →
      less l l' = false ∧ (j < r - 1 → less l' l = true)

theorem cb_linear_rule_holds : cb_linear_rule := by
  intro losses scores hne hn
  cases losses with
  | nil => exact absurd rfl hne
  | cons x xs =>
  obtain ⟨v, hv, hk1, hkle, hmax, hfirst⟩ := find_result isGreater better_isGreater x xs hn
  refine ⟨_, rfl, hk1, hkle, ?_⟩
  intro j l l' hl hl'
  have := get_unique hl' hv; subst this
  have hln := hn l (List.mem_of_getElem? hl)
  have hvn := hn l' (List.mem_of_getElem? hl')
  refine ⟨?_, fun hj => ?_⟩
  · have := hmax j l hl; rwa [isGreater_eq hvn hln] at this
  · have := hfirst j l hj hl; rwa [isGreater_eq hln hvn] at this



/-- With log scaling, the selected row maximizes score among rows within 1.5x the
minimum non-NaN loss, whatever other rows hold NaN losses. -/
def cb_log_nan : Prop := ∀ (losses scores : List JF) (scale : Option LossScale) (r : Nat) (m : JF),
  scale ≠ some .linear → scores.length = losses.length →
  (∀ s ∈ scores, s ≠ .nan ∧ s ≠ .negInf) →
  minimum (losses.filter (· != .nan)) = .ok m → chooseBest losses scores scale = .ok r →
  ∀ (j : Nat) s s', Eligible losses m j → scores[j]? = some s → scores[r - 1]? = some s' →
    less s' s = false

theorem cb_log_nan_refuted : ¬ cb_log_nan := by
  intro h
  have hcb : chooseBest [.fin 2, .fin 1, .nan] [.fin 0, .fin 1, .fin 0] (some .log) = .ok 1 :=
    ok_of_toOption (by decide +kernel)
  have hmin : minimum ([JF.fin 2, .fin 1, .nan].filter (· != .nan)) = .ok (.fin 1) :=
    ok_of_toOption (by decide +kernel)
  have := h [.fin 2, .fin 1, .nan] [.fin 0, .fin 1, .fin 0] (some .log) 1 (.fin 1) (by decide) rfl
    (by decide) hmin hcb 1 (.fin 1) (.fin 0)
    ⟨.fin 1, rfl, by decide +kernel⟩ rfl rfl
  revert this; decide +kernel

/-- One frontier row is always selected, whatever its loss and score. -/
def cb_single : Prop := ∀ (l s : JF) (scale : Option LossScale), chooseBest [l] [s] scale = .ok 1

theorem cb_single_holds : cb_single := by
  intro l s scale
  unfold chooseBest
  split
  · rfl
  · cases h : lessEq l (.fin (3 / 2) * l) <;>
      simp [minimum, maskScores, h, argmax, findAux, bind, Except.bind, pure, Except.pure] <;> rfl

/-- An empty loss vector throws the empty-reduction ArgumentError under both scalings. -/
def cb_empty : Prop := ∀ (scores : List JF) (scale : Option LossScale),
  chooseBest [] scores scale = .error emptyReduction

theorem cb_empty_holds : cb_empty := by
  intro scores scale; unfold chooseBest; split <;> rfl

/-- `options = nothing` selects exactly as `loss_scale = :log`. -/
def cb_nothing_is_log : Prop := ∀ (losses scores : List JF),
  chooseBest losses scores none = chooseBest losses scores (some .log)

theorem cb_nothing_is_log_holds : cb_nothing_is_log := by
  intro losses scores; simp [chooseBest]

end SymReg.MLJ
