import SymReg.MLJ.ReportLemmas

namespace SymReg.MLJ
open DynExpr SymReg.HofMig

theorem formatHof_spec {rt : ScalarRuntime} {scale : LossScale} {compute : Nat → Int} {h : Hof}
    {fresh a : Nat} {F : Formatted} (hf : formatHof rt scale compute h fresh = .ok (F, a)) :
    formatSpec rt scale compute (calculatePareto h fresh).1 = .ok F := by
  rw [formatHof_eq] at hf
  cases hs : formatSpec rt scale compute (calculatePareto h fresh).1 with
  | error e => rw [hs] at hf; cases hf
  | ok G => rw [hs] at hf; cases hf; rfl

theorem mapM_ok {f : α → Jl β} : ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
    ys.length = xs.length ∧ ∀ (t : Nat) x y, xs[t]? = some x → ys[t]? = some y → f x = .ok y := by
  intro xs
  induction xs with
  | nil => intro ys h; simp [pure, Except.pure] at h; subst h; simp
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok zs =>
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        subst h
        obtain ⟨hl, hg⟩ := ih zs hxs
        refine ⟨by simp [hl], ?_⟩
        intro t a b ha hb
        cases t with
        | zero => simp at ha hb; subst ha; subst hb; exact hx
        | succ t => exact hg t a b (by simpa using ha) (by simpa using hb)

theorem mapM_of {f : α → Jl β} : ∀ (xs : List α),
    (∀ x ∈ xs, ∃ y, f x = .ok y) → ∃ ys, xs.mapM f = .ok ys := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons x xs ih =>
    intro h
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]⟩

/-- Formatted losses are copies of the losses of existing hall slots. -/
theorem front_loss {h : Hof} {fresh : Nat} {x : Member} (hx : x ∈ (calculatePareto h fresh).1) :
    ∃ s ∈ h.slots, s.exists = true ∧ s.member.loss = x.loss ∧ s.member.complexity = x.complexity := by
  obtain ⟨s, hs, he, heq⟩ := front_member hx
  have h1 := congrArg Member.loss heq
  have h2 := congrArg Member.complexity heq
  exact ⟨s, hs, he, h1, h2⟩

/-! ## Single-target reports -/

def VectorLengths (v : Formatted) (n : Nat) : Prop :=
  v.trees.length = n ∧ v.losses.length = n ∧ v.complexities.length = n ∧ v.scores.length = n

def rep_lengths : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D) (ws : Bool)
    (fresh f : Nat) (r : Report1),
  fullReport1 m fr ws fresh = .ok (r, f) →
  ∃ (before after : Formatted),
    formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh = .ok (before, f) ∧
    let n := (calculatePareto fr.state.hof fresh).1.length
    VectorLengths before n ∧
    (∀ strs, r.equationStrings = some strs → strs.length = n) ∧
    (VectorLengths after n →
      r.equations.length = n ∧ r.losses.length = n ∧
      r.complexities.length = n ∧ r.scores.length = n) ∧
    dispatch1 m.selection before fr.options m.selectionState =
      .ok (r.bestIdx, after, r.selectionState, r.selectionCalls)

private theorem typed_rows_length (rt : ScalarRuntime) (scale : LossScale)
    (rows : List (ScoreFloat × Int)) (prev : Option (ScoreFloat × Int)) (out : List ScoreFloat)
    (h : typedScoreRows rt scale rows prev = .ok out) : out.length = rows.length := by
  induction rows generalizing prev out with
  | nil => cases h; rfl
  | cons p ps ih =>
    cases hs : rowScore rt scale p.1 p.2 prev with
    | error e => simp [typedScoreRows, hs, bind, Except.bind] at h
    | ok s =>
      cases ht : typedScoreRows rt scale ps (some p) with
      | error e => simp [typedScoreRows, hs, ht, bind, Except.bind] at h
      | ok tail =>
        simp [typedScoreRows, hs, ht, bind, Except.bind, pure, Except.pure] at h
        subst out
        simp [ih _ _ ht]

private theorem scores_length {rt : ScalarRuntime} {scale : LossScale} {compute : Nat → Int}
    {front : List Member} {out : List JF}
    (h : scoreRows rt scale compute front none = .ok out) : out.length = front.length := by
  unfold scoreRows at h
  cases hr : typedScoreRows rt scale
      (front.map fun m => (m.scoreLoss rt.precision, (resolveComplexity compute m).2)) none with
  | error e => simp [hr, Except.map] at h
  | ok values =>
    simp [hr, Except.map] at h
    subst out
    simpa using typed_rows_length _ _ _ _ _ hr

theorem format_row_count {rt : ScalarRuntime} {scale : LossScale} {compute : Nat → Int}
    {h : Hof} {fresh f : Nat} {F : Formatted}
    (hf : formatHof rt scale compute h fresh = .ok (F, f)) :
    VectorLengths F (calculatePareto h fresh).1.length := by
  obtain ⟨_, hsc, ht, hl, hc⟩ := formatSpec_ok (formatHof_spec hf)
  exact ⟨by simp [ht], by simp [hl], by simp [hc], scores_length hsc⟩

theorem rep_lengths_holds : rep_lengths := by
  intro U D m fr ws fresh f r h
  obtain ⟨F, updated, hF, hd, he, hl, hc, hs, hstr⟩ := fullReport1_ok h
  have hv := format_row_count hF
  refine ⟨F, updated, hF, hv, ?_, ?_, hd⟩
  · intro strs hst
    rw [hstr] at hst
    split at hst
    · cases hst; simpa [strings1] using hv.1
    · cases hst
  · simpa [he, hl, hc, hs, VectorLengths]

def rep_best : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D) (ws : Bool)
    (fresh f : Nat) (r : Report1),
  fullReport1 m fr ws fresh = .ok (r, f) →
  ∃ F : Formatted, formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh = .ok (F, f) ∧
    (F.trees = [] → r.bestIdx = 0 ∧ r.selectionCalls = []) ∧
    (F.trees ≠ [] → r.selectionCalls = [⟨F, fr.options, r.bestIdx⟩])

theorem rep_best_holds : rep_best := by
  intro U D m fr ws fresh f r h
  obtain ⟨F, _, hF, hd, _, _, _, _, _⟩ := fullReport1_ok h
  refine ⟨F, hF, ?_, ?_⟩
  · intro h0
    simp [dispatch1, h0, pure, Except.pure] at hd
    exact ⟨hd.1.symm, hd.2.2.2⟩
  · intro h0
    have hn : F.trees.isEmpty = false := by cases hf : F.trees <;> simp_all
    cases hsel : m.selection F fr.options m.selectionState with
    | error e => simp [dispatch1, hn, hsel, bind, Except.bind] at hd
    | ok p =>
      obtain ⟨best, after, state⟩ := p
      simp [dispatch1, hn, hsel, bind, Except.bind, pure, Except.pure] at hd
      rw [← hd.1, ← hd.2.2.2]

def rep_order : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D) (ws : Bool)
    (fresh f : Nat) (r : Report1),
  ((fr.state.hof.slots.filter Slot.exists).map Slot.member).Pairwise
    (fun a b => a.complexity < b.complexity) →
  (∀ s ∈ fr.state.hof.slots, s.exists = true → s.member.complexity ≠ -1) →
  fullReport1 m fr ws fresh = .ok (r, f) →
  ∃ F, formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh = .ok (F, f) ∧
    F.complexities.Pairwise (· < ·) ∧
    (r.complexities = F.complexities → r.complexities.Pairwise (· < ·))

example : (([⟨specimen (.fin 1) (.fin 2) 1, true⟩, ⟨specimen (.fin 0) (.fin 1) 2, true⟩] : List Slot).filter
    Slot.exists |>.map Slot.member).Pairwise (fun a b => a.complexity < b.complexity) ∧
    ∀ s ∈ ([⟨specimen (.fin 1) (.fin 2) 1, true⟩, ⟨specimen (.fin 0) (.fin 1) 2, true⟩] : List Slot),
      s.exists = true → s.member.complexity ≠ -1 := by decide

theorem rep_order_holds : rep_order := by
  intro U D m fr ws fresh f r hpair hcache h
  obtain ⟨F, _, hF, _, _, _, _, _, _⟩ := fullReport1_ok h
  obtain ⟨_, _, _, _, hFc⟩ := formatSpec_ok (formatHof_spec hF)
  have hres : (calculatePareto fr.state.hof fresh).1.map (fun x => (resolveComplexity fr.options.compute x).2) =
      (frontRaw [] fr.state.hof.slots).map Member.complexity := by
    have h1 : (calculatePareto fr.state.hof fresh).1.map (fun x => (resolveComplexity fr.options.compute x).2) =
        (calculatePareto fr.state.hof fresh).1.map Member.complexity := by
      apply List.map_congr_left
      intro x hx
      obtain ⟨s, hs, he, _, hcx⟩ := front_loss hx
      have : x.complexity ≠ -1 := hcx ▸ hcache s hs he
      simp [resolveComplexity, this]
    have h2 : (calculatePareto fr.state.hof fresh).1.map Member.complexity =
        ((calculatePareto fr.state.hof fresh).1.map strip).map Member.complexity := by
      rw [List.map_map]; rfl
    rw [h1, h2, calculatePareto, copyMembers_strip, List.map_map]; rfl
  have hp : F.complexities.Pairwise (· < ·) := by
    rw [hFc, hres]
    exact List.pairwise_map.mpr (frontier_increasing_holds _ hpair)
  exact ⟨F, hF, hp, fun he => he.symm ▸ hp⟩

/-- Formatted losses are never NaN: the frontier skips NaN losses. -/
theorem front_nonnan {h : Hof} {fresh : Nat} {x : Member} (hx : x ∈ (calculatePareto h fresh).1) :
    x.loss ≠ .nan := by
  have hmem : strip x ∈ (frontRaw [] h.slots).map strip := by
    rw [← copyMembers_strip (frontRaw [] h.slots) fresh]
    exact List.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
  have hl := congrArg Member.loss hyx
  simp only [strip] at hl
  rw [← hl]
  exact frontRaw_nonnan [] h.slots y hy

/-- Facts on a formatted report needed by the default selection. -/
theorem report_inputs {U D : Type} {m : Regressor} {fr : FitResult State1 U D} {ws : Bool}
    {fresh f : Nat} {r : Report1} (hsel : m.selection = chooseBestMethod)
    (h : fullReport1 m fr ws fresh = .ok (r, f)) :
    ∃ F : Formatted, (if F.trees.isEmpty then (Except.ok 0 : Jl Int) else
        (chooseBest F.losses F.scores (some fr.options.scale)).map Int.ofNat) = .ok r.bestIdx ∧
      F.trees = r.equations ∧ F.losses = r.losses ∧
      F.scores = r.scores ∧ F.complexities = r.complexities ∧
      F.losses.length = F.trees.length ∧ F.scores.length = F.trees.length ∧
      (∀ l ∈ F.losses, l ≠ .nan) ∧
      (fr.options.scale = .log → ∀ l ∈ F.losses, less l (.fin 0) = false) ∧
      (∀ s ∈ F.scores, s ≠ .nan ∧ s ≠ .negInf) := by
  obtain ⟨F, updated, hF, hd0, he, hl, hc, hs, _⟩ := fullReport1_ok h
  have hselect : updated = F ∧
      (if F.trees.isEmpty then .ok 0 else
        (chooseBest F.losses F.scores (some fr.options.scale)).map Int.ofNat) = .ok r.bestIdx := by
    cases hn : F.trees.isEmpty with
    | true =>
      simp [dispatch1, hn, pure, Except.pure] at hd0
      exact ⟨hd0.2.1.symm, by simp [hn, hd0.1]⟩
    | false =>
      cases hb : chooseBest F.losses F.scores (some fr.options.scale) with
      | error e => simp [dispatch1, hsel, chooseBestMethod, hn, hb, bind, Except.bind] at hd0
      | ok k =>
        simp [dispatch1, hsel, chooseBestMethod, hn, hb, bind, Except.bind, pure, Except.pure] at hd0
        exact ⟨hd0.2.1.symm, by simp [hn, hb, Except.map, hd0.1]⟩
  obtain ⟨hupd, hd⟩ := hselect
  subst updated
  obtain ⟨hneg, hsc, ht, hFl, _⟩ := formatSpec_ok (formatHof_spec hF)
  have h1 : F.losses.length = F.trees.length := by simp [hFl, ht]
  have h2 : F.scores.length = F.trees.length := by simpa [ht] using scores_length hsc
  refine ⟨F, hd, he.symm, hl.symm, hs.symm, hc.symm, by omega, by omega, ?_, ?_, ?_⟩
  · intro l hlm
    rw [hFl] at hlm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hlm
    exact front_nonnan hx
  · intro hlog l hlm
    rw [hFl] at hlm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hlm
    exact hneg hlog x hx
  · exact scoreRows_good _ _ _ _ _ _ hsc

def rep_default_rule : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D)
    (ws : Bool) (fresh f : Nat) (r : Report1),
  m.selection = chooseBestMethod → fr.options.scale = .log →
  (∀ s ∈ fr.state.hof.slots, s.exists = true → s.member.loss ≠ .nan) →
  fullReport1 m fr ws fresh = .ok (r, f) → r.equations ≠ [] →
  ∃ (k : Nat) (mn : JF), r.bestIdx = k ∧ minimum r.losses = .ok mn ∧ 1 ≤ k ∧ k ≤ r.losses.length ∧
    Eligible r.losses mn (k - 1) ∧
    ∀ (j : Nat) s s', Eligible r.losses mn j → r.scores[j]? = some s → r.scores[k - 1]? = some s' →
      less s' s = false ∧ (j < k - 1 → less s s' = true)

theorem rep_default_rule_holds : rep_default_rule := by
  intro U D m fr ws fresh f r hsel hlog _ h hne
  obtain ⟨F, hd, he, hl, hs, _, hlen1, hlen2, hln, hneg, hsc⟩ := report_inputs hsel h
  have hFne : F.trees ≠ [] := he ▸ hne
  have hLne : F.losses ≠ [] := by
    intro h0; apply hFne; rw [← List.length_eq_zero_iff, ← hlen1, h0]; rfl
  obtain ⟨k, mn, hcb, hmin, hk1, hkle, helig, hmax⟩ :=
    cb_log_rule_holds F.losses F.scores (some .log) (by decide) hLne (by omega)
      (fun l hl' => ⟨hln l hl', hneg hlog l hl'⟩) hsc
  have ht0 : F.trees.isEmpty = false := by cases hf : F.trees <;> simp_all
  simp [ht0, hlog, hcb, Except.map] at hd
  rw [← hl, ← hs]
  exact ⟨k, mn, hd.symm, hmin, hk1, hkle, helig, hmax⟩

def rep_linear_rule : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D)
    (ws : Bool) (fresh f : Nat) (r : Report1),
  m.selection = chooseBestMethod → fr.options.scale = .linear →
  (∀ s ∈ fr.state.hof.slots, s.exists = true → s.member.loss ≠ .nan) →
  fullReport1 m fr ws fresh = .ok (r, f) → r.equations ≠ [] →
  ∃ k : Nat, r.bestIdx = k ∧ 1 ≤ k ∧ k ≤ r.losses.length ∧
    ∀ (j : Nat) l l', r.losses[j]? = some l → r.losses[k - 1]? = some l' →
      less l l' = false ∧ (j < k - 1 → less l' l = true)

theorem rep_linear_rule_holds : rep_linear_rule := by
  intro U D m fr ws fresh f r hsel hlin _ h hne
  obtain ⟨F, hd, he, hl, _, _, hlen1, _, hln, _, _⟩ := report_inputs hsel h
  have hFne : F.trees ≠ [] := he ▸ hne
  have hLne : F.losses ≠ [] := by
    intro h0; apply hFne; rw [← List.length_eq_zero_iff, ← hlen1, h0]; rfl
  obtain ⟨k, hcb, hk1, hkle, hmin⟩ := cb_linear_rule_holds F.losses F.scores hLne hln
  have ht0 : F.trees.isEmpty = false := by cases hf : F.trees <;> simp_all
  simp [ht0, hlin, hcb, Except.map] at hd
  rw [← hl]
  exact ⟨k, hd.symm, hk1, hkle, hmin⟩


def cb_linear_nan : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D)
    (ws : Bool) (fresh f : Nat) (r : Report1),
  m.selection = chooseBestMethod → fr.options.scale = .linear →
  fullReport1 m fr ws fresh = .ok (r, f) → r.equations ≠ [] →
  ∃ (k : Nat) (value : JF), r.bestIdx = k ∧ r.losses[k - 1]? = some value ∧
    value ≠ .nan ∧ ∀ l ∈ r.losses, less l value = false

theorem cb_linear_nan_holds : cb_linear_nan := by
  intro U D m fr ws fresh f r hsel hlin hr hne
  obtain ⟨F, hd, he, hl, _, _, hlen, _, hln, _, _⟩ := report_inputs hsel hr
  have ht : F.trees ≠ [] := he ▸ hne
  have hn : F.losses ≠ [] := by
    intro h; apply ht; rw [← List.length_eq_zero_iff, ← hlen, h]; rfl
  obtain ⟨k, hc, hk1, hk2, hmin⟩ := cb_linear_rule_holds F.losses F.scores hn hln
  have ht0 : F.trees.isEmpty = false := by cases hf : F.trees <;> simp_all
  simp [ht0, hlin, hc, Except.map] at hd
  have hidx : k - 1 < F.losses.length := by omega
  have hv : F.losses[k - 1]? = some F.losses[k - 1] := List.getElem?_eq_getElem hidx
  rw [← hl]
  refine ⟨k, _, hd.symm, hv, hln _ (List.mem_of_getElem? hv), ?_⟩
  intro l hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  exact (hmin j l _ hj hv).1



def rep_strings : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D)
    (fresh f : Nat) (r : Report1),
  fullReport1 m fr true fresh = .ok (r, f) →
  ∃ F, formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh = .ok (F, f) ∧
    r.equationStrings = some (F.trees.map (fr.options.render · fr.variableNames)) ∧
    (r.equations = F.trees → r.equationStrings = some (r.equations.map
      (fr.options.render · fr.variableNames)))

theorem rep_strings_holds : rep_strings := by
  intro U D m fr fresh f r h
  obtain ⟨F, _, hF, _, _, _, _, _, hstr⟩ := fullReport1_ok h
  refine ⟨F, hF, ?_, ?_⟩
  · simpa [strings1] using hstr
  · intro he; simpa [strings1, he] using hstr

/-! ## A NaN loss in the hall -/

instance unitDims : Dims Unit := ⟨inferInstance, ()⟩

/-- A runtime whose logarithm has the sign of `log` on (0, 1). -/
def signRt : ScalarRuntime := ⟨fun _ q => if q < 1 then -1 else 1, .float64⟩

def plainOpts (scale : LossScale) : Opts := ⟨signRt, scale, fun _ => 1, fun _ _ => "", fun _ _ => ([], true), 0⟩

def slotOf (loss : JF) (c : Int) (tree : Nat) : Slot := ⟨⟨.fin 0, loss, c, tree, 0, 1, 0, 0, -1, false⟩, true⟩

def defaultModel : Regressor := ⟨.srRegressor, 100, chooseBestMethod, "multithreading", 0⟩

def fit1Of (h : Hof) (scale : LossScale) : Fit1 Unit :=
  ⟨defaultModel, ⟨0, h⟩, 100, 1, plainOpts scale, ["x1"], none, false, none, none⟩

/-- Losses [2, 1, NaN] at complexities 1, 2, 3. -/
def nanHof : Hof := ⟨[slotOf (.fin 2) 1 0, slotOf (.fin 1) 2 1, slotOf .nan 3 2]⟩

def rep_default_nan : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult State1 U D)
    (ws : Bool) (fresh f : Nat) (r : Report1),
  m.selection = chooseBestMethod → fr.options.scale = .log →
  fullReport1 m fr ws fresh = .ok (r, f) → r.equations ≠ [] →
  (∀ l ∈ r.losses, l ≠ .nan) ∧
  ∃ (k : Nat) (mn score : JF), r.bestIdx = k ∧ 1 ≤ k ∧
    minimum r.losses = .ok mn ∧ Eligible r.losses mn (k - 1) ∧
    r.scores[k - 1]? = some score ∧
    ∀ (j : Nat) s, Eligible r.losses mn j → r.scores[j]? = some s → less score s = false

theorem rep_default_nan_holds : rep_default_nan := by
  intro U D m fr ws fresh f r hsel hlog h hne
  obtain ⟨F, hd, he, hl, hs, _, hlen1, hlen2, hln, hneg, hsc⟩ := report_inputs hsel h
  have hFne : F.trees ≠ [] := he ▸ hne
  have hLne : F.losses ≠ [] := by
    intro h0; apply hFne; rw [← List.length_eq_zero_iff, ← hlen1, h0]; rfl
  obtain ⟨k, mn, hcb, hmin, hk1, hkle, helig, hmax⟩ :=
    cb_log_rule_holds F.losses F.scores (some .log) (by decide) hLne (by omega)
      (fun l hl' => ⟨hln l hl', hneg hlog l hl'⟩) hsc
  have ht0 : F.trees.isEmpty = false := by cases hf : F.trees <;> simp_all
  simp [ht0, hlog, hcb, Except.map] at hd
  have hk : k - 1 < F.scores.length := by omega
  have hscore := List.getElem?_eq_getElem (l := F.scores) hk
  rw [← hl, ← hs]
  exact ⟨hln, k, mn, _, hd.symm, hk1, hmin, helig, hscore,
    fun j s hj hsj => (hmax j s _ hj hsj hscore).1⟩

/-- The NaN slot is skipped, so row 2 (loss 1) is the only row within 1.5x the minimum. -/
example : (fullReport1 defaultModel (fit1Of nanHof .log) true 0).toOption.map
    (fun p => (p.1.bestIdx, p.1.losses)) = some (2, [.fin 2, .fin 1]) := by decide +kernel

/-! ## Multitarget reports -/

def rep_lengthsK : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult StateK U D) (ws : Bool)
    (fresh f : Nat) (r : ReportK),
  fullReportK m fr ws fresh = .ok (r, f) →
  ∃ before : List Formatted,
    formatMany fr.options.rt fr.options.scale fr.options.compute fr.state.hofs fresh = .ok (before, f) ∧
    before.length = fr.state.hofs.length ∧
    (∀ (t : Nat) F, before[t]? = some F → ∃ n, VectorLengths F n) ∧
    r.equationStrings = (if ws then some (before.map fun F =>
      F.trees.map (fr.options.render · fr.variableNames)) else none)

theorem rep_lengthsK_holds : rep_lengthsK := by
  intro U D m fr ws fresh f r h
  obtain ⟨Fs, _, hF, _, _, _, _, _, hstr⟩ := fullReportK_ok h
  obtain ⟨hlen, hget⟩ := formatMany_ok _ _ _ _ _ _ _ hF
  refine ⟨Fs, hF, hlen, ?_, ?_⟩
  · intro t F ht
    obtain ⟨_, _, _, _, hf⟩ := hget t F ht
    exact ⟨_, format_row_count hf⟩
  · simpa [stringsK, strings1, List.map_map, Function.comp_def] using hstr

theorem selectTargets_calls (sel : SelectionMethod) (o : Opts) (fs : List Formatted)
    (initial state : Nat) (bs : List Int) (updated : List Formatted) (calls : List SelectionCall)
    (h : selectTargets sel o fs initial = .ok (bs, updated, state, calls)) :
    calls.map SelectionCall.vectors = fs ∧
    calls.map SelectionCall.index = bs ∧
    ∀ c ∈ calls, c.options = o := by
  induction fs generalizing initial state bs updated calls with
  | nil =>
    simp [selectTargets] at h
    obtain ⟨rfl, _, _, rfl⟩ := h
    simp
  | cons F Fs ih =>
    cases hsel : sel F o initial with
    | error e => simp [selectTargets, hsel, bind, Except.bind] at h
    | ok p =>
      obtain ⟨b, u, s⟩ := p
      cases hr : selectTargets sel o Fs s with
      | error e => simp [selectTargets, hsel, hr, bind, Except.bind] at h
      | ok q =>
        obtain ⟨bs', us, s', cs⟩ := q
        simp [selectTargets, hsel, hr, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, _, _, rfl⟩ := h
        obtain ⟨hv, hb, ho⟩ := ih s s' bs' us cs hr
        simpa [hv, hb] using ho

def rep_bestK : Prop := ∀ (U D : Type) (m : Regressor) (fr : FitResult StateK U D) (ws : Bool)
    (fresh f : Nat) (r : ReportK),
  fullReportK m fr ws fresh = .ok (r, f) →
  ∃ Fs, formatMany fr.options.rt fr.options.scale fr.options.compute fr.state.hofs fresh = .ok (Fs, f) ∧
    ((∃ F ∈ Fs, F.trees = []) → r.selectionCalls = [] ∧ r.bestIdx = Fs.map (fun _ => 0)) ∧
    ((∀ F ∈ Fs, F.trees ≠ []) →
      r.selectionCalls.map SelectionCall.vectors = Fs ∧
      r.selectionCalls.map SelectionCall.index = r.bestIdx ∧
      ∀ c ∈ r.selectionCalls, c.options = fr.options)

theorem rep_bestK_holds : rep_bestK := by
  intro U D m fr ws fresh f r h
  obtain ⟨Fs, updated, hF, hd, _, _, _, _, _⟩ := fullReportK_ok h
  refine ⟨Fs, hF, ?_, ?_⟩
  · intro ⟨F, hF, he⟩
    have ha : Fs.any (fun f => f.trees.isEmpty) = true :=
      List.any_eq_true.mpr ⟨F, hF, by simp [he]⟩
    simp [dispatchK, ha] at hd
    exact ⟨hd.2.2.2, hd.1.symm⟩
  · intro hall
    have ha : Fs.any (fun f => f.trees.isEmpty) = false := by
      cases hb : Fs.any (fun f => f.trees.isEmpty)
      · rfl
      · obtain ⟨F, hF, ht⟩ := List.any_eq_true.mp hb
        exact (hall F hF (by simpa using ht)).elim
    simp only [dispatchK, ha, Bool.false_eq_true, if_false] at hd
    exact selectTargets_calls _ _ _ _ _ _ _ _ hd

end SymReg.MLJ
