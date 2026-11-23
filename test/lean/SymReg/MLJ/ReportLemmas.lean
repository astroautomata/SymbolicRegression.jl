import SymReg.MLJ.SelectProps
import SymReg.HofMig.Frontier
import SymReg.HofMig.ScoreProofs

namespace SymReg.MLJ
open DynExpr SymReg.HofMig
open DynExpr.Expressions.Sampling (greater)

/-! ## Formatting does not depend on the identity supply -/

/-- A member without its two allocation identities. -/
def strip (m : Member) : Member := { m with objectId := 0, treeId := 0 }

theorem copyMembers_strip (ms : List Member) (fresh : Nat) :
    (copyMembers ms fresh).1.map strip = ms.map strip := by
  induction ms generalizing fresh with
  | nil => rfl
  | cons m ms ih => simp [copyMembers, copyMember, strip, ih]

/-- `format_hall_of_fame` on an explicit front, src/HallOfFame.jl:284-325. -/
def formatSpec (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int)
    (front : List Member) : Jl Formatted := do
  if scale = .log ∧ front.any (fun m => less m.loss (.fin 0)) then
    throw (.domainError negativeLossMessage)
  let scores ← scoreRows rt scale compute front none
  return ⟨front.map Member.tree, scores, front.map Member.loss,
    front.map (fun m => (resolveComplexity compute m).2)⟩

theorem formatHof_eq (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int) (h : Hof)
    (fresh : Nat) : formatHof rt scale compute h fresh =
      (formatSpec rt scale compute (calculatePareto h fresh).1).map
        (fun F => (F, (calculatePareto h fresh).2)) := by
  cases hp : calculatePareto h fresh with
  | mk front f =>
    simp only [formatHof, formatSpec, hp]
    have hh : (firstNegative scale front).isSome =
        decide (scale = .log ∧ front.any (fun m => less m.loss (.fin 0)) = true) := by
      by_cases hs : scale = .log
      · simp only [firstNegative, hs, if_true, List.isSome_find?, true_and]
        cases ha : front.any (fun m => less m.loss (.fin 0)) with
        | false => simp [← List.any_eq_true, ha]
        | true => simp [← List.any_eq_true, ha]
      · simp [firstNegative, hs]
    cases hn : firstNegative scale front with
    | some m =>
      have hg : scale = .log ∧ front.any (fun m => less m.loss (.fin 0)) = true := by
        simpa [hn] using hh.symm
      rw [if_pos hg]
      rfl
    | none =>
      have hg : ¬ (scale = .log ∧ front.any (fun m => less m.loss (.fin 0)) = true) := by
        simpa [hn] using hh.symm
      rw [if_neg hg]
      cases scoreRows rt scale compute front none <;> rfl

theorem resolve_strip (compute : Nat → Int) (m : Member) :
    (resolveComplexity compute (strip m)).2 = (resolveComplexity compute m).2 := by
  by_cases hc : m.complexity = -1 <;> simp [resolveComplexity, strip, hc]

theorem scoreRows_strip (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int) :
    ∀ (ms : List Member) (prev : Option (JF × Int)),
      scoreRows rt scale compute (ms.map strip) prev = scoreRows rt scale compute ms prev := by
  intro ms prev
  have hp : (fun m : Member => ((strip m).scoreLoss rt.precision, (resolveComplexity compute (strip m)).2)) =
      (fun m : Member => (m.scoreLoss rt.precision, (resolveComplexity compute m).2)) := by
    funext m
    rw [resolve_strip]
    rfl
  simp only [scoreRows, List.map_map, Function.comp_def, hp]

theorem formatSpec_strip (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int)
    (ms : List Member) : formatSpec rt scale compute (ms.map strip) = formatSpec rt scale compute ms := by
  simp only [formatSpec, scoreRows_strip, List.any_map, List.map_map]
  have h1 : Member.tree ∘ strip = Member.tree := rfl
  have h2 : Member.loss ∘ strip = Member.loss := rfl
  have h3 : (fun m => (resolveComplexity compute m).2) ∘ strip =
      fun m => (resolveComplexity compute m).2 := funext fun m => resolve_strip compute m
  have h4 : (fun m => less m.loss (.fin 0)) ∘ strip = fun m => less m.loss (.fin 0) := rfl
  rw [h1, h2, h3, h4]

theorem formatSpec_pareto (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int) (h : Hof)
    (fresh : Nat) : formatSpec rt scale compute (calculatePareto h fresh).1 =
      formatSpec rt scale compute ((frontRaw [] h.slots).map strip) := by
  rw [← formatSpec_strip rt scale compute (calculatePareto h fresh).1, calculatePareto,
    copyMembers_strip]

theorem formatHof_fresh {rt : ScalarRuntime} {scale : LossScale} {compute : Nat → Int} {h : Hof}
    {f1 f2 a : Nat} {F : Formatted} (hf : formatHof rt scale compute h f1 = .ok (F, a)) :
    formatHof rt scale compute h f2 = .ok (F, (calculatePareto h f2).2) := by
  rw [formatHof_eq, formatSpec_pareto] at hf ⊢
  cases hs : formatSpec rt scale compute ((frontRaw [] h.slots).map strip) with
  | error e => rw [hs] at hf; cases hf
  | ok G => rw [hs] at hf; cases hf; rfl

/-! ## Facts about formatted fronts -/

theorem front_member {h : Hof} {fresh : Nat} {x : Member} (hx : x ∈ (calculatePareto h fresh).1) :
    ∃ s ∈ h.slots, s.exists = true ∧ strip s.member = strip x := by
  have hmem : strip x ∈ (frontRaw [] h.slots).map strip := by
    rw [← copyMembers_strip (frontRaw [] h.slots) fresh]
    exact List.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
  have := (frontRaw_sublist [] h.slots).subset hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp this
  obtain ⟨hs, he⟩ := List.mem_filter.mp hs
  exact ⟨s, hs, he, hyx⟩

theorem formatSpec_ok {rt : ScalarRuntime} {scale : LossScale} {compute : Nat → Int}
    {front : List Member} {F : Formatted} (h : formatSpec rt scale compute front = .ok F) :
    (scale = .log → ∀ m ∈ front, less m.loss (.fin 0) = false) ∧
    scoreRows rt scale compute front none = .ok F.scores ∧ F.trees = front.map Member.tree ∧
    F.losses = front.map Member.loss ∧
    F.complexities = front.map (fun m => (resolveComplexity compute m).2) := by
  simp only [formatSpec] at h
  split at h
  · cases h
  · rename_i hneg
    cases hs : scoreRows rt scale compute front none with
    | error e => rw [hs] at h; cases h
    | ok sc =>
      rw [hs] at h; cases h
      refine ⟨fun hl m hm => ?_, rfl, rfl, rfl, rfl⟩
      cases hlm : less m.loss (.fin 0)
      · rfl
      · exact absurd ⟨hl, List.any_eq_true.mpr ⟨m, hm, hlm⟩⟩ hneg

theorem scoreRows_good (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int) :
    ∀ (ms : List Member) (prev : Option (JF × Int)) (out : List JF),
      scoreRows rt scale compute ms prev = .ok out → ∀ s ∈ out, s ≠ .nan ∧ s ≠ .negInf := by
  intro ms prev out h s hs
  simp only [scoreRows] at h
  cases hv : typedScoreRows rt scale
      (ms.map fun m => (m.scoreLoss rt.precision, (resolveComplexity compute m).2))
      (prev.map fun (l, c) => (⟨rt.precision, l, false⟩, c)) with
  | error e => simp [hv, Except.map] at h
  | ok scores =>
    simp [hv, Except.map] at h
    subst out
    obtain ⟨score, hm, rfl⟩ := List.mem_map.mp hs
    exact typedScoreRows_good _ _ _ _ _ hv _ hm

/-! ## Decomposing reports -/

theorem fullReport1_ok {m : Regressor} {fr : FitResult State1 U D} {ws : Bool} {fresh f : Nat}
    {r : Report1} (h : fullReport1 m fr ws fresh = .ok (r, f)) :
    ∃ F updated, formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh = .ok (F, f) ∧
      dispatch1 m.selection F fr.options m.selectionState =
        .ok (r.bestIdx, updated, r.selectionState, r.selectionCalls) ∧
      r.equations = updated.trees ∧ r.losses = updated.losses ∧
      r.complexities = updated.complexities ∧ r.scores = updated.scores ∧
      r.equationStrings = (if ws then some (strings1 fr.options F.trees fr.variableNames) else none) := by
  simp only [fullReport1] at h
  cases hF : formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh with
  | error e => rw [hF] at h; cases h
  | ok p =>
    obtain ⟨F, f'⟩ := p
    rw [hF] at h
    cases hd : dispatch1 m.selection F fr.options m.selectionState with
    | error e => simp [hd, bind, Except.bind] at h
    | ok p =>
      obtain ⟨b, updated, state, calls⟩ := p
      simp [hd, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨F, updated, rfl, hd, rfl, rfl, rfl, rfl, rfl⟩

theorem fullReport1_of {m : Regressor} {fr : FitResult State1 U D} {ws : Bool} {fresh f : Nat}
    {F updated : Formatted} {b : Int} {state : Nat} {calls : List SelectionCall}
    (hF : formatHof fr.options.rt fr.options.scale fr.options.compute fr.state.hof fresh = .ok (F, f))
    (hd : dispatch1 m.selection F fr.options m.selectionState = .ok (b, updated, state, calls)) :
    fullReport1 m fr ws fresh = .ok (⟨b, updated.trees,
      (if ws then some (strings1 fr.options F.trees fr.variableNames) else none),
      updated.losses, updated.complexities, updated.scores, state, calls⟩, f) := by
  simp [fullReport1, hF, hd, bind, Except.bind, pure, Except.pure]

theorem formatMany_ok (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int) :
    ∀ (hs : List Hof) (fresh f : Nat) (Fs : List Formatted),
      formatMany rt scale compute hs fresh = .ok (Fs, f) →
      Fs.length = hs.length ∧ ∀ (t : Nat) F, Fs[t]? = some F →
        ∃ h g g', hs[t]? = some h ∧ formatHof rt scale compute h g = .ok (F, g') := by
  intro hs
  induction hs with
  | nil => intro fresh f Fs h; simp [formatMany, pure, Except.pure] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | cons h hs ih =>
    intro fresh f Fs hh
    cases h1 : formatHof rt scale compute h fresh with
    | error e => simp [formatMany, h1, bind, Except.bind] at hh
    | ok p =>
      obtain ⟨F, g⟩ := p
      cases h2 : formatMany rt scale compute hs g with
      | error e => simp [formatMany, h1, h2, bind, Except.bind] at hh
      | ok q =>
        obtain ⟨Fs', g'⟩ := q
        simp [formatMany, h1, h2, bind, Except.bind, pure, Except.pure] at hh
        obtain ⟨rfl, rfl⟩ := hh
        obtain ⟨hl, ht⟩ := ih g g' Fs' h2
        refine ⟨by simp [hl], ?_⟩
        intro t G hG
        cases t with
        | zero => simp at hG; subst hG; exact ⟨h, fresh, g, rfl, h1⟩
        | succ t => simpa using ht t G (by simpa using hG)

theorem fullReportK_ok {m : Regressor} {fr : FitResult StateK U D} {ws : Bool} {fresh f : Nat}
    {r : ReportK} (h : fullReportK m fr ws fresh = .ok (r, f)) :
    ∃ Fs updated, formatMany fr.options.rt fr.options.scale fr.options.compute fr.state.hofs fresh = .ok (Fs, f) ∧
      dispatchK m.selection Fs fr.options m.selectionState =
        .ok (r.bestIdx, updated, r.selectionState, r.selectionCalls) ∧
      r.equations = updated.map Formatted.trees ∧ r.losses = updated.map Formatted.losses ∧
      r.complexities = updated.map Formatted.complexities ∧ r.scores = updated.map Formatted.scores ∧
      r.equationStrings =
        (if ws then some (stringsK fr.options (Fs.map Formatted.trees) fr.variableNames) else none) := by
  simp only [fullReportK] at h
  cases hF : formatMany fr.options.rt fr.options.scale fr.options.compute fr.state.hofs fresh with
  | error e => rw [hF] at h; cases h
  | ok p =>
    obtain ⟨Fs, f'⟩ := p
    rw [hF] at h
    cases hd : dispatchK m.selection Fs fr.options m.selectionState with
    | error e => simp [hd, bind, Except.bind] at h
    | ok p =>
      obtain ⟨b, updated, state, calls⟩ := p
      simp [hd, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Fs, updated, rfl, hd, rfl, rfl, rfl, rfl, rfl⟩

end SymReg.MLJ
