import SymReg.MLJ.FitProps
import SymReg.MLJ.UnitsProps

/-! Witnesses that the preconditions of the MLJ properties are satisfiable. -/

namespace SymReg.MLJ
open DynExpr SymReg.HofMig

theorem ok_of_isSome {e : Except ε α} (h : e.toOption.isSome = true) : ∃ a, e = .ok a := by
  cases e with
  | error => simp [Except.toOption] at h
  | ok a => exact ⟨a, rfl⟩

/-- Losses [2, 1] at complexities 1, 2. -/
def twoHof : Hof := ⟨[slotOf (.fin 2) 1 0, slotOf (.fin 1) 2 1]⟩

theorem twoHof_report :
    (fullReport1 defaultModel (fit1Of twoHof .log) false 0).toOption.map (·.1.equations) =
      some [0, 1] := by decide +kernel

/-- Preconditions of `mlj-rep-default-rule`, `mlj-rep-order` and `mlj-pred-idx`. -/
example : ∃ r f, fullReport1 defaultModel (fit1Of twoHof .log) false 0 = .ok (r, f) ∧
    r.equations ≠ [] ∧ r.equations[((1 : Int) - 1).toNat]? = some 0 ∧
    (∀ s ∈ (fit1Of twoHof .log).state.hof.slots, s.exists = true → s.member.loss ≠ .nan) ∧
    ((twoHof.slots.filter Slot.exists).map Slot.member).Pairwise
      (fun a b => a.complexity < b.complexity) ∧
    NotSelector oneCell ∧
    getMatrixAndInfo unitServices.subscript oneCell = .ok (⟨1, [[.fin 0]]⟩, ["x1"], ["x"], [()]) ∧
    ["x1"] = (fit1Of twoHof .log).variableNames ∧
    unitsMatch (cleanUnitsVec [()]) (fit1Of twoHof .log).xUnits = .ok true := by
  have h := twoHof_report
  cases hr : fullReport1 defaultModel (fit1Of twoHof .log) false 0 with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    simp [Except.toOption] at h
    exact ⟨p.1, p.2, rfl, by simp [h], by simp [h], by decide, by decide, trivial,
      ok_of_toOption (by decide), rfl, rfl⟩

def unitFitServices : FitServices Unit :=
  ⟨fun _ => .ok (plainOpts .log), fun _ _ => .ok (), fun _ => .ok ⟨0, twoHof⟩,
    fun _ => .ok ⟨0, [twoHof, twoHof]⟩, fun _ => ""⟩

def yVec : Data Unit := .vector [(.fin 1, ())]
def yTwo : Data Unit := .matrix 1 [[(.fin 1, ())], [(.fin 2, ())]]

/-- The fit result `unitFitServices` produces for `defaultModel`. -/
def fitted : Fit1 Unit :=
  ⟨defaultModel, ⟨0, twoHof⟩, 100, 1, plainOpts .log, ["x1"], none, false, none, none⟩

/-- Preconditions of `mlj-fit-fresh` and `mlj-fitted-params`. -/
example : ∃ p, fit1 unitFitServices defaultModel oneCell yVec none 0 = .ok p :=
  ok_of_isSome (by decide +kernel)

/-- Preconditions of `mlj-update-warm`. -/
example : ∃ p, update1 unitFitServices defaultModel (some fitted) oneCell yVec none 0 = .ok p :=
  ok_of_isSome (by decide +kernel)

/-- Preconditions of `mlj-update-decrease` and `mlj-clean-negative`. -/
example : unitFitServices.getOptions { defaultModel with niterations := 50 } = .ok (plainOpts .log) ∧
    unitFitServices.checkWarm fitted.options (plainOpts .log) = .ok () ∧
    getMatrixAndInfo unitFitServices.subscript oneCell = .ok (⟨1, [[.fin 0]]⟩, ["x1"], ["x"], [()]) ∧
    formatY1 yVec = .ok ([.fin 1], none, ()) ∧
    ({ defaultModel with niterations := 50 } : Regressor).niterations < fitted.niterations ∧
    ({ defaultModel with niterations := -1 } : Regressor).niterations < 0 :=
  ⟨rfl, rfl, ok_of_toOption (by decide), rfl, by decide, by decide⟩

/-- Preconditions of `mlj-fit-multi-targets`. -/
example : ∃ p, fitK unitFitServices defaultModel oneCell yTwo (some [.fin 1]) 0 = .ok p :=
  ok_of_isSome (by decide +kernel)

instance boolDims : Dims Bool := ⟨inferInstance, false⟩

/-- Preconditions of `mlj-units-unwrap-error`: feature 1 mixes two dimensions. -/
example : (∀ p ∈ ([] : List (Cell Bool × List (Cell Bool))), ∀ x ∈ p.2, x.2 = p.1.2) ∧
    (∃ x ∈ [((.fin 0 : JF), true)], x.2 ≠ ((.fin 0 : JF), false).2) ∧
    (∀ r ∈ ([] : List (List (Cell Bool))), r ≠ []) := by decide

end SymReg.MLJ
