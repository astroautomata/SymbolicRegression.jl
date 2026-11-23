import SymReg.Loss.Witnesses

namespace SymReg.Loss
open DynExpr

/-- Documented baseline: evaluate the constant sample-average predictor with the
same configured expression builder and objective (`src/Dataset.jl:33-38`). -/
def baselineAtAverage (d : Dataset) (o : Options) (y : List JF) : Jl JF := do
  let e ← o.createExpression (targetAverage y d.full.weights) d
  let (value, _) ← evalLoss e d o
  pure (updateFromValue d.full value).baselineLoss

/-- Updating a numeric dataset should store the documented average-predictor loss. -/
def baseline_average : Prop :=
  ∀ (d : Dataset) (o : Options) (y : List JF),
    d.indices = none → getY d = .ok y → y.isEmpty = false →
    (updateBaselineLoss d o).map (fun d => d.full.baselineLoss) = baselineAtAverage d o y

theorem baseline_average_refuted : ¬ baseline_average := by
  intro h
  have hbad := h witnessDataset squaredOptions [.fin 2, .fin 4] rfl rfl rfl
  have hdifferent :
      (updateBaselineLoss witnessDataset squaredOptions).map (fun d => d.full.baselineLoss) ≠
        baselineAtAverage witnessDataset squaredOptions [.fin 2, .fin 4] := by
    decide +kernel
  exact hdifferent hbad

/-- The numeric Dataset constructor should record the documented mean of its targets. -/
def dataset_average : Prop :=
  ∀ (columns : List (List JF)) (y : List JF) (weights : Option (List JF)),
    columns.length = y.length → y.isEmpty = false →
    (∀ w, weights = some w → w.length = y.length) →
    (numericDataset columns (some y) weights).full.avgY = some (targetAverage y weights)

theorem dataset_average_refuted : ¬ dataset_average := by
  intro h
  have hbad := h [[.fin 1], [.fin 2]] [.fin 2, .fin 4] none rfl rfl
    (by intro w hw; cases hw)
  cases hbad

/-- An explicit index list should select columns, targets and weights for the
ordinary elementwise objective just as a SubDataset does. -/
def explicit_index : Prop :=
  ∀ (e : Expr) (d : Dataset) (o : Options) (idx : List Nat),
    o.lossFunction = none → o.lossFunctionExpression = none →
    (evalLoss e d o true (some idx)).map Prod.fst =
      (evalLoss e { d with indices := some idx } o).map Prod.fst

theorem explicit_index_refuted : ¬ explicit_index := by
  intro h
  let d := numericDataset [[.fin 1], [.fin 3]] (some [.fin 0, .fin 0])
    (some [.fin 1, .fin 3])
  let e := Expr.expression (.feature 1) 0
  have hbad := h e d squaredOptions [1] rfl rfl
  have hdifferent :
      (evalLoss e d squaredOptions true (some [1])).map Prod.fst ≠
        (evalLoss e { d with indices := some [1] } squaredOptions).map Prod.fst := by
    decide +kernel
  exact hdifferent hbad

end SymReg.Loss
