import SymReg.Loss.Core

namespace SymReg.Loss
open DynExpr

/-- Column-major matrix representation for rectangular sample columns
(`src/Dataset.jl:22`; DE `Runtime/Array.lean:20-24`). -/
def columnsMatrix (columns : List (List JF)) : JMat JF :=
  let nrows := (columns.head?.getD []).length
  { nrows := nrows
    ncols := columns.length
    data := Array.ofFn (fun i : Fin (nrows * columns.length) =>
      ((columns[i.val / nrows]?.getD [])[i.val % nrows]?).getD (.fin 0))
    size_eq := by simp }

/-- DE evaluation, with the ordinary addition enum and no allocation buffer.
This uses the actual imported evaluator rather than defining new tree semantics
(`src/LossFunctions.jl:87-89,103-105`). -/
def deEvaluation (e : Expr) (columns : List (List JF)) : Jl Reply :=
  fromDE (Eval.evalTreeArray {} ⟨fun _ _ => .error (.userError "unused turbo extension")⟩
    2 e.tree (columnsMatrix columns)
    ⟨[[], [fun xs => match xs with | [x, y] => x + y | _ => .nan]]⟩
    ⟨false, false, true, .none, true⟩)

/-- Ordinary squared real error, the L2DistLoss numeric specialization
(`src/LossFunctions.jl:58,69`). -/
def squaredError (x y : JF) : JF := (x - y) * (x - y)

/-- A numeric option instance for concrete counterexamples; the evaluator is DE's.
Context is absent in every counterexample below. -/
def squaredOptions : Options :=
  { elementwise := .supervised (fun x y => .ok (squaredError x y))
    run := fun e columns context =>
      (deEvaluation e columns).map (fun reply => (reply, context)) }

/-- The numeric Dataset constructor's average branch is unreachable because
`eltype(y) isa Number` is false: eltype returns a type object, not a numeric value
(`src/Dataset.jl:183-191`). The other constructor fields here are its loss projections. -/
def numericDataset (columns : List (List JF)) (y : Option (List JF))
    (weights : Option (List JF) := none) : Dataset :=
  ⟨{ columns := columns, y := y, weights := weights, avgY := none,
     useBaseline := true, baselineLoss := .fin 1 }, none⟩

/-- The documented numeric sample mean, weighted when weights are present
(`src/Dataset.jl:33,36-38,186-189`). This is a specification, not the constructor. -/
def targetAverage (y : List JF) (weights : Option (List JF)) : JF :=
  match weights with
  | none => sumF y / .fin (y.length : Rat)
  | some w => sumF (List.zipWith JF.mul y w) / sumF w

/-- A nonempty, one-feature numeric dataset used to witness reasonable preconditions. -/
def witnessDataset : Dataset := numericDataset [[.fin 1], [.fin 2]] (some [.fin 2, .fin 4])

def witnessExpr : Expr := .expression (.const (.fin 0)) 0

end SymReg.Loss
