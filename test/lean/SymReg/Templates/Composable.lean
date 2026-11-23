import DynExpr.Eval.Refute
import DynExpr.Expressions.Wrapper
import DynExpr.NodeUtils.Values
import SymReg.Templates.Structure

/-!
`ValidVector` arithmetic and `ComposableExpression` calls, `src/ComposableExpression.jl:155-419`.
A composable expression is DE's `Expression` wrapper (`DynExpr.Expressions.Expression` with
`Settings`); its evaluation is DE's `eval_tree_array(::AbstractExpression, ...)` forwarding
(`DynExpr.Expressions.forwardEval`), parametrised by the tree evaluator.
-/

namespace SymReg.Templates
open DynExpr DynExpr.Expressions

/-- `ValidVector`, `src/ComposableExpression.jl:174-178`. -/
structure VV (T : Type) where
  x : List T
  valid : Bool
  deriving DecidableEq, Repr

/-- An operand of the overloaded operators and calls: a `ValidVector` or a `Number`
(`src/ComposableExpression.jl:211-213,380-412`). -/
inductive Arg (T : Type) where
  | vv (v : VV T)
  | num (a : T)

/-- `_is_valid`, `src/ComposableExpression.jl:315-316`. -/
def Arg.isValid {T : Type} : Arg T → Bool
  | .vv v => v.valid
  | .num _ => true

/-- The first `ValidVector` operand (`something(map(xi -> xi isa ValidVector ? xi : nothing, x)...)`,
`src/ComposableExpression.jl:299-301`). -/
def firstVV {T : Type} : List (Arg T) → Option (VV T)
  | [] => none
  | .vv v :: _ => some v
  | .num _ :: as => firstVV as

/-- Result length of Julia broadcasting over the operands: vectors of length one broadcast,
all other vector lengths must agree. -/
def bcastLen {T : Type} (args : List (Arg T)) : Option Nat :=
  let ls := args.filterMap fun | .vv v => some v.x.length | .num _ => none
  match ls.filter (· ≠ 1) with
  | [] => some 1
  | n :: rest => if rest.all (· = n) then some n else none

/-- Default element for out-of-range broadcast reads, which successful broadcasts never make. -/
private instance instInhabitedJF : Inhabited JF := ⟨.nan⟩

/-- Element `j` of a broadcast operand. -/
def argAt {T : Type} [Inhabited T] : Arg T → Nat → T
  | .vv v, j => if v.x.length = 1 then v.x[0]! else v.x[j]!
  | .num a, _ => a

/-- `safe_op.(vx...)`, `src/ComposableExpression.jl:276-280`; the (safe) operator is arbitrary. -/
def broadcastOp {T : Type} [Inhabited T] (f : List T → T) (args : List (Arg T)) : Jl (List T) :=
  match bcastLen args with
  | none => .error (.errorException "DimensionMismatch")
  | some n => .ok ((List.range n).map fun j => f (args.map (argAt · j)))

/-- `apply_operator` with `_apply_operator`, `_apply_operator_values` and `_match_eltype`,
`src/ComposableExpression.jl:276-327`, for `JF` data (`_match_eltype` is the identity when the
element type is unchanged). Validity of the result is DE's `is_valid_array`. -/
def applyOp (f : List JF → JF) (args : List (Arg JF)) : Jl (VV JF) :=
  if args.all Arg.isValid then do
    let r ← broadcastOp f args
    pure ⟨r, NodeUtils.isValidArray r⟩
  else match firstVV args with
    | some v => .ok ⟨v.x, false⟩
    | none => .error (.argumentError "No value arguments present")

/-- Operands of an overloaded operator, including plain `AbstractVector`s, which the
`ValidVector` methods reject (`src/ComposableExpression.jl:387-393`). -/
inductive Operand (T : Type) where
  | arg (a : Arg T)
  | plain (xs : List T)

/-- The binary operator methods of `src/ComposableExpression.jl:380-394`. -/
def binaryOp (f : List JF → JF) : Operand JF → Operand JF → Jl (VV JF)
  | .arg (.vv a), .arg b => applyOp f [.vv a, b]
  | .arg (.num y), .arg (.vv b) => applyOp f [.num y, .vv b]
  | .arg (.vv _), .plain _ => .error (.errorException "ValidVectorMixError")
  | .plain _, .arg (.vv _) => .error (.errorException "ValidVectorMixError")
  | _, _ => .error (.methodError "no method")

/-- The array accessors overloaded on `ValidVector`, `src/ComposableExpression.jl:415-419`. -/
inductive VVAccess where
  | length | push | getindex | size | append | setindex

/-- Each accessor throws `ValidVectorAccessError`. -/
def vvAccess {T : Type} (_ : VVAccess) (_ : VV T) : Jl Unit :=
  .error (.errorException "ValidVectorAccessError")

/-- `eval_tree_array(ex, X; eval_context)` on a composable expression: DE's
`AbstractExpression` forwarding with input validation, `typed` for an `OperatorEnum`. -/
def evalCE (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool))
    (ex : Expression JF (Settings JF)) (X : JMat JF) : Jl (List JF × Bool) :=
  forwardEval treeEval ex X ex.metadata.typed none

/-- `(ex::AbstractComposableExpression)(x::Union{ValidVector,Number}, ...)`,
`src/ComposableExpression.jl:211-240`: numbers are filled to the first `ValidVector`'s length;
with any invalid operand the result is the first operand's data, marked invalid, and nothing is
evaluated; otherwise the operands are stacked as the rows of the input matrix. -/
def callMixed (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool))
    (ex : Expression JF (Settings JF)) (args : List (Arg JF)) : Jl (VV JF) :=
  match firstVV args with
  | none => .error (.errorException "TypeError: findfirst returned nothing")
  | some sample =>
    let valid : List (VV JF) := args.map fun
      | .vv v => v
      | .num a => ⟨List.replicate sample.x.length a, true⟩
    if valid.all (·.valid) then
      match JMat.ofRows (valid.map (·.x)) with
      | none => .error (.errorException "DimensionMismatch")
      | some X => (evalCE treeEval ex X).map fun r => ⟨r.1, r.2⟩
    else match valid with
      | v :: _ => .ok ⟨v.x, false⟩
      | [] => .error (.argumentError "collection must be non-empty")

/-- Vector call, `src/ComposableExpression.jl:186-202`: invalid results are returned as
`x .* NaN`. -/
def callVectors (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool))
    (ex : Expression JF (Settings JF)) (xs : List (List JF)) : Jl (List JF) := do
  let r ← callMixed treeEval ex (xs.map fun x => .vv ⟨x, true⟩)
  if r.valid then pure r.x else pure (r.x.map fun v => JF.mul v .nan)

/-- Scalar call, `src/ComposableExpression.jl:203-209`: one-sample `ValidVector`s and
`only(_get_value(...))`. -/
def callNumbers (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool))
    (ex : Expression JF (Settings JF)) (xs : List JF) : Jl JF := do
  let r ← callMixed treeEval ex (xs.map fun a => .vv ⟨[a], true⟩)
  match r.x with
  | [y] => pure y
  | _ => .error (.argumentError "Collection must contain exactly one element")

/-- Zero-argument call, `src/ComposableExpression.jl:241-251`, on a `0×1` matrix with the
default evaluation context. -/
def callZero (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool))
    (ex : Expression JF (Settings JF)) : Jl JF := do
  let (out, complete) ← forwardEval treeEval ex ⟨0, 1, #[], rfl⟩ ex.metadata.typed none
  match out with
  | [y] => pure (if complete then y else .nan)
  | _ => .error (.argumentError "Collection must contain exactly one element")

mutual
/-- Composition `f(g1, g2, ...)`, `src/ComposableExpression.jl:253-269`. `copy` of a plain
`Node` breaks sharing, so every copied leaf is a distinct object; `foreach` tests
`degree == 0` before calling the closure (DE `src/base.jl` `call_mapreducer`) and so does not
descend into a replaced leaf; `set_node!` installs a fresh copy of the argument tree. Feature
`i` reads `xs_trees[i]` with bounds checking. -/
def compose {T : Type} (xs : List (Tree T)) : Tree T → Jl (Tree T)
  | .const v => .ok (.const v)
  | .feature i => if i = 0 then .error .boundsError else
      match xs[i - 1]? with
      | some s => .ok s
      | none => .error .boundsError
  | .branch op cs => do pure (.branch op (← composeL xs cs))
/-- Children of `compose`. -/
def composeL {T : Type} (xs : List (Tree T)) : List (Tree T) → Jl (List (Tree T))
  | [] => .ok []
  | c :: cs => do pure ((← compose xs c) :: (← composeL xs cs))
end

/-- `with_contents(ex, tree)` keeps the outer expression's metadata (`src/ComposableExpression.jl:268`). -/
def composeEx {T M : Type} (ex : Expression T M) (args : List (Expression T M)) : Jl (Expression T M) := do
  pure (with_contents ex (← compose (args.map get_contents) ex.tree))

/-! ## Properties -/

theorem isValidArray_iff (xs : List JF) : NodeUtils.isValidArray xs = xs.all JF.valid := by
  unfold NodeUtils.isValidArray NodeUtils.isValid
  rw [DynExpr.Eval.jf_foldl_valid]
  cases h : xs.all JF.valid <;> simp [JF.valid, h]

/-- Operator semantics on `ValidVector`s: with all operands valid, the result is the
pointwise (broadcast) operator result and is valid exactly when every value is finite; with an
invalid operand, the operator is not evaluated and the result is the first `ValidVector`'s
data marked invalid; mixing with a plain vector throws `ValidVectorMixError`. -/
def applyValidity : Prop :=
  ∀ (f : List JF → JF) (args : List (Arg JF)) (v : VV JF),
    (applyOp f args = .ok v →
      (v.valid = true ↔ (args.all Arg.isValid = true ∧ v.x.all JF.valid = true)) ∧
      (args.all Arg.isValid = true → ∃ n, bcastLen args = some n ∧
        v.x = (List.range n).map fun j => f (args.map (argAt · j)))) ∧
    (args.all Arg.isValid = false → firstVV args = some v → applyOp f args = .ok ⟨v.x, false⟩) ∧
    ∀ xs, binaryOp f (.arg (.vv v)) (.plain xs) = .error (.errorException "ValidVectorMixError") ∧
      binaryOp f (.plain xs) (.arg (.vv v)) = .error (.errorException "ValidVectorMixError")

theorem applyValidity_holds : applyValidity := by
  intro f args v
  refine ⟨fun h => ?_, fun hv hf => ?_, fun xs => ⟨rfl, rfl⟩⟩
  · unfold applyOp at h
    by_cases hall : args.all Arg.isValid = true
    · rw [if_pos hall] at h
      unfold broadcastOp at h
      cases hb : bcastLen args with
      | none => rw [hb] at h; cases h
      | some n =>
        rw [hb] at h
        cases h
        refine ⟨by simp [isValidArray_iff, hall], fun _ => ⟨n, rfl, rfl⟩⟩
    · rw [if_neg hall] at h
      cases hf : firstVV args with
      | none => rw [hf] at h; cases h
      | some w =>
        rw [hf] at h; cases h
        exact ⟨by simp [hall], fun h' => absurd h' hall⟩
  · unfold applyOp; rw [if_neg (by simp [hv]), hf]

example : applyOp (fun _ => .fin 1) [.vv ⟨[.fin 0], true⟩] = .ok ⟨[.fin 1], true⟩ := rfl

/-- An incomplete evaluation under a vector call yields only `NaN`s. -/
def vectorCallNaN : Prop :=
  ∀ treeEval (ex : Expression JF (Settings JF)) (xs : List (List JF)) out,
    callMixed treeEval ex (xs.map fun x => .vv ⟨x, true⟩) = .ok ⟨out, false⟩ →
    callVectors treeEval ex xs = .ok (out.map fun _ => .nan)

theorem mul_nan (v : JF) : JF.mul v .nan = .nan := by cases v <;> rfl

theorem vectorCallNaN_holds : vectorCallNaN := by
  intro treeEval ex xs out h
  simp only [callVectors, h, okBind]
  simp [mul_nan]

/-- Mixed calls: numbers become constant vectors of the first `ValidVector`'s length; an
invalid operand short-circuits to the first operand's data marked invalid; otherwise the call
evaluates the stacked operand rows. -/
def mixedCall : Prop :=
  ∀ treeEval (ex : Expression JF (Settings JF)) (args : List (Arg JF)) (sample : VV JF),
    firstVV args = some sample →
    let valid : List (VV JF) := args.map fun
      | .vv v => v
      | .num a => ⟨List.replicate sample.x.length a, true⟩
    (valid.all (·.valid) = false → ∃ v ∈ valid.head?, callMixed treeEval ex args = .ok ⟨v.x, false⟩) ∧
    ∀ X, JMat.ofRows (valid.map (·.x)) = some X → valid.all (·.valid) = true →
      callMixed treeEval ex args = (evalCE treeEval ex X).map fun r => ⟨r.1, r.2⟩

theorem mixedCall_holds : mixedCall := by
  intro treeEval ex args sample hs
  refine ⟨fun hv => ?_, fun X hX hv => ?_⟩
  · cases args with
    | nil => simp [firstVV] at hs
    | cons a as =>
      refine ⟨_, rfl, ?_⟩
      simp only [callMixed, hs] at hv ⊢
      rw [if_neg (by simp only [List.map_cons] at hv ⊢; rw [hv]; simp)]
      rfl
  · simp only [callMixed, hs]
    rw [if_pos hv, hX]

/-- The default evaluator: DE's `eval_tree_array` with `EvalContext()` (early exit, fused
kernels, no buffer) on binary-degree nodes. -/
def deEval (t : Tree JF) (X : JMat JF) (o : OpEnum JF) : Jl (List JF × Bool) :=
  DynExpr.Eval.obs (DynExpr.Eval.evalTreeArray {} DynExpr.Eval.Ex.noImpl 2 t X o
    (DynExpr.Eval.plainCtx true true .none))

/-- The scalar call returns the same value as the one-sample vector call, which maps an
incomplete evaluation to `NaN`. -/
def scalarCallAgrees : Prop :=
  ∀ (ex : Expression JF (Settings JF)) (xs : List JF) (y : JF),
    callNumbers deEval ex xs = .ok y → callVectors deEval ex (xs.map fun a => [a]) = .ok [y]

/-- `-(inv(x1))` under `OperatorEnum(1 => (inv, -), 2 => (+, /))`. -/
def negInv : Expression JF (Settings JF) :=
  ⟨.branch 2 [.branch 1 [.feature 1]], ⟨some DynExpr.Eval.Ex.ops, none, true⟩⟩

/-- The single sample `x1 = 0`. -/
def X1 : JMat JF := ⟨1, 1, #[.fin 0], rfl⟩

theorem ofRows_X1 : JMat.ofRows [[JF.fin 0]] = some X1 := by
  unfold JMat.ofRows
  rw [dif_pos (by decide)]
  rfl

theorem forwardEval_ok (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool))
    (ex : Expression JF (Settings JF)) (o : OpEnum JF) (X : JMat JF)
    (ho : ex.metadata.operators = some o) (hm : maxFeature ex.tree ≤ X.nrows) (typed : Bool) :
    forwardEval treeEval ex X typed none = treeEval ex.tree X o := by
  cases typed <;> simp [forwardEval, validateInput, get_operators, ho, hm, get_tree]

theorem negInv_mixed : callMixed deEval negInv [.vv ⟨[.fin 0], true⟩] = .ok ⟨[.posInf], false⟩ := by
  have h := (mixedCall_holds deEval negInv [.vv ⟨[.fin 0], true⟩] ⟨[.fin 0], true⟩ rfl).2 X1
    ofRows_X1 rfl
  rw [h, evalCE, forwardEval_ok deEval negInv _ X1 rfl (by simp [negInv, maxFeature, X1])]
  decide +kernel

theorem negInv_scalar : callNumbers deEval negInv [.fin 0] = .ok .posInf := by
  simp only [callNumbers, List.map_cons, List.map_nil, negInv_mixed]; rfl
theorem negInv_vector : callVectors deEval negInv [[.fin 0]] = .ok [.nan] := by
  simp only [callVectors, List.map_cons, List.map_nil, negInv_mixed]; rfl

theorem scalarCallAgrees_refuted : ¬ scalarCallAgrees := by
  intro h
  have := h negInv [.fin 0] .posInf negInv_scalar
  simp only [List.map_cons, List.map_nil] at this
  rw [negInv_vector] at this
  cases this

/-- Zero-argument calls: a tree reading a feature fails the typed input check (`max_feature`
exceeds the zero rows); otherwise the single value is returned when evaluation completes and
`NaN` when it does not. -/
def zeroArgCall : Prop :=
  ∀ treeEval (ex : Expression JF (Settings JF)) (o : OpEnum JF),
    ex.metadata.operators = some o → ex.metadata.typed = true →
    (0 < maxFeature ex.tree → ∃ msg, callZero treeEval ex = .error (.assertionError msg)) ∧
    (maxFeature ex.tree = 0 → ∀ y complete, treeEval ex.tree ⟨0, 1, #[], rfl⟩ o = .ok ([y], complete) →
      callZero treeEval ex = .ok (if complete then y else .nan))

theorem zeroArgCall_holds : zeroArgCall := by
  intro treeEval ex o ho ht
  refine ⟨fun hpos => ⟨"max_feature(ex) <= size(X, 1)", ?_⟩, fun hz y complete he => ?_⟩
  · simp only [callZero, forwardEval, validateInput, get_operators, ho, ht, okBind, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true]
    rw [if_neg (by simp; omega)]
    rfl
  · simp only [callZero, forwardEval, validateInput, get_operators, ho, ht, okBind, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true]
    rw [if_pos (by simp [hz])]
    simp only [okBind, get_tree, he]
    rfl

example : maxFeature (Tree.const (JF.fin 1)) = 0 := by simp [maxFeature]

/-- Arity checks: a `ValidVector` call with fewer rows than the expression's largest feature
fails DE's typed input check before evaluation. -/
def arityChecks : Prop :=
  ∀ treeEval (ex : Expression JF (Settings JF)) (o : OpEnum JF) (vs : List (VV JF)) X,
    ex.metadata.operators = some o → ex.metadata.typed = true → vs ≠ [] →
    vs.all (·.valid) = true → JMat.ofRows (vs.map (·.x)) = some X →
    vs.length < maxFeature ex.tree →
    callMixed treeEval ex (vs.map .vv) = .error (.assertionError "max_feature(ex) <= size(X, 1)")

theorem ofRows_nrows {T : Type} (xs : List (List T)) (X : JMat T) (h : JMat.ofRows xs = some X) :
    X.nrows = xs.length := by
  unfold JMat.ofRows at h
  split at h
  · cases h; rfl
  · cases h

theorem arityChecks_holds : arityChecks := by
  intro treeEval ex o vs X ho ht hne hv hX hlt
  cases vs with
  | nil => exact absurd rfl hne
  | cons v vs =>
    have hmap : ((v :: vs).map Arg.vv).map (fun a : Arg JF => match a with
        | .vv w => w | .num a => (⟨List.replicate v.x.length a, true⟩ : VV JF)) = v :: vs := by
      simp only [List.map_map]
      exact List.map_id'' (fun _ => rfl) _
    have hn := ofRows_nrows _ X hX
    simp only [List.length_map] at hn
    unfold callMixed
    rw [show firstVV ((v :: vs).map Arg.vv) = some v from rfl]
    dsimp only
    rw [hmap, if_pos hv, hX]
    simp only [evalCE, forwardEval, validateInput, get_operators, ho, ht, okBind, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true]
    rw [if_neg (by omega)]
    rfl

/-- Literal feature replacement, with original branch operators and child order. -/
def substituteContents {T : Type} (atFeature : Nat → Tree T) : Tree T → Tree T
  | .const v => .const v
  | .feature i => atFeature i
  | .branch op cs => .branch op (cs.map (substituteContents atFeature))

private theorem composeContents {T : Type} (xs : List (Tree T)) (t r : Tree T)
    (h : compose xs t = .ok r) :
    r = substituteContents (fun i => xs[i - 1]?.getD (.feature i)) t := by
  induction t using Tree.induction generalizing r with
  | hc v => cases h; simp [substituteContents]
  | hf i =>
    simp only [compose] at h
    split at h
    · cases h
    · cases hx : xs[i - 1]? with
      | none => rw [hx] at h; cases h
      | some s => rw [hx] at h; cases h; simp [substituteContents, hx]
  | hb op cs ih =>
    simp only [compose] at h
    cases hl : composeL xs cs with
    | error e => rw [hl] at h; cases h
    | ok rs =>
      rw [hl] at h; cases h
      suffices hmap : rs = cs.map (substituteContents fun i => xs[i - 1]?.getD (.feature i)) by
        simp [substituteContents, hmap]
      induction cs generalizing rs with
      | nil => cases hl; rfl
      | cons c cs ihc =>
        simp only [composeL] at hl
        cases hc : compose xs c with
        | error e => rw [hc] at hl; cases hl
        | ok r =>
          rw [hc, okBind] at hl
          cases hs : composeL xs cs with
          | error e => rw [hs] at hl; cases hl
          | ok rs =>
            rw [hs] at hl; cases hl
            simp only [List.map_cons, ih c (by simp) r hc,
              ihc (fun c' h' => ih c' (by simp [h'])) rs hs]

private theorem composeTreeDenote
    (T : Type) (o : OpEnum T) (xs : List (Tree T)) (t r : Tree T)
    (x : Nat → Option T) (h : compose xs t = .ok r) :
    r.denote o x = t.denote o (fun i => if i = 0 then none else (xs[i - 1]?).bind (Tree.denote o x)) := by
  revert r x h
  induction t using Tree.induction with
  | hc v => intro r x h; cases h; simp [Tree.denote]
  | hf i =>
    intro r x h
    simp only [compose] at h
    by_cases hi : i = 0
    · simp [hi] at h
    · simp only [hi, ↓reduceIte] at h
      cases hx : xs[i - 1]? with
      | none => rw [hx] at h; cases h
      | some s => rw [hx] at h; cases h; simp [Tree.denote, hi, hx]
  | hb op cs ih =>
    intro r x h
    simp only [compose] at h
    cases hl : composeL xs cs with
    | error e => rw [hl] at h; cases h
    | ok rs =>
      rw [hl] at h; cases h
      have key : ∀ (cs : List (Tree T)) rs, (∀ c ∈ cs, ∀ r x, compose xs c = .ok r →
          r.denote o x = c.denote o (fun i => if i = 0 then none else (xs[i - 1]?).bind (Tree.denote o x))) →
          composeL xs cs = .ok rs →
          rs.mapM (Tree.denote o x) = cs.mapM (Tree.denote o
            (fun i => if i = 0 then none else (xs[i - 1]?).bind (Tree.denote o x))) ∧ rs.length = cs.length := by
        intro cs
        induction cs with
        | nil => intro rs _ h; cases h; exact ⟨rfl, rfl⟩
        | cons c cs ihc =>
          intro rs hall h
          simp only [composeL] at h
          cases hc : compose xs c with
          | error e => rw [hc] at h; cases h
          | ok r1 =>
            rw [hc, okBind] at h
            cases hcs : composeL xs cs with
            | error e => rw [hcs] at h; cases h
            | ok rs' =>
              rw [hcs] at h; cases h
              obtain ⟨h1, h2⟩ := ihc rs' (fun c' hc' => hall c' (by simp [hc'])) hcs
              refine ⟨?_, by simp [h2]⟩
              simp only [List.mapM_cons, hall c (by simp) r1 x hc, h1]
      obtain ⟨h1, h2⟩ := key cs rs ih hl
      simp only [Tree.denote, h1, h2]

def composeDenote : Prop :=
  ∀ (T : Type) (ex : Expression T (Settings T)) (args : List (Expression T (Settings T)))
    (r : Expression T (Settings T)),
    args ≠ [] → composeEx ex args = .ok r →
    r.metadata = ex.metadata ∧
    r.tree = substituteContents
      (fun i => ((args.map get_contents)[i - 1]?).getD (.feature i)) ex.tree ∧
    ∀ o x, ex.metadata.operators = some o →
      r.tree.denote o x = ex.tree.denote o
        (fun i => if i = 0 then none else
          (args[i - 1]?).bind fun a => a.tree.denote o x) ∧
      ∀ (argOps : Expression T (Settings T) → OpEnum T),
        (∀ a ∈ args, a.tree.denote (argOps a) x = a.tree.denote o x) →
        r.tree.denote o x = ex.tree.denote o
          (fun i => if i = 0 then none else
            (args[i - 1]?).bind fun a => a.tree.denote (argOps a) x)

theorem composeDenote_holds : composeDenote := by
  intro T ex args r _ h
  simp only [composeEx] at h
  cases hc : compose (args.map get_contents) ex.tree with
  | error e => rw [hc] at h; cases h
  | ok t =>
    rw [hc] at h; cases h
    refine ⟨rfl, composeContents _ _ _ hc, fun o x _ => ?_⟩
    have hd := composeTreeDenote T o _ _ _ x hc
    have he : ∀ i : Nat, ((args.map get_contents)[i]?).bind (Tree.denote o x) =
        (args[i]?).bind (fun a : Expression T (Settings T) => a.tree.denote o x) := by
      intro i
      rw [List.getElem?_map]
      cases args[i]? <;> rfl
    simp only [he] at hd
    refine ⟨hd, fun argOps agree => hd.trans ?_⟩
    congr 1
    funext i
    split
    · rfl
    · cases ha : args[i - 1]? with
      | none => rfl
      | some a => exact (agree a (List.mem_of_getElem? ha)).symm

example : ∃ args : List (Expression JF (Settings JF)), args ≠ [] :=
  ⟨[⟨.const (.fin 1), ⟨none, none, true⟩⟩], by simp⟩

/-- Composition fails with a `BoundsError` exactly when some feature is not covered by an
argument; covered compositions keep the outer expression's metadata. -/
def composeBounds : Prop :=
  ∀ (T M : Type) (ex : Expression T M) (args : List (Expression T M)),
    args ≠ [] →
    (args.length < maxFeature ex.tree → composeEx ex args = .error .boundsError) ∧
    ∀ r, composeEx ex args = .ok r → r.metadata = ex.metadata

theorem compose_err {T : Type} (xs : List (Tree T)) :
    ∀ t : Tree T, ∀ e, compose xs t = .error e → e = .boundsError := by
  intro t
  induction t using Tree.induction with
  | hc v => intro e h; simp [compose] at h
  | hf i =>
    intro e h
    simp only [compose] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl
  | hb op cs ih =>
    intro e h
    have key : ∀ cs : List (Tree T), (∀ c ∈ cs, ∀ e, compose xs c = .error e → e = .boundsError) →
        ∀ e, composeL xs cs = .error e → e = .boundsError := by
      intro cs
      induction cs with
      | nil => intro _ e h; simp [composeL] at h
      | cons c cs ihc =>
        intro hall e h
        simp only [composeL] at h
        cases hc : compose xs c with
        | error e' => rw [hc] at h; cases h; exact hall c (by simp) _ hc
        | ok r =>
          rw [hc, okBind] at h
          cases hcs : composeL xs cs with
          | error e' => rw [hcs] at h; cases h; exact ihc (fun c' h' => hall c' (by simp [h'])) _ hcs
          | ok rs => rw [hcs] at h; cases h
    simp only [compose] at h
    cases hl : composeL xs cs with
    | error e' => rw [hl] at h; cases h; exact key cs ih _ hl
    | ok rs => rw [hl] at h; cases h

theorem maxFeature_compose {T : Type} (xs : List (Tree T)) :
    ∀ t : Tree T, xs.length < maxFeature t → compose xs t = .error .boundsError := by
  intro t
  induction t using Tree.induction with
  | hc v => intro h; simp [maxFeature] at h
  | hf i =>
    intro h
    simp only [maxFeature] at h
    simp only [compose]
    by_cases hi : i = 0
    · simp [hi]
    · rw [if_neg hi, List.getElem?_eq_none (by omega)]
  | hb op cs ih =>
    intro h
    simp only [maxFeature] at h
    have key : ∀ cs : List (Tree T), (∀ c ∈ cs, xs.length < maxFeature c → compose xs c = .error .boundsError) →
        xs.length < (cs.map maxFeature).foldr max 0 → composeL xs cs = .error .boundsError := by
      intro cs
      induction cs with
      | nil => intro _ h; simp at h
      | cons c cs ihc =>
        intro hall h
        simp only [List.map_cons, List.foldr_cons] at h
        simp only [composeL]
        by_cases hc : xs.length < maxFeature c
        · rw [hall c (by simp) hc]; rfl
        · have hr : xs.length < (cs.map maxFeature).foldr max 0 := by omega
          have he := ihc (fun c' hc' => hall c' (by simp [hc'])) hr
          cases hcomp : compose xs c with
          | error e' => rw [compose_err xs c e' hcomp]; rfl
          | ok r => simp only [okBind, he]; rfl
    simp [compose, key cs ih h]

theorem composeBounds_holds : composeBounds := by
  intro T M ex args _
  refine ⟨fun h => ?_, fun r h => ?_⟩
  · simp only [composeEx]
    rw [maxFeature_compose _ ex.tree (by simpa using h)]
    rfl
  · simp only [composeEx] at h
    cases hc : compose (args.map get_contents) ex.tree with
    | error e => rw [hc] at h; cases h
    | ok t => rw [hc] at h; cases h; rfl

-- Source: src/ComposableExpression.jl:96-101
/-
function DE.get_variable_names(
    ex::AbstractComposableExpression,
    variable_names::Union{Nothing,AbstractVector{<:AbstractString}}=nothing,
)
    return @something(variable_names, DE.get_metadata(ex).variable_names, Some(nothing))
end
-/
def composableVariableNames {A : Type} (override : Option A) (metadata : Jl (Option A)) : Jl (Option A) :=
  match override with
  | some xs => .ok (some xs)
  | none => metadata

-- Source: src/ComposableExpression.jl:395-397
/-
function Base.literal_pow(::typeof(^), x::ValidVector, ::Val{p}) where {p}
    return apply_operator(Fix{1}(Fix{3}(Base.literal_pow, Val(p)), ^), x)
end
-/
-- Source: src/ComposableExpression.jl:295-325. The inference result supplies
-- the inferred element type and the final Julia type assertion.
def validLiteralPow (scalar : List JF → JF) (inferred : Option (Nat × (VV JF → Bool)))
    (sourceType : Nat) (convert : Nat → JF → Jl JF) (x : VV JF) : Jl (VV JF) :=
  if x.valid then applyOp scalar [.vv x] else
  match inferred with
  | none => .ok ⟨x.x, false⟩
  | some (target, accepts) => do
    let values ← if target = sourceType then pure x.x else x.x.mapM (convert target)
    let out : VV JF := ⟨values, false⟩
    if accepts out then pure out else throw (.errorException "TypeError")

def literalPowInvalid : Prop := ∀ scalar source target convert (xs : List JF) accepts,
  (∀ r, validLiteralPow scalar (some (target, accepts)) source convert ⟨xs, false⟩ = .ok r →
    r.valid = false ∧ (target = source → r.x = xs) ∧
    (target ≠ source → xs.mapM (convert target) = .ok r.x)) ∧
  (∀ e, target ≠ source → xs.mapM (convert target) = .error e →
    validLiteralPow scalar (some (target, accepts)) source convert ⟨xs, false⟩ = .error e) ∧
  validLiteralPow scalar none source convert ⟨xs, false⟩ = .ok ⟨xs, false⟩

theorem literalPowInvalid_holds : literalPowInvalid := by
  intro scalar source target convert xs accepts
  refine ⟨?_, ?_, rfl⟩
  · intro r h
    by_cases ht : target = source
    · simp [validLiteralPow, ht, bind, Except.bind, pure, Except.pure] at h
      split at h <;> cases h
      simp [ht]
    · cases hc : xs.mapM (convert target) with
      | error e => simp [validLiteralPow, ht, hc, bind, Except.bind] at h
      | ok v =>
        simp [validLiteralPow, ht, hc, bind, Except.bind, pure, Except.pure] at h
        split at h <;> cases h
        simp [ht]
  · intro e ht he
    simp [validLiteralPow, ht, he, bind, Except.bind]

def composableNamesPriority : Prop := ∀ (metadata : Jl (Option (List String))) xs,
  composableVariableNames (some xs) metadata = .ok (some xs) ∧
  (∀ err, metadata = .error err → composableVariableNames none metadata = .error err)

theorem composableNamesPriority_holds : composableNamesPriority := by
  intro metadata xs
  exact ⟨rfl, fun _ h => h⟩

end SymReg.Templates
