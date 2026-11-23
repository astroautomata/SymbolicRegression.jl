import SymReg.Templates.Template
import SymReg.Complexity
import DynExpr.NodeUtils.Nodes

/-!
Template complexity, constant counting, copying and equality, mutation and crossover hooks,
parameter initialisation, `copy_into!` and printing, `src/TemplateExpression.jl:411-416,
514-541,651-701,707-784,966-1123,1168-1170`.
-/

namespace SymReg.Templates
open DynExpr DynExpr.Expressions SymReg.Complexity
/-! ## Complexity -/

/-- The argument of a user complexity function: the template itself or one inner expression. -/
inductive AnyEx (M : Type) where
  | template (t : TExpr M)
  | inner (e : Expression JF M)

/-- `options.complexity_mapping`: a `ComplexityMapping` or a user function. -/
inductive CMapping (M : Type) where
  | weights (m : CMap)
  | custom (f : AnyEx M → Int)

/-- `compute_complexity(::AbstractExpression, options)`, `src/Complexity.jl:20-27`, on an
inner expression. -/
def innerComplexity {M : Type} (D : Nat) : CMapping M → Expression JF M → Jl Int
  | .weights m, e => computeComplexityT D m e.tree
  | .custom f, e => pure (f (.inner e))

/-- `sum(f, itr)` on a nonempty tuple. -/
def sumJ {α : Type} (f : α → Jl Int) : List α → Jl Int
  | [] => throw (.argumentError "reducing over an empty collection is not allowed")
  | a :: as => do as.foldlM (fun acc b => do pure (acc + (← f b))) (← f a)

/-- `compute_complexity(::TemplateExpression, options)`, `src/TemplateExpression.jl:707-716`. -/
def templateComplexity {M : Type} (D : Nat) (mp : CMapping M) (ex : TExpr M) : Jl Int :=
  sumJ (innerComplexity D mp) ex.inners

theorem foldl_sum {α : Type} (f : α → Jl Int) :
    ∀ (as : List α) (cs : List Int) (a0 : Int), as.mapM f = .ok cs →
      as.foldlM (fun acc b => do pure (acc + (← f b))) a0 = .ok (a0 + cs.sum)
  | [], cs, a0, h => by cases h; simp
  | a :: as, cs, a0, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok c =>
      cases hl : as.mapM f with
      | error e => rw [ha, hl] at h; cases h
      | ok cs' =>
        rw [ha, hl] at h
        cases h
        simp only [List.foldlM_cons, ha, okBind, pure_bind]
        rw [foldl_sum f as cs' (a0 + c) hl]
        simp only [List.sum_cons]
        congr 1; omega

/-- A template's complexity is the sum of its inner expressions' complexities under the same
mapping, whatever its parameters and combiner. -/
def complexitySum : Prop :=
  ∀ (M : Type) (D : Nat) (mp : CMapping M) (ex : TExpr M) (cs : List Int),
    ex.inners ≠ [] → ex.inners.mapM (innerComplexity D mp) = .ok cs →
      templateComplexity D mp ex = .ok cs.sum ∧
      ∀ ex' : TExpr M, ex'.inners = ex.inners → templateComplexity D mp ex' = .ok cs.sum

theorem complexitySum_holds : complexitySum := by
  intro M D mp ex cs hne h
  have key : ∀ ex' : TExpr M, ex'.inners = ex.inners → templateComplexity D mp ex' = .ok cs.sum := by
    intro ex' he
    unfold templateComplexity
    rw [he]
    cases hi : ex.inners with
    | nil => exact absurd hi hne
    | cons a as =>
      rw [hi, List.mapM_cons] at h
      cases ha : innerComplexity D mp a with
      | error e => rw [ha] at h; cases h
      | ok c =>
        cases hl : as.mapM (innerComplexity D mp) with
        | error e => rw [ha, hl] at h; cases h
        | ok cs' =>
          rw [ha, hl] at h
          cases h
          simp only [sumJ, ha, okBind]
          rw [foldl_sum _ as cs' c hl]
          simp
  exact ⟨key ex rfl, key⟩

/-- With a user complexity function, a template's complexity should be that function's value
on the template. -/
def complexityCustom : Prop :=
  ∀ (M : Type) (D : Nat) (f : AnyEx M → Int) (ex : TExpr M),
    ex.inners ≠ [] → templateComplexity D (.custom f) ex = .ok (f (.template ex))

/-- `TemplateStructure{(:f, :g)}` with `f = g = x1`. -/
def exFG : TExpr (Settings JF) :=
  ⟨⟨["f", "g"], [], [1, 1], []⟩,
    [⟨.feature 1, ⟨some DynExpr.Eval.Ex.ops, none, true⟩⟩, ⟨.feature 1, ⟨some DynExpr.Eval.Ex.ops, none, true⟩⟩], []⟩

theorem complexityCustom_refuted : ¬ complexityCustom := by
  intro h
  have := h _ 0 (fun _ => 7) exFG (by simp [exFG])
  simp [templateComplexity, exFG, sumJ, innerComplexity] at this

/-! ## Scalar constants -/

theorem constants_length {T : Type} :
    ∀ t : Tree T, (NodeUtils.getConstants t).length = NodeUtils.countConstantNodes t := by
  intro t
  induction t using Tree.induction with
  | hc v => simp [NodeUtils.getConstants, NodeUtils.countConstantNodes]
  | hf i => simp [NodeUtils.getConstants, NodeUtils.countConstantNodes]
  | hb op cs ih =>
    simp only [NodeUtils.getConstants, NodeUtils.countConstantNodes, List.length_flatMap]
    congr 1
    exact List.map_congr_left ih

/-- `count_scalar_constants(::TemplateExpression)`, `src/TemplateExpression.jl:1110-1123`,
on plain inner trees (one scalar per constant node and per parameter entry). -/
def templateCount {M : Type} (ex : TExpr M) : Nat :=
  (ex.inners.map fun e => NodeUtils.countScalarConstants e.tree).sum +
    if ex.s.hasParams then (ex.params.map List.length).sum else 0

/-- The flat vector of `get_scalar_constants`, `src/TemplateExpression.jl:454-467`, on plain
inner trees: inner constants in key order, then the packed parameter vectors. -/
def pureConstants {M : Type} (ex : TExpr M) : List JF :=
  ex.inners.flatMap (fun e => NodeUtils.getConstants e.tree) ++
    if ex.s.hasParams then ex.params.flatten else []

/-- The constant count agrees with the length of the constants vector. -/
def countAgrees : Prop := ∀ (M : Type) (ex : TExpr M), templateCount ex = (pureConstants ex).length

theorem countAgrees_holds : countAgrees := by
  intro M ex
  simp only [templateCount, pureConstants, List.length_append, List.length_flatMap,
    NodeUtils.countScalarConstants, constants_length]
  split <;> simp [List.length_flatten]

/-! ## Copy and equality -/

/-- Julia `==` on `Float64`. -/
def jeq (x y : JF) : Bool := x != .nan && x == y

mutual
/-- DE's `Node` `==`: equal shapes, operators and features, constants by `==`. -/
def treeEq : Tree JF → Tree JF → Bool
  | .const a, .const b => jeq a b
  | .feature i, .feature j => i == j
  | .branch o cs, .branch o' ds => o == o' && treesEq cs ds
  | _, _ => false
/-- Children of `treeEq`. -/
def treesEq : List (Tree JF) → List (Tree JF) → Bool
  | [], [] => true
  | c :: cs, d :: ds => treeEq c d && treesEq cs ds
  | _, _ => false
end

/-- Vector `==`: equal lengths and elementwise `==`. -/
def vecEq : List JF → List JF → Bool
  | [], [] => true
  | a :: as, b :: bs => jeq a b && vecEq as bs
  | _, _ => false

/-- `==` on templates (DE `AbstractExpression` equality: contents then metadata, with the
`ParamVector`s compared elementwise). -/
def templateEq {M : Type} [DecidableEq M] (a b : TExpr M) : Bool :=
  a.s == b.s && treesEq (a.inners.map (·.tree)) (b.inners.map (·.tree)) &&
    a.inners.map (·.metadata) == b.inners.map (·.metadata) &&
    a.params.length == b.params.length && ((a.params.zip b.params).all fun p => vecEq p.1 p.2)

/-- `Base.copy(::TemplateExpression)`, `src/TemplateExpression.jl:411-416`: copies of every
inner expression and parameter vector, with equal values. -/
def copyT {M : Type} (ex : TExpr M) : TExpr M :=
  { ex with inners := ex.inners.map fun e => ⟨e.tree, e.metadata⟩, params := ex.params.map id }

theorem jeq_self (x : JF) : jeq x x = true ↔ x ≠ .nan := by
  cases x <;> simp [jeq]

mutual
theorem treeEq_self : ∀ t : Tree JF, treeEq t t = true ↔ ∀ c ∈ NodeUtils.getConstants t, c ≠ .nan
  | .const a => by simp [treeEq, NodeUtils.getConstants, jeq_self]
  | .feature i => by simp [treeEq, NodeUtils.getConstants]
  | .branch o cs => by
    simp only [treeEq, beq_self_eq_true, Bool.true_and, NodeUtils.getConstants, List.mem_flatMap]
    rw [treesEq_self cs]
    constructor
    · intro h c ⟨t, ht, hc⟩; exact (h t ht) c hc
    · intro h t ht c hc; exact h c ⟨t, ht, hc⟩
theorem treesEq_self : ∀ ts : List (Tree JF),
    treesEq ts ts = true ↔ ∀ t ∈ ts, ∀ c ∈ NodeUtils.getConstants t, c ≠ .nan
  | [] => by simp [treesEq]
  | t :: ts => by
    simp only [treesEq, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [treeEq_self t, treesEq_self ts]
end

theorem vecEq_self : ∀ xs : List JF, vecEq xs xs = true ↔ ∀ x ∈ xs, x ≠ .nan
  | [] => by simp [vecEq]
  | x :: xs => by simp [vecEq, jeq_self, vecEq_self xs]

/-- A copy equals its original exactly when no inner constant and no parameter is `NaN`. -/
def copyEq : Prop :=
  ∀ (M : Type) [DecidableEq M] (ex : TExpr M),
    templateEq (copyT ex) ex = true ↔
      (∀ e ∈ ex.inners, ∀ c ∈ NodeUtils.getConstants e.tree, c ≠ .nan) ∧ ∀ p ∈ ex.params, ∀ v ∈ p, v ≠ .nan

theorem zip_self {α : Type} : ∀ l : List α, l.zip l = l.map fun a => (a, a)
  | [] => rfl
  | a :: l => by simp [zip_self l]

theorem copyT_eq {M : Type} (ex : TExpr M) : copyT ex = ex := by
  cases ex with
  | mk s inners params =>
    simp only [copyT, List.map_id]
    congr
    conv => rhs; rw [<- List.map_id inners]
    rfl

theorem copyEq_holds : copyEq := by
  intro M _ ex
  rw [copyT_eq]
  simp only [templateEq, beq_self_eq_true, Bool.true_and, Bool.and_true, Bool.and_eq_true,
    treesEq_self, zip_self, List.all_map, List.all_eq_true, Function.comp_def, vecEq_self,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

end SymReg.Templates
