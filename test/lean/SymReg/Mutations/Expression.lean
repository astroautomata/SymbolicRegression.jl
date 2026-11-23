import SymReg.Mutations.Core
import DynExpr.Expressions.Aliasing

namespace SymReg.Mutations
open DynExpr DynExpr.NodeBase

variable {T : Type}

/-! ## Expressions -/

/-- `get_contents_for_mutation(ex, rng)` (`src/MutationFunctions.jl:38-40`): the contents and
the context `nothing`. -/
def getContentsForMutation (ex : Expressions.Aliasing.Expression) : M T (Addr × Unit) :=
  pure (Expressions.Aliasing.getContents ex, ())

/-- `with_contents_for_mutation(ex, new_contents, nothing)` (`src/MutationFunctions.jl:49-51`):
`with_contents(ex, new_contents)` keeps the metadata. -/
def withContentsForMutation (ex : Expressions.Aliasing.Expression) (new : Addr) (_ : Unit) :
    Expressions.Aliasing.Expression :=
  Expressions.Aliasing.withContents ex new

/-- `get_nfeatures_for_mutation(ex, context, nfeatures)` (`src/MutationFunctions.jl:62-64`). -/
def getNfeaturesForMutation (_ : Expressions.Aliasing.Expression) (_ : Unit) (nfeatures : Int) : Int :=
  nfeatures

/-- The expression method shared by the mutations (`src/MutationFunctions.jl:83-87`, and the
same pattern at lines 104-110, 123-135, 188-195, 209-221, 253-265, 298-310, 359-363,
381-394, 556-559, 576-579, 621-625): mutate the contents, rewrap. `nf` receives
`get_nfeatures_for_mutation(ex, context, nfeatures)`. -/
def onExpr (ex : Expressions.Aliasing.Expression) (nfeatures : Int) (f : Int → Addr → M T Addr) :
    M T Expressions.Aliasing.Expression := do
  let (tree, ctx) ← getContentsForMutation (T := T) ex
  let nf := getNfeaturesForMutation ex ctx nfeatures
  let t' ← f nf tree
  pure (withContentsForMutation ex t' ctx)

/-- `backsolve_rewrite_random_node(ex::AbstractExpression, ...)`
(`src/MutationFunctions.jl:671-685`) for expression types other than `Expression`, and the
`Expression` method (`src/MutationFunctions.jl:687-701`): `isExpression` selects the method. -/
def backsolveExpr (D fuel : Nat) (ops : BacksolveOps T) (isFloat : Bool)
    (curmaxsize : Int) (isExpression : Bool) (ex : Expressions.Aliasing.Expression) :
    M T Expressions.Aliasing.Expression :=
  if !isExpression then
    liftJ (.error (.argumentError "backsolve_rewrite_random_node does not support this expression type"))
  else do
    let t' ← backsolveRewriteRandomNode D fuel ops isFloat curmaxsize (Expressions.Aliasing.getContents ex)
    pure (Expressions.Aliasing.withContents ex t')
def expr_wrappers_spec : Prop :=
  ∀ (T : Type) (ex : Expressions.Aliasing.Expression) (nf : Int)
    (f : Int → Addr → M T Addr) (s : St T),
    getContentsForMutation (T := T) ex s = .ok ((ex.contents, ()), s) ∧
    getNfeaturesForMutation ex () nf = nf ∧
    (∀ root after, f nf ex.contents s = .ok (root, after) →
      ∃ child, onExpr ex nf f s = .ok (child, after) ∧
        child.contents = root ∧ child.metadata = ex.metadata) ∧
    (∀ e, f nf ex.contents s = .error e → onExpr ex nf f s = .error e)
theorem expr_wrappers_spec_holds : expr_wrappers_spec := by
  intro T ex nf f s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro root after h
    refine ⟨Expressions.Aliasing.withContents ex root, ?_, rfl, rfl⟩
    change (f nf ex.contents >>= fun a => pure (Expressions.Aliasing.withContents ex a)) s = _
    exact (bindM h).trans rfl
  · intro e h
    change (f nf ex.contents >>= fun a => pure (Expressions.Aliasing.withContents ex a)) s = _
    exact bindM_err h
end SymReg.Mutations
