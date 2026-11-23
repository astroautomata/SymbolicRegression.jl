import SymReg.ConstOpt.Core
import SymReg.Templates.ConstantsProps

namespace SymReg.ConstOpt
open DynExpr
open SymReg.Templates

/-- Adapter from the template slice's state-preserving Julia result into the
successful-return interface used by constant optimization. Template scalar
selection/write-back remains entirely in `src/TemplateExpression.jl:454-508`'s model. -/
def templateHooks (T : Type) (fuel : Nat) {V : Type} : ParameterHooks T (TConst T V) TOptRefs where
  get := fun _ x => optGet fuel x
  set := fun _ values refs x =>
    match optSet x values refs with
    | .ok () state => .ok state
    | .err error _ => .error error

def templateOptimizationRoundtrip : Prop :=
  ∀ (T V : Type) fuel root width (encode : V → List T) (x : TConst T V) original refs,
    FixedPacking x.codec width encode →
    (templateHooks T fuel).get root x = .ok (original, refs) →
    (templateHooks T fuel).set root original refs x = .ok x ∧
    ((refs.scalarRefs.flatMap TRefs.ref).Nodup → x.paramRefs.Nodup →
      ∀ values : List T, values.length = original.length →
      ∃ out, (templateHooks T fuel).set root values refs x = .ok out ∧
        (templateHooks T fuel).get root out = .ok (values, refs))

example : (templateHooks JF 2).get 7 xTwoParams =
      .ok ([JF.fin 2, .fin 5, .fin 7], ⟨[⟨1, [0]⟩], 3⟩) ∧
    (([⟨1, [0]⟩] : List TRefs).flatMap TRefs.ref).Nodup ∧
    ([JF.fin 1, .fin 3, .fin 9] : List JF).length = [JF.fin 2, .fin 5, .fin 7].length :=
  ⟨rfl, by decide, rfl⟩

end SymReg.ConstOpt
