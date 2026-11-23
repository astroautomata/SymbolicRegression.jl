import SymReg.MutateGen.WeightsProps
import SymReg.MutateGen.HandlerProps
import SymReg.CrossMut.Engine

namespace SymReg.CrossMut
open DynExpr SymReg.MutateGen

/-- `src/Mutations.jl:132-173`: registration uses type identity, not list order.
Reuse the existing complete Kind, builtinKinds, defaultMutations and field map. -/
def builtinOnce : Prop := ∀ k : Kind,
  (builtinKinds.filter (fun t => t = k)).length =
    (if k ∈ builtinKinds then 1 else 0) ∧
  ((defaultMutations.map Prod.fst).filter (fun t => t = k)).length =
    (if k ∈ builtinKinds then 1 else 0)

theorem builtinOnce_holds : builtinOnce := by
  intro k
  cases k <;> simp [builtinKinds, defaultMutations]

/-- `src/MutationWeights.jl:96-112` maps each declared field to exactly its
registered documented kind. Every kind has exactly one weight-field name. -/
def fieldBijection : Prop := ∀ k : Kind,
  ((fieldNames.map documentedKind).filter (fun t => t = k)).length =
    (if k ∈ builtinKinds then 1 else 0)

theorem fieldBijection_holds : fieldBijection := by
  intro k
  cases k <;> simp [fieldNames, documentedKind, builtinKinds]

def namesConsistent : Prop := ∀ name : WName,
  mutationFromSymbol name.sym = .ok (documentedKind name)
theorem namesConsistent_holds : namesConsistent := by intro name; cases name <;> rfl

/-- `src/Mutations.jl:43-61,113-118`: keyword defaults are stored directly;
ConstantMutationContext starts at one. Configuration has no validation here. -/
def constantConfig (factor : JF := .fin (86 / 1000))
    (negate : JF := .fin (1 / 100)) : JF × JF := (factor, negate)
def backsolveConfig (library : Int := 500) (terms : Int := 8)
    (improvement : JF := .fin (1 / 1000)) (attempts : Int := 8) :=
  (library, terms, improvement, attempts)
def contextScale (scale : JF := .fin 1) := scale

private def configurationForwardingContract : Prop := ∀ factor negate library terms improvement attempts scale,
  constantConfig factor negate = (factor, negate) ∧
  backsolveConfig library terms improvement attempts = (library, terms, improvement, attempts) ∧
  contextScale scale = scale

private theorem configurationForwardingContract_holds : configurationForwardingContract := by
  intro factor negate library terms improvement attempts scale
  exact ⟨rfl,rfl,rfl⟩

private def configurationForwardingLaw : Prop :=
  ∀ (E : Type) (mf : MF E) (member : SymReg.MutateGen.Member E) (tree : E) attempt rng scale,
    let (child, draws) := mf.mutateConstant scale tree rng
    mutateH mf .constant (contextScale scale) member tree attempt rng =
      .ok ({ out := .tree child }, adv rng draws)

private theorem configurationForwardingLaw_holds : configurationForwardingLaw := by
  intro E mf member tree attempt rng scale
  rfl

def configurationForwarding : Prop := configurationForwardingContract ∧ configurationForwardingLaw

theorem configurationForwarding_holds : configurationForwarding := ⟨configurationForwardingContract_holds, configurationForwardingLaw_holds⟩

/-- `src/Crossovers.jl:35-43`: the default list contains one subtree kind of
weight one. Membership is quantified over kind, rather than an unused input. -/
def defaultCrossovers : List (CrossKind × JF) := [(.subtree, .fin 1)]
def defaultCrossoverMembership : Prop := ∀ k w,
  defaultCrossovers.length = 1 ∧
    ((k, w) ∈ defaultCrossovers ↔ k = .subtree ∧ w = .fin 1)
theorem defaultCrossoverMembership_holds : defaultCrossoverMembership := by
  intro k w; simp [defaultCrossovers, Prod.mk.injEq]

private def customResultForwardingContract : Prop := ∀ id a b result swap,
  crossover swap (fun _ _ _ => .ok result) a b (.custom id) = .ok result

private theorem customResultForwardingContract_holds : customResultForwardingContract := by intro id a b result swap; rfl

private def customResultForwardingLaw : Prop := ∀ id a b swap,
  crossover swap (fun kind first second => .ok ⟨first, second, (kind : Rat)⟩)
      a b (.custom id) = .ok ⟨a, b, (id : Rat)⟩

private theorem customResultForwardingLaw_holds : customResultForwardingLaw := by
  intro id a b swap
  rfl

def customResultForwarding : Prop := customResultForwardingContract ∧ customResultForwardingLaw

theorem customResultForwarding_holds : customResultForwarding := ⟨customResultForwardingContract_holds, customResultForwardingLaw_holds⟩

-- Source: src/Crossover.jl:81-83
-- function crossover(member1, member2, c::AbstractCrossover, options; kws...)
--     return error("Unknown crossover type: $(typeof(c))")
-- end
def defaultCustomCrossover (typeName : Nat → String) (kind _first _second : Nat) : Jl CrossResult :=
  .error (.errorException ("Unknown crossover type: " ++ typeName kind))

def unknownCrossover : Prop := ∀ typeName id a b swap,
  crossover swap (defaultCustomCrossover typeName) a b (.custom id) =
    .error (.errorException ("Unknown crossover type: " ++ typeName id))

theorem unknownCrossover_holds : unknownCrossover := by
  intro typeName id a b swap
  rfl

end SymReg.CrossMut
