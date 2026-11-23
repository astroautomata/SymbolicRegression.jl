import SymReg.Interface.Evaluation
import SymReg.Mutations.Leaf
import SymReg.Options.Core

namespace SymReg.Interface
open DynExpr

-- Source: src/InterfaceDataTypes.jl:11-14
-- init_value(::Type{T}) where {T<:Number} = zero(T)
-- function init_value(::Type{T}) where {T}
--     return error("No `init_value` method defined for type $T. Please define one.")
-- end
def initValue (number : Bool) (typeName : String) (zero : String → ExceptT JlError (StateM S) T) :
    ExceptT JlError (StateM S) T :=
  if number then zero typeName else throw (.errorException
    ("No `init_value` method defined for type " ++ typeName ++ ". Please define one."))

/-- sample_value's Number dispatch forwards rng and T to randn; options are
unused. Unsupported randn types propagate their exception, without conversion.
src/InterfaceDataTypes.jl:27-30. -/
def sampleValue (number : Bool) (typeName : String) (randn : R → Jl T)
    (rng : R) (_options : O) : Jl T :=
  if number then randn rng else .error (.errorException
    ("No `sample_value` method defined for type " ++ typeName ++ ". Please define one."))

/-- The generic ConstantMutation method is an extension point that always
throws, independent of RNG, value, temperature and mutation field values.
Numeric mutation lives in MutationFunctions.jl and is reused below.
src/InterfaceDataTypes.jl:37-39. -/
def mutateFallback (typeName : String) (_rng : R) (_value : T)
    (_temperature perturbation negateProbability : Rat) : Jl T :=
  .error (.errorException
    ("No `mutate_value` method defined for type " ++ typeName ++ ". Please define one."))

/-- Default parse_scope returns nothing for every type.
src/InterfaceDataTypes.jl:20. -/
def parseScope (_typeName : String) : Option Nat := none

inductive EnumKind where
  | standard | generic

-- Source: src/InterfaceDynamicExpressions.jl:368-382
-- function define_alias_operators(
--     @nospecialize(operators::Union{OperatorEnum,GenericOperatorEnum})
-- )
--     # We undo some of the aliases so that the user doesn't need to use, e.g.,
--     # `safe_pow(x1, 1.5)`. They can use `x1 ^ 1.5` instead.
--     constructor = isa(operators, OperatorEnum) ? OperatorEnum : GenericOperatorEnum
--     @assert operators.ops isa Tuple{Vararg{Any,2}}
--     # TODO: Support for 3-ary operators
--     return constructor(;
--         binary_operators=map(inverse_opmap, operators.ops[2]),
--         unary_operators=map(inverse_opmap, operators.ops[1]),
--         define_helper_functions=false,
--         empty_old_operators=false,
--     )
-- end
def defineAliasOperators (kind : EnumKind) (ops : List (List Nat))
    (construct : EnumKind → List Nat → List Nat → Bool → Bool → ExceptT JlError (StateM S) A) :
    ExceptT JlError (StateM S) A :=
  match ops with
  | [unary, binary] => construct kind (unary.map SymReg.Options.inverseOpmap)
      (binary.map SymReg.Options.inverseOpmap) false false
  | _ => throw (.assertionError "operators.ops isa Tuple{Vararg{Any,2}}")

-- Source: src/InterfaceDynamicExpressions.jl:356-367
-- macro extend_operators(options)
--     operators = :($(options).operators)
--     type_requirements = AbstractOptions
--     alias_operators = gensym("alias_operators")
--     return quote
--         if !isa($(options), $type_requirements)
--             error("You must pass an options type to `@extend_operators`.")
--         end
--         $alias_operators = $define_alias_operators($operators)
--         $(DE).@extend_operators $alias_operators
--     end |> esc
-- end
def extendOperators (evaluate : ExceptT JlError (StateM S) O) (isOptions : O → Bool)
    (readOperators : O → ExceptT JlError (StateM S) (EnumKind × List (List Nat)))
    (construct : EnumKind → List Nat → List Nat → Bool → Bool → ExceptT JlError (StateM S) A)
    (extend : A → ExceptT JlError (StateM S) R) : ExceptT JlError (StateM S) R := do
  if !isOptions (← evaluate) then
    throw (.errorException "You must pass an options type to `@extend_operators`.")
  let (kind, ops) ← readOperators (← evaluate)
  extend (← defineAliasOperators kind ops construct)

/-- Distributed-expression fallback hooks.
src/InterfaceDynamicExpressions.jl:410-417. -/
def requireCopyToWorkers (_expressionType : String) : Bool := false

def makeExampleInputs (optionType : String) (_scalarType : T) (_dataset : D) : Jl R :=
  .error (.errorException
    ("`make_example_inputs` is not implemented for `" ++ optionType ++ "`."))

def numericInit : Prop := ∀ (T : Type) (requested : String) (reply : Jl T),
  ((initValue true requested (fun t => ExceptT.mk fun calls => (reply, calls ++ [t]))).run []) =
    (reply, [requested])
theorem numericInit_holds : numericInit := by intro T requested reply; rfl

def numericSample : Prop := ∀ (T R O : Type) (typeName : String) (draw : R → Jl T)
  (rng : R) (options : O), sampleValue true typeName draw rng options = draw rng
 theorem numericSample_holds : numericSample := by intro T R O typeName draw rng options; rfl

def genericHooksFail : Prop := ∀ (T R O : Type) (name : String) (zero : String → ExceptT JlError (StateM Unit) T)
  (draw : R → Jl T) (rng : R) (options : O) (value : T) (temperature pert pneg : Rat),
  ((initValue false name zero).run ()) = (.error (.errorException
    ("No `init_value` method defined for type " ++ name ++ ". Please define one.")), ()) ∧
  sampleValue false name draw rng options = .error (.errorException
    ("No `sample_value` method defined for type " ++ name ++ ". Please define one.")) ∧
  mutateFallback name rng value temperature pert pneg = .error (.errorException
    ("No `mutate_value` method defined for type " ++ name ++ ". Please define one.")) ∧
  parseScope name = none
 theorem genericHooksFail_holds : genericHooksFail := by
  intro T R O name zero draw rng options value temperature pert pneg
  exact ⟨rfl,rfl,rfl,rfl⟩

private def constantMutationForwardingContract : Prop := ∀ (T : Type) (mul : T → Rat → T)
  (pw : Rat → Rat → Rat) (pert temperature pneg : Rat) (value : T)
  (state : SymReg.Mutations.St T),
  SymReg.Mutations.mutateValue' mul pw pert temperature pneg value state =
    SymReg.Mutations.mutateValue mul pw pert temperature pneg value state

private theorem constantMutationForwardingContract_holds : constantMutationForwardingContract := by
  intro T mul pw pert temperature pneg value state; rfl

private def constantMutationForwardingLaw : Prop := SymReg.Mutations.mutate_value_spec

private theorem constantMutationForwardingLaw_holds : constantMutationForwardingLaw :=
  SymReg.Mutations.mutate_value_spec_holds

private def unsupportedConstantMutation : Prop := ∀ (T R : Type) (name : String)
  (rng : R) (value : T) (temperature factor probability : Rat),
  mutateFallback name rng value temperature factor probability = .error (.errorException
    ("No `mutate_value` method defined for type " ++ name ++ ". Please define one."))

def constantMutationForwarding : Prop :=
  constantMutationForwardingContract ∧ constantMutationForwardingLaw ∧ unsupportedConstantMutation

theorem constantMutationForwarding_holds : constantMutationForwarding :=
  ⟨constantMutationForwardingContract_holds, constantMutationForwardingLaw_holds,
    by intro T R name rng value temperature factor probability; rfl⟩

def aliasConstruction : Prop := ∀ (A : Type) (kind : EnumKind) (unary binary : List Nat)
  (reply : Jl A),
  ((defineAliasOperators kind [unary,binary] (fun k u b dh eo =>
    ExceptT.mk fun calls => (reply, calls ++ [(k, u, b, dh, eo)]))).run []) =
    (reply, [(kind, unary.map SymReg.Options.inverseOpmap,
      binary.map SymReg.Options.inverseOpmap, false, false)])
theorem aliasConstruction_holds : aliasConstruction := by intro A kind unary binary reply; rfl

def macroForwarding : Prop := ∀ (O A R : Type) (first second : O) (isOptions : O → Bool)
  (readOperators : O → Jl (EnumKind × List (List Nat))) (alias : Jl A) (result : A → Jl R),
  let evaluate : ExceptT JlError (StateM (Nat × List (O ⊕ A))) O :=
    ExceptT.mk fun (n, calls) => (.ok (if n = 0 then first else second), (n + 1, calls))
  let run := (extendOperators evaluate isOptions
    (fun o => ExceptT.mk fun (n, calls) => (readOperators o, (n, calls ++ [.inl o])))
    (fun _ _ _ _ _ => ExceptT.mk fun s => (alias, s))
    (fun a => ExceptT.mk fun (n, calls) => (result a, (n, calls ++ [.inr a])))).run (0, [])
  run = if isOptions first then
    match readOperators second with
    | .error e => (.error e, (2, [.inl second]))
    | .ok (_, [_, _]) =>
      match alias with
      | .error e => (.error e, (2, [.inl second]))
      | .ok a => (result a, (2, [.inl second, .inr a]))
    | .ok _ => (.error (.assertionError "operators.ops isa Tuple{Vararg{Any,2}}"),
      (2, [.inl second]))
  else (.error (.errorException "You must pass an options type to `@extend_operators`."), (1, []))
theorem macroForwarding_holds : macroForwarding := by
  intro O A R first second isOptions readOperators alias result
  cases hc : isOptions first
  · simp [extendOperators, hc, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind,
      ExceptT.mk, ExceptT.run, throwThe, throw, MonadExceptOf.throw] <;> rfl
  · cases hr : readOperators second with
    | error e =>
      simp [extendOperators, hc, hr, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind,
        ExceptT.mk, ExceptT.run] <;> rfl
    | ok ops =>
      obtain ⟨k, ops⟩ := ops
      rcases ops with _ | ⟨u, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> cases alias <;>
        simp [extendOperators, defineAliasOperators, hc, hr, bind, ExceptT.bind,
          ExceptT.bindCont, StateT.bind, ExceptT.mk, ExceptT.run,
          throwThe, throw, MonadExceptOf.throw] <;> rfl

def workerFallbacks : Prop := ∀ (T D R : Type) (typeName : String) (scalar : T) (dataset : D),
  requireCopyToWorkers typeName = false ∧ makeExampleInputs (R := R) typeName scalar dataset =
    .error (.errorException ("`make_example_inputs` is not implemented for `" ++ typeName ++ "`."))
 theorem workerFallbacks_holds : workerFallbacks := by
  intro T D R typeName scalar dataset; exact ⟨rfl,rfl⟩

end SymReg.Interface
