import SymReg.Search.Extras

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

/-- Type/value identities for the Julia constructor services in
`src/SearchUtils.jl:43-50`. Concrete node and expression implementations are external. -/
structure TypeServices where
  nodeWithType : Nat → Nat
  initialValue : Nat → Nat
  constructNode : Nat → Nat → Nat
  createExpression : Nat → Nat
  expressionType : Nat → Nat
  memberWithTypes : Nat → Nat → Nat → Nat

/-- `infer_popmember_type`, `src/SearchUtils.jl:43-50`. -/
def inferPopmemberType (valueType lossType : Nat) (services : TypeServices) : Nat :=
  let nodeType := services.nodeWithType valueType
  let prototype := services.constructNode nodeType (services.initialValue valueType)
  let expression := services.createExpression prototype
  services.memberWithTypes valueType lossType (services.expressionType expression)

 def inferred_type_stability : Prop := ∀ (valueType lossType : Nat) (services : TypeServices)
    (createLeft createRight : Nat → Nat),
  let prototype := services.constructNode (services.nodeWithType valueType)
    (services.initialValue valueType)
  services.expressionType (createLeft prototype) = services.expressionType (createRight prototype) →
    inferPopmemberType valueType lossType { services with createExpression := createLeft } =
    inferPopmemberType valueType lossType { services with createExpression := createRight }
 theorem inferred_type_stability_holds : inferred_type_stability := by
  intro valueType lossType services createLeft createRight
  dsimp only
  intro ht
  simp only [inferPopmemberType, ht]
example : (fun (_ : Nat) => 1) ((fun n => n) 0) =
    (fun (_ : Nat) => 1) ((fun n => n + 1) 0) := rfl

/-- `init_dummy_pops`, `src/SearchUtils.jl:412-428`. The prototype is reused only
at output 1/population 1; every other slot invokes the population constructor service. -/
def initDummyPops (outputs populations : Nat) (prototype : List Member)
    (construct : Nat → Nat → List Member) : List (List (List Member)) :=
  (List.range outputs).map fun j => (List.range populations).map fun i =>
    if i = 0 ∧ j = 0 then prototype else construct j i

 def dummy_storage_shape : Prop := ∀ (outputs populations : Nat) (prototype : List Member)
    (construct : Nat → Nat → List Member),
  prototype.length = 1 → (∀ j i, (construct j i).length = 1) →
  let storage := initDummyPops outputs populations prototype construct
  storage.length = outputs ∧
    (∀ row ∈ storage, row.length = populations) ∧
    (∀ row ∈ storage, ∀ pop ∈ row, pop.length = 1)
 theorem dummy_storage_shape_holds : dummy_storage_shape := by
  intro outputs populations prototype construct hp hc
  dsimp only
  constructor
  · simp [initDummyPops]
  constructor
  · intro row hr
    simp only [initDummyPops, List.mem_map] at hr
    obtain ⟨j, _, rfl⟩ := hr
    simp
  · intro row hr pop hm
    simp only [initDummyPops, List.mem_map] at hr
    obtain ⟨j, _, rfl⟩ := hr
    simp only [List.mem_map] at hm
    obtain ⟨i, _, he⟩ := hm
    subst pop
    split <;> simp [hp, hc]
example : let m := specimen (.fin 0) (.fin 1)
  [m].length = 1 ∧ ∀ (_ _ : Nat), [m].length = 1 := by simp

end SymReg.Search
