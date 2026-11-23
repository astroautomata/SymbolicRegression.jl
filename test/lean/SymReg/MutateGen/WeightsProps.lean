import SymReg.MutateGen.Weights

namespace SymReg.MutateGen
open DynExpr

/-- `_mutations_from_weights(w)` pairs every field with the mutation its docstring names,
in field order; its weights are `convert(Vector, w)`; `copy(w)` has the same fields. -/
def from_weights : Prop := ∀ w : MutationWeights,
  mutationsFromWeights w = .ok (fieldNames.map fun f => (documentedKind f, w.get f)) ∧
  (fieldNames.map fun f => (documentedKind f, w.get f)).map Prod.snd = convertVector w ∧
  copyWeights w = .ok w

theorem from_weights_holds : from_weights := by
  intro w
  exact ⟨rfl, rfl, rfl⟩

/-- The default weight `default_mutations()` gives the mutation of each field. -/
def defaultOfField : WName → JF
  | .mutate_constant => .fin (353 / 10000)
  | .mutate_operator => .fin (363 / 100)
  | .mutate_feature => .fin (1 / 10)
  | .swap_operands => .fin (608 / 100000)
  | .rotate_tree => .fin (142 / 100)
  | .add_node => .fin (771 / 10000)
  | .insert_node => .fin (244 / 100)
  | .delete_node => .fin (369 / 1000)
  | .simplify => .fin (148 / 100000)
  | .randomize => .fin (695 / 100000)
  | .do_nothing => .fin (431 / 1000)
  | .optimize => .fin 0
  | .backsolve => .fin 0
  | .form_connection => .fin (1 / 2)
  | .break_connection => .fin (1 / 10)

theorem defaultOfField_mem : ∀ f, (documentedKind f, defaultOfField f) ∈ defaultMutations := by
  intro f
  cases f <;> simp [documentedKind, defaultOfField, defaultMutations]

def declaredKeywordFields : List WName :=
  [.mutate_constant, .mutate_operator, .mutate_feature, .swap_operands, .rotate_tree,
   .add_node, .insert_node, .delete_node, .simplify, .randomize, .do_nothing,
   .optimize, .backsolve, .form_connection, .break_connection]

def keywordValue {α : Type} [WeightConversion α] (kws : List (String × α))
    (name : WName) : Jl JF :=
  match (kws.find? (fun p => p.1 = name.sym)).map Prod.snd with
  | none => .ok (defaultOfField name)
  | some x => WeightConversion.toFloat64 x

/-- A deprecation error takes precedence over validation. The first unknown
keyword takes precedence over conversions. With known keys, conversions run
in declaration order and the positional fields are not normalized. -/
def kw_weights : Prop := ∀ (α : Type) [WeightConversion α] (kws : List (String × α)),
  (∀ e, mutationWeightsKw (.error e) kws = .error e) ∧
  (∀ (pre post : List (String × α)) k v,
    kws = pre ++ (k, v) :: post →
    (∀ p ∈ pre, p.1 ∈ declaredKeywordFields.map WName.sym) →
    k ∉ declaredKeywordFields.map WName.sym →
    mutationWeightsKw (.ok ()) kws = .error (unknownWeight k)) ∧
  ((∀ p ∈ kws, p.1 ∈ declaredKeywordFields.map WName.sym) →
    mutationWeightsKw (.ok ()) kws =
      ((declaredKeywordFields.mapM (keywordValue kws)) >>= MutationWeights.ofList))

theorem kw_weights_holds : kw_weights := by
  intro α inst kws
  refine ⟨fun e => rfl, ?_, ?_⟩
  · intro pre post k v hp hpre hk
    have hpre' : pre.find? (fun p => !(fieldNames.map WName.sym).contains p.1) = none := by
      rw [List.find?_eq_none]
      intro p hp
      have h := hpre p hp
      change p.1 ∈ fieldNames.map WName.sym at h
      simp [h]
    have hk' : (fieldNames.map WName.sym).contains k = false := by
      change k ∉ fieldNames.map WName.sym at hk
      simpa using hk
    subst kws
    change mutationWeights (pre ++ (k, v) :: post) = _
    unfold mutationWeights
    rw [List.find?_append, hpre']
    simp only [List.find?_cons, hk', Bool.not_false, Option.none_or] <;> rfl
  · intro hall
    have hf : kws.find? (fun p => !(fieldNames.map WName.sym).contains p.1) = none := by
      rw [List.find?_eq_none]
      intro p hp
      have h := hall p hp
      change p.1 ∈ fieldNames.map WName.sym at h
      simp [h]
    have he : ∀ f, (do
        let k ← mutationFromSymbol f.sym
        let d ← dictLookup defaultMutations k
        match kws.find? (fun p => p.1 = f.sym) with
        | some (_, value) => WeightConversion.toFloat64 value
        | none => pure d) = keywordValue kws f := by
      intro f
      have hk : mutationFromSymbol f.sym = .ok (documentedKind f) := by cases f <;> rfl
      have hd : dictLookup defaultMutations (documentedKind f) = .ok (defaultOfField f) := by
        cases f <;> rfl
      rw [hk]
      change ((dictLookup defaultMutations (documentedKind f)) >>= _) = _
      rw [hd]
      unfold keywordValue
      cases h : kws.find? (fun p => p.1 = f.sym) with
      | none => rfl
      | some p => cases p; rfl
    unfold mutationWeightsKw
    change mutationWeights kws = _
    unfold mutationWeights
    rw [hf]
    change (fieldNames.mapM _ >>= MutationWeights.ofList) = _
    exact congrArg (fun f => fieldNames.mapM f >>= MutationWeights.ofList) (funext he)

example : (mutationWeightsKw (.ok ()) [("optimize", JF.fin 4)]).map
    (fun w => w.optimize) = .ok (.fin 4) := rfl

end SymReg.MutateGen
