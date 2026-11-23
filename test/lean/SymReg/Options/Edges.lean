import SymReg.Options.Laws

namespace SymReg.Options
open DynExpr SymReg.Complexity SymReg.HeapLemmas

def emptyComplexityTypeError : Prop :=
  (∀ ops, complexityMapping (some []) none none ops .any = .error (.methodError "one(::Type{Any})")) ∧
  (complexityMapping (some []) none none [[11],[]] WeightType.int =
    .ok ⟨⟨true,[[1],[]],.scalar 1,1⟩,WeightType.int⟩) ∧
  promoteWeight WeightType.int (promoteWeight WeightType.int .any) = .any

private theorem anyComplexityRow (ops : List Nat) :
    (ops.mapM fun _ => (WeightType.any.one >>= fun _ => WeightType.any.cast 1)) =
      if ops.isEmpty then .ok [] else .error (.methodError "one(::Type{Any})") := by
  cases ops <;> simp [WeightType.one, List.mapM_cons, Bind.bind, Except.bind] <;> rfl

private theorem anyComplexityRows (ops : List (List Nat)) :
    (ops.mapM fun row => row.mapM fun _ => (WeightType.any.one >>= fun _ => WeightType.any.cast 1)) =
      if ops.all List.isEmpty then .ok (ops.map fun _ => []) else .error (.methodError "one(::Type{Any})") := by
  induction ops with
  | nil => rfl
  | cons row ops ih =>
    rw [List.mapM_cons, anyComplexityRow]
    cases row with
    | nil =>
      simp only [List.isEmpty, ite_true, List.all_cons, Bool.true_and, List.map_cons]
      change (ops.mapM (fun (row : List Nat) => row.mapM fun _ =>
        (WeightType.any.one >>= fun _ => WeightType.any.cast 1))).map ([] :: ·) = _
      rw [ih]
      split <;> rfl
    | cons x xs => rfl

theorem emptyComplexityTypeError_holds : emptyComplexityTypeError := by
  refine ⟨?_, rfl, rfl⟩
  intro ops
  change ((ops.mapM fun row => row.mapM fun _ =>
    (WeightType.any.one >>= fun _ => WeightType.any.cast 1)) >>= fun rows => do
      let v ← lookupVariable .any none
      let c ← lookupConstant .any none
      promotedMapping (rows.map (.any, ·)) (.any,v) (.any,c)) =
    .error (.methodError "one(::Type{Any})")
  rw [anyComplexityRows]
  split <;> rfl

private theorem promoteUniformInt (rows : List (List Int)) :
    promotedTypes ((rows.map (WeightType.int, ·)).map Prod.fst) WeightType.int WeightType.int =
      WeightType.int := by
  have fold (ts : List WeightType) (h : ∀ t ∈ ts, t = WeightType.int) :
      ts.foldl promoteWeight WeightType.int = WeightType.int := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      have ht := h t (by simp)
      subst t
      change ts.foldl promoteWeight WeightType.int = _
      exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
  cases rows with
  | nil => rfl
  | cons row rows =>
    change (((rows.map (WeightType.int, ·)).map Prod.fst) ++
      [WeightType.int,WeightType.int]).foldl promoteWeight WeightType.int = _
    apply fold
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
      rfl
    · simpa using ht

theorem emptyIntComplexity_all_layouts (ops : List (List Nat)) :
    complexityMapping (some []) none none ops WeightType.int =
      .ok ⟨⟨true, ops.map (fun row => row.map (fun _ => 1)), .scalar 1, 1⟩, WeightType.int⟩ := by
  change ((ops.mapM fun row => row.mapM (fun _ => (pure (1 : Int) : Jl Int))) >>= fun rows =>
    promotedMapping (rows.map (WeightType.int, ·)) (WeightType.int, .scalar 1)
      (WeightType.int, 1)) = _
  simp only [List.mapM_pure]
  change promotedMapping _ _ _ = _
  unfold promotedMapping
  rw [promoteUniformInt]
  have hrow (xs : List Nat) :
      (xs.map (fun _ => (1 : Int))).mapM WeightType.int.cast = .ok (xs.map fun _ => 1) := by
    rw [List.mapM_map]
    change (xs.mapM (fun _ => (pure (1 : Int) : Jl Int))) = _
    rw [List.mapM_pure]
    rfl
  dsimp only
  simp only [List.map_map, Function.comp_def]
  have hv : castVariable WeightType.int (.scalar 1) = .ok (.scalar 1) := rfl
  rw [hv]
  change ((ops.map (fun row => (WeightType.int, row.map fun _ => (1 : Int)))).mapM
    (fun row => row.2.mapM WeightType.int.cast) >>= fun rows =>
      .ok (⟨⟨true, rows, .scalar 1, 1⟩, WeightType.int⟩ : TypedMapping)) = _
  rw [List.mapM_map]
  simp only [Function.comp_def, hrow]
  change ((ops.mapM (fun row => (pure (row.map fun _ => (1 : Int)) : Jl (List Int)))) >>= _) = _
  rw [List.mapM_pure]
  rfl

/-- All weight fields survive conversion, and the default ConstantMutation gets
exactly the Float64 conversions of the resolved perturbation and sign-flip parameters. -/
def constantMutationDefaults : Prop := ∀ (w : SymReg.MutateGen.MutationWeights) d,
  ∃ pairs, mutationBase w d = .ok pairs ∧
    pairs.head? = some (⟨.constant, 0, some (SymReg.Loss.LossPrecision.round .float64 d.perturbation,
      SymReg.Loss.LossPrecision.round .float64 d.flipProbability)⟩, w.mutate_constant) ∧
    pairs.map Prod.snd = SymReg.MutateGen.convertVector w

theorem constantMutationDefaults_holds : constantMutationDefaults := by
  intro w d
  exact ⟨_, rfl, rfl, rfl⟩

/-- Historical defaults select the size limit; the optimizer limits, log loss
scaling, display precision and default loss are version-independent. -/
private def documentedLiteralDefaultsContract : Prop := ∀ version : Option Version,
  (supplyDefaults { version }).maxsize = (defaultOptions version).maxsize ∧
  resolveOptimizer { version } = .ok (.absent, 8, 10000) ∧
  ({ version := version } : Args).printPrecision = 5 ∧
  ({ version := version } : Args).lossScale = "log" ∧
  ({ version := version } : Args).elementwiseLoss.getD 0 = 0 ∧
  ({ version := version } : Args).algorithm = .existing 0 ∧
  ({ version := version } : Args).inputStream = 0

private theorem documentedLiteralDefaultsContract_holds : documentedLiteralDefaultsContract := by
  intro version
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def documentedLiteralDefaultsLaw : Prop := ∀ version : Option Version,
  (supplyDefaults { version }).maxsize =
    (if version.any Version.beforeOne then 20 else 30) ∧
  resolveOptimizer { version } = .ok (.absent, 8, 10000) ∧
  let a : Args := { version }
  (construct {} a).map (fun o => (o.printPrecision.value, o.lossScale,
    o.elementwiseLoss, o.optimizerAlgorithm, o.inputStream)) =
  (constructParts {} a).map (fun parts => (5, "log", 0, parts.optimizerAlgorithm, 0)) ∧
  ∀ o, construct {} a = .ok o → o.optimizerAlgorithm = 0

def documentedLiteralDefaults : Prop := documentedLiteralDefaultsContract ∧ documentedLiteralDefaultsLaw

def operatorEnumResolution : Prop := ∀ (raw : List (List Nat)) typeId (u b : List Nat) id
    (make : Option Nat → List (List Nat) → Jl Operators),
  let expected := raw.map (List.map canonical)
  let generic : Operators := ⟨raw,false,typeId⟩
  let builtin : Operators := ⟨raw,true,typeId⟩
  resolveOperators make (some generic) none (mapOperators raw) = .ok generic ∧
  (resolveOperators make (some builtin) none (mapOperators raw)).map (fun o => (o.ops,o.runtimeType)) =
    .ok (expected,.standard expected) ∧
  resolveOperators make none (some id) (mapOperators [u,b]) = make (some id) [u.map canonical,b.map canonical] ∧
  (construct {} {operators := some ⟨[[11],[5,6]],false,typeId⟩}).map (fun o => (o.operators.ops,o.lookupOps)) =
    .ok ([[11],[5,6]],[[110],[105,105]]) ∧
  (construct {} {operators := some ⟨[[11],[5,6]],true,typeId⟩}).map (fun o => o.operators.runtimeType) =
    .ok (.standard [[110],[105,105]])

end SymReg.Options
