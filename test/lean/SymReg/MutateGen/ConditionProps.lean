import SymReg.MutateGen.Condition

namespace SymReg.MutateGen
open DynExpr DynExpr.NodeBase

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-! ## Lemmas -/

theorem weightsOf_update (op : JF → JF) (ws : Weights) (M : Kind → Bool) (k : Kind) :
    weightsOf (updateWeight op ws M) k = if M k then (weightsOf ws k).map op else weightsOf ws k := by
  induction ws with
  | nil => by_cases hM : M k <;> simp [weightsOf, updateWeight, hM]
  | cons p ws ih =>
    obtain ⟨m, w⟩ := p
    simp only [weightsOf, updateWeight] at ih ⊢
    by_cases hmk : m = k
    · subst hmk
      by_cases hM : M m <;> simp_all
    · by_cases hM : M m <;> by_cases hMk : M k <;> simp_all

theorem map_fst_update (op : JF → JF) (ws : Weights) (M : Kind → Bool) :
    (updateWeight op ws M).map Prod.fst = ws.map Prod.fst := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    simp only [updateWeight, List.map_cons] at ih ⊢
    by_cases hM : M p.1 <;> simp [hM, ih]

/-- All entries of kind `k` have weight zero. -/
def AllZero (ws : Weights) (k : Kind) : Prop := ∀ w ∈ weightsOf ws k, w = .fin 0

/-- Split every branch of `conditionMutationWeights` and simplify the per-kind weights. -/
macro "cond_split" : tactic => `(tactic|
  (unfold conditionMutationWeights conditionMutateConstant scaleWeight setWeight
   simp only []
   repeat' split
   all_goals simp_all [AllZero, weightsOf_update, isa, map_fst_update]))

/-! ## Properties: what conditioning disables -/

/-- `_update_weight!(op, weights, M)` replaces the weight `w` of exactly the entries whose
mutation `isa M` by `op(w)` and leaves the mutation of every entry and the length
unchanged; `_set_weight!` and `_scale_weight!` are the instances `op = Returns(value)` and
`op = w -> roundFloat64(w * roundFloat64(factor))`. -/
def update_weight : Prop := ∀ (op : JF → JF) (ws : Weights) (M : Kind → Bool) (v f : JF),
  (∀ (i : Nat) (p : Kind × JF), ws[i]? = some p →
    (updateWeight op ws M)[i]? = some (p.1, if M p.1 then op p.2 else p.2)) ∧
  (updateWeight op ws M).length = ws.length ∧
  setWeight ws M v = updateWeight (fun _ => v) ws M ∧
  scaleWeight ws M f = updateWeight (fun w => SymReg.Loss.LossPrecision.round .float64
    (w * SymReg.Loss.LossPrecision.round .float64 f)) ws M

theorem update_weight_holds : update_weight := by
  intro op ws M v f
  refine ⟨?_, by simp [updateWeight], rfl, rfl⟩
  intro i p hp
  simp only [updateWeight, List.getElem?_map, hp, Option.map_some]
  by_cases hM : M p.1 <;> simp [hM]

/-- On a leaf tree (`tree.degree == 0`), conditioning zeroes `OperatorMutation`,
`SwapOperandsMutation`, `DeleteNodeMutation` and `SimplifyMutation`; on a variable leaf
also `OptimizeMutation` and `ConstantMutation`; on a constant leaf `FeatureMutation`. -/
def leaf_disable : Prop := ∀ (ws : Weights) (c : CondIn), c.isTemplate = false → c.tree.degree = 0 →
  (AllZero (conditionMutationWeights ws c) .operator ∧
    AllZero (conditionMutationWeights ws c) .swapOperands ∧
    AllZero (conditionMutationWeights ws c) .deleteNode ∧
    AllZero (conditionMutationWeights ws c) .simplify) ∧
  (isConstLeaf c.tree = false →
    AllZero (conditionMutationWeights ws c) .optimize ∧ AllZero (conditionMutationWeights ws c) .constant) ∧
  (isConstLeaf c.tree = true → AllZero (conditionMutationWeights ws c) .feature)

set_option maxHeartbeats 1000000 in
theorem leaf_disable_holds : leaf_disable := by
  intro ws c ht hd
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun hk => ⟨?_, ?_⟩, fun hk => ?_⟩ <;> cond_split

example : (Tree.feature 1 : Tree JF).degree = 0 ∧ isConstLeaf (Tree.feature 1 : Tree JF) = false ∧
    (Tree.const (.fin 1) : Tree JF).degree = 0 ∧ isConstLeaf (Tree.const (.fin 1) : Tree JF) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- For expression types that do not preserve sharing (plain `Node`), conditioning zeroes
`FormConnectionMutation` and `BreakConnectionMutation` on every tree. -/
def sharing_disable : Prop := ∀ (ws : Weights) (c : CondIn), c.preserveSharing = false →
  AllZero (conditionMutationWeights ws c) .formConnection ∧
  AllZero (conditionMutationWeights ws c) .breakConnection

theorem sharing_disable_holds : sharing_disable := by
  intro ws c hp
  constructor <;> cond_split

/-- The common size, feature and simplify rules apply to nonleaves and templates.
Only the generic nonleaf method checks for binary nodes and scales constant weights. -/
def nonleaf_rules : Prop := ∀ (ws : Weights) (c : CondIn),
  (c.tree.degree ≠ 0 ∨ c.isTemplate = true) →
  (c.nfeatures ≤ 1 → AllZero (conditionMutationWeights ws c) .feature) ∧
  (c.complexity ≥ c.curmaxsize →
    AllZero (conditionMutationWeights ws c) .addNode ∧ AllZero (conditionMutationWeights ws c) .insertNode) ∧
  (c.shouldSimplify = false → AllZero (conditionMutationWeights ws c) .simplify) ∧
  (c.isTemplate = false → anyT c.D (fun t => t.degree == 2) c.tree = false →
    AllZero (conditionMutationWeights ws c) .swapOperands) ∧
  (c.isTemplate = true →
    weightsOf (conditionMutationWeights ws c) .constant = weightsOf ws .constant ∧
    weightsOf (conditionMutationWeights ws c) .swapOperands = weightsOf ws .swapOperands) ∧
  (c.isTemplate = false → weightsOf (conditionMutationWeights ws c) .constant =
    (weightsOf ws .constant).map (fun w => SymReg.Loss.LossPrecision.round .float64
      (w * SymReg.Loss.LossPrecision.round .float64
        (.fin ((min 8 (max (NodeUtils.countConstantNodes c.tree) c.scalarConsts) : Nat) / 8)))))

set_option maxHeartbeats 1000000 in
theorem nonleaf_rules_holds : nonleaf_rules := by
  intro ws c hd
  rcases hd with hd | ht <;>
    refine ⟨fun h => ?_, fun h => ⟨?_, ?_⟩, fun h => ?_, fun ht hb => ?_,
      fun ht => ⟨?_, ?_⟩, fun ht => ?_⟩ <;> cond_split

example : (Tree.branch 1 [.feature 1, .const (.fin 2)] : Tree JF).degree ≠ 0 := by decide

/-- Conditioning keeps every entry's mutation and the list length, and leaves the weights
of `RotateTreeMutation`, `RandomizeMutation`, `DoNothingMutation`, `BacksolveMutation` and
every user-defined mutation unchanged. -/
def frame : Prop := ∀ (ws : Weights) (c : CondIn),
  (conditionMutationWeights ws c).map Prod.fst = ws.map Prod.fst ∧
  ∀ k, (k = .rotateTree ∨ k = .randomize ∨ k = .doNothing ∨ k = .backsolve ∨ ∃ n, k = .custom n) →
    weightsOf (conditionMutationWeights ws c) k = weightsOf ws k

set_option maxHeartbeats 1000000 in
theorem frame_holds : frame := by
  intro ws c
  refine ⟨by cond_split, ?_⟩
  intro k hk
  rcases hk with rfl | rfl | rfl | rfl | ⟨n, rfl⟩ <;> cond_split

/-! ## Properties: mutations left enabled although they cannot apply -/

/-- `swap_operands` swaps two children of a node with `degree > 1`
(`src/MutationFunctions.jl:88-101`), so conditioning keeps `SwapOperandsMutation`'s weight
whenever some node has at least two children. -/
def swap_kept : Prop := ∀ (ws : Weights) (c : CondIn), DegLe c.D c.tree →
  someNode (fun t => decide (t.degree > 1)) c.tree = true →
  weightsOf (conditionMutationWeights ws c) .swapOperands = weightsOf ws .swapOperands

theorem swap_kept_refuted : ¬ swap_kept := by
  intro h
  have := h [(.swapOperands, .fin 1)]
    ⟨3, .branch 1 [.feature 1, .feature 2, .feature 3], false, 0, 1, 10, 3, true, false⟩
    (by simp [DegLe]) (by decide)
  exact absurd this (by decide)

/-- `mutate_feature` returns the tree unchanged when `nfeatures <= 1`
(`src/MutationFunctions.jl:200`), so conditioning zeroes `FeatureMutation` then. -/
def feature_nfeatures : Prop := ∀ (ws : Weights) (c : CondIn), c.nfeatures ≤ 1 →
  AllZero (conditionMutationWeights ws c) .feature

theorem feature_nfeatures_refuted : ¬ feature_nfeatures := by
  intro h
  have := h [(.feature, .fin 1)] ⟨2, .feature 1, false, 0, 1, 10, 1, true, false⟩ (by decide) (.fin 1) (by decide)
  exact absurd this (by decide)

/-- Conditioning zeroes `AddNodeMutation` and `InsertNodeMutation` whenever the member's
complexity is at least `curmaxsize` (`src/Mutate.jl:203-207`). -/
def add_maxsize : Prop := ∀ (ws : Weights) (c : CondIn), c.complexity ≥ c.curmaxsize →
  AllZero (conditionMutationWeights ws c) .addNode ∧ AllZero (conditionMutationWeights ws c) .insertNode

theorem add_maxsize_refuted : ¬ add_maxsize := by
  intro h
  have := (h [(.addNode, .fin 1)] ⟨2, .feature 1, false, 0, 3, 3, 2, true, false⟩ (by decide)).1 (.fin 1) (by decide)
  exact absurd this (by decide)

/-- Is a variable leaf. -/
def isVariable : Tree JF → Bool
  | .feature _ => true
  | _ => false

/-- `mutate_feature` returns the tree unchanged when it has no variable leaf
(`src/MutationFunctions.jl:201`), so conditioning zeroes `FeatureMutation` then, as it does
for a constant leaf (`src/Mutate.jl:187-189`). -/
def feature_needs_variable : Prop := ∀ (ws : Weights) (c : CondIn),
  someNode isVariable c.tree = false → AllZero (conditionMutationWeights ws c) .feature

theorem feature_needs_variable_refuted : ¬ feature_needs_variable := by
  intro h
  have := h [(.feature, .fin 1)] ⟨2, .branch 1 [.const (.fin 1), .const (.fin 2)], false, 2, 3, 10, 2, true, false⟩
    (by decide) (.fin 1) (by decide)
  exact absurd this (by decide)

/-- `optimize_constants` returns the member unchanged with no evaluations when there is no
constant to optimize (`src/ConstantOptimization.jl:148-150`), so conditioning zeroes
`OptimizeMutation` then, as it does for a variable leaf (`src/Mutate.jl:184-186`). -/
def optimize_needs_constant : Prop := ∀ (ws : Weights) (c : CondIn),
  NodeUtils.countConstantNodes c.tree = 0 → c.scalarConsts = 0 →
  AllZero (conditionMutationWeights ws c) .optimize

theorem optimize_needs_constant_refuted : ¬ optimize_needs_constant := by
  intro h
  have := h [(.optimize, .fin 1)] ⟨2, .branch 1 [.feature 1, .feature 2], false, 0, 3, 10, 2, true, false⟩
    (by simp [NodeUtils.countConstantNodes]) rfl (.fin 1) (by decide)
  exact absurd this (by decide)

/-- `randomly_rotate_tree!` returns the tree unchanged when no node is a valid rotation
root (`src/MutationFunctions.jl:626-630`), so conditioning zeroes `RotateTreeMutation`
then. -/
def rotate_needs_root : Prop := ∀ (ws : Weights) (c : CondIn),
  someNode validRotationRoot c.tree = false → AllZero (conditionMutationWeights ws c) .rotateTree

theorem rotate_needs_root_refuted : ¬ rotate_needs_root := by
  intro h
  have := h [(.rotateTree, .fin 1)] ⟨2, .feature 1, false, 0, 1, 10, 2, true, false⟩ (by decide) (.fin 1) (by decide)
  exact absurd this (by decide)

-- Source: src/Mutate.jl:133-136. Stock Vector positions are represented zero-based.
def stockWeightAccess : WeightAccess Weights Kind JF JF where
  indices ws := List.range ws.length
  get ws i := match ws[i]? with
    | some p => .ok p
    | none => .error .boundsError
  assign ws i p := if i < ws.length then (.ok (), ws.set i p) else (.error .boundsError, ws)

private theorem set_after_prefix {A : Type} (done tail : List A) (p q : A) :
    (done ++ p :: tail).set done.length q = done ++ q :: tail := by
  induction done with
  | nil => rfl
  | cons x xs ih => simp [List.set, ih]

private theorem stock_update_loop (op : JF → JF) (M : Kind → Bool) (done ws : Weights) :
    updateWeightSlots stockWeightAccess M (fun w v => (.ok (op v), w))
      (List.range' done.length ws.length) (done ++ ws) =
      (.ok (), done ++ updateWeight op ws M) := by
  induction ws generalizing done with
  | nil => simp [updateWeightSlots, updateWeight]
  | cons p ws ih =>
    have hg : (done ++ p :: ws)[done.length]? = some p := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hb : done.length < (done ++ p :: ws).length := by simp
    simp only [List.length_cons, List.range'_succ, updateWeightSlots, stockWeightAccess, hg]
    have hn : (done ++ [p]).length = done.length + 1 := by simp
    obtain ⟨k, w⟩ := p
    by_cases hM : M k = true
    · let p' : Kind × JF := (k, op w)
      have hnp : (done ++ [p']).length = done.length + 1 := by simp
      simp only [hM, ↓reduceIte, hb, set_after_prefix]
      simpa only [List.append_assoc, List.singleton_append, hnp, updateWeight, List.map_cons,
        hM, ↓reduceIte, p', stockWeightAccess] using ih (done ++ [p'])
    · simp only [hM, Bool.false_eq_true, ↓reduceIte]
      simpa only [List.append_assoc, List.singleton_append, hn, updateWeight, List.map_cons,
        hM, Bool.false_eq_true, ↓reduceIte, stockWeightAccess] using ih (done ++ [(k, w)])

/-- The checked stock-vector loop agrees with the elementwise specification, and
both stock wrappers apply their conversion at the reached call site. -/
def stock_update_weight : Prop := update_weight ∧
  ∀ (op : JF → JF) (ws : Weights) (M : Kind → Bool) (v f : JF),
    updateWeightInPlace stockWeightAccess M (fun w x => (.ok (op x), w)) ws =
      (.ok (), updateWeight op ws M) ∧
    setWeightInPlace stockWeightAccess M
      (fun w => (.ok (SymReg.Loss.LossPrecision.round .float64 v), w)) ws =
      (.ok (), setWeight ws M (SymReg.Loss.LossPrecision.round .float64 v)) ∧
    scaleWeightInPlace stockWeightAccess M (fun w => (.ok (SymReg.Loss.LossPrecision.round .float64 f), w))
      (fun w x factor => (.ok (SymReg.Loss.LossPrecision.round .float64 (x * factor)), w)) ws =
      (.ok (), scaleWeight ws M f)

private theorem stock_update (op : JF → JF) (ws : Weights) (M : Kind → Bool) :
    updateWeightInPlace stockWeightAccess M (fun w x => (.ok (op x), w)) ws =
      (.ok (), updateWeight op ws M) := by
  simpa only [updateWeightInPlace, stockWeightAccess, List.nil_append, List.length_nil, List.range_eq_range']
    using stock_update_loop op M [] ws

theorem stock_update_weight_holds : stock_update_weight := by
  refine ⟨update_weight_holds, ?_⟩
  intro op ws M v f
  exact ⟨stock_update op ws M, stock_update _ ws M, stock_update _ ws M⟩

end SymReg.MutateGen
