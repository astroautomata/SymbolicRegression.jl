import DynExpr.NodeBase.TreeOps
import DynExpr.Runtime.Value

/-!
Model and equivalence proof for constant-free subtree hoisting during constant optimization
(`src/ConstantOptimization.jl`: `_has_any_constant`, `_plan_hoist`, `_collect_hoist_inputs!`,
`_build_hoisted_node`, `_try_hoist_for_optimization`; `src/Dataset.jl`: `with_eval_X`).
-/

namespace SymReg.ConstOpt
open DynExpr DynExpr.NodeBase

-- Decidable equality for `Tree T` from `[DecidableEq T]`.
mutual
  def treeEq {T : Type} [DecidableEq T] : Tree T → Tree T → Bool
    | .const a, .const b => decide (a = b)
    | .feature i, .feature j => decide (i = j)
    | .branch o1 cs1, .branch o2 cs2 => decide (o1 = o2) && treeListEq cs1 cs2
    | _, _ => false

  def treeListEq {T : Type} [DecidableEq T] : List (Tree T) → List (Tree T) → Bool
    | [], [] => true
    | a :: as, b :: bs => treeEq a b && treeListEq as bs
    | _, _ => false
end

mutual
  theorem treeEq_iff {T : Type} [DecidableEq T] :
      ∀ (a b : Tree T), treeEq a b = true ↔ a = b
    | .const x, .const y => by simp [treeEq]
    | .feature i, .feature j => by simp [treeEq]
    | .branch o1 cs1, .branch o2 cs2 => by
      simp only [treeEq, Bool.and_eq_true, decide_eq_true_eq, treeListEq_iff, Tree.branch.injEq]
    | .const _, .feature _ | .const _, .branch _ _
    | .feature _, .const _ | .feature _, .branch _ _
    | .branch _ _, .const _ | .branch _ _, .feature _ => by simp [treeEq]

  theorem treeListEq_iff {T : Type} [DecidableEq T] :
      ∀ (as bs : List (Tree T)), treeListEq as bs = true ↔ as = bs
    | [], [] => by simp [treeListEq]
    | a :: as, b :: bs => by
      simp only [treeListEq, Bool.and_eq_true, treeEq_iff, treeListEq_iff, List.cons.injEq]
    | [], _ :: _ | _ :: _, [] => by simp [treeListEq]
end

instance {T : Type} [DecidableEq T] : DecidableEq (Tree T) := fun a b =>
  if h : treeEq a b = true then isTrue ((treeEq_iff a b).mp h)
  else isFalse (fun heq => h ((treeEq_iff a b).mpr heq))

-- `_has_any_constant(node)` (`src/ConstantOptimization.jl:225-232`).
mutual
  def hasAnyConstant {T : Type} : Tree T → Bool
    | .const _ => true
    | .feature _ => false
    | .branch _ cs => hasAnyConstantF cs

  def hasAnyConstantF {T : Type} : List (Tree T) → Bool
    | [] => false
    | c :: cs => hasAnyConstant c || hasAnyConstantF cs
end

-- `_plan_hoist(node)` (`src/ConstantOptimization.jl:178-189`).
mutual
  def planHoist {T : Type} : Tree T → Bool × Nat
    | .const _ => (true, 0)
    | .feature _ => (false, 0)
    | .branch _ cs =>
      let (anyC, nh) := planHoistF cs
      if anyC then (true, nh) else (false, 1)

  def planHoistF {T : Type} : List (Tree T) → Bool × Nat
    | [] => (false, 0)
    | c :: cs =>
      let (c1, h1) := planHoist c
      let (c2, h2) := planHoistF cs
      (c1 || c2, h1 + h2)
end

mutual
  theorem planHoist_fst {T : Type} : ∀ t : Tree T, (planHoist t).1 = hasAnyConstant t
    | .const _ => rfl
    | .feature _ => rfl
    | .branch _ cs => by
      simp only [planHoist, hasAnyConstant]
      have h := planHoistF_fst cs
      cases hp : planHoistF cs with
      | mk anyC nh =>
        rw [hp] at h
        cases anyC <;> simp_all

  theorem planHoistF_fst {T : Type} : ∀ cs : List (Tree T), (planHoistF cs).1 = hasAnyConstantF cs
    | [] => rfl
    | c :: cs => by
      simp only [planHoistF, hasAnyConstantF]
      rw [← planHoist_fst c, ← planHoistF_fst cs]
end

-- Pointwise tree evaluation on 1-based feature environment `env : Nat → T` and operator
-- semantics `opEval : Nat → List T → T`.
mutual
  def evalTree {T : Type} (opEval : Nat → List T → T) (env : Nat → T) : Tree T → T
    | .const v => v
    | .feature f => env f
    | .branch op cs => opEval op (evalTreeF opEval env cs)

  def evalTreeF {T : Type} (opEval : Nat → List T → T) (env : Nat → T) : List (Tree T) → List T
    | [] => []
    | c :: cs => evalTree opEval env c :: evalTreeF opEval env cs
end

-- In-order constant replacement mirroring `set_scalar_constants!(tree, x, refs)`.
mutual
  def setConsts {T : Type} : Tree T → List T → Tree T × List T
    | .const _, x :: rest => (.const x, rest)
    | .const v, [] => (.const v, [])
    | .feature f, xs => (.feature f, xs)
    | .branch op cs, xs =>
      let (cs', rest) := setConstsF cs xs
      (.branch op cs', rest)

  def setConstsF {T : Type} : List (Tree T) → List T → List (Tree T) × List T
    | [], xs => ([], xs)
    | c :: cs, xs =>
      let (c', xs1) := setConsts c xs
      let (cs', xs2) := setConstsF cs xs1
      (c' :: cs', xs2)
end

mutual
  theorem setConsts_of_no_const {T : Type} :
      ∀ (t : Tree T) (xs : List T), hasAnyConstant t = false → setConsts t xs = (t, xs)
    | .const _, _, h => by simp [hasAnyConstant] at h
    | .feature _, _, _ => rfl
    | .branch op cs, xs, h => by
      simp only [hasAnyConstant] at h
      simp only [setConsts, setConstsF_of_no_const cs xs h]

  theorem setConstsF_of_no_const {T : Type} :
      ∀ (cs : List (Tree T)) (xs : List T), hasAnyConstantF cs = false → setConstsF cs xs = (cs, xs)
    | [], _, _ => rfl
    | c :: cs, xs, h => by
      simp only [hasAnyConstantF, Bool.or_eq_false_iff] at h
      simp only [setConstsF, setConsts_of_no_const c xs h.1, setConstsF_of_no_const cs xs h.2]
end

/-- One-based `findfirst(==(x), xs)` returning `0` when absent. -/
def findIdx1 {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: ys =>
    if x = y then 1
    else if findIdx1 x ys = 0 then 0
    else findIdx1 x ys + 1

theorem findIdx1_mem {α : Type} [DecidableEq α] {x : α} :
    ∀ {xs : List α}, x ∈ xs →
      1 ≤ findIdx1 x xs ∧ findIdx1 x xs ≤ xs.length ∧ xs[findIdx1 x xs - 1]? = some x
  | [], h => by cases h
  | y :: ys, h => by
    by_cases hxy : x = y
    · subst hxy; simp [findIdx1]
    · have hmem : x ∈ ys := by
        rcases List.mem_cons.mp h with rfl | hm
        · exact absurd rfl hxy
        · exact hm
      have ⟨h1, h2, h3⟩ := findIdx1_mem hmem
      have hne : findIdx1 x ys ≠ 0 := by omega
      have hval : findIdx1 x (y :: ys) = findIdx1 x ys + 1 := by
        simp [findIdx1, hxy, hne]
      rw [hval]
      refine ⟨by omega, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · have hsub : findIdx1 x ys + 1 - 1 = (findIdx1 x ys - 1) + 1 := by omega
        rw [hsub]
        simpa using h3

/-- Push `x` to the end of `xs` only if not already present (deduplicating push). -/
def pushUnique {α : Type} [DecidableEq α] (xs : List α) (x : α) : List α :=
  if x ∈ xs then xs else xs ++ [x]

theorem mem_pushUnique_self {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    x ∈ pushUnique xs x := by
  unfold pushUnique
  by_cases h : x ∈ xs <;> simp [h]

theorem mem_pushUnique_of_mem {α : Type} [DecidableEq α] {xs : List α} {a x : α}
    (ha : a ∈ xs) : a ∈ pushUnique xs x := by
  unfold pushUnique
  by_cases h : x ∈ xs <;> simp [h, ha]

-- `_collect_hoist_inputs!(node, orig_features, hoisted_nodes)` (`src/ConstantOptimization.jl:191-223`).
mutual
  def collectHoistInputs {T : Type} [DecidableEq T]
      (t : Tree T) (orig : List Nat) (hoisted : List (Tree T)) :
      List Nat × List (Tree T) :=
    match t with
    | .const _ => (orig, hoisted)
    | .feature _ => (orig, hoisted)
    | .branch op cs =>
      if !hasAnyConstantF cs then
        (orig, pushUnique hoisted (.branch op cs))
      else
        collectHoistChildren cs orig hoisted

  def collectHoistChildren {T : Type} [DecidableEq T]
      (cs : List (Tree T)) (orig : List Nat) (hoisted : List (Tree T)) :
      List Nat × List (Tree T) :=
    match cs with
    | [] => (orig, hoisted)
    | ch :: rest =>
      let (orig1, hoisted1) :=
        match ch with
        | .const _ => (orig, hoisted)
        | .feature f => (pushUnique orig f, hoisted)
        | .branch _ _ => collectHoistInputs ch orig hoisted
      collectHoistChildren rest orig1 hoisted1
end

-- Coverage invariant: every feature leaf below a constant-bearing node is in `orig`,
-- and every maximal constant-free branch is in `hoisted`.
mutual
  def HoistCovers {T : Type} (orig : List Nat) (hoisted : List (Tree T)) : Tree T → Prop
    | .const _ => True
    | .feature f => f ∈ orig
    | .branch op cs =>
      if hasAnyConstantF cs then HoistCoversF orig hoisted cs
      else (.branch op cs) ∈ hoisted

  def HoistCoversF {T : Type} (orig : List Nat) (hoisted : List (Tree T)) : List (Tree T) → Prop
    | [] => True
    | c :: cs => HoistCovers orig hoisted c ∧ HoistCoversF orig hoisted cs
end

mutual
  theorem hoistCovers_mono {T : Type} {orig orig' : List Nat} {hoisted hoisted' : List (Tree T)}
      (ho : ∀ f ∈ orig, f ∈ orig') (hh : ∀ n ∈ hoisted, n ∈ hoisted') :
      ∀ t : Tree T, HoistCovers orig hoisted t → HoistCovers orig' hoisted' t
    | .const _, _ => trivial
    | .feature _, hf => ho _ hf
    | .branch op cs, h => by
      unfold HoistCovers at h ⊢
      split at h <;> rename_i hc
      · simp only [hc, ↓reduceIte]
        exact hoistCoversF_mono ho hh cs h
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hh _ h

  theorem hoistCoversF_mono {T : Type} {orig orig' : List Nat} {hoisted hoisted' : List (Tree T)}
      (ho : ∀ f ∈ orig, f ∈ orig') (hh : ∀ n ∈ hoisted, n ∈ hoisted') :
      ∀ cs : List (Tree T), HoistCoversF orig hoisted cs → HoistCoversF orig' hoisted' cs
    | [], _ => trivial
    | c :: cs, ⟨h1, h2⟩ => ⟨hoistCovers_mono ho hh c h1, hoistCoversF_mono ho hh cs h2⟩
end

mutual
  theorem collectHoistInputs_mono {T : Type} [DecidableEq T] :
      ∀ (t : Tree T) (orig : List Nat) (hoisted : List (Tree T)),
        (∀ f ∈ orig, f ∈ (collectHoistInputs t orig hoisted).1) ∧
        (∀ n ∈ hoisted, n ∈ (collectHoistInputs t orig hoisted).2)
    | .const _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
    | .feature _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
    | .branch op cs, orig, hoisted => by
      unfold collectHoistInputs
      cases hc : hasAnyConstantF cs
      · simp only [Bool.not_false, ↓reduceIte]
        exact ⟨fun _ h => h, fun _ h => mem_pushUnique_of_mem h⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact collectHoistChildren_mono cs orig hoisted

  theorem collectHoistChildren_mono {T : Type} [DecidableEq T] :
      ∀ (cs : List (Tree T)) (orig : List Nat) (hoisted : List (Tree T)),
        (∀ f ∈ orig, f ∈ (collectHoistChildren cs orig hoisted).1) ∧
        (∀ n ∈ hoisted, n ∈ (collectHoistChildren cs orig hoisted).2)
    | [], _, _ => ⟨fun _ h => h, fun _ h => h⟩
    | ch :: rest, orig, hoisted => by
      unfold collectHoistChildren
      cases ch with
      | const v => exact collectHoistChildren_mono rest orig hoisted
      | feature f =>
        have ⟨h1, h2⟩ := collectHoistChildren_mono rest (pushUnique orig f) hoisted
        exact ⟨fun a ha => h1 a (mem_pushUnique_of_mem ha), h2⟩
      | branch op sub =>
        have ⟨ho1, hh1⟩ := collectHoistInputs_mono (.branch op sub) orig hoisted
        have ⟨ho2, hh2⟩ := collectHoistChildren_mono rest
          (collectHoistInputs (.branch op sub) orig hoisted).1
          (collectHoistInputs (.branch op sub) orig hoisted).2
        exact ⟨fun a ha => ho2 a (ho1 a ha), fun n hn => hh2 n (hh1 n hn)⟩
end

mutual
  theorem collectHoistInputs_covers_branch {T : Type} [DecidableEq T] :
      ∀ (op : Nat) (cs : List (Tree T)) (orig : List Nat) (hoisted : List (Tree T)),
        let res := collectHoistInputs (.branch op cs) orig hoisted
        HoistCovers res.1 res.2 (.branch op cs)
    | op, cs, orig, hoisted => by
      dsimp only
      unfold collectHoistInputs HoistCovers
      cases hc : hasAnyConstantF cs
      · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
        exact mem_pushUnique_self hoisted (.branch op cs)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact collectHoistChildren_covers cs orig hoisted

  theorem collectHoistChildren_covers {T : Type} [DecidableEq T] :
      ∀ (cs : List (Tree T)) (orig : List Nat) (hoisted : List (Tree T)),
        let res := collectHoistChildren cs orig hoisted
        HoistCoversF res.1 res.2 cs
    | [], _, _ => trivial
    | ch :: rest, orig, hoisted => by
      dsimp only
      unfold collectHoistChildren HoistCoversF
      cases ch with
      | const v =>
        exact ⟨trivial, collectHoistChildren_covers rest orig hoisted⟩
      | feature f =>
        have hmono := collectHoistChildren_mono rest (pushUnique orig f) hoisted
        refine ⟨hmono.1 f (mem_pushUnique_self orig f),
          collectHoistChildren_covers rest (pushUnique orig f) hoisted⟩
      | branch op sub =>
        let r1 := collectHoistInputs (.branch op sub) orig hoisted
        have hcov1 : HoistCovers r1.1 r1.2 (.branch op sub) :=
          collectHoistInputs_covers_branch op sub orig hoisted
        have hmono := collectHoistChildren_mono rest r1.1 r1.2
        exact ⟨hoistCovers_mono hmono.1 hmono.2 (.branch op sub) hcov1,
          collectHoistChildren_covers rest r1.1 r1.2⟩
end

-- `_build_hoisted_node(node, orig_features, hoisted_nodes, m_orig, opt_refs)`
-- (`src/ConstantOptimization.jl:234-278`).
mutual
  def buildHoistedNode {T : Type} [DecidableEq T]
      (orig : List Nat) (hoisted : List (Tree T)) : Tree T → Tree T
    | .const v => .const v
    | .feature f => .feature (findIdx1 f orig)
    | .branch op cs =>
      if !hasAnyConstantF cs then
        .feature (orig.length + findIdx1 (.branch op cs) hoisted)
      else
        .branch op (buildHoistedNodeF orig hoisted cs)

  def buildHoistedNodeF {T : Type} [DecidableEq T]
      (orig : List Nat) (hoisted : List (Tree T)) : List (Tree T) → List (Tree T)
    | [] => []
    | c :: cs => buildHoistedNode orig hoisted c :: buildHoistedNodeF orig hoisted cs
end

/-- Hoisted feature table `X_hoisted` constructed in `_try_hoist_for_optimization`
(`src/ConstantOptimization.jl:308-324`): first `m_orig` rows copy `X_base[orig[i], :]`,
next `k` rows store `eval_tree_array(hoisted[m], X_base, ops)`. -/
def hoistedEnv {T : Type} (opEval : Nat → List T → T) (env : Nat → T)
    (orig : List Nat) (hoisted : List (Tree T)) (defaultVal : T) (idx : Nat) : T :=
  if idx = 0 then defaultVal
  else if idx ≤ orig.length then
    match orig[idx - 1]? with
    | some f => env f
    | none => defaultVal
  else
    match hoisted[idx - orig.length - 1]? with
    | some h => evalTree opEval env h
    | none => defaultVal

mutual
  theorem hoist_eval_equiv_aux {T : Type} [DecidableEq T]
      (opEval : Nat → List T → T) (env : Nat → T) (defaultVal : T)
      (orig : List Nat) (hoisted : List (Tree T)) :
      ∀ (t : Tree T) (xs : List T),
        HoistCovers orig hoisted t →
        (setConsts (buildHoistedNode orig hoisted t) xs).2 = (setConsts t xs).2 ∧
        evalTree opEval (hoistedEnv opEval env orig hoisted defaultVal)
          (setConsts (buildHoistedNode orig hoisted t) xs).1 =
        evalTree opEval env (setConsts t xs).1
    | .const v, xs, _ => by
      cases xs <;> simp [buildHoistedNode, setConsts, evalTree]
    | .feature f, xs, hcov => by
      simp only [HoistCovers] at hcov
      have ⟨h1, h2, h3⟩ := findIdx1_mem hcov
      have hne : findIdx1 f orig ≠ 0 := by omega
      simp [buildHoistedNode, setConsts, evalTree, hoistedEnv, hne, h2, h3]
    | .branch op cs, xs, hcov => by
      unfold HoistCovers at hcov
      unfold buildHoistedNode
      cases hc : hasAnyConstantF cs
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hcov
        simp only [Bool.not_false, ↓reduceIte]
        have ⟨h1, h2, h3⟩ := findIdx1_mem hcov
        have hnz : orig.length + findIdx1 (.branch op cs) hoisted ≠ 0 := by omega
        have hgt : ¬ (orig.length + findIdx1 (.branch op cs) hoisted ≤ orig.length) := by omega
        have hsub : orig.length + findIdx1 (.branch op cs) hoisted - orig.length - 1 =
            findIdx1 (.branch op cs) hoisted - 1 := by omega
        have hsc : setConsts (.branch op cs) xs = (.branch op cs, xs) :=
          setConsts_of_no_const (.branch op cs) xs (by simp [hasAnyConstant, hc])
        rw [hsc]
        simp only [setConsts, evalTree, hoistedEnv, hnz, hgt, ↓reduceIte, hsub, h3]
        exact ⟨trivial, trivial⟩
      · simp only [hc, ↓reduceIte] at hcov
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have ⟨hrem, heval⟩ := hoist_eval_equiv_auxF opEval env defaultVal orig hoisted cs xs hcov
        simp only [setConsts, evalTree]
        exact ⟨hrem, congrArg (opEval op) heval⟩

  theorem hoist_eval_equiv_auxF {T : Type} [DecidableEq T]
      (opEval : Nat → List T → T) (env : Nat → T) (defaultVal : T)
      (orig : List Nat) (hoisted : List (Tree T)) :
      ∀ (cs : List (Tree T)) (xs : List T),
        HoistCoversF orig hoisted cs →
        (setConstsF (buildHoistedNodeF orig hoisted cs) xs).2 = (setConstsF cs xs).2 ∧
        evalTreeF opEval (hoistedEnv opEval env orig hoisted defaultVal)
          (setConstsF (buildHoistedNodeF orig hoisted cs) xs).1 =
        evalTreeF opEval env (setConstsF cs xs).1
    | [], xs, _ => ⟨rfl, rfl⟩
    | c :: cs, xs, ⟨hc, hcs⟩ => by
      have ⟨hrem1, heval1⟩ := hoist_eval_equiv_aux opEval env defaultVal orig hoisted c xs hc
      simp only [buildHoistedNodeF, setConstsF]
      have hrem1' : (setConsts (buildHoistedNode orig hoisted c) xs).2 = (setConsts c xs).2 := hrem1
      have ⟨hrem2, heval2⟩ := hoist_eval_equiv_auxF opEval env defaultVal orig hoisted cs
        (setConsts c xs).2 hcs
      rw [hrem1']
      refine ⟨hrem2, ?_⟩
      simp only [evalTreeF, heval1, heval2]
end

/-- End-to-end hoisting soundness (`src/ConstantOptimization.jl:178-328`):
for any non-leaf tree `t` with at least one constant and one hoisted subtree (`planHoist`),
`_collect_hoist_inputs!` + `_build_hoisted_node` + `X_hoisted` preserves constant-parameter
order and evaluates identically to the original tree for every parameter vector `xs` and
every sample feature environment `env`. -/
def hoist_eval_equiv : Prop :=
  ∀ (T : Type) [DecidableEq T] (opEval : Nat → List T → T) (env : Nat → T) (defaultVal : T)
    (op : Nat) (cs : List (Tree T)) (xs : List T),
    let t := Tree.branch op cs
    let (orig, hoisted) := collectHoistInputs t [] []
    let t' := buildHoistedNode orig hoisted t
    (setConsts t' xs).2 = (setConsts t xs).2 ∧
    evalTree opEval (hoistedEnv opEval env orig hoisted defaultVal) (setConsts t' xs).1 =
      evalTree opEval env (setConsts t xs).1 ∧
    (planHoist t).1 = hasAnyConstant t

theorem hoist_eval_equiv_holds : hoist_eval_equiv := by
  intro T _ opEval env defaultVal op cs xs
  dsimp only
  have hcov := collectHoistInputs_covers_branch op cs [] []
  have ⟨h1, h2⟩ := hoist_eval_equiv_aux opEval env defaultVal
    (collectHoistInputs (.branch op cs) [] []).1
    (collectHoistInputs (.branch op cs) [] []).2
    (.branch op cs) xs hcov
  exact ⟨h1, h2, planHoist_fst (.branch op cs)⟩

/-- `with_eval_X(dataset, X_eval)` (`src/Dataset.jl:110-136`) replaces only the evaluation
matrix `eval_X` (and updates `nfeatures = size(X_eval, 1)`) while preserving `X`, `y`,
`weights`, `n`, `use_baseline`, and `baseline_loss`. -/
structure HoistDataset (M : Type) where
  rawX : M
  evalX : M
  n : Nat
  nfeatures : Nat
  y : List JF
  weights : Option (List JF)
  useBaseline : Bool
  baselineLoss : JF

def withEvalX {M : Type} (d : HoistDataset M) (newEvalX : M) (newNFeatures : Nat) :
    HoistDataset M :=
  { d with evalX := newEvalX, nfeatures := newNFeatures }

def with_eval_x_frame : Prop :=
  ∀ (M : Type) (d : HoistDataset M) (x' : M) (nf' : Nat),
    let d' := withEvalX d x' nf'
    d'.evalX = x' ∧ d'.nfeatures = nf' ∧
    d'.rawX = d.rawX ∧ d'.n = d.n ∧ d'.y = d.y ∧ d'.weights = d.weights ∧
    d'.useBaseline = d.useBaseline ∧ d'.baselineLoss = d.baselineLoss

theorem with_eval_x_frame_holds : with_eval_x_frame := by
  intro M d x' nf'
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SymReg.ConstOpt
