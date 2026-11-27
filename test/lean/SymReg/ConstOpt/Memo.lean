import DynExpr.NodeBase.TreeOps

/-!
Model and soundness proof for dirty-bit subtree memoization (`MemoPlan`) during
FiniteDiff constant optimization (`src/ConstantOptimization.jl`: `MemoNode`, `MemoPlan`,
`_build_memo_masks`, `_consume_const_mask!`, `_assign_memo_slots`, `_check_memo_ok`,
`_eval_memo_record`, `_eval_memo_read`, `_eval_with_memo`).
-/

namespace SymReg.ConstOpt
open DynExpr DynExpr.NodeBase

-- Count constant leaves in a tree in pre-order DFS order.
mutual
  def countConsts {T : Type} : Tree T → Nat
    | .const _ => 1
    | .feature _ => 0
    | .branch _ cs => countConstsF cs

  def countConstsF {T : Type} : List (Tree T) → Nat
    | [] => 0
    | c :: cs => countConsts c + countConstsF cs
end

-- Replace constant leaves in pre-order DFS order using 0-based `xs : Nat → T`,
-- starting at `idx`, returning `(updatedTree, nextIdx)`.
mutual
  def setConstsAt {T : Type} (xs : Nat → T) : Tree T → Nat → Tree T × Nat
    | .const _, idx => (.const (xs idx), idx + 1)
    | .feature f, idx => (.feature f, idx)
    | .branch op cs, idx =>
      let (cs', idx') := setConstsAtF xs cs idx
      (.branch op cs', idx')

  def setConstsAtF {T : Type} (xs : Nat → T) : List (Tree T) → Nat → List (Tree T) × Nat
    | [], idx => ([], idx)
    | c :: cs, idx =>
      let (c', idx1) := setConstsAt xs c idx
      let (cs', idx2) := setConstsAtF xs cs idx1
      (c' :: cs', idx2)
end

mutual
  theorem setConstsAt_snd {T : Type} (xs : Nat → T) :
      ∀ (t : Tree T) (idx : Nat), (setConstsAt xs t idx).2 = idx + countConsts t
    | .const _, idx => rfl
    | .feature _, idx => by simp [setConstsAt, countConsts]
    | .branch _ cs, idx => setConstsAtF_snd xs cs idx

  theorem setConstsAtF_snd {T : Type} (xs : Nat → T) :
      ∀ (cs : List (Tree T)) (idx : Nat), (setConstsAtF xs cs idx).2 = idx + countConstsF cs
    | [], idx => by simp [setConstsAtF, countConstsF]
    | c :: cs, idx => by
      simp only [setConstsAtF, countConstsF]
      rw [setConstsAtF_snd xs cs (setConstsAt xs c idx).2, setConstsAt_snd xs c idx, Nat.add_assoc]
end

mutual
  theorem setConstsAt_agree {T : Type} (xs1 xs2 : Nat → T) :
      ∀ (t : Tree T) (idx : Nat),
        (∀ i, idx ≤ i → i < idx + countConsts t → xs1 i = xs2 i) →
        (setConstsAt xs1 t idx).1 = (setConstsAt xs2 t idx).1
    | .const _, idx, h => by
      simp only [setConstsAt]
      exact congrArg Tree.const (h idx (Nat.le_refl _) (by simp [countConsts]))
    | .feature _, _, _ => rfl
    | .branch op cs, idx, h => by
      simp only [setConstsAt]
      exact congrArg (Tree.branch op) (setConstsAtF_agree xs1 xs2 cs idx h)

  theorem setConstsAtF_agree {T : Type} (xs1 xs2 : Nat → T) :
      ∀ (cs : List (Tree T)) (idx : Nat),
        (∀ i, idx ≤ i → i < idx + countConstsF cs → xs1 i = xs2 i) →
        (setConstsAtF xs1 cs idx).1 = (setConstsAtF xs2 cs idx).1
    | [], _, _ => rfl
    | c :: cs, idx, h => by
      simp only [setConstsAtF]
      have hc : (setConstsAt xs1 c idx).1 = (setConstsAt xs2 c idx).1 :=
        setConstsAt_agree xs1 xs2 c idx (fun i hi1 hi2 =>
          h i hi1 (by simp only [countConstsF]; omega))
      have hidx1 : (setConstsAt xs1 c idx).2 = idx + countConsts c := setConstsAt_snd xs1 c idx
      have hidx2 : (setConstsAt xs2 c idx).2 = idx + countConsts c := setConstsAt_snd xs2 c idx
      rw [hidx1, hidx2]
      have hcs : (setConstsAtF xs1 cs (idx + countConsts c)).1 =
          (setConstsAtF xs2 cs (idx + countConsts c)).1 :=
        setConstsAtF_agree xs1 xs2 cs (idx + countConsts c) (fun i hi1 hi2 =>
          h i (by omega) (by simp only [countConstsF]; omega))
      rw [hc, hcs]
end

/-- One-bit `BitVec 64` mask `UInt64(1) << idx`. -/
def bit64 (idx : Nat) : BitVec 64 := (1#64 : BitVec 64) <<< idx

theorem bit64_getLsbD (idx i : Nat) (hi : i < 64) :
    (bit64 idx).getLsbD i = decide (i = idx) := by
  unfold bit64
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hlt : i < idx
  · have hne : i ≠ idx := by omega
    simp [hi, hlt, hne]
  · have hnot : ¬ (i < idx) := hlt
    simp only [hi, hnot, decide_true, decide_false, Bool.not_false, Bool.and_true, Bool.true_and]
    rw [BitVec.getLsbD_one]
    by_cases heq : i = idx
    · subst heq; simp
    · have hsub : i - idx ≠ 0 := by omega
      simp [heq, hsub]

/-- Memoization tree mirroring `MemoNode{T,NT}` (`src/ConstantOptimization.jl:192-198`). -/
inductive MemoTree (T : Type) where
  | node (tree : Tree T) (mask : BitVec 64) (slot : Nat) (hasSlots : Bool) (children : List (MemoTree T))

def MemoTree.tree {T : Type} : MemoTree T → Tree T
  | .node t _ _ _ _ => t

def MemoTree.mask {T : Type} : MemoTree T → BitVec 64
  | .node _ m _ _ _ => m

def MemoTree.slot {T : Type} : MemoTree T → Nat
  | .node _ _ s _ _ => s

def MemoTree.hasSlots {T : Type} : MemoTree T → Bool
  | .node _ _ _ hs _ => hs

def MemoTree.children {T : Type} : MemoTree T → List (MemoTree T)
  | .node _ _ _ _ cs => cs

-- `_consume_const_mask!(node, const_idx)` (`src/ConstantOptimization.jl:244-261`).
mutual
  def consumeConstMask {T : Type} : Tree T → Nat → BitVec 64 × Nat
    | .const _, idx => (bit64 idx, idx + 1)
    | .feature _, idx => (0, idx)
    | .branch _ cs, idx => consumeConstMaskF cs idx

  def consumeConstMaskF {T : Type} : List (Tree T) → Nat → BitVec 64 × Nat
    | [], idx => (0, idx)
    | c :: cs, idx =>
      let (m1, idx1) := consumeConstMask c idx
      let (m2, idx2) := consumeConstMaskF cs idx1
      (m1 ||| m2, idx2)
end

-- `is_constant(node)` predicate matching `DynamicExpressions.is_constant`.
mutual
  def isConstantTree {T : Type} : Tree T → Bool
    | .const _ => true
    | .feature _ => false
    | .branch _ cs => isConstantTreeF cs

  def isConstantTreeF {T : Type} : List (Tree T) → Bool
    | [] => true
    | c :: cs => isConstantTree c && isConstantTreeF cs
end

-- `_build_memo_masks(node, const_idx)` (`src/ConstantOptimization.jl:215-242`).
mutual
  def buildMemoMasks {T : Type} : Tree T → Nat → MemoTree T × Nat
    | .const v, idx => (.node (.const v) (bit64 idx) 0 false [], idx + 1)
    | .feature f, idx => (.node (.feature f) 0 0 false [], idx)
    | .branch op cs, idx =>
      if isConstantTree (.branch op cs) then
        let (m, idx') := consumeConstMask (.branch op cs) idx
        (.node (.branch op cs) m 0 false [], idx')
      else
        let (mcs, m, idx') := buildMemoMasksF cs idx
        (.node (.branch op cs) m 0 false mcs, idx')

  def buildMemoMasksF {T : Type} : List (Tree T) → Nat → List (MemoTree T) × BitVec 64 × Nat
    | [], idx => ([], 0, idx)
    | c :: cs, idx =>
      let (mc, idx1) := buildMemoMasks c idx
      let (mcs, m2, idx2) := buildMemoMasksF cs idx1
      (mc :: mcs, mc.mask ||| m2, idx2)
end

-- Structural alignment between a `MemoTree` (after mask building and arbitrary slot assignment)
-- and its underlying `Tree T` starting at constant index `idx`.
mutual
  inductive MemoAligned {T : Type} : MemoTree T → Tree T → Nat → Prop where
    | leaf (t : Tree T) (m : BitVec 64) (slot : Nat) (idx : Nat) :
        idx + countConsts t ≤ 64 →
        (∀ i, i < 64 → m.getLsbD i = decide (idx ≤ i ∧ i < idx + countConsts t)) →
        MemoAligned (.node t m slot false []) t idx
    | branch (op : Nat) (cs : List (Tree T)) (mcs : List (MemoTree T))
        (m : BitVec 64) (slot : Nat) (hasSlots : Bool) (idx : Nat) :
        isConstantTree (.branch op cs) = false →
        idx + countConsts (.branch op cs) ≤ 64 →
        (∀ i, i < 64 → m.getLsbD i = decide (idx ≤ i ∧ i < idx + countConsts (.branch op cs))) →
        MemoAlignedF mcs cs idx →
        MemoAligned (.node (.branch op cs) m slot hasSlots mcs) (.branch op cs) idx

  inductive MemoAlignedF {T : Type} : List (MemoTree T) → List (Tree T) → Nat → Prop where
    | nil (idx : Nat) : MemoAlignedF [] [] idx
    | cons (mc : MemoTree T) (c : Tree T) (mcs : List (MemoTree T)) (cs : List (Tree T)) (idx : Nat) :
        MemoAligned mc c idx →
        MemoAlignedF mcs cs (idx + countConsts c) →
        MemoAlignedF (mc :: mcs) (c :: cs) idx
end

private theorem MemoAligned.mask_spec {T : Type} {mt : MemoTree T} {t : Tree T} {idx : Nat}
    (h : MemoAligned mt t idx) :
    ∀ i, i < 64 → mt.mask.getLsbD i = decide (idx ≤ i ∧ i < idx + countConsts t) := by
  cases h <;> assumption

private theorem interval_or_decide (a b c d i : Nat) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c = d) :
    (decide (a ≤ i ∧ i < b) || decide (b ≤ i ∧ i < c)) = decide (a ≤ i ∧ i < d) := by
  subst hcd
  by_cases h1 : a ≤ i ∧ i < b
  · have h3 : a ≤ i ∧ i < c := by omega
    simp [h1, h3]
  · by_cases h2 : b ≤ i ∧ i < c
    · have h3 : a ≤ i ∧ i < c := by omega
      simp [h2, h3]
    · have h3 : ¬ (a ≤ i ∧ i < c) := by omega
      simp [h1, h2, h3]

mutual
  theorem consumeConstMask_spec {T : Type} :
      ∀ (t : Tree T) (idx : Nat),
        (consumeConstMask t idx).2 = idx + countConsts t ∧
        (∀ i, i < 64 → (consumeConstMask t idx).1.getLsbD i =
          decide (idx ≤ i ∧ i < idx + countConsts t))
    | .const _, idx => by
      refine ⟨rfl, fun i hi => ?_⟩
      simp only [consumeConstMask, countConsts, bit64_getLsbD idx i hi]
      by_cases h : i = idx
      · subst h; simp
      · have hne : ¬ (idx ≤ i ∧ i < idx + 1) := by omega
        simp [h, hne]
    | .feature _, idx => by
      refine ⟨by simp [consumeConstMask, countConsts], fun i _ => ?_⟩
      have hne : ¬ (idx ≤ i ∧ i < idx) := by omega
      simp [consumeConstMask, countConsts, hne]
    | .branch _ cs, idx => consumeConstMaskF_spec cs idx

  theorem consumeConstMaskF_spec {T : Type} :
      ∀ (cs : List (Tree T)) (idx : Nat),
        (consumeConstMaskF cs idx).2 = idx + countConstsF cs ∧
        (∀ i, i < 64 → (consumeConstMaskF cs idx).1.getLsbD i =
          decide (idx ≤ i ∧ i < idx + countConstsF cs))
    | [], idx => by
      refine ⟨by simp [consumeConstMaskF, countConstsF], fun i _ => ?_⟩
      have hne : ¬ (idx ≤ i ∧ i < idx) := by omega
      simp [consumeConstMaskF, countConstsF, hne]
    | c :: cs, idx => by
      have ⟨hidx1, hm1⟩ := consumeConstMask_spec c idx
      have ⟨hidx2, hm2⟩ := consumeConstMaskF_spec cs (consumeConstMask c idx).2
      refine ⟨?_, fun i hi => ?_⟩
      · simp only [consumeConstMaskF, countConstsF]
        rw [hidx2, hidx1, Nat.add_assoc]
      · simp only [consumeConstMaskF, BitVec.getLsbD_or]
        rw [hm1 i hi, hm2 i hi, hidx1]
        exact interval_or_decide idx (idx + countConsts c) (idx + countConsts c + countConstsF cs)
          (idx + countConstsF (c :: cs)) i (by omega) (by omega) (by simp [countConstsF]; omega)
end

mutual
  theorem buildMemoMasks_aligned {T : Type} :
      ∀ (t : Tree T) (idx : Nat), idx + countConsts t ≤ 64 →
        (buildMemoMasks t idx).2 = idx + countConsts t ∧
        MemoAligned (buildMemoMasks t idx).1 t idx
    | .const v, idx, hle => by
      refine ⟨rfl, MemoAligned.leaf (.const v) (bit64 idx) 0 idx hle fun i hi => ?_⟩
      rw [bit64_getLsbD idx i hi]
      by_cases h : i = idx
      · subst h; simp [countConsts]
      · have hne : ¬ (idx ≤ i ∧ i < idx + 1) := by omega
        simp [countConsts, h, hne]
    | .feature f, idx, hle => by
      refine ⟨by simp [buildMemoMasks, countConsts],
        MemoAligned.leaf (.feature f) 0 0 idx hle fun i _ => ?_⟩
      have hne : ¬ (idx ≤ i ∧ i < idx) := by omega
      simp [countConsts, hne]
    | .branch op cs, idx, hle => by
      unfold buildMemoMasks
      cases hct : isConstantTree (.branch op cs)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have ⟨hidx, hm, hal⟩ := buildMemoMasksF_aligned cs idx hle
        exact ⟨hidx, MemoAligned.branch op cs _ _ 0 false idx hct hle hm hal⟩
      · simp only [↓reduceIte]
        have ⟨hidx, hm⟩ := consumeConstMask_spec (.branch op cs) idx
        exact ⟨hidx, MemoAligned.leaf (.branch op cs) _ 0 idx hle hm⟩

  theorem buildMemoMasksF_aligned {T : Type} :
      ∀ (cs : List (Tree T)) (idx : Nat), idx + countConstsF cs ≤ 64 →
        (buildMemoMasksF cs idx).2.2 = idx + countConstsF cs ∧
        (∀ i, i < 64 → (buildMemoMasksF cs idx).2.1.getLsbD i =
          decide (idx ≤ i ∧ i < idx + countConstsF cs)) ∧
        MemoAlignedF (buildMemoMasksF cs idx).1 cs idx
    | [], idx, _ => by
      refine ⟨by simp [buildMemoMasksF, countConstsF],
        fun i _ => by
          have hne : ¬ (idx ≤ i ∧ i < idx) := by omega
          simp [buildMemoMasksF, countConstsF, hne],
        MemoAlignedF.nil idx⟩
    | c :: cs, idx, hle => by
      have hlec : idx + countConsts c ≤ 64 := by simp [countConstsF] at hle; omega
      have ⟨hidx1, hal1⟩ := buildMemoMasks_aligned c idx hlec
      have hlecs : (buildMemoMasks c idx).2 + countConstsF cs ≤ 64 := by
        rw [hidx1]; simp [countConstsF] at hle; omega
      have ⟨hidx2, hm2, hal2⟩ := buildMemoMasksF_aligned cs (buildMemoMasks c idx).2 hlecs
      have hm1 := hal1.mask_spec
      refine ⟨?_, fun i hi => ?_, ?_⟩
      · simp only [buildMemoMasksF, countConstsF]
        rw [hidx2, hidx1, Nat.add_assoc]
      · simp only [buildMemoMasksF, BitVec.getLsbD_or]
        rw [hm1 i hi, hm2 i hi, hidx1]
        exact interval_or_decide idx (idx + countConsts c) (idx + countConsts c + countConstsF cs)
          (idx + countConstsF (c :: cs)) i (by omega) (by omega) (by simp [countConstsF]; omega)
      · exact MemoAlignedF.cons _ c _ cs idx hal1 (hidx1 ▸ hal2)
end

/-- Evaluation result mirroring `ResultOk{Vector{T}}`. -/
structure EvalRes (V : Type) where
  val : V
  ok : Bool
  deriving DecidableEq

/-- `_check_memo_ok(res, eval_context)` (`src/ConstantOptimization.jl:345-355`):
enforces `is_valid_array(res.x)` when `early_exit = Val(true)`. -/
def checkMemoOk {V : Type} (validCheck : V → Bool) (r : EvalRes V) : EvalRes V :=
  if !r.ok then r
  else if !validCheck r.val then ⟨r.val, false⟩
  else r

-- Reference unmemoized evaluator matching `_eval_tree_array` with `early_exit = Val(true)`.
mutual
  def evalRef {T V : Type} (evalLeaf : Tree T → EvalRes V)
      (applyOp : Nat → List V → EvalRes V) (validCheck : V → Bool) :
      Tree T → EvalRes V
    | .const v => checkMemoOk validCheck (evalLeaf (.const v))
    | .feature f => checkMemoOk validCheck (evalLeaf (.feature f))
    | .branch op cs =>
      if isConstantTree (.branch op cs) then
        checkMemoOk validCheck (evalLeaf (.branch op cs))
      else
        match evalRefF evalLeaf applyOp validCheck cs with
        | .error bad => bad
        | .ok vs => checkMemoOk validCheck (applyOp op vs)

  def evalRefF {T V : Type} (evalLeaf : Tree T → EvalRes V)
      (applyOp : Nat → List V → EvalRes V) (validCheck : V → Bool) :
      List (Tree T) → Except (EvalRes V) (List V)
    | [] => .ok []
    | c :: cs =>
      let r := evalRef evalLeaf applyOp validCheck c
      if !r.ok then .error r
      else match evalRefF evalLeaf applyOp validCheck cs with
        | .error bad => .error bad
        | .ok vs => .ok (r.val :: vs)
end

-- `_eval_memo_read` (`src/ConstantOptimization.jl:408-471`):
-- reuses `cache[slot]` whenever `(mnode.mask & diff_mask) == 0 && mnode.slot > 0`,
-- and otherwise evaluates recursively with `_check_memo_ok`.
mutual
  def evalMemoRead {T V : Type} (evalLeaf : Tree T → EvalRes V)
      (applyOp : Nat → List V → EvalRes V) (validCheck : V → Bool)
      (diffMask : BitVec 64) (cache : Nat → V) (xs : Nat → T) :
      MemoTree T → Nat → EvalRes V
    | .node t mask slot hasSlots children, idx =>
      if (mask &&& diffMask) == 0 then
        if slot > 0 then ⟨cache slot, true⟩
        else evalRef evalLeaf applyOp validCheck (setConstsAt xs t idx).1
      else if !hasSlots then
        evalRef evalLeaf applyOp validCheck (setConstsAt xs t idx).1
      else
        match t with
        | .branch op _ =>
          match evalMemoReadF evalLeaf applyOp validCheck diffMask cache xs children idx with
          | .error bad => bad
          | .ok vs => checkMemoOk validCheck (applyOp op vs)
        | _ => evalRef evalLeaf applyOp validCheck (setConstsAt xs t idx).1

  def evalMemoReadF {T V : Type} (evalLeaf : Tree T → EvalRes V)
      (applyOp : Nat → List V → EvalRes V) (validCheck : V → Bool)
      (diffMask : BitVec 64) (cache : Nat → V) (xs : Nat → T) :
      List (MemoTree T) → Nat → Except (EvalRes V) (List V)
    | [], _ => .ok []
    | mc :: mcs, idx =>
      let r := evalMemoRead evalLeaf applyOp validCheck diffMask cache xs mc idx
      if !r.ok then .error r
      else match evalMemoReadF evalLeaf applyOp validCheck diffMask cache xs mcs
          (idx + countConsts mc.tree) with
        | .error bad => .error bad
        | .ok vs => .ok (r.val :: vs)
end

-- Cache validity established by a successful `_eval_memo_record` call at `baseX`:
-- every slotted node holds the exact valid evaluation of its subtree under `baseX`.
mutual
  def CacheValid {T V : Type} (evalLeaf : Tree T → EvalRes V)
      (applyOp : Nat → List V → EvalRes V) (validCheck : V → Bool)
      (baseX : Nat → T) (cache : Nat → V) : MemoTree T → Nat → Prop
    | .node t _ slot _ children, idx =>
      (slot > 0 → evalRef evalLeaf applyOp validCheck (setConstsAt baseX t idx).1 = ⟨cache slot, true⟩) ∧
      CacheValidF evalLeaf applyOp validCheck baseX cache children idx

  def CacheValidF {T V : Type} (evalLeaf : Tree T → EvalRes V)
      (applyOp : Nat → List V → EvalRes V) (validCheck : V → Bool)
      (baseX : Nat → T) (cache : Nat → V) : List (MemoTree T) → Nat → Prop
    | [], _ => True
    | mc :: mcs, idx =>
      CacheValid evalLeaf applyOp validCheck baseX cache mc idx ∧
      CacheValidF evalLeaf applyOp validCheck baseX cache mcs (idx + countConsts mc.tree)
end

/-- `diff_mask` computed in `_eval_with_memo` (`src/ConstantOptimization.jl:479-485`):
bit `i < nconst` is set iff `newX i ≠ baseX i`. -/
def DiffMaskSpec {T : Type} (nconst : Nat) (baseX newX : Nat → T) (diff : BitVec 64) : Prop :=
  ∀ i, i < nconst → i < 64 → diff.getLsbD i = false → newX i = baseX i

mutual
  private theorem isConstantTree_setConstsAt {T : Type} (xs : Nat → T) :
      ∀ (t : Tree T) (idx : Nat), isConstantTree (setConstsAt xs t idx).1 = isConstantTree t
    | .const _, _ => rfl
    | .feature _, _ => rfl
    | .branch _ cs, idx => isConstantTreeF_setConstsAtF xs cs idx

  private theorem isConstantTreeF_setConstsAtF {T : Type} (xs : Nat → T) :
      ∀ (cs : List (Tree T)) (idx : Nat), isConstantTreeF (setConstsAtF xs cs idx).1 = isConstantTreeF cs
    | [], _ => rfl
    | c :: cs, idx => by
      simp only [setConstsAtF, isConstantTreeF]
      rw [isConstantTree_setConstsAt xs c idx, isConstantTreeF_setConstsAtF xs cs (setConstsAt xs c idx).2]
end

-- Core theorem: whenever `base_valid = true` (`CacheValid`) and `diff` covers all changed
-- constant coordinates (`DiffMaskSpec`), `_eval_memo_read` agrees identically (both value and
-- `ok` validity flag, including early exit) with unmemoized `evalRef` under `newX`.
mutual
  theorem memo_read_equiv_aux {T V : Type}
      (evalLeaf : Tree T → EvalRes V) (applyOp : Nat → List V → EvalRes V)
      (validCheck : V → Bool) (nconst : Nat) (baseX newX : Nat → T)
      (diff : BitVec 64) (cache : Nat → V)
      (hdiff : DiffMaskSpec nconst baseX newX diff) :
      ∀ (mt : MemoTree T) (t : Tree T) (idx : Nat),
        idx + countConsts t ≤ nconst →
        MemoAligned mt t idx →
        CacheValid evalLeaf applyOp validCheck baseX cache mt idx →
        evalMemoRead evalLeaf applyOp validCheck diff cache newX mt idx =
          evalRef evalLeaf applyOp validCheck (setConstsAt newX t idx).1
    | .node t mask slot hasSlots children, t0, idx, hbound, hal, hcv => by
      have ht : t = t0 := by cases hal <;> rfl
      subst ht
      unfold evalMemoRead
      by_cases hzero : (mask &&& diff) == 0
      · simp only [hzero, ↓reduceIte]
        by_cases hslot : slot > 0
        · simp only [hslot, ↓reduceIte]
          have hband : mask &&& diff = 0 := beq_iff_eq.mp hzero
          have hmask : ∀ i, i < 64 → mask.getLsbD i = decide (idx ≤ i ∧ i < idx + countConsts t) := by
            cases hal <;> assumption
          have hle64 : idx + countConsts t ≤ 64 := by cases hal <;> assumption
          have hset : (setConstsAt newX t idx).1 = (setConstsAt baseX t idx).1 := by
            apply setConstsAt_agree newX baseX t idx
            intro i hi1 hi2
            have hi64 : i < 64 := by omega
            have hinc : i < nconst := by omega
            have hbi : (mask &&& diff).getLsbD i = false := by
              rw [hband]; simp
            rw [BitVec.getLsbD_and, hmask i hi64] at hbi
            have htrue : decide (idx ≤ i ∧ i < idx + countConsts t) = true :=
              decide_eq_true ⟨hi1, hi2⟩
            rw [htrue, Bool.true_and] at hbi
            exact hdiff i hinc hi64 hbi
          rw [hset, hcv.1 hslot]
        · simp [hslot]
      · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
        by_cases hhs : hasSlots
        · simp only [hhs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hal with
          | leaf _ _ _ _ _ _ => cases hhs
          | branch op cs _ _ _ _ _ hnotc _ _ half =>
            have hnotc' : isConstantTree (setConstsAt newX (.branch op cs) idx).1 = false := by
              rw [isConstantTree_setConstsAt]; exact hnotc
            have hchildren := memo_read_equiv_auxF evalLeaf applyOp validCheck nconst baseX newX
              diff cache hdiff children cs idx hbound half hcv.2
            simp only [setConstsAt, evalRef]
            rw [show isConstantTree (.branch op (setConstsAtF newX cs idx).1) = false from hnotc']
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hchildren]
        · simp [hhs]

  theorem memo_read_equiv_auxF {T V : Type}
      (evalLeaf : Tree T → EvalRes V) (applyOp : Nat → List V → EvalRes V)
      (validCheck : V → Bool) (nconst : Nat) (baseX newX : Nat → T)
      (diff : BitVec 64) (cache : Nat → V)
      (hdiff : DiffMaskSpec nconst baseX newX diff) :
      ∀ (mcs : List (MemoTree T)) (cs : List (Tree T)) (idx : Nat),
        idx + countConstsF cs ≤ nconst →
        MemoAlignedF mcs cs idx →
        CacheValidF evalLeaf applyOp validCheck baseX cache mcs idx →
        evalMemoReadF evalLeaf applyOp validCheck diff cache newX mcs idx =
          evalRefF evalLeaf applyOp validCheck (setConstsAtF newX cs idx).1
    | [], [], _, _, .nil _, _ => rfl
    | mc :: mcs, c :: cs, idx, hbound, .cons _ _ _ _ _ halc half, ⟨hcvc, hcvf⟩ => by
      have hmt : mc.tree = c := by cases halc <;> rfl
      rw [hmt] at hcvf
      have hbc : idx + countConsts c ≤ nconst := by simp [countConstsF] at hbound; omega
      have hbf : idx + countConsts c + countConstsF cs ≤ nconst := by
        simp [countConstsF] at hbound; omega
      have hc := memo_read_equiv_aux evalLeaf applyOp validCheck nconst baseX newX
        diff cache hdiff mc c idx hbc halc hcvc
      have hrest := memo_read_equiv_auxF evalLeaf applyOp validCheck nconst baseX newX
        diff cache hdiff mcs cs (idx + countConsts c) hbf half hcvf
      have hsnd : (setConstsAt newX c idx).2 = idx + countConsts c := setConstsAt_snd newX c idx
      simp only [evalMemoReadF, setConstsAtF, evalRefF, hmt, hc, hsnd, hrest]
end

-- Slot assignment (`_assign_memo_slots`) preserves `MemoAligned` regardless of which
-- nonzero slots and `hasSlots` flags are chosen.
mutual
  def assignSlots {T : Type} (chooseSlot : MemoTree T → Nat) : MemoTree T → MemoTree T
    | .node t m _ _ [] => .node t m (chooseSlot (.node t m 0 false [])) false []
    | .node t m _ _ cs =>
      let cs' := assignSlotsF chooseSlot cs
      let hs := cs'.any (fun c => decide (c.slot > 0) || c.hasSlots)
      .node t m (chooseSlot (.node t m 0 false cs)) hs cs'

  def assignSlotsF {T : Type} (chooseSlot : MemoTree T → Nat) : List (MemoTree T) → List (MemoTree T)
    | [] => []
    | c :: cs => assignSlots chooseSlot c :: assignSlotsF chooseSlot cs
end

mutual
  theorem assignSlots_aligned {T : Type} (chooseSlot : MemoTree T → Nat) :
      ∀ {mt : MemoTree T} {t : Tree T} {idx : Nat},
        MemoAligned mt t idx → MemoAligned (assignSlots chooseSlot mt) t idx
    | _, _, _, .leaf t m slot idx hle hm =>
      MemoAligned.leaf t m _ idx hle hm
    | _, _, _, .branch op cs mcs m slot hs idx hnc hle hm half => by
      cases mcs with
      | nil =>
        cases half
        exact MemoAligned.branch op [] [] m _ false idx hnc hle hm (MemoAlignedF.nil idx)
      | cons mc rest =>
        exact MemoAligned.branch op cs _ m _ _ idx hnc hle hm (assignSlotsF_aligned chooseSlot half)

  theorem assignSlotsF_aligned {T : Type} (chooseSlot : MemoTree T → Nat) :
      ∀ {mcs : List (MemoTree T)} {cs : List (Tree T)} {idx : Nat},
        MemoAlignedF mcs cs idx → MemoAlignedF (assignSlotsF chooseSlot mcs) cs idx
    | _, _, _, .nil idx => MemoAlignedF.nil idx
    | _, _, _, .cons mc c mcs cs idx hc hcs =>
      MemoAlignedF.cons _ c _ cs idx (assignSlots_aligned chooseSlot hc) (assignSlotsF_aligned chooseSlot hcs)
end

/-- End-to-end MemoPlan soundness (`src/ConstantOptimization.jl:215-523`):
1. Building masks via `_build_memo_masks` and assigning arbitrary slots via `_assign_memo_slots`
   preserves `MemoAligned` and exact constant count (`nconst ≤ 64`).
2. Whenever `base_valid = true` (`CacheValid`) and `diff` reflects all changed constants
   (`DiffMaskSpec`), `_eval_memo_read` agrees identically (values and `ok` validity flag,
   including `_check_memo_ok` early exit) with fresh unmemoized evaluation of the tree.
3. When `diff = 0`, `(setConstsAt newX t 0).1 = (setConstsAt baseX t 0).1`, so writing `newX`
   via `set_optimizable_parameters!` and returning `base_loss` matches unmemoized `Evaluator`. -/
def memo_plan_sound : Prop :=
  ∀ (T V : Type) (evalLeaf : Tree T → EvalRes V) (applyOp : Nat → List V → EvalRes V)
    (validCheck : V → Bool) (chooseSlot : MemoTree T → Nat)
    (t : Tree T) (nconst : Nat) (baseX newX : Nat → T) (diff : BitVec 64) (cache : Nat → V),
    countConsts t = nconst → nconst ≤ 64 →
    DiffMaskSpec nconst baseX newX diff →
    let mt := assignSlots chooseSlot (buildMemoMasks t 0).1
    (buildMemoMasks t 0).2 = nconst ∧
    (CacheValid evalLeaf applyOp validCheck baseX cache mt 0 →
      evalMemoRead evalLeaf applyOp validCheck diff cache newX mt 0 =
        evalRef evalLeaf applyOp validCheck (setConstsAt newX t 0).1) ∧
    (diff = 0 → (setConstsAt newX t 0).1 = (setConstsAt baseX t 0).1)

theorem memo_plan_sound_holds : memo_plan_sound := by
  intro T V evalLeaf applyOp validCheck chooseSlot t nconst baseX newX diff cache hc hle hdiff
  have hle64 : 0 + countConsts t ≤ 64 := by omega
  have ⟨hcnt, hal0⟩ := buildMemoMasks_aligned t 0 hle64
  have hal := assignSlots_aligned chooseSlot hal0
  refine ⟨by omega, ?_, ?_⟩
  · intro hcv
    exact memo_read_equiv_aux evalLeaf applyOp validCheck nconst baseX newX diff cache hdiff
      (assignSlots chooseSlot (buildMemoMasks t 0).1) t 0 (by omega) hal hcv
  · intro hzero
    apply setConstsAt_agree newX baseX t 0
    intro i hi1 hi2
    have hinc : i < nconst := by omega
    have hi64 : i < 64 := by omega
    exact hdiff i hinc hi64 (by rw [hzero]; simp)

end SymReg.ConstOpt
