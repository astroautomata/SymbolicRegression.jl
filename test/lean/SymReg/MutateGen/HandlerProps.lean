import SymReg.MutateGen.EngineLemmas

namespace SymReg.MutateGen
open DynExpr
open DynExpr.Expressions.Sampling (RNG draw)

/-- The tree mutations' `mutate!` methods (constant, operator, feature, swap, add, insert,
delete, form/break connection, rotate, randomize) return the mutated copy as `tree` with
`num_evals = 0`, `return_immediately = false` and `success = true`, and only consume draws
of the task-local stream. -/
def tree_handlers : Prop := ∀ (E : Type) (mf : MF E) (k : Kind) (scale : JF) (m : Member E) (t : E)
  (a : Nat) (rng : RNG),
  k ∈ [.constant, .operator, .feature, .swapOperands, .addNode, .insertNode, .deleteNode,
    .formConnection, .breakConnection, .rotateTree, .randomize] →
  ∃ t' rng', mutateH mf k scale m t a rng = .ok ({ out := .tree t', evals := .fin 0, imm := false, success := true }, rng') ∧
    rng'.draws = rng.draws

theorem tree_handlers_holds : tree_handlers := by
  intro E mf k scale m t a rng hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [mutateH, treeStep]
  all_goals first
    | exact ⟨_, _, rfl, rfl⟩
    | (split <;> exact ⟨_, _, rfl, rfl⟩)

/-- `AddNodeMutation` appends a random operator when its first draw is below `0.5` and
prepends one otherwise (`src/Mutate.jl:673-679`). -/
def add_node_choice : Prop := ∀ (E : Type) (mf : MF E) (scale : JF) (m : Member E) (t : E) (a : Nat)
  (rng : RNG),
  mutateH mf .addNode scale m t a rng =
    .ok (treeStep (if rng.draws rng.cursor < 1 / 2 then mf.appendRandomOp else mf.prependRandomOp) t (draw rng).2)

theorem add_node_choice_holds : add_node_choice := by
  intro E mf scale m t a rng
  simp only [mutateH, draw]
  by_cases hu : rng.draws rng.cursor < 1 / 2 <;> simp only [hu, ↓reduceIte] <;> rfl

/-- `DoNothingMutation` returns immediately with a newly allocated member holding the copy
of the parent's tree, the parent's cost and loss, and `parent = parent_ref`. -/
def do_nothing_child : Prop := ∀ (E : Type) (mf : MF E) (scale : JF) (m : Member E) (t : E) (a : Nat)
  (rng : RNG) (s : St E) (po pr : Nat) (complexity : E → Int), s.Inv →
  ∃ r, mutateH mf .doNothing scale m t a rng = .ok (r, rng) ∧ r.imm = true ∧ r.success = true ∧
    r.evals = .fin 0 ∧ ∃ o, (materialise s po pr complexity r.out).1 = .member o ∧ s.objs o = none ∧
      (materialise s po pr complexity r.out).2.objs o = some ⟨t, m.cost, m.loss, o, o, pr, complexity t⟩

theorem do_nothing_child_holds : do_nothing_child := by
  intro E mf scale m t a rng s po pr complexity hi
  refine ⟨_, rfl, rfl, rfl, rfl, s.next, rfl, ?_, by simp [materialise, createChild, St.write]⟩
  cases h : s.objs s.next with
  | none => rfl
  | some x => have := hi _ x h; omega

example : (⟨fun _ => none, 0, { draws := fun _ => 0 }, [], []⟩ : St Nat).Inv := by
  intro o m h; cases h

/-- A user mutation type without a `mutate!` method raises
`ErrorException("Unknown mutation type: ...")` (`src/Mutate.jl:605-607`). -/
def unknown_mutation : Prop := ∀ (E : Type) (mf : MF E) (n : Nat) (scale : JF) (m : Member E) (t : E)
  (a : Nat) (rng : RNG), mf.custom n = none →
  mutateH mf (.custom n) scale m t a rng =
    .error (.errorException ("Unknown mutation type: " ++ mf.customTypeDisplay n))

theorem unknown_mutation_holds : unknown_mutation := by
  intro E mf n scale m t a rng h
  simp [mutateH, h]
  rfl

/-! ## Backsolve -/

section
variable {E : Type}

theorem bsLoop_success (b : BS E) (pc : JF) : ∀ (n : Nat) (t : E) (setup : Option Nat) (ev : JF)
    (rng : RNG), (bsLoop b pc n t setup ev rng).1.imm = true →
    ∃ t' c l, (bsLoop b pc n t setup ev rng).1.out = .child t' c l ∧
      (bsLoop b pc n t setup ev rng).1.success = true ∧
      b.constraints t' (b.complexity t') = true ∧ b.evalCost t' = (c, l) ∧
      improvedGate (if b.subDataset then b.freshParentCost else pc) c = true := by
  intro n
  induction n with
  | zero => intro t setup ev rng h; simp [bsLoop] at h
  | succ n ih =>
    intro t setup ev rng h
    simp only [bsLoop] at h ⊢
    repeat' split at h
    all_goals (repeat' split) <;> simp_all
    all_goals exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, by simp_all, rfl, by simp_all⟩

theorem bsLoop_failure (b : BS E) (pc : JF)
    (hres : ∀ t n x, b.splice (b.splice t n x) n (b.sub t n) = t) :
    ∀ (n : Nat) (t : E) (setup : Option Nat) (ev : JF) (rng : RNG),
    (bsLoop b pc n t setup ev rng).1.imm = false →
    (bsLoop b pc n t setup ev rng).1.out = .tree t ∧ (bsLoop b pc n t setup ev rng).1.success = false := by
  intro n
  induction n with
  | zero => intro t setup ev rng _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro t setup ev rng h
    simp only [bsLoop] at h ⊢
    repeat' split at h
    all_goals (repeat' split) <;> simp_all

end

/-- A backsolve result that returns immediately carries a newly made child whose tree
passed `check_constraints` with its own complexity, whose cost and loss are `eval_cost` of
that tree, and whose cost passed the improvement gate against the parent's cost (re-evaluated
on the batch for a `SubDataset`). -/
def backsolve_success : Prop := ∀ (E : Type) (b : BS E) (pm : Member E) (t : E) (rng : RNG)
  (r : HRes E) (rng' : RNG), backsolveH b pm t rng = (r, rng') → r.imm = true →
  ∃ t' c l, r.out = .child t' c l ∧ r.success = true ∧ b.constraints t' (b.complexity t') = true ∧
    b.evalCost t' = (c, l) ∧ improvedGate (if b.subDataset then b.freshParentCost else pm.cost) c = true

theorem backsolve_success_holds : backsolve_success := by
  intro E b pm t rng r rng' h hi
  unfold backsolveH at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hi
  · have h1 := congrArg Prod.fst h
    simp only at h1
    subst h1
    exact bsLoop_success b pm.cost _ _ _ _ _ hi

/-- When `set_child!` undoes itself (`set_child!(parent, node, idx)` after
`set_child!(parent, new_node, idx)` restores the tree), a backsolve result that does not
return immediately reports `success = false` and hands back the input copy unchanged: every
rejected candidate is reverted. -/
def backsolve_restores : Prop := ∀ (E : Type) (b : BS E) (pm : Member E) (t : E) (rng : RNG)
  (r : HRes E) (rng' : RNG), (∀ t n x, b.splice (b.splice t n x) n (b.sub t n) = t) →
  backsolveH b pm t rng = (r, rng') → r.imm = false → r.out = .tree t ∧ r.success = false

theorem backsolve_restores_holds : backsolve_restores := by
  intro E b pm t rng r rng' hres h hi
  unfold backsolveH at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl⟩
  · have h1 := congrArg Prod.fst h
    simp only at h1
    subst h1
    exact bsLoop_failure b pm.cost hres _ _ _ _ _ hi

example : ∀ (t n x : Nat), (fun (t : Nat) (_ : Nat) (_ : Nat) => t) ((fun t _ _ => t) t n x) n
    ((fun (t : Nat) (_ : Nat) => t) t n) = t := fun _ _ _ => rfl

end SymReg.MutateGen
