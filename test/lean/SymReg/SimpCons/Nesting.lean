import SymReg.SimpCons.Constraints

namespace SymReg.SimpCons
open DynExpr DynExpr.NodeBase SymReg.Constraints SymReg.HeapLemmas

private theorem pureFold {T R B : Type} (D : Nat) (fl : Tree T → R)
    (fb : Tree T → B) (op : B → List R → R) (t : Tree T) :
    tmrT (m := Jl) D (fun t => pure (fl t)) (fun t => pure (fb t))
      (fun b rs => pure (op b rs)) t =
    .ok (Id.run (tmrT (m := Id) D (fun t => pure (fl t))
      (fun t => pure (fb t)) (fun b rs => pure (op b rs)) t)) := by
  induction t using Tree.induction with
  | hc v => rfl
  | hf i => rfl
  | hb o cs ih =>
    have forest : ∀ k, tmrF (m := Jl) D (fun t => pure (fl t)) (fun t => pure (fb t))
        (fun b rs => pure (op b rs)) k cs = .ok
      (Id.run (tmrF (m := Id) D (fun t => pure (fl t)) (fun t => pure (fb t))
        (fun b rs => pure (op b rs)) k cs)) := by
      intro k
      induction k generalizing cs with
      | zero => cases cs <;> rfl
      | succ k ihk =>
        cases cs with
        | nil => rfl
        | cons c rest =>
          simp only [tmrF]
          rw [ih c List.mem_cons_self]
          rw [ihk rest (fun c hc => ih c (List.mem_cons_of_mem _ hc))]
          rfl
    simp only [tmrT]
    split
    · rfl
    · rw [forest]; rfl

private theorem heapFold {T R B : Type} (g : SGraph T) (D fuel root : Nat) (t : Tree T)
    (fl : SCell T → Jl R) (fb : SCell T → Jl B) (op : B → List R → Jl R)
    (FL : Tree T → Jl R) (FB : Tree T → Jl B)
    (hl : ∀ c l, c.degree = 0 → leafOf c = some l → fl c = FL l)
    (hb : ∀ c (ts : List (Tree T)), c.degree = ts.length → 0 < ts.length →
      fb c = FB (.branch c.op ts))
    (hu : Graph.unfold g.view fuel root = some t) (hd : DegLe D t) :
    (treeMapreduceH (σ := Unit) g D true true (fun _ c => StateT.lift (fl c))
      (fun _ c => StateT.lift (fb c)) (fun b rs => StateT.lift (op b rs))
      (fun r _ => r) fuel root).run' () = tmrT D FL FB op t := by
  have h := tmrH_plain g D fl fb op (fun r _ => r) FL FB hl hb fuel root t [] hu hd
  unfold treeMapreduceH
  simp only [Bool.not_true, Bool.and_false, StateT.run'_eq, StateT.run_bind]
  rw [h]
  cases tmrT (m := Jl) D FL FB op t <;> rfl

/-- Sharing does not remove paths. Only branch matches contribute to a path's
count, but the final root test reads the stored degree and operator even at a leaf. -/
def graphNestedPaths : Prop :=
  ∀ (T : Type) (g : SGraph T) D fuel root (t : Tree T) (c : SCell T) degree op,
    Graph.unfold g.view fuel root = some t → DegLe D t → t.Representable →
    g.cells root = some c →
    nestedH g D fuel root degree op =
      .ok ((pathCount degree op t : Int) -
        if c.degree = degree ∧ c.op = op then 1 else 0)

theorem graphNestedPaths_holds : graphNestedPaths := by
  intro T g D fuel root t c degree op hu hd hr hc
  have ht :
      (treeMapreduceH (σ := Unit) g D true true (fun _ _ => StateT.lift (pure (0 : Int)))
        (fun _ c => StateT.lift (pure (if c.degree = degree ∧ c.op = op then (1 : Int) else 0)))
        (fun p cs => StateT.lift (pure (p + maxList cs))) (fun r _ => r) fuel root).run' () =
      .ok (Id.run (tmrT D (fun _ => pure (0 : Int))
        (fun s => pure (if s.degree = degree ∧ opOf s = op then (1 : Int) else 0))
        (fun p cs => pure (p + maxList cs)) t)) := by
    rw [heapFold g D fuel root t (fun _ => pure (0 : Int))
      (fun c => pure (if c.degree = degree ∧ c.op = op then (1 : Int) else 0))
      (fun p cs => pure (p + maxList cs)) (fun _ => pure (0 : Int))
      (fun s => pure (if s.degree = degree ∧ opOf s = op then (1 : Int) else 0))
      (by intros; rfl) (by intros c ts h _; simp [Tree.degree, opOf, h]; rfl) hu hd]
    exact pureFold D _ _ _ t
  have hn :
      Id.run (tmrT D (fun _ => pure (0 : Int))
        (fun s => pure (if s.degree = degree ∧ opOf s = op then (1 : Int) else 0))
        (fun p cs => pure (p + maxList cs)) t) = (pathCount degree op t : Int) := by
    rw [tree_mapreduce_fold_holds T Int Int D _ _ _ t hd, nest_fold degree op t hr]
    rfl
  unfold nestedH
  rw [ht, hn]
  simp [ok_bind, Heap.read, hc, pure_ok]

/-- The graph depth check counts the deepest unfolded path, despite sharing. -/
def graphDepthPaths : Prop :=
  ∀ (T : Type) (g : SGraph T) D fuel root t,
    Graph.unfold g.view fuel root = some t → DegLe D t → t.Representable →
    depthH g D fuel root = .ok (t.depth : Int)

theorem graphDepthPaths_holds : graphDepthPaths := by
  intro T g D fuel root t hu hd hr
  unfold depthH
  rw [heapFold g D fuel root t (fun _ => pure (1 : Int)) (fun _ => pure (1 : Int))
    (fun p cs => pure (p + maxList cs)) (fun _ => pure (1 : Int))
    (fun _ => pure (1 : Int)) (by intros; rfl) (by intros; rfl) hu hd]
  rw [pureFold]
  exact congrArg Except.ok (countDepth_eq D t hd hr)

example :
    depthH (mkGraph [featC 0] : SGraph Nat) 2 1 0 = .ok 1 ∧
    nestedH (mkGraph [featC 0] : SGraph Nat) 2 1 0 0 0 = .ok (-1) := by decide

example :
    Graph.unfold sharedSum.view 2 1 =
      some (Tree.branch 1 [Tree.feature 1, Tree.feature 1]) ∧
    DegLe 2 (Tree.branch 1 [Tree.feature 1, Tree.feature 1] : Tree Nat) ∧
    (Tree.branch 1 [Tree.feature 1, Tree.feature 1] : Tree Nat).Representable ∧
    sharedSum.cells 1 = some (br2 1 [0, 0]) := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simp [DegLe]
  · simp [Tree.Representable]

end SymReg.SimpCons
