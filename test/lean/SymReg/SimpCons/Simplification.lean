import SymReg.SimpCons.Constraints
import DynExpr.Simplify.SimplifyProofs
import DynExpr.Simplify.PatchProofs
import DynExpr.Simplify.CombineProofs
import DynExpr.Simplify.CombineBang
import DynExpr.Simplify.JFLaws

namespace SymReg.SimpCons
open DynExpr DynExpr.Simplify SymReg.HeapLemmas

/-- Composable `simplify_tree!`, `src/ComposableExpression.jl:118-125`.
Conversion to Expression retains the root and metadata. DE's with_contents overload
unwraps the returned Expression (`DynamicExpressions src/Expression.jl:210-214`). -/
def composableSimplify {T M : Type} [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Ex T M) (operators : Option (CEnum T)) (fuel : Nat) (g : Graph T) :
    Jl (Ex T M × Graph T) := patchSimplify ex operators fuel g

inductive ContentsLayout where
  | plainBinary
  | other
  deriving DecidableEq

-- Source: src/ComposableExpression.jl:118-125; DE src/Simplify.jl:22-25
-- inner_ex = DE.$name(convert(Expression, ex), operators)
-- return with_contents(ex, inner_ex)
def composableCombine {T M : Type} [Add T] [Mul T] [Sub T]
    (ex : Ex T M) (operators : Option (CEnum T)) (fuel : Nat) (g : Graph T)
    (layout : ContentsLayout := .plainBinary) : Jl (Ex T M × Graph T) :=
  match layout with
  | .plainBinary => patchCombineDeprecated ex operators fuel g
  | .other => pure (ex, g)

/-- The simplification sequence in `src/SingleIteration.jl:95-99`. It uses both
returned wrappers and mutates the original contents objects without copying. -/
def simplifyMemberTree {T M : Type} [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Ex T M) (operators : Option (CEnum T)) (fuel : Nat) (g : Graph T) :
    Jl (Ex T M × Graph T) := do
  let (ex, g) ← composableSimplify ex operators fuel g
  composableCombine ex operators fuel g

/-- The keyed contents and metadata of a template expression at
`src/TemplateExpression.jl:1047-1067`; metadata includes parameters and its combiner. -/
structure Template (T M : Type) where
  inners : List (Nat × Ex T M)
  metadata : M

/-- The ordered `map` over a template's named tuple, with shared mutable node heap,
`src/TemplateExpression.jl:1052-1054,1064-1066`. -/
def mapInners {T M : Type} (f : Ex T M → Graph T → Jl (Ex T M × Graph T)) :
    List (Nat × Ex T M) → Graph T → Jl (List (Nat × Ex T M) × Graph T)
  | [], g => pure ([], g)
  | (key, ex) :: rest, g => do
    let (ex, g) ← f ex g
    let (rest, g) ← mapInners f rest g
    pure ((key, ex) :: rest, g)

/-- Template `simplify_tree!`, `src/TemplateExpression.jl:1059-1067`. -/
def templateSimplify {T M : Type} [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Template T M) (operators : Option (CEnum T)) (fuel : Nat) (g : Graph T) :
    Jl (Template T M × Graph T) := do
  let (inners, g) ← mapInners (fun e h => composableSimplify e operators fuel h) ex.inners g
  pure (⟨inners, ex.metadata⟩, g)

/-- Template `combine_operators`, `src/TemplateExpression.jl:1047-1055`. -/
def templateCombine {T M : Type} [Add T] [Mul T] [Sub T]
    (ex : Template T M) (operators : Option (CEnum T)) (fuel : Nat) (g : Graph T) :
    Jl (Template T M × Graph T) := do
  let (inners, g) ← mapInners (fun e h => composableCombine e operators fuel h) ex.inners g
  pure (⟨inners, ex.metadata⟩, g)

/-- The constant-folding wrapper retains root identity and all metadata and unfolds
to the DE specification, on every well-formed input including aliased nodes. -/
def composableFoldSpec : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Ex T M) operators D nf fuel (g : Graph T) t,
    g.unfold fuel ex.tree = some t → t.WF D (operators.getD ex.operators).toOpEnum.nops nf →
    ∃ g', composableSimplify ex operators fuel g = .ok (ex, g') ∧
      g'.unfold fuel ex.tree = some (simplifyPure (operators.getD ex.operators).toOpEnum t)

theorem composableFoldSpec_holds : composableFoldSpec := by
  intro T M _ _ _ _ _ ex operators D nf fuel g t hu hw
  obtain ⟨g', hs, ht⟩ := simplify_matches_spec_proof T _ D nf fuel g ex.tree t hu hw
  refine ⟨g', ?_, ht⟩
  simp [composableSimplify, patchSimplify, hs, pure_ok, ok_bind]

/-- Composable folding preserves denotation for every binding and arbitrary operators. -/
def composableFoldDenote : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Ex T M) operators D nf fuel (g : Graph T) t,
    g.unfold fuel ex.tree = some t → t.WF D (operators.getD ex.operators).toOpEnum.nops nf →
    ∃ g' t', composableSimplify ex operators fuel g = .ok (ex, g') ∧
      g'.unfold fuel ex.tree = some t' ∧
      ∀ x, t'.denote (operators.getD ex.operators).toOpEnum x =
        t.denote (operators.getD ex.operators).toOpEnum x

theorem composableFoldDenote_holds : composableFoldDenote := by
  intro T M _ _ _ _ _ ex operators D nf fuel g t hu hw
  obtain ⟨g', t', hs, ht, hd⟩ := simplify_preserves_denote_proof T _ D nf fuel g ex.tree t hu hw
  refine ⟨g', t', ?_, ht, hd⟩
  simp [composableSimplify, patchSimplify, hs, pure_ok, ok_bind]

/-- Composable folding never manufactures a nonfinite constant absent from the input. -/
def composableValidConstants : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Ex T M) operators D nf fuel (g : Graph T) t,
    g.unfold fuel ex.tree = some t → t.WF D (operators.getD ex.operators).toOpEnum.nops nf →
    ∃ g' t', composableSimplify ex operators fuel g = .ok (ex, g') ∧
      g'.unfold fuel ex.tree = some t' ∧
      ∀ v, HasConst v t' → JlValue.valid v = true ∨ HasConst v t

theorem composableValidConstants_holds : composableValidConstants := by
  intro T M _ _ _ _ _ ex operators D nf fuel g t hu hw
  obtain ⟨g', t', hs, ht, hv⟩ := simplify_no_invalid_fold_proof T _ D nf fuel g ex.tree t hu hw
  refine ⟨g', t', ?_, ht, hv⟩
  simp [composableSimplify, patchSimplify, hs, pure_ok, ok_bind]

/-- Folding cannot increase depth or invalidate the operator/feature indices. -/
def composableFoldWF : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Ex T M) operators D nf fuel (g : Graph T) t,
    g.unfold fuel ex.tree = some t → t.WF D (operators.getD ex.operators).toOpEnum.nops nf →
    ∃ g' t', composableSimplify ex operators fuel g = .ok (ex, g') ∧
      g'.unfold fuel ex.tree = some t' ∧
      t'.WF D (operators.getD ex.operators).toOpEnum.nops nf ∧ t'.depth ≤ t.depth

theorem composableFoldWF_holds : composableFoldWF := by
  intro T M _ _ _ _ _ ex operators D nf fuel g t hu hw
  obtain ⟨g', t', hs, ht, hw', hd⟩ := simplify_wf_proof T _ D nf fuel g ex.tree t hu hw
  refine ⟨g', t', ?_, ht, hw', hd⟩
  simp [composableSimplify, patchSimplify, hs, pure_ok, ok_bind]

/-- The wrapper retains its metadata and adopts the dispatched DE root by identity.
GraphNode and plain nodes with a different maximum degree use the fallback. -/
def composableCombineSpec : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] (ex : Ex T M)
    operators fuel (g : Graph T),
    composableCombine ex operators fuel g .other = .ok (ex, g) ∧
    ∀ r g' e h,
      combineOps (operators.getD ex.operators) fuel g ex.tree = .ok (r, g') →
      composableCombine ex operators fuel g .plainBinary = .ok (e, h) →
      e.tree = r ∧ e.kind = ex.kind ∧ e.operators = ex.operators ∧ e.other = ex.other ∧ h = g'

theorem composableCombineSpec_holds : composableCombineSpec := by
  intro T M _ _ _ ex operators fuel g
  refine ⟨rfl, ?_⟩
  intro r g' e h hc hs
  simp [composableCombine, patchCombineDeprecated, patchCombine, hc, pure_ok, ok_bind] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Combination on alias-free composable contents preserves denotation under DE's
commutative-ring arithmetic laws; arbitrary other operators remain arbitrary. -/
def composableCombineDenote : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [Neg T] [Inhabited T], RingLaws T →
    ∀ (ex : Ex T M) operators nf fuel (g : Graph T) t,
    g.unfold fuel ex.tree = some t → t.WF 2 (operators.getD ex.operators).nops nf →
    Graph.NoAlias g ex.tree →
    ∃ e g' t', composableCombine ex operators fuel g = .ok (e, g') ∧
      g'.unfold fuel e.tree = some t' ∧
      ∀ x, t'.denote (operators.getD ex.operators).toOpEnum x =
        t.denote (operators.getD ex.operators).toOpEnum x

theorem composableCombineDenote_holds : composableCombineDenote := by
  intro T M _ _ _ _ _ laws ex operators nf fuel g t hu hw hna
  obtain ⟨r, g', t', hc, ht, hd⟩ :=
    combine_preserves_denote_ring_proof T laws _ nf fuel g ex.tree t hu hw hna
  refine ⟨{ ex with tree := r }, g', t', ?_, ht, hd⟩
  simp [composableCombine, patchCombineDeprecated, patchCombine, hc, pure_ok, ok_bind]

/-- Combination never increases the ordinary node count on alias-free contents. -/
def composableCombineSize : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] (ex : Ex T M)
    operators nf fuel (g : Graph T) t,
    g.unfold fuel ex.tree = some t → t.WF 2 (operators.getD ex.operators).nops nf →
    Graph.NoAlias g ex.tree →
    ∃ e g' t', composableCombine ex operators fuel g = .ok (e, g') ∧
      g'.unfold fuel e.tree = some t' ∧
      t'.WF 2 (operators.getD ex.operators).nops nf ∧ t'.size ≤ t.size

theorem composableCombineSize_holds : composableCombineSize := by
  intro T M _ _ _ ex operators nf fuel g t hu hw hna
  obtain ⟨r, g', t', hc, ht, hw', hd⟩ := combine_wf_proof T _ nf fuel g ex.tree t hu hw hna
  refine ⟨{ ex with tree := r }, g', t', ?_, ht, hw', hd⟩
  simp [composableCombine, patchCombineDeprecated, patchCombine, hc, pure_ok, ok_bind]

private theorem mapInners_keys {T M : Type}
    (f : Ex T M → Graph T → Jl (Ex T M × Graph T))
    (xs : List (Nat × Ex T M)) (g : Graph T) (ys : List (Nat × Ex T M)) (g' : Graph T)
    (h : mapInners f xs g = .ok (ys, g')) : ys.map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing g ys g' with
  | nil => cases h; rfl
  | cons p xs ih =>
    rcases p with ⟨key, ex⟩
    cases hf : f ex g with
    | error err =>
      have he : mapInners f ((key, ex) :: xs) g = .error err := by
        rw [mapInners, hf]
        rfl
      rw [he] at h
      cases h
    | ok p =>
      rcases p with ⟨ex', h1⟩
      cases hr : mapInners f xs h1 with
      | error err =>
        have he : mapInners f ((key, ex) :: xs) g = .error err := by
          simp only [mapInners, hf, ok_bind]
          rw [hr]
          rfl
        rw [he] at h
        cases h
      | ok p =>
        rcases p with ⟨zs, h2⟩
        simp [mapInners, hf, hr, pure_ok, ok_bind] at h
        rcases h with ⟨rfl, rfl⟩
        simp [ih h1 zs h2 hr]

/-- Template wrappers keep the named tuple keys and outer metadata, including
parameter vectors and the combiner, on every successful call. -/
def templateMetadata : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T]
    (ex : Template T M) operators fuel (g : Graph T) e g',
    (templateSimplify ex operators fuel g = .ok (e, g') ∨
      templateCombine ex operators fuel g = .ok (e, g')) →
    e.inners.map Prod.fst = ex.inners.map Prod.fst ∧ e.metadata = ex.metadata

theorem templateMetadata_holds : templateMetadata := by
  intro T M _ _ _ _ _ ex operators fuel g e g' h
  rcases h with h | h
  · cases hm : mapInners (fun e h => composableSimplify e operators fuel h) ex.inners g with
    | error err => simp [templateSimplify, hm] at h
    | ok p =>
      rcases p with ⟨inners, h1⟩
      simp [templateSimplify, hm, pure_ok, ok_bind] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨mapInners_keys _ _ _ _ _ hm, rfl⟩
  · cases hm : mapInners (fun e h => composableCombine e operators fuel h) ex.inners g with
    | error err => simp [templateCombine, hm] at h
    | ok p =>
      rcases p with ⟨inners, h1⟩
      simp [templateCombine, hm, pure_ok, ok_bind] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨mapInners_keys _ _ _ _ _ hm, rfl⟩

/-- A value observed through a root still held by a hall-of-fame member,
`src/SingleIteration.jl:96-99`; `denS` is DE's structural denotation. -/
def observe (o : CEnum JF) (fuel root : Nat) (x : Nat → Option JF) (g : Graph JF) : Option JF :=
  (g.unfold fuel root).bind (denS o.toOpEnum x)

/-- Population simplification should leave another member sharing the old root's
value unchanged, even when each individual input tree is alias-free. -/
def sharedMemberUnchanged : Prop :=
  ∀ (o : CEnum JF) fuel (g : Graph JF) root t (x : Nat → Option JF),
    g.unfold fuel root = some t → t.WF 2 o.nops 1 → Graph.NoAlias g root →
    (match simplifyMemberTree (⟨.expression, root, o, ()⟩ : Ex JF Unit) none fuel g with
      | .ok (_, h) => observe o fuel root x h
      | .error _ => none) = observe o fuel root x g

theorem sharedMemberUnchanged_refuted : ¬ sharedMemberUnchanged := by
  intro h
  let g := (Graph.ofTree (Heap.empty : Graph JF) tPlus12).2
  let root := (Graph.ofTree (Heap.empty : Graph JF) tPlus12).1
  have hu : g.unfold 10 root = some tPlus12 :=
    Graph.unfold_ofTree _ _ (by simp [tPlus12, Tree.Representable]) _
      (by simp [tPlus12, Tree.depth])
  have hw : tPlus12.WF 2 opsPMTD.nops 1 := by simp [tPlus12, Tree.WF, CEnum.nops, opsPMTD]
  have hh := h opsPMTD 10 g root tPlus12 bindX3 hu hw (Graph.noAlias_ofTree _ _)
  have before : observe opsPMTD 10 root bindX3 g = some (.fin 6) := by decide +kernel
  have after : (match simplifyMemberTree (⟨.expression, root, opsPMTD, ()⟩ : Ex JF Unit) none 10 g with
      | .ok (_, h) => observe opsPMTD 10 root bindX3 h
      | .error _ => none) = some (.fin 8) := by decide +kernel
  rw [before, after] at hh
  cases hh

example : ∃ (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 opsPMTD.nops 1 ∧ Graph.NoAlias g root :=
  ⟨(Graph.ofTree (Heap.empty : Graph JF) tPlus12).2,
    (Graph.ofTree (Heap.empty : Graph JF) tPlus12).1, tPlus12,
    Graph.unfold_ofTree _ _ (by simp [tPlus12, Tree.Representable]) _
      (by simp [tPlus12, Tree.depth]),
    by simp [tPlus12, Tree.WF, CEnum.nops, opsPMTD], Graph.noAlias_ofTree _ _⟩

example : RingLaws JF := jf_ringLaws

example :
    let g := (Graph.ofTree (Heap.empty : Graph JF) (.feature 1)).2
    let ex : Template JF Unit := ⟨[(1, ⟨.expression, 0, opsPMTD, ()⟩)], ()⟩
    templateSimplify ex none 1 g = .ok (ex, g) := rfl

end SymReg.SimpCons
