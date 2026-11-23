import SymReg.PopMember.Core

namespace SymReg.PopMember
open DynExpr
open SymReg.HofMig (Member copyMember)

def lineage : Prop :=
  ∀ t ti mi c l n ref parent flag birth stream cursor m cursor',
    construct t ti mi c l n ref parent (some flag) birth stream cursor = (.ok m, cursor') →
    (birth flag = .ok m.birth ∧ m.parent = parent ∧
      (copyMember m (mi + ti + 1)).1.reference = m.reference ∧
      (copyMember m (mi + ti + 1)).1.parent = parent ∧
      (copyMember m (mi + ti + 1)).1.birth = m.birth) ∧
    (ref ≠ -1 → m.reference = ref ∧ cursor' = cursor) ∧
    (ref = -1 → m.reference = generateReference (stream cursor) ∧ cursor' = cursor + 1)

theorem lineage_holds : lineage := by
  intro t ti mi c l n ref parent flag birth stream cursor m cursor' h
  cases hb : birth flag with
  | error e => by_cases hr : ref = -1 <;> simp [construct, hr, hb, Except.map] at h
  | ok b =>
    by_cases hr : ref = -1 <;> simp [construct, hr, hb, Except.map] at h <;>
      rcases h with ⟨rfl, rfl⟩ <;> simp [hr, copyMember]

example : (construct 0 0 1 (.fin 1) (.fin 0) none (-1) (-1) (some false)
    (fun _ => .ok 2) (fun _ => 4) 0).snd = 1 := by decide

def evaluatedRejectsUnknown : Prop :=
  ∀ (E : Type) (tree : E) (create : E → Jl (Nat × Nat)) compute evaluate oi ref parent det birth stream cursor c,
    let run := constructEvaluated create compute evaluate tree oi c ref parent det birth stream cursor
    (∀ e, create tree = .error e → run = ((.error e, cursor), [.create])) ∧
    (∀ ex ti, create tree = .ok (ex, ti) →
      (c = some (-1) → run = ((.error (.assertionError "set_complexity != -1"), cursor), [.create])) ∧
      (c = none → compute ex = .ok (-1) →
        run = ((.error (.assertionError "set_complexity != -1"), cursor), [.create, .complexity])) ∧
      (c = none → ∀ e, compute ex = .error e → run = ((.error e, cursor), [.create, .complexity])))

theorem evaluatedRejectsUnknown_holds : evaluatedRejectsUnknown := by
  intro E tree create compute evaluate oi ref parent det birth stream cursor c
  constructor
  · intro e h
    simp [constructEvaluated, h]
  · intro ex ti h
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [constructEvaluated]

def scoreAlias : Prop :=
  ∀ (M A : Type) getField setField invalidate (m : M) (a : A),
    getProperty getField (.ok ()) "score" = @getProperty A getField (.ok ()) "cost" ∧
    setProperty setField invalidate (.ok ()) m "score" a =
      setProperty setField invalidate (.ok ()) m "cost" a

theorem scoreAlias_holds : scoreAlias := by
  intro M A getField setField invalidate m a
  exact ⟨rfl, rfl⟩

private def invalidateStock (m : Member) : Jl Member := .ok { m with complexity := -1 }

private def writeTree (m : Member) (_ : String) (tree : Option Nat) : Jl Member :=
  match tree with
  | none => .error (.errorException "TypeError")
  | some t => .ok { m with tree := t }

def cacheAccess : Prop := ∀ (m : Member) tree,
  let reject := setProperty writeTree invalidateStock (.ok ()) m "complexity" tree
  let update := setProperty writeTree invalidateStock (.ok ()) m "tree" tree
  (∃ e, reject.1 = .error (.errorException e)) ∧ reject.2 = m ∧
  update.2.complexity = -1 ∧ update.2.tree = tree.getD m.tree ∧
  (∀ e, getProperty (fun _ => .ok m.complexity) (.ok ()) "complexity" ≠ .ok e) ∧
  (tree = none → update.1 = .error (.errorException "TypeError"))

theorem cacheAccess_holds : cacheAccess := by
  intro m tree
  cases tree <;> simp [setProperty, invalidateStock, writeTree, getProperty]

def typeRoundTrip : Prop := ∀ old p n bounds,
  (withTypeParameters old p bounds = .ok (.concrete p) ↔
    bounds.dataOK p.data = true ∧ bounds.lossOK p.loss = true ∧
    bounds.expressionData p.expression = some p.data) ∧
  (∀ q, replaceExpression p n bounds = .ok (.concrete q) →
    q.data = p.data ∧ q.loss = p.loss ∧ expressionType q = n ∧
    bounds.expressionData (expressionType q) = some q.data) ∧
  (bounds.expressionData n ≠ some p.data → replaceExpression p n bounds = .error (.methodError "with_expression_type"))

theorem typeRoundTrip_holds : typeRoundTrip := by
  intro old p n bounds
  constructor
  · simp [withTypeParameters, Bool.and_eq_true, and_assoc]
  · constructor
    · intro q h
      by_cases hn : bounds.expressionData n = some p.data
      · simp [replaceExpression, hn, withExpressionType] at h
        cases h
        exact ⟨rfl, rfl, rfl, hn⟩
      · simp [replaceExpression, hn] at h
    · intro hn
      simp [replaceExpression, hn]

def appendOutput (s chunk : String) : Jl Unit × String := (.ok (), s ++ chunk)

def showLayout : Prop :=
  ∀ (m : Member) (renderTree : Nat → String) (renderScalar : JF → String) initial,
    showMember appendOutput (fun t => .ok (renderTree t)) (fun x => .ok (renderScalar x)) m initial =
      (.ok (), initial ++ ("PopMember(tree = (" ++ renderTree m.tree ++ "), loss = " ++
        renderScalar m.loss ++ ", cost = " ++ renderScalar m.cost ++ ")"))

theorem showLayout_holds : showLayout := by
  intro m renderTree renderScalar initial
  simp [showMember, showMember.output, appendOutput, shower, Except.map, String.append_assoc]

open DynExpr.Registry

def entries : List Entry := [
  { id := "popmember-lineage", juliaFile := "src/PopMember.jl",
    juliaFns := ["PopMember", "generate_reference", "copy"],
    statement := "Successful construction records the birth supplied by get_birth_order and retains the supplied parent. Only a sentinel ref draws from the task-local random stream. Copy retains birth, ref and parent.",
    preconditions := "64-bit Julia; ordinary PopMember; successful construction.", status := .proven,
    prop := ``lineage, thm := some ``lineage_holds,
    notes := "The field documentation calls ref a unique reference ID. Generation draws abs(rand(Int)) without checking prior IDs, so collisions remain possible; each task draws from its own default RNG state." },
  { id := "popmember-evaluated-complexity", juliaFile := "src/PopMember.jl",
    juliaFns := ["PopMember"],
    statement := "The dataset constructor propagates expression-creation or complexity errors and rejects both supplied and computed cache sentinels before evaluating the loss or drawing a reference.",
    preconditions := "None.", status := .proven,
    prop := ``evaluatedRejectsUnknown, thm := some ``evaluatedRejectsUnknown_holds },
  { id := "popmember-score-alias", juliaFile := "src/PopMember.jl",
    juliaFns := ["getproperty", "setproperty!"],
    statement := "A deprecated score read or write has the same effect and result as the corresponding cost access after the warning returns.",
    preconditions := "Deprecation warning returns normally.", status := .proven,
    prop := ``scoreAlias, thm := some ``scoreAlias_holds },
  { id := "popmember-cache-access", juliaFile := "src/PopMember.jl",
    juliaFns := ["getproperty", "setproperty!"],
    statement := "The property API rejects direct cache reads and writes. Tree assignment writes -1 to the cache even if the new tree has the wrong type.",
    preconditions := "Stock PopMember fields.",
    status := .proven, prop := ``cacheAccess, thm := some ``cacheAccess_holds },
  { id := "popmember-type-parameters", juliaFile := "src/PopMember.jl",
    juliaFns := ["constructorof", "with_expression_type", "with_type_parameters", "expression_type", "default_popmember_type"],
    statement := "Respecialization accepts exactly the data, loss and expression types allowed by PopMember bounds. Expression replacement preserves the data and loss types and rejects a mismatched expression data type.",
    preconditions := "Julia supplies type-subtyping relations.", status := .proven,
    prop := ``typeRoundTrip, thm := some ``typeRoundTrip_holds },
  { id := "popmember-show-layout", juliaFile := "src/PopMember.jl",
    juliaFns := ["show", "shower"],
    statement := "PopMember display prints the rendered tree in parentheses, then rendered loss, then rendered cost, with the documented field labels and delimiters.",
    preconditions := "Rendering and output succeed.", status := .proven,
    prop := ``showLayout, thm := some ``showLayout_holds }
]

end SymReg.PopMember
