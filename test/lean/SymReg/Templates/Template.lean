import SymReg.Templates.Composable

/-!
`TemplateExpression` values, construction, `get_tree`, variable checks and evaluation,
`src/TemplateExpression.jl:316-567,857-898,1150-1166`. NamedTuples are lists in key order;
the trees of a template are its inner `ComposableExpression`s in structure-key order.
-/

namespace SymReg.Templates
open DynExpr DynExpr.Expressions

/-- A `TemplateExpression`: structure, inner expressions in key order and parameter vectors
in `num_parameters` key order (`src/TemplateExpression.jl:316-344`). -/
structure TExpr (M : Type) where
  s : TStructure
  inners : List (Expression JF M)
  params : List (List JF)

/-- A supplied parameter value: an `AbstractVector` or anything else. -/
inductive PArg where
  | vec (xs : List JF)
  | other

/-- One parameter vector, `src/TemplateExpression.jl:365-385`: a missing key gets
`init_value(T)` (zero) entries; vectors are kept as given. -/
def paramFor (sp : List (String × PArg)) (k : String) (n : Int) : Jl (List JF) :=
  match (sp.lookup k).getD (.vec (List.replicate n.toNat (.fin 0))) with
  | .other => throw (.argumentError s!"Expected `parameters.{k}` to be an `AbstractVector`")
  | .vec xs => if (xs.length : Int) = n then pure xs
      else throw (.errorException s!"DimensionMismatch: Expected `parameters.{k}` to have length {n}")

/-- `final_parameters`, `src/TemplateExpression.jl:356-394`. -/
def buildParams (s : TStructure) (sup : Option (List (String × PArg))) : Jl (List (List JF)) :=
  if s.hasParams then
    let sp := sup.getD []
    if (sp.map Prod.fst).all (· ∈ s.pkeys) then
      (s.pkeys.zip s.numParams).mapM fun p => paramFor sp p.1 p.2
    else throw (.argumentError "Template parameter names must be a subset of the parameter keys")
  else if (sup.map List.isEmpty).getD true then pure []
  else throw (.assertionError "Expected `parameters` to not be specified")

/-- The keyword constructor followed by the inner constructor's key assertion,
`src/TemplateExpression.jl:338,346-397`. -/
def ctor {M : Type} (s : TStructure) (ks : List String) (inners : List (Expression JF M))
    (sup : Option (List (String × PArg))) : Jl (TExpr M) := do
  let ps ← buildParams s sup
  if ks = s.keys then pure ⟨s, inners, ps⟩
  else throw (.assertionError "keys(trees) == get_function_keys(metadata.structure)")

/-- `max(values(num_features)...)`. -/
def maxNF (s : TStructure) : Int :=
  match s.numFeatures with
  | [] => 0
  | a :: as => as.foldl max a

/-- `get_tree`, `src/TemplateExpression.jl:543-567`: one feature tree per variable up to
`max(num_features)`, zipped with the inner expressions, then the combiner on the inner
trees (`combineT` is the user's `combine` on composable expressions, observed on trees). -/
def getTree {M : Type} (combineT : List (Tree JF) → List (Tree JF) → Jl (Tree JF)) (ex : TExpr M) :
    Jl (Tree JF) :=
  let vars := (ex.inners.zip (List.range (maxNF ex.s).toNat)).map fun p => Tree.feature (p.2 + 1)
  if ex.s.hasParams then
    throw (.argumentError "`get_tree` is not implemented for TemplateExpression with parameters")
  else combineT (ex.inners.map (·.tree)) vars

/-- `contains_features_greater_than`, `src/TemplateExpression.jl:1159-1166`. -/
def containsGreater {T : Type} (m : Int) : Tree T → Bool
  | .const _ => false
  | .feature i => decide ((i : Int) > m)
  | .branch _ cs => (cs.map (containsGreater m)).any id

/-- `has_invalid_variables`, `src/TemplateExpression.jl:1150-1158`; `num_features[key]` is
read positionally, as `keys(trees) == keys(num_features)` holds after construction. -/
def hasInvalid {M : Type} (ex : TExpr M) : Bool :=
  (ex.inners.zip ex.s.numFeatures).any fun p => containsGreater p.2 p.1.tree

/-- What the user's `combine` returns. -/
inductive COut where
  | vv (v : VV JF)
  | other

/-- The user's `combine(contents, [parameters], ValidVector rows...)`. -/
abbrev Combiner := List (Expression JF (Settings JF)) → List (List JF) → List (VV JF) → Jl COut

/-- `eval_tree_array(::TemplateExpression, X)`, `src/TemplateExpression.jl:857-886`, with
`X` given by its rows; `_match_input_eltype` is the identity for `JF` data. -/
def templateEval (combine : Combiner) (ex : TExpr (Settings JF)) (rows : List (List JF)) :
    Jl (Option (List JF) × Bool) :=
  if hasInvalid ex then pure (none, false) else do
    let r ← combine ex.inners (if ex.s.hasParams then ex.params else [])
      (rows.map fun r => ⟨r, true⟩)
    match r with
    | .vv v => pure (some v.x, v.valid)
    | .other => throw (.errorException "TemplateReturnError")

/-- `(ex::TemplateExpression)(X)`, `src/TemplateExpression.jl:887-896`. -/
def templateCall (combine : Combiner) (ex : TExpr (Settings JF)) (rows : List (List JF)) :
    Jl (Option (List JF)) := do
  let (r, v) ← templateEval combine ex rows
  pure (if v then r else none)

/-! ## Properties -/

theorem mapM_ok_map {α β : Type} (f : α → Jl β) (g : α → β) :
    ∀ (l : List α) (ys : List β), (∀ a ∈ l, ∀ b, f a = .ok b → b = g a) →
      l.mapM f = .ok ys → ys = l.map g
  | [], ys, _, h => by cases h; rfl
  | a :: l, ys, hf, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      cases hl : l.mapM f with
      | error e => rw [ha, hl] at h; cases h
      | ok bs =>
        rw [ha, hl] at h
        cases h
        rw [hf a (by simp) b ha, mapM_ok_map f g l bs (fun a' ha' => hf a' (by simp [ha'])) hl]
        rfl

theorem mapM_error_of {α β : Type} (f : α → Jl β) :
    ∀ (l : List α), (∃ a ∈ l, ∃ e, f a = .error e) → ∃ e, l.mapM f = .error e
  | [], ⟨_, ha, _⟩ => by cases ha
  | a :: l, ⟨a', ha', e, he⟩ => by
    rw [List.mapM_cons]
    cases ha : f a with
    | error e' => exact ⟨e', rfl⟩
    | ok b =>
      rcases List.mem_cons.mp ha' with rfl | ha'
      · rw [he] at ha; cases ha
      · obtain ⟨e2, he2⟩ := mapM_error_of f l ⟨a', ha', e, he⟩
        exact ⟨e2, by rw [he2]; rfl⟩

/-- The constructor keeps exactly the structure's key order: trees in that order are stored
with the built parameters, any other order (including a permutation) fails the assertion. -/
def ctorKeys : Prop :=
  ∀ (M : Type) (s : TStructure) (ks : List String) (inners : List (Expression JF M)) sup ps,
    buildParams s sup = .ok ps →
      (ks = s.keys → ctor s ks inners sup = .ok ⟨s, inners, ps⟩) ∧
      (ks ≠ s.keys →
        ctor s ks inners sup = .error (.assertionError "keys(trees) == get_function_keys(metadata.structure)"))

theorem ctorKeys_holds : ctorKeys := by
  intro M s ks inners sup ps hp
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [ctor, hp, okBind]
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

example : ctor (M := Unit) ⟨["f", "g"], [], [1, 1], []⟩ ["g", "f"] [] none =
    .error (.assertionError "keys(trees) == get_function_keys(metadata.structure)") :=
  (ctorKeys_holds Unit ⟨["f", "g"], [], [1, 1], []⟩ ["g", "f"] [] none [] rfl).2 (by decide)

/-- The default for a missing parameter key, and supplied vectors kept as given. -/
def paramValue (sp : List (String × PArg)) (p : String × Int) : List JF :=
  match sp.lookup p.1 with
  | some (.vec xs) => xs
  | _ => List.replicate p.2.toNat (.fin 0)

/-- Parameter construction: names outside the structure's parameter keys are rejected; on
success the vectors follow `num_parameters` order, a supplied vector is stored as given and a
missing one is zero-filled; a supplied vector of the wrong length is rejected; and a
structure without parameters accepts only an absent or empty parameter tuple. -/
def ctorParams : Prop :=
  ∀ (s : TStructure) (sp : List (String × PArg)),
    (s.hasParams = true →
      (¬ (sp.map Prod.fst).all (· ∈ s.pkeys) → ∃ msg, buildParams s (some sp) = .error (.argumentError msg)) ∧
      (∀ ps, buildParams s (some sp) = .ok ps → ps = (s.pkeys.zip s.numParams).map (paramValue sp)) ∧
      (∀ k n xs, (k, n) ∈ s.pkeys.zip s.numParams → sp.lookup k = some (.vec xs) →
        (xs.length : Int) ≠ n → ∃ e, buildParams s (some sp) = .error e)) ∧
    (s.hasParams = false →
      buildParams s none = .ok [] ∧ (sp ≠ [] → ∃ msg, buildParams s (some sp) = .error (.assertionError msg)))

theorem paramFor_ok (sp : List (String × PArg)) (p : String × Int) (b : List JF)
    (h : paramFor sp p.1 p.2 = .ok b) : b = paramValue sp p := by
  unfold paramFor at h
  unfold paramValue
  cases hl : sp.lookup p.1 with
  | none =>
    rw [hl] at h
    simp only [Option.getD_none] at h
    split at h
    · cases h; rfl
    · cases h
  | some a =>
    rw [hl] at h
    cases a with
    | other => cases h
    | vec xs =>
      simp only [Option.getD_some] at h
      split at h
      · cases h; rfl
      · cases h

theorem ctorParams_holds : ctorParams := by
  intro s sp
  refine ⟨fun hp => ⟨fun hn => ⟨"Template parameter names must be a subset of the parameter keys", ?_⟩,
    fun ps h => ?_, fun k n xs hm hl hne => ?_⟩,
    fun hp => ⟨?_, fun hne => ⟨"Expected `parameters` to not be specified", ?_⟩⟩⟩
  · simp only [buildParams, hp, ↓reduceIte, Option.getD_some]
    rw [if_neg hn]; rfl
  · simp only [buildParams, hp, ↓reduceIte, Option.getD_some] at h
    split at h
    · exact mapM_ok_map _ _ _ ps (fun p _ b hb => paramFor_ok sp p b hb) h
    · cases h
  · simp only [buildParams, hp, ↓reduceIte, Option.getD_some]
    split
    · apply mapM_error_of
      refine ⟨(k, n), hm,
        .errorException s!"DimensionMismatch: Expected `parameters.{k}` to have length {n}", ?_⟩
      simp only [paramFor, hl, Option.getD_some]
      rw [if_neg hne]; rfl
    · exact ⟨_, rfl⟩
  · simp [buildParams, hp]
  · cases sp with
    | nil => exact absurd rfl hne
    | cons a sp => simp [buildParams, hp]; rfl

example : buildParams ⟨["f"], ["p"], [1], [2]⟩ (some [("p", .vec [.fin 1])]) =
    .error (.errorException "DimensionMismatch: Expected `parameters.p` to have length 2") := by decide

/-- `get_tree` should succeed for every parameter-free template whose combiner succeeds on
`max(num_features)` variables. -/
def getTreeTotal : Prop :=
  ∀ (M : Type) (ex : TExpr M) (combineT : List (Tree JF) → List (Tree JF) → Jl (Tree JF)),
    ex.s.hasParams = false →
    (∀ vs, vs.length = (maxNF ex.s).toNat → ∃ t, combineT (ex.inners.map (·.tree)) vs = .ok t) →
    ∃ t, getTree combineT ex = .ok t

/-- `TemplateStructure{(:f,)}(((; f), (a, b)) -> f(a, b))`, so `num_features = (f=2,)`. -/
def sF2 : TStructure := ⟨["f"], [], [2], []⟩

/-- `f(a, b)` on the trees, with the destructuring `(a, b)` bounds-checked. -/
def callF2 (ts vs : List (Tree JF)) : Jl (Tree JF) :=
  match ts, vs with
  | [t], [a, b] => compose [a, b] t
  | _, _ => .error .boundsError

/-- The template `f = x1`. -/
def exF2 : TExpr (Settings JF) :=
  ⟨sF2, [⟨.feature 1, ⟨some DynExpr.Eval.Ex.ops, none, true⟩⟩], []⟩

theorem getTreeTotal_refuted : ¬ getTreeTotal := by
  intro h
  obtain ⟨t, ht⟩ := h _ exF2 callF2 rfl (fun vs hvs => by
    match vs, hvs with
    | [a, b], _ => exact ⟨a, by simp [callF2, exF2, compose]⟩)
  change (Except.error .boundsError : Jl (Tree JF)) = .ok t at ht
  cases ht

theorem containsGreater_iff {T : Type} (m : Int) (hm : 0 ≤ m) :
    ∀ t : Tree T, containsGreater m t = decide ((maxFeature t : Int) > m) := by
  intro t
  induction t using Tree.induction with
  | hc v => simp [containsGreater, maxFeature]; omega
  | hf i => simp [containsGreater, maxFeature]
  | hb op cs ih =>
    simp only [containsGreater, maxFeature]
    induction cs with
    | nil => simp; omega
    | cons c cs ihc =>
      simp only [List.map_cons, List.any_cons, id, List.foldr_cons]
      rw [ih c (by simp), ihc (fun c' hc' => ih c' (by simp [hc']))]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rcases Nat.le_total (maxFeature c) ((cs.map maxFeature).foldr max 0) with hle | hle
      · rw [Nat.max_eq_right hle]; omega
      · rw [Nat.max_eq_left hle]; omega

/-- `has_invalid_variables` holds exactly when some inner expression reads a feature beyond
its key's `num_features`. -/
def invalidVars : Prop :=
  ∀ (M : Type) (ex : TExpr M), (∀ m ∈ ex.s.numFeatures, 0 ≤ m) →
    (hasInvalid ex = true ↔ ∃ p ∈ ex.inners.zip ex.s.numFeatures, (maxFeature p.1.tree : Int) > p.2)

theorem invalidVars_holds : invalidVars := by
  intro M ex hnf
  simp only [hasInvalid, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [containsGreater_iff _ (hnf _ (List.of_mem_zip hp).2)] at h
    exact ⟨p, hp, of_decide_eq_true h⟩
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, ?_⟩
    rw [containsGreater_iff _ (hnf _ (List.of_mem_zip hp).2)]
    exact decide_eq_true h

/-- Evaluation contract: invalid variables give `(nothing, false)` (and `nothing` from the
call) whatever the combiner; otherwise the combiner receives the parameters (when present)
and one valid copy of each row, its `ValidVector` is returned as `(x, valid)` and the call
yields `x` exactly when `valid`, and a non-`ValidVector` result throws `TemplateReturnError`. -/
def evalContract : Prop :=
  ∀ (combine : Combiner) (ex : TExpr (Settings JF)) rows,
    (hasInvalid ex = true →
      templateEval combine ex rows = .ok (none, false) ∧ templateCall combine ex rows = .ok none) ∧
    (hasInvalid ex = false →
      let args := rows.map fun r => (⟨r, true⟩ : VV JF)
      let ps := if ex.s.hasParams then ex.params else []
      (∀ v, combine ex.inners ps args = .ok (.vv v) →
        templateEval combine ex rows = .ok (some v.x, v.valid) ∧
        templateCall combine ex rows = .ok (if v.valid then some v.x else none)) ∧
      (combine ex.inners ps args = .ok .other →
        templateEval combine ex rows = .error (.errorException "TemplateReturnError")) ∧
      (∀ e, combine ex.inners ps args = .error e → templateEval combine ex rows = .error e))

theorem evalContract_holds : evalContract := by
  intro combine ex rows
  refine ⟨fun h => ?_, fun h => ⟨fun v hv => ?_, fun hv => ?_, fun e hv => ?_⟩⟩
  · simp [templateCall, templateEval, h]
  · simp only [templateCall, templateEval, h, Bool.false_eq_true, ↓reduceIte, hv, okBind]
    exact ⟨rfl, by cases v.valid <;> rfl⟩
  · simp only [templateEval, h, Bool.false_eq_true, ↓reduceIte, hv, okBind]; rfl
  · simp only [templateEval, h, Bool.false_eq_true, ↓reduceIte, hv, errBind]

/-- The one-key template `((; f), (x,)) -> f(x)`. -/
def sF1 : TStructure := ⟨["f"], [], [1], []⟩

/-- Its combiner: the composable call `f(x)` on the single row. -/
def callF1 (treeEval : Tree JF → JMat JF → OpEnum JF → Jl (List JF × Bool)) : Combiner :=
  fun inners _ args => match inners, args with
    | [f], [x] => (callMixed treeEval f [.vv x]).map .vv
    | _, _ => .error .boundsError

/-- A one-input identity template evaluates exactly like its inner composable expression on
the same data, validity included. -/
def evalIdentity : Prop :=
  ∀ treeEval (f : Expression JF (Settings JF)) (row : List JF) (X : JMat JF),
    maxFeature f.tree ≤ 1 → JMat.ofRows [row] = some X →
    templateEval (callF1 treeEval) ⟨sF1, [f], []⟩ [row] =
      (evalCE treeEval f X).map fun r => (some r.1, r.2)

theorem evalIdentity_holds : evalIdentity := by
  intro treeEval f row X hm hX
  have hinv : hasInvalid (⟨sF1, [f], []⟩ : TExpr (Settings JF)) = false := by
    simp only [hasInvalid, sF1, List.zip_cons_cons, List.zip_nil_right, List.any_cons, List.any_nil,
      Bool.or_false]
    rw [containsGreater_iff _ (by decide)]
    simp only [decide_eq_false_iff_not]
    omega
  have hc := (mixedCall_holds treeEval f [.vv ⟨row, true⟩] ⟨row, true⟩ rfl).2 X hX rfl
  have hp : sF1.hasParams = false := rfl
  simp only [templateEval, hinv, Bool.false_eq_true, ↓reduceIte, hp, List.map_cons, List.map_nil,
    callF1]
  rw [hc]
  cases evalCE treeEval f X <;> rfl

-- Source: src/TemplateExpression.jl:428-439
/-
function DE.get_variable_names(
    e::TemplateExpression,
    variable_names::Union{AbstractVector{<:AbstractString},Nothing}=nothing,
)
    return if variable_names !== nothing
        variable_names
    elseif hasproperty(get_metadata(e), :variable_names)
        get_metadata(e).variable_names
    else
        nothing
    end
end
-/
def templateVariableNames {A : Type} (override : Option A) (metadata : Option (Option A)) : Option A :=
  match override with
  | some xs => some xs
  | none => match metadata with | none => none | some xs => xs

def templateNamesPriority : Prop := ∀ (override : Option (List String)) metadata names,
  templateVariableNames override metadata = some names ↔
    override = some names ∨ (override = none ∧ metadata = some (some names))

theorem templateNamesPriority_holds : templateNamesPriority := by
  intro override metadata names
  cases override <;> cases metadata <;> simp [templateVariableNames]

end SymReg.Templates
