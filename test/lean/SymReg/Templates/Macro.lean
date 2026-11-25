import SymReg.Templates.Builder

/-!
`@template_spec` expansion (`src/TemplateExpressionMacro.jl:37-160`) on a small model of Julia
syntax trees, and `parse_expression(::NamedTuple)` for templates
(`src/TemplateExpression.jl:1293-1436`).
-/

namespace SymReg.Templates
open DynExpr

/-- The Julia syntax the macro inspects. -/
inductive MExpr where
  | sym (s : String)
  | num (n : Nat)
  | tuple (xs : List MExpr)
  | assign (name : String) (v : MExpr)
  | lam (args : MExpr) (body : Nat)

/-- `Meta.isexpr(arg, :(=))`. -/
def MExpr.isAssign : MExpr → Bool
  | .assign _ _ => true
  | _ => false

/-- The name of a `name = value` entry. -/
def MExpr.lhs : MExpr → String
  | .assign n _ => n
  | _ => ""

/-- The fields of the generated `TemplateExpressionSpec(TemplateStructure{K,Kp}(f; ...))`. -/
structure MacroOut where
  keys : List MExpr
  pkeys : Option (List String)
  numParameters : Option MExpr
  numFeatures : Option MExpr
  prototype : Option MExpr
  fargs : List MExpr
  body : Nat

/-- The recognised keywords `(parameters, expressions, num_features, prototype)`. -/
abbrev Kws := Option MExpr × Option MExpr × Option MExpr × Option MExpr

/-- Set a keyword once, `src/TemplateExpressionMacro.jl:51-63`. -/
def setOnce (name : String) (cur : Option MExpr) (v : MExpr) : Jl (Option MExpr) :=
  match cur with
  | some _ => throw (.errorException s!"cannot set `{name}` keyword twice")
  | none => pure (some v)

/-- The keyword loop, `src/TemplateExpressionMacro.jl:48-70`. -/
def collectKws : List MExpr → Kws → Jl Kws
  | [], acc => pure acc
  | .assign n v :: rest, (ps, es, nf, pr) => do
    let acc ← if n = "parameters" then do pure (← setOnce n ps v, es, nf, pr)
      else if n = "expressions" then do pure (ps, ← setOnce n es v, nf, pr)
      else if n = "num_features" then do pure (ps, es, ← setOnce n nf v, pr)
      else if n = "prototype" then do pure (ps, es, nf, ← setOnce n pr v)
      else throw (.errorException s!"unrecognized keyword {n}")
    collectKws rest acc
  | _ :: _, _ => throw (.errorException "no positional args accepted after the first")

/-- The `parameters` check and names, `src/TemplateExpressionMacro.jl:79-100,138-139`. -/
def pkeysOf : Option MExpr → Jl (Option (List String))
  | none => pure none
  | some (.tuple xs) =>
    if xs.all MExpr.isAssign then pure (some (xs.map MExpr.lhs))
    else throw (.argumentError "parameters must be a tuple of parameter name-size pairs")
  | some _ => throw (.argumentError "parameters must be a tuple of parameter name-size pairs")

/-- `template_spec(func, args...)`, `src/TemplateExpressionMacro.jl:41-160`. -/
def templateSpecM (func : MExpr) (args : List MExpr) : Jl MacroOut := do
  let (ps, es, nf, pr) ← collectKws args (none, none, none, none)
  let es ← match es with
    | some e => pure e
    | none => throw (.argumentError "expressions must be specified")
  let keys ← match es with
    | .tuple xs => pure xs
    | _ => throw (.argumentError "expressions must be a tuple of the form `(f, g, ...)`")
  let pkeys ← pkeysOf ps
  match func with
  | .lam (.tuple fargs) body => pure ⟨keys, pkeys, ps, nf, pr, fargs, body⟩
  | .lam _ _ => throw (.argumentError "Expected a tuple of arguments for the function arguments")
  | _ => throw (.argumentError "Expected a do block")

/-- Macro expansion: the structure keys are the `expressions` entries in order, the parameter
keys are the `parameters` names in order with `num_parameters` the `parameters` tuple itself,
`num_features` and `prototype` pass through, and the combiner takes the do-block arguments. -/
def macroExpand : Prop :=
  ∀ (fargs : List MExpr) (body : Nat) (keys pdecls : List MExpr) (nf pr : MExpr),
    pdecls.all MExpr.isAssign = true →
    templateSpecM (.lam (.tuple fargs) body)
      [.assign "expressions" (.tuple keys), .assign "parameters" (.tuple pdecls),
        .assign "num_features" nf, .assign "prototype" pr] =
      .ok ⟨keys, some (pdecls.map MExpr.lhs), some (.tuple pdecls), some nf, some pr, fargs, body⟩ ∧
    templateSpecM (.lam (.tuple fargs) body) [.assign "expressions" (.tuple keys)] =
      .ok ⟨keys, none, none, none, none, fargs, body⟩

theorem macroExpand_holds : macroExpand := by
  intro fargs body keys pdecls nf pr hp
  have hp' : ∀ x ∈ pdecls, x.isAssign = true := by simpa using hp
  constructor
  · simp [templateSpecM, collectKws, setOnce, pkeysOf]; rw [if_pos hp']; rfl
  · simp [templateSpecM, collectKws, setOnce, pkeysOf]

/-- Macro errors: a repeated, unknown or positional argument is rejected, as is a missing or
non-tuple `expressions`, a `parameters` entry that is not `name = size`, and a body that is not
a do block with a tuple of arguments. -/
def macroErrors : Prop :=
  ∀ (func : MExpr) (args : List MExpr) (n : String) (v w e : MExpr) (rest : List MExpr),
    (∃ msg, templateSpecM func (.assign "expressions" v :: .assign "expressions" w :: rest) = .error (.errorException msg)) ∧
    (n ≠ "parameters" → n ≠ "expressions" → n ≠ "num_features" → n ≠ "prototype" →
      ∃ msg, templateSpecM func (.assign n v :: rest) = .error (.errorException msg)) ∧
    (∃ msg, templateSpecM func (.sym "f" :: rest) = .error (.errorException msg)) ∧
    (∃ msg, templateSpecM func [] = .error (.argumentError msg)) ∧
    (∃ msg, templateSpecM func [.assign "expressions" (.sym "f")] = .error (.argumentError msg)) ∧
    (∃ msg, templateSpecM func [.assign "expressions" (.tuple []), .assign "parameters" (.tuple [.sym "p"])] =
      .error (.argumentError msg)) ∧
    (∃ msg, templateSpecM (.sym "f") [.assign "expressions" (.tuple [e])] = .error (.argumentError msg))

theorem macroErrors_holds : macroErrors := by
  intro func args n v w e rest
  refine ⟨⟨"cannot set `expressions` keyword twice", ?_⟩,
    fun h1 h2 h3 h4 => ⟨s!"unrecognized keyword {n}", ?_⟩,
    ⟨"no positional args accepted after the first", rfl⟩, ⟨"expressions must be specified", rfl⟩,
    ⟨"expressions must be a tuple of the form `(f, g, ...)`", rfl⟩,
    ⟨"parameters must be a tuple of parameter name-size pairs", rfl⟩, ⟨"Expected a do block", rfl⟩⟩
  · simp [templateSpecM, collectKws, setOnce]; rfl
  · simp [templateSpecM, collectKws, h1, h2, h3, h4]; rfl

/-! ## `parse_expression` for templates -/

/-- Element type a parsed inner string gets. -/
inductive FTy where
  | f32
  | f64
  deriving DecidableEq, Repr

/-- A guess entry: an expression string (its largest `#N` placeholder and the type of its
floating-point literals, if any), a vector, or anything else. -/
inductive GVal where
  | str (maxVar : Nat) (lit : Option FTy)
  | vec (xs : List JF)
  | other

/-- What a successful parse builds before the template constructor: inner element types and
parameter vectors. -/
structure Parsed where
  types : List FTy
  params : Option (List (String × List JF))

/-- One parameter vector, `src/TemplateExpression.jl:1376-1383`. -/
def paramEntry (p : String × GVal) : Jl (String × List JF) :=
  match p.2 with
  | .vec xs => pure (p.1, xs)
  | _ => throw (.argumentError s!"Expected `parameters.{p.1}` to be an `AbstractVector`")

/-- The parameter vectors, `src/TemplateExpression.jl:1372-1385`. -/
def paramsOf : Option (List (String × GVal)) → Jl (Option (List (String × List JF)))
  | none => pure none
  | some kv => Except.map some (kv.mapM paramEntry)

/-- The element type of one parsed inner string, `src/TemplateExpression.jl:1386-1424`. -/
def typeOf (ex : List (String × GVal)) (k : String) : Jl FTy :=
  match ex.lookup k with
  | some (.str _ lit) => pure (lit.getD .f32)
  | _ => throw (.argumentError s!"Expected template expression `{k}` to be a string")

/-- All inner expressions have one type. -/
def sameType : List FTy → Bool
  | [] => true
  | t :: ts => ts.all (· = t)

/-- `promote_type` on `Float32`/`Float64` (`src/TemplateExpression.jl:1417`). -/
def promoteFTy : FTy → FTy → FTy
  | .f64, _ | _, .f64 => .f64
  | .f32, .f32 => .f32

/-- Common promoted element type of parsed component trees. -/
def commonFTy : List FTy → FTy
  | [] => .f32
  | t :: ts => ts.foldl promoteFTy t

/-- Every guess name is an expression or parameter name. -/
def namesOk (fkeys pkeys : List String) (ex : List (String × GVal)) : Bool :=
  (ex.map Prod.fst).all (· ∈ fkeys ++ pkeys)

/-- Every expression has a guess. -/
def exprsOk (fkeys : List String) (ex : List (String × GVal)) : Bool :=
  fkeys.all (· ∈ ex.map Prod.fst)

/-- The parameter keys given as flat guess entries. -/
def flatKeys (pkeys : List String) (ex : List (String × GVal)) : List String :=
  pkeys.filter (· ∈ ex.map Prod.fst)

/-- `parse_expression(ex::NamedTuple; expression_spec, parameters)`,
`src/TemplateExpression.jl:1346-1440`. Each inner string is parsed on its own by DE's
`parse_expression`, then all parsed trees are converted to `promote_type(map(eltype, ...)...)`
so the template constructor receives a uniform inner expression type. -/
def parseNT (fkeys pkeys : List String) (ex : List (String × GVal))
    (kwParams : Option (List (String × GVal))) : Jl Parsed :=
  if !namesOk fkeys pkeys ex then
    throw (.argumentError "Template guess names must be expression or parameter names")
  else if !exprsOk fkeys ex then
    throw (.argumentError "Template guesses must provide every expression")
  else if !((flatKeys pkeys ex).isEmpty || kwParams.isNone) then
    throw (.argumentError "Template parameters must be supplied either flat or by keyword, not both")
  else do
    let params ← paramsOf (if (flatKeys pkeys ex).isEmpty then kwParams
      else some ((flatKeys pkeys ex).filterMap fun k => (ex.lookup k).map (k, ·)))
    let types ← fkeys.mapM (typeOf ex)
    let promoted := types.map fun _ => commonFTy types
    if sameType promoted then pure ⟨promoted, params⟩
    else throw (.methodError "no method matching TemplateExpression(::NamedTuple{...})")

/-- Guess validation: names outside the expression and parameter keys, a missing expression,
and parameters given both flat and by keyword are rejected; without flat or keyword
parameters a successful parse has no parameters. -/
def parseChecks : Prop :=
  ∀ (fkeys pkeys : List String) (ex : List (String × GVal)) kw (p : Parsed),
    (namesOk fkeys pkeys ex = false →
      parseNT fkeys pkeys ex kw = .error (.argumentError "Template guess names must be expression or parameter names")) ∧
    (namesOk fkeys pkeys ex = true → exprsOk fkeys ex = false →
      parseNT fkeys pkeys ex kw = .error (.argumentError "Template guesses must provide every expression")) ∧
    (namesOk fkeys pkeys ex = true → exprsOk fkeys ex = true → flatKeys pkeys ex ≠ [] → kw.isSome →
      parseNT fkeys pkeys ex kw =
        .error (.argumentError "Template parameters must be supplied either flat or by keyword, not both")) ∧
    (parseNT fkeys pkeys ex kw = .ok p → flatKeys pkeys ex = [] → kw = none → p.params = none)

theorem parseChecks_holds : parseChecks := by
  intro fkeys pkeys ex kw p
  refine ⟨fun h => by simp [parseNT, h]; rfl, fun h1 h2 => by simp [parseNT, h1, h2]; rfl,
    fun h1 h2 h3 h4 => ?_, fun h hf hk => ?_⟩
  · have he : (flatKeys pkeys ex).isEmpty = false := by
      cases hl : flatKeys pkeys ex with
      | nil => exact absurd hl h3
      | cons _ _ => rfl
    have hk : kw.isNone = false := by cases kw <;> simp_all
    simp only [parseNT, h1, h2, he, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.or_false,
      Bool.not_false]
    rfl
  · subst hk
    unfold parseNT at h
    simp only [hf, List.isEmpty_nil, Option.isNone_none, Bool.or_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, paramsOf, pureOk, okBind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases ht : fkeys.mapM (typeOf ex) with
        | error e => rw [ht] at h; cases h
        | ok ts =>
          rw [ht] at h
          simp only [okBind] at h
          split at h
          · cases h; rfl
          · cases h

private theorem sameType_map_const (ts : List FTy) (c : FTy) :
    sameType (ts.map fun _ => c) = true := by
  cases ts with
  | nil => rfl
  | cons _ rest => simp [sameType]

private theorem lookup_mem_of_mem_map_fst (ex : List (String × GVal)) (k : String)
    (h : k ∈ ex.map Prod.fst) : ∃ v, ex.lookup k = some v ∧ (k, v) ∈ ex := by
  induction ex with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk; exact ⟨b, by simp [List.lookup], by simp⟩
    · simp only [List.map_cons, List.mem_cons, hk, false_or] at h
      obtain ⟨v, hl, hm⟩ := ih h
      have hne : (k == a) = false := by simp [hk]
      exact ⟨v, by simp [List.lookup, hne, hl], List.mem_cons_of_mem _ hm⟩

private theorem mapM_typeOf_ok (ex : List (String × GVal))
    (hstr : ∀ q ∈ ex, ∃ m l, q.2 = .str m l) :
    ∀ ks : List String, (∀ k ∈ ks, k ∈ ex.map Prod.fst) →
      ∃ ts, ks.mapM (typeOf ex) = .ok ts
  | [], _ => ⟨[], rfl⟩
  | k :: ks, hmem => by
    obtain ⟨v, hlook, hq⟩ := lookup_mem_of_mem_map_fst ex k (hmem k List.mem_cons_self)
    obtain ⟨m, l, hv⟩ := hstr (k, v) hq
    simp only at hv
    have htk : typeOf ex k = .ok (l.getD .f32) := by simp [typeOf, hlook, hv]
    obtain ⟨ts, hts⟩ := mapM_typeOf_ok ex hstr ks (fun k' hk' => hmem k' (List.mem_cons_of_mem _ hk'))
    exact ⟨l.getD .f32 :: ts, by simp [List.mapM_cons, htk, hts]⟩

/-- `parse_expression` accepts every guess that supplies one expression string per
expression key and the parameters by keyword. -/
def parseAccepts : Prop :=
  ∀ (fkeys : List String) (ex : List (String × GVal)),
    ex.map Prod.fst = fkeys → (∀ q ∈ ex, ∃ m l, q.2 = .str m l) →
    ∃ p, parseNT fkeys [] ex none = .ok p

theorem parseAccepts_holds : parseAccepts := by
  intro fkeys ex hkeys hstr
  have hnames : namesOk fkeys [] ex = true := by
    simp [namesOk, hkeys]
  have hexprs : exprsOk fkeys ex = true := by
    simp [exprsOk, hkeys]
  have hflat : flatKeys [] ex = [] := rfl
  obtain ⟨ts, hts⟩ := mapM_typeOf_ok ex hstr fkeys (fun k hk => by rw [hkeys]; exact hk)
  refine ⟨⟨ts.map fun _ => commonFTy ts, none⟩, ?_⟩
  unfold parseNT
  simp only [hnames, hexprs, hflat, List.isEmpty_nil, Option.isNone_none, Bool.or_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, paramsOf, pureOk, okBind, hts,
    sameType_map_const]

example : parseNT ["f", "g"] [] [("f", .str 1 (some .f64)), ("g", .str 2 none)] none =
    .ok ⟨[.f64, .f64], none⟩ := rfl

end SymReg.Templates
