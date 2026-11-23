import SymReg.Templates.TemplateMut
import DynExpr.NodeUtils.Preallocation
import SymReg.Templates.Constants

/-!
Template constant mutation, parameter initialisation, `allocate_container`/`copy_into!` and
printing, `src/TemplateExpression.jl:514-541,651-701,719-784,1069-1108`.
-/

namespace SymReg.Templates
open DynExpr DynExpr.Expressions

/-- `has_constants(::TemplateExpression)`, `src/TemplateExpression.jl:1069-1074`, on plain
inner trees. -/
def templateHasConstants {M : Type} (ex : TExpr M) : Bool :=
  ex.inners.any fun e => !(NodeUtils.getConstants e.tree).isEmpty

/-- `regular_constant_mutation`, `src/TemplateExpression.jl:1082`; `coin` is `rand(rng, Bool)`. -/
def regularBranch {M : Type} (ex : TExpr M) (coin : Bool) : Bool :=
  !ex.s.hasParams || (templateHasConstants ex && coin)

/-- The parameter branch, `src/TemplateExpression.jl:1088-1106`: key position `kIdx`, then
`rand(rng, 1:num_params)` (which throws on an empty range) and the sampled indices `idxs`
(without replacement); `mv j v` is `_mutate_value` at index `j`. Parameters are written in
place. -/
def mutateParams {M : Type} (ex : TExpr M) (kIdx : Nat) (idxs : List Nat) (mv : Nat → JF → JF) :
    Jl (TExpr M) := do
  let n ← match ex.s.numParams[kIdx]? with
    | some n => pure n
    | none => throw .boundsError
  if n < 1 then throw (.argumentError "collection must be non-empty")
  else pure { ex with params := ex.params.mapIdx fun i p =>
    if i = kIdx then p.mapIdx fun j v => if j ∈ idxs then mv j v else v else p }

/-- Constant mutation of a template takes the inner-constant branch whenever there are no
parameters, the parameter branch whenever there are parameters but no inner constants, and
the parameter branch keeps the structure, the inner expressions, every parameter length and
every entry outside the sampled key and indices. -/
def mutConst : Prop :=
  ∀ (M : Type) (ex : TExpr M) (coin : Bool) (kIdx : Nat) (idxs : List Nat) (mv : Nat → JF → JF) ex',
    (ex.s.hasParams = false → regularBranch ex coin = true) ∧
    (ex.s.hasParams = true → templateHasConstants ex = false → regularBranch ex coin = false) ∧
    (mutateParams ex kIdx idxs mv = .ok ex' →
      ex'.s = ex.s ∧ ex'.inners = ex.inners ∧
      ∀ i, (ex'.params[i]?).map List.length = (ex.params[i]?).map List.length ∧
        ∀ j, (i ≠ kIdx ∨ j ∉ idxs) → ex'.params[i]?.bind (·[j]?) = ex.params[i]?.bind (·[j]?))

theorem mutConst_holds : mutConst := by
  intro M ex coin kIdx idxs mv ex'
  refine ⟨fun h => by simp [regularBranch, h], fun h hc => by simp [regularBranch, h, hc], fun h => ?_⟩
  unfold mutateParams at h
  cases hn : ex.s.numParams[kIdx]? with
  | none => rw [hn] at h; cases h
  | some n =>
    rw [hn] at h
    simp only [pureOk, okBind] at h
    split at h
    · cases h
    · cases h
      refine ⟨rfl, rfl, fun i => ⟨?_, fun j hj => ?_⟩⟩
      · simp only [List.getElem?_mapIdx]
        cases ex.params[i]? with
        | none => rfl
        | some p => simp only [Option.map_some]; split <;> simp
      · simp only [List.getElem?_mapIdx]
        cases ex.params[i]? with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          split
          · rename_i hi
            simp only [List.getElem?_mapIdx]
            cases p[j]? with
            | none => rfl
            | some v =>
              simp only [Option.map_some]
              rw [if_neg (by rcases hj with h | h; exact absurd hi h; exact h)]
          · rfl

/-- Constant mutation should succeed on every template that the constructor accepts. -/
def mutConstTotal : Prop :=
  ∀ (M : Type) (ex : TExpr M) (kIdx : Nat) (idxs : List Nat) (mv : Nat → JF → JF),
    kIdx < ex.s.pkeys.length → ex.s.pkeys.length = ex.s.numParams.length →
    (∀ n ∈ ex.s.numParams, 0 ≤ n) → ∃ ex', mutateParams ex kIdx idxs mv = .ok ex'

/-- `num_parameters = (p=0,)`, which the structure and the constructor accept. -/
def exP0 : TExpr Unit := ⟨⟨["f"], ["p"], [1], [0]⟩, [⟨.feature 1, ()⟩], [[]]⟩

example : buildParams exP0.s none = .ok [[]] := by decide

theorem mutConstTotal_refuted : ¬ mutConstTotal := by
  intro h
  obtain ⟨ex', hx⟩ := h Unit exP0 0 [] (fun _ v => v) (by decide) rfl (by decide)
  simp [mutateParams, exP0] at hx

/-- The result of a `parameter_initializer` call. -/
inductive InitOut where
  | nt (kv : List (String × PArg))
  | other

/-- One initialised parameter, `src/TemplateExpression.jl:686-698`. -/
def initEntry (kv : List (String × PArg)) (p : String × Int) : Jl (String × List JF) :=
  match field kv p.1 with
  | .error e => .error e
  | .ok .other => .error (.argumentError s!"`parameter_initializer` must return an `AbstractVector` for parameter `{p.1}`")
  | .ok (.vec xs) =>
    if (xs.length : Int) = p.2 then .ok (p.1, xs)
    else .error (.errorException s!"DimensionMismatch: wrong number of values for parameter `{p.1}`")

/-- `_initialize_template_parameters` with a user initializer, `src/TemplateExpression.jl:664-701`. -/
def initWith (np : List (String × Int)) : InitOut → Jl (List (String × List JF))
  | .other => throw (.argumentError "`parameter_initializer` must return a `NamedTuple`")
  | .nt kv =>
    if setEq (kv.map Prod.fst) (np.map Prod.fst) then np.mapM (initEntry kv)
    else throw (.argumentError "`parameter_initializer` returned keys that differ from `num_parameters`")

/-- The initializer's vector for key `k`. -/
def initVec (kv : List (String × PArg)) (k : String) : List JF :=
  match kv.lookup k with
  | some (.vec xs) => xs
  | _ => []

theorem mapM_ok_each {α β : Type} (f : α → Jl β) :
    ∀ (l : List α) (ys : List β), l.mapM f = .ok ys → ∀ a ∈ l, ∃ b, f a = .ok b
  | [], _, _, a, ha => by cases ha
  | a :: l, ys, h, a', ha' => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      cases hl : l.mapM f with
      | error e => rw [ha, hl] at h; cases h
      | ok bs =>
        rcases List.mem_cons.mp ha' with rfl | ha'
        · exact ⟨b, ha⟩
        · exact mapM_ok_each f l bs hl a' ha'

/-- A user initializer must return a NamedTuple of vectors whose key set is that of
`num_parameters`; the result follows `num_parameters` order whatever the initializer's key
order, takes each vector by key, and every vector has its declared length. -/
def initOrder : Prop :=
  ∀ (np : List (String × Int)) (out : InitOut) (ps : List (String × List JF)),
    (out = .other → ∃ msg, initWith np out = .error (.argumentError msg)) ∧
    (∀ kv, out = .nt kv → setEq (kv.map Prod.fst) (np.map Prod.fst) = false →
      ∃ msg, initWith np out = .error (.argumentError msg)) ∧
    (∀ kv, out = .nt kv → initWith np out = .ok ps →
      ps = np.map (fun p => (p.1, initVec kv p.1)) ∧ ∀ p ∈ np, ((initVec kv p.1).length : Int) = p.2)

theorem initEntry_ok (kv : List (String × PArg)) (p : String × Int) (b : String × List JF)
    (hb : initEntry kv p = .ok b) : b = (p.1, initVec kv p.1) ∧ ((initVec kv p.1).length : Int) = p.2 := by
  unfold initEntry field at hb
  unfold initVec
  cases hl : kv.lookup p.1 with
  | none => rw [hl] at hb; cases hb
  | some a =>
    rw [hl] at hb
    cases a with
    | other => cases hb
    | vec xs =>
      simp only at hb
      split at hb
      · cases hb; exact ⟨rfl, by assumption⟩
      · cases hb

theorem initOrder_holds : initOrder := by
  intro np out ps
  refine ⟨fun h => ⟨_, by rw [h]; rfl⟩, fun kv h hs => ⟨_, by rw [h]; simp only [initWith, hs]; rfl⟩,
    fun kv h hok => ?_⟩
  subst h
  simp only [initWith] at hok
  split at hok
  · refine ⟨mapM_ok_map _ _ np ps (fun p _ b hb => (initEntry_ok kv p b hb).1) hok, fun p hp => ?_⟩
    obtain ⟨b, hb⟩ := mapM_ok_each _ np ps hok p hp
    exact (initEntry_ok kv p b hb).2
  · cases hok

structure TemplateCopyContents (T M : Type) where
  trees : List (String × (Addr × M))
  parameters : List (String × Nat)

structure TemplateCopyStore (T : Type) where
  nodes : Graph T
  arrays : Nat → Option (List T)

structure TemplateCopyContainer where
  trees : List (List Addr)
  parameters : List (String × Nat)

private def copyInnerSlots {T M : Type} (fuel : Nat) (source : Graph T) :
    List (List Addr) → List (String × (Addr × M)) → Graph T →
    Res (Graph T) (List (String × (Addr × M)))
  | [], [], nodes => .ok [] nodes
  | slots :: rest, (key, root, info) :: trees, nodes =>
    match NodeUtils.copyInto source false slots nodes fuel root with
    | .error err => .err err nodes
    | .ok (copied, nodes', _, _) =>
      match copyInnerSlots fuel source rest trees nodes' with
      | .ok roots nodes'' => .ok ((key, copied, info) :: roots) nodes''
      | .err err nodes'' => .err err nodes''
  | _, _, nodes => .err (.argumentError "tuple lengths must match") nodes

private def copyParameterSlots {T : Type} (source : Nat → Option (List T))
    (dest : List (String × Nat)) :
    List (String × Nat) → (Nat → Option (List T)) →
    Res (Nat → Option (List T)) Unit
  | [], arrays => .ok () arrays
  | (key, sourceAddr) :: rest, arrays =>
    match dest.lookup key with
    | none => .err (.errorException s!"no field {key}") arrays
    | some addr =>
      match source sourceAddr, arrays addr with
      | some values, some old =>
        if old.length = values.length then
          copyParameterSlots source dest rest
            (fun a => if a = addr then some values else arrays a)
        else .err (.userError "DimensionMismatch") arrays
      | _, _ => .err .undefRefError arrays

-- Source: src/TemplateExpression.jl:530-541
/-
function DE.copy_into!(dest::PreallocatedTemplateExpression, src::TemplateExpression)
    ts = get_contents(src)
    parameters = get_metadata(src).parameters
    new_contents = NamedTuple{keys(ts)}(map(DE.copy_into!, values(dest.trees), values(ts)))
    for k in keys(parameters)
        dest.parameters[k][:] = (parameters[k]::ParamVector)[:]
    end
    new_parameters = NamedTuple{keys(parameters)}(
        map(p -> ParamVector(p), values(dest.parameters))
    )
    return with_metadata(with_contents(src, new_contents); parameters=new_parameters)
end
-/
def copyInto {T M : Type} (fuel : Nat) (dest : TemplateCopyContainer)
    (src : TemplateCopyContents T M) (source out : TemplateCopyStore T) :
    Res (TemplateCopyStore T) (TemplateCopyContents T M) :=
  match copyInnerSlots fuel source.nodes dest.trees src.trees out.nodes with
  | .err err nodes => .err err {out with nodes}
  | .ok trees nodes =>
    match copyParameterSlots source.arrays dest.parameters src.parameters out.arrays with
    | .err err arrays => .err err ⟨nodes, arrays⟩
    | .ok () arrays =>
      if dest.parameters.length = src.parameters.length then
        .ok ⟨trees, (src.parameters.map Prod.fst).zip (dest.parameters.map Prod.snd)⟩
          ⟨nodes, arrays⟩
      else .err (.argumentError "tuple lengths must match") ⟨nodes, arrays⟩

private def copiedNodeCount {T : Type} : Tree T → Nat
  | .const _ | .feature _ => 1
  | .branch _ children => 1 + (children.map copiedNodeCount).sum

def copyIntoRoundtrip : Prop :=
  ∀ (T M : Type) fuel (dest : TemplateCopyContainer) (src : TemplateCopyContents T M)
    (source initial : TemplateCopyStore T) (views : List (Tree T)),
    src.trees.mapM (fun e => source.nodes.unfold fuel e.2.1) = some views →
    dest.trees.length = views.length →
    (∀ p ∈ dest.trees.zip views, copiedNodeCount p.2 ≤ p.1.length) →
    dest.trees.flatten.Nodup →
    (∀ a ∈ dest.trees.flatten, ∃ c, initial.nodes.cells a = some c) →
    dest.parameters.map Prod.fst = src.parameters.map Prod.fst →
    (dest.parameters.map Prod.snd).Nodup →
    (∀ p ∈ src.parameters.zip dest.parameters,
      ∃ xs ys, source.arrays p.1.2 = some xs ∧ initial.arrays p.2.2 = some ys ∧
        xs.length = ys.length) →
    ∃ result out, copyInto fuel dest src source initial = .ok result out ∧
      result.trees.mapM (fun e => out.nodes.unfold fuel e.2.1) = some views ∧
      result.parameters = dest.parameters ∧
      (∀ p ∈ result.trees.zip dest.trees, p.1.2.1 ∈ p.2) ∧
      (∀ p ∈ src.parameters.zip dest.parameters, out.arrays p.2.2 = source.arrays p.1.2) ∧
      (∀ a, a ∉ dest.trees.flatten → out.nodes.cells a = initial.nodes.cells a) ∧
      (∀ a, a ∉ dest.parameters.map Prod.snd → out.arrays a = initial.arrays a)

/-- `_colors(Val(n))`, `src/TemplateExpression.jl:719-723`. -/
def colors (n : Nat) : List String :=
  (List.range n).map fun i => ["magenta", "green", "red", "blue", "yellow", "cyan"][i % 6]!

/-- The components of `string_tree(::TemplateExpression)` with `pretty = false`: every inner
expression (rendered with `#i` variable names) then every parameter vector, under its key. -/
def tmplParts {M : Type} (render : Expression JF M → String) (renderP : List JF → String)
    (ex : TExpr M) : List (String × String) :=
  ex.s.keys.zip (ex.inners.map render) ++
    (if ex.s.hasParams then ex.s.pkeys.zip (ex.params.map renderP) else [])

/-- `string_tree(::TemplateExpression)`, `src/TemplateExpression.jl:726-784`: the components
joined by `"; "`, coloured cyclically. -/
def stringTree {M : Type} (render : Expression JF M → String) (renderP : List JF → String)
    (ex : TExpr M) : String :=
  "; ".intercalate ((tmplParts render renderP ex).map fun p => p.1 ++ " = " ++ p.2)

/-- The printed template lists the keys then the parameter keys, in order, each with its
rendering, and the component colours repeat with period six. -/
def stringParts : Prop :=
  ∀ (M : Type) (render : Expression JF M → String) (renderP : List JF → String) (ex : TExpr M),
    ex.s.keys.length = ex.inners.length → ex.s.pkeys.length = ex.params.length →
    (tmplParts render renderP ex).map Prod.fst = ex.s.keys ++ (if ex.s.hasParams then ex.s.pkeys else []) ∧
    ∀ n i, i + 6 < n → (colors n)[i]? = (colors n)[i + 6]?

theorem stringParts_holds : stringParts := by
  intro M render renderP ex hk hp
  refine ⟨?_, fun n i hi => ?_⟩
  · unfold tmplParts
    rw [List.map_append, List.map_fst_zip (by simp [hk])]
    split
    · rw [List.map_fst_zip (by simp [hp])]
    · rfl
  · simp only [colors, List.getElem?_map, List.getElem?_range (by omega : i < n),
      List.getElem?_range hi, Option.map_some]
    rw [show (i + 6) % 6 = i % 6 by omega]

example : stringTree (M := Unit) (fun _ => "#1") (fun _ => "[5.0, 7.0]")
    ⟨⟨["f", "g"], ["p"], [1, 1], [2]⟩, [⟨.feature 1, ()⟩, ⟨.feature 1, ()⟩], [[.fin 5, .fin 7]]⟩ =
    "f = #1; g = #1; p = [5.0, 7.0]" := by decide

end SymReg.Templates
