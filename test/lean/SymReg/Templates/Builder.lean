import SymReg.Templates.TemplateInit

/-!
`create_expression`, `init_params`, `embed_metadata` and `strip_metadata`
(`src/ExpressionBuilder.jl`), the default expression specs (`src/ExpressionSpec.jl`,
`src/TemplateExpression.jl:1174-1258`), the template builder hooks
(`src/TemplateExpression.jl:569-649,703-705`) and composable construction
(`src/ComposableExpression.jl:64-150`, `src/TemplateExpression.jl:835-851`).
Metadata is a NamedTuple of metadata values; `ref n` is a mutable object with identity `n`.
SR defines no `ParametricExpression` methods: a DE `ParametricExpression` goes through the
generic `AbstractExpression` builder, with its parameter matrix among the expression options.
-/

namespace SymReg.Templates
open DynExpr

/-- A metadata value. -/
inductive MV where
  | nothing
  | ops (n : Nat)
  | names (xs : List String)
  | ref (n : Nat)
  | val (n : Nat)
  deriving DecidableEq, Repr

/-- A NamedTuple of metadata values. -/
abbrev NT := List (String × MV)

/-- The positions of `a` in `(; a..., b...)`, with `b`'s values where `b` has the key. -/
def ntOver (b a : NT) : NT := a.map fun p => (p.1, (b.lookup p.1).getD p.2)

/-- The new keys of `b` in `(; a..., b...)`, in order. -/
def ntNew (a b : NT) : NT := b.filter fun p => !(a.map Prod.fst).contains p.1

/-- `(; a..., b...)`. -/
def ntMerge (a b : NT) : NT := ntOver b a ++ ntNew a b

/-- The options fields the builder reads. -/
structure BOpts where
  ops : MV
  eo : NT
  exprType : Nat

/-- An expression as the generic builder sees it: tree, metadata and concrete type. -/
structure BEx where
  tree : Tree JF
  md : NT
  ty : Nat

/-- `init_params` with the generic `extra_init_params` and `sort_params`,
`src/ExpressionBuilder.jl:65-91`. -/
def initParamsB (o : BOpts) (names : MV) (embed : Bool) : NT :=
  ntMerge [("operators", if embed then o.ops else .nothing),
    ("variable_names", if embed then names else .nothing)] o.eo

/-- `create_expression(t, options, dataset, N, E, Val(embed))`,
`src/ExpressionBuilder.jl:46-64`, on a node. -/
def createB (o : BOpts) (names : MV) (t : Tree JF) (embed : Bool) : BEx :=
  ⟨t, initParamsB o names embed, o.exprType⟩

/-- The argument of `create_expression`. -/
inductive CArg where
  | value (v : JF)
  | node (t : Tree JF)
  | expr (e : BEx)

/-- The dispatch of `create_expression`, `src/ExpressionBuilder.jl:20-64`: a value is first
wrapped in a constant node; an expression is returned as is under a type assertion. -/
def createAny (o : BOpts) (names : MV) (embed : Bool) : CArg → Jl BEx
  | .value v => pure (createB o names (.const v) embed)
  | .node t => pure (createB o names t embed)
  | .expr e => if e.ty = o.exprType then pure e else throw (.errorException "TypeError: in typeassert")

/-- `consistency_checks` then `with_metadata(ex; init_params(...)...)`,
`src/ExpressionBuilder.jl:95-109,151-155`. -/
def withInitB (o : BOpts) (names : MV) (embed : Bool) (ex : BEx) : Jl BEx :=
  if ex.ty = o.exprType then pure ⟨ex.tree, ntMerge ex.md (initParamsB o names embed), ex.ty⟩
  else throw (.assertionError "Need prototype to be of type options.expression_type")

/-- `embed_metadata(ex, options, dataset)`. -/
def embedB (o : BOpts) (names : MV) := withInitB o names true
/-- `strip_metadata(ex, options, dataset)`. -/
def stripB (o : BOpts) (names : MV) := withInitB o names false

theorem lookup_none_iff {β : Type} (k : String) : ∀ l : List (String × β),
    l.lookup k = none ↔ k ∉ l.map Prod.fst
  | [] => by simp [List.lookup]
  | (a, b) :: l => by
    by_cases h : k = a
    · subst h; simp [List.lookup]
    · have : (k == a) = false := by simp [h]
      simp [List.lookup, this, lookup_none_iff k l, h]

theorem lookup_cons_ne {β : Type} {k a : String} (b : β) (l : List (String × β)) (h : k ≠ a) :
    ((a, b) :: l).lookup k = l.lookup k := by
  have : (k == a) = false := by simp [h]
  simp [List.lookup, this]

theorem ntMerge_keys (a b : NT) :
    (ntMerge a b).map Prod.fst = a.map Prod.fst ++ (ntNew a b).map Prod.fst := by
  simp [ntMerge, ntOver, Function.comp_def]

/-- Overriding `p`'s entries absent from `m` with `q` gives `q`'s entries absent from `m`, when
`p` and `q` have the same distinct keys. -/
theorem filter_override (m : List String) : ∀ (p q : NT),
    p.map Prod.fst = q.map Prod.fst → (q.map Prod.fst).Nodup →
    ntOver q (p.filter fun e => !m.contains e.1) = q.filter fun e => !m.contains e.1
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (k, a) :: p, (k', b) :: q, h, hnd => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have hnd' : k ∉ q.map Prod.fst ∧ (q.map Prod.fst).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have ih := filter_override m p q h hnd'.2
    have hcongr : ntOver ((k, b) :: q) (p.filter fun e => !m.contains e.1) =
        ntOver q (p.filter fun e => !m.contains e.1) := by
      apply List.map_congr_left
      intro e he
      have hk : e.1 ∈ q.map Prod.fst := h ▸ List.mem_map_of_mem (List.mem_filter.mp he).1
      rw [lookup_cons_ne b q (fun h' => hnd'.1 (by rw [<- h']; exact hk))]
    by_cases hm : m.contains k = true
    · have hf : (!m.contains k) = false := by rw [hm]; rfl
      rw [List.filter_cons_of_neg (by rw [hf]; decide), List.filter_cons_of_neg (by rw [hf]; decide),
        hcongr, ih]
    · have ht : (!m.contains k) = true := by rw [Bool.eq_false_iff.mpr hm]; rfl
      rw [List.filter_cons_of_pos (p := fun e : String × MV => !m.contains e.1) (a := (k, a)) ht,
        List.filter_cons_of_pos (p := fun e : String × MV => !m.contains e.1) (a := (k, b)) ht]
      simp only [ntOver, List.map_cons] at hcongr ih ⊢
      rw [hcongr, ih]
      simp [List.lookup]

/-- Merging the same distinct key set twice keeps only the second values. -/
theorem ntMerge_twice (m p q : NT) (h : p.map Prod.fst = q.map Prod.fst) (hnd : (q.map Prod.fst).Nodup) :
    ntMerge (ntMerge m p) q = ntMerge m q := by
  have hiff : ∀ k, p.lookup k = none ↔ q.lookup k = none := fun k => by
    rw [lookup_none_iff, lookup_none_iff, h]
  have h1 : ntOver q (ntOver p m) = ntOver q m := by
    simp only [ntOver, List.map_map]
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_apply]
    cases hq : q.lookup e.1 with
    | none => rw [(hiff e.1).mpr hq]; rfl
    | some v => rfl
  have h2 := filter_override (m.map Prod.fst) p q h hnd
  have h3 : ntNew (ntMerge m p) q = [] := by
    unfold ntNew
    rw [List.filter_eq_nil_iff]
    intro e he
    have hk : e.1 ∈ p.map Prod.fst := h ▸ List.mem_map_of_mem he
    obtain ⟨e', he', hee⟩ := List.mem_map.mp hk
    have hmem : e.1 ∈ (ntMerge m p).map Prod.fst := by
      rw [ntMerge_keys, List.mem_append]
      by_cases hm : e.1 ∈ m.map Prod.fst
      · exact Or.inl hm
      · refine Or.inr (List.mem_map.mpr ⟨e', List.mem_filter.mpr ⟨he', ?_⟩, hee⟩)
        rw [hee]; simpa using hm
    simp [hmem]
  show ntOver q (ntMerge m p) ++ ntNew (ntMerge m p) q = ntOver q m ++ ntNew m q
  rw [h3, List.append_nil, ntMerge]
  simp only [ntOver, List.map_append] at h1 h2 ⊢
  rw [h1]
  unfold ntNew
  rw [h2]

/-- Merging into a NamedTuple with the same distinct keys gives the new NamedTuple. -/
theorem ntMerge_same (m q : NT) (h : m.map Prod.fst = q.map Prod.fst) (hnd : (q.map Prod.fst).Nodup) :
    ntMerge m q = q := by
  have hq : ntNew m q = [] := by
    unfold ntNew
    rw [List.filter_eq_nil_iff]; intro e he; rw [h]; simpa using List.mem_map_of_mem (f := Prod.fst) he
  have hm := filter_override [] m q h hnd
  simp only [List.contains_nil, Bool.not_false] at hm
  rw [List.filter_eq_self.mpr (fun _ _ => rfl), List.filter_eq_self.mpr (fun _ _ => rfl)] at hm
  unfold ntMerge
  rw [hq, List.append_nil, hm]

theorem initParams_keys (o : BOpts) (names : MV) (e e' : Bool) :
    (initParamsB o names e).map Prod.fst = (initParamsB o names e').map Prod.fst := by
  simp [initParamsB, ntMerge_keys, ntNew]

theorem initParams_nodup (o : BOpts) (names : MV) (e : Bool) (hnd : (o.eo.map Prod.fst).Nodup) :
    ((initParamsB o names e).map Prod.fst).Nodup := by
  rw [initParamsB, ntMerge_keys]
  have hsub : ((ntNew [("operators", if e then o.ops else .nothing),
      ("variable_names", if e then names else .nothing)] o.eo).map Prod.fst).Nodup :=
    ((List.filter_sublist).map Prod.fst).nodup hnd
  have hnot : ∀ k ∈ (ntNew [("operators", if e then o.ops else .nothing),
      ("variable_names", if e then names else .nothing)] o.eo).map Prod.fst,
      k ≠ "operators" ∧ k ≠ "variable_names" := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    have := (List.mem_filter.mp hp).2
    simp at this
    exact ⟨fun h => this.1 h, fun h => this.2 h⟩
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨fun h => (hnot _ h).2 rfl, hsub⟩⟩
  intro h
  rcases List.mem_cons.mp h with h | h
  · exact absurd h (by decide)
  · exact (hnot _ h).1 rfl

/-- Embedding and stripping metadata are idempotent and each undoes the other: for any
expression of the options' type, strip(embed(ex)) = strip(ex), embed(strip(ex)) = embed(ex) and
embed(embed(ex)) = embed(ex); and embedding a non-embedded `create_expression` result equals
creating with embedded metadata. -/
def embedStrip : Prop :=
  ∀ (o : BOpts) (names : MV) (ex : BEx) (t : Tree JF), (o.eo.map Prod.fst).Nodup → ex.ty = o.exprType →
    (embedB o names ex >>= stripB o names) = stripB o names ex ∧
    (stripB o names ex >>= embedB o names) = embedB o names ex ∧
    (embedB o names ex >>= embedB o names) = embedB o names ex ∧
    ∃ e, embedB o names (createB o names t false) = .ok e ∧ e.tree = t ∧
      e.md = (createB o names t true).md ∧ e.ty = o.exprType

theorem embedStrip_holds : embedStrip := by
  intro o names ex t hnd hty
  have tw : ∀ e e', ntMerge (ntMerge ex.md (initParamsB o names e)) (initParamsB o names e') =
      ntMerge ex.md (initParamsB o names e') := fun e e' =>
    ntMerge_twice _ _ _ (initParams_keys o names e e') (initParams_nodup o names e' hnd)
  refine ⟨?_, ?_, ?_, ⟨⟨t, ntMerge (initParamsB o names false) (initParamsB o names true), o.exprType⟩,
    by show (if o.exprType = o.exprType then _ else _) = _; rw [if_pos rfl]; rfl, rfl, ?_, rfl⟩⟩
  · simp only [embedB, stripB, withInitB, hty, ↓reduceIte, pureOk, okBind]; rw [tw]
  · simp only [embedB, stripB, withInitB, hty, ↓reduceIte, pureOk, okBind]; rw [tw]
  · simp only [embedB, withInitB, hty, ↓reduceIte, pureOk, okBind]; rw [tw]
  · exact ntMerge_same _ _ (initParams_keys o names false true) (initParams_nodup o names true hnd)

/-- `create_expression` dispatch: a value becomes a constant node, a node is wrapped with
`init_params`, and an expression of the options' type is returned unchanged (any other type
fails the type assertion); with the default `ExpressionSpec` (no expression options) the
metadata is `(operators=nothing, variable_names=nothing)`, or the options' operators and the
dataset's names when embedded. -/
def createDispatch : Prop :=
  ∀ (o : BOpts) (names : MV) (embed : Bool) (v : JF) (e : BEx),
    (createAny o names embed (.value v)).map BEx.tree = (createAny o names embed (.node (.const v))).map BEx.tree ∧
    (e.ty = o.exprType → ∃ e', createAny o names embed (.expr e) = .ok e' ∧ e'.tree = e.tree ∧ e'.md = e.md) ∧
    (e.ty ≠ o.exprType → ∃ msg, createAny o names embed (.expr e) = .error (.errorException msg)) ∧
    (o.eo = [] → (createB o names (.const v) embed).md =
      [("operators", if embed then o.ops else .nothing), ("variable_names", if embed then names else .nothing)])

theorem createDispatch_holds : createDispatch := by
  intro o names embed v e
  refine ⟨rfl, fun h => ⟨e, by simp [createAny, h], rfl, rfl⟩,
    fun h => ⟨"TypeError: in typeassert", by simp [createAny, h]; rfl⟩,
    fun h => by simp [createB, initParamsB, ntMerge, ntOver, ntNew, h]⟩

/-- Expressions created from the same options should not share a mutable metadata object. -/
def createIndependent : Prop :=
  ∀ (o : BOpts) (names : MV) (t1 t2 : Tree JF) (embed : Bool) (n : Nat),
    MV.ref n ∈ (createB o names t1 embed).md.map Prod.snd →
    MV.ref n ∉ (createB o names t2 embed).md.map Prod.snd

/-- `expression_options = (; parameters=P, parameter_names=["p"])` for a DE
`ParametricExpression`, the only way that type receives its parameter matrix. -/
def parametricOpts : BOpts := ⟨.ops 0, [("parameters", .ref 0), ("parameter_names", .names ["p"])], 1⟩

theorem createIndependent_refuted : ¬ createIndependent := by
  intro h
  exact h parametricOpts .nothing (.const (.fin 1)) (.const (.fin 2)) false 0 (by decide) (by decide)

/-! ## Population members, populations and halls of fame -/

/-- The member fields the builder touches. -/
structure BMember where
  tree : BEx
  cost : Int
  loss : Int
  ref : Nat
  parent : Nat
  birth : Nat

/-- `embed_metadata(member)`, `src/ExpressionBuilder.jl:110-122`: `create_child` with a fresh
reference `fresh`, the member's reference as parent and a new birth. -/
def embedMember (o : BOpts) (names : MV) (fresh birth : Nat) (m : BMember) : Jl BMember := do
  let t ← embedB o names m.tree
  pure ⟨t, m.cost, m.loss, fresh, m.ref, birth⟩

/-- `strip_metadata(member::PopMember)`, `src/ExpressionBuilder.jl:156-168`: same reference and
parent, a new birth. -/
def stripMember (o : BOpts) (names : MV) (birth : Nat) (m : BMember) : Jl BMember := do
  let t ← stripB o names m.tree
  pure ⟨t, m.cost, m.loss, m.ref, m.parent, birth⟩

/-- `embed_metadata`/`strip_metadata` on a `Population`, a `HallOfFame` (members, with the
`exists` flags kept) or a vector of them, `src/ExpressionBuilder.jl:123-141,169-180`; `f` is the
member-level function, given each member's position for its fresh values. -/
def mapMembers (f : Nat → BMember → Jl BMember) (ms : List BMember) : Jl (List BMember) :=
  (ms.zipIdx.map fun p => (p.2, p.1)).mapM fun p => f p.1 p.2

theorem mapM_length {α β : Type} (f : α → Jl β) :
    ∀ (l : List α) (ys : List β), l.mapM f = .ok ys → ys.length = l.length
  | [], ys, h => by cases h; rfl
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      cases hl : l.mapM f with
      | error e => rw [ha, hl] at h; cases h
      | ok bs => rw [ha, hl] at h; cases h; simp [mapM_length f l bs hl]

/-- Member metadata round trip: stripping an embedded member gives the stripped expression
with the same cost and loss, under the fresh reference of the embedding, whose parent is the
original member; collection maps keep the number of members. -/
def memberRoundtrip : Prop :=
  ∀ (o : BOpts) (names : MV) (fresh b1 b2 : Nat) (m : BMember),
    (o.eo.map Prod.fst).Nodup → m.tree.ty = o.exprType →
    (∃ t m', stripB o names m.tree = .ok t ∧
      (embedMember o names fresh b1 m >>= stripMember o names b2) = .ok m' ∧
      m'.tree.md = t.md ∧ m'.tree.tree = t.tree ∧ m'.cost = m.cost ∧ m'.loss = m.loss ∧
      m'.ref = fresh ∧ m'.parent = m.ref) ∧
    ∀ (f : Nat → BMember → Jl BMember) ms ys, mapMembers f ms = .ok ys → ys.length = ms.length

theorem memberRoundtrip_holds : memberRoundtrip := by
  intro o names fresh b1 b2 m hnd hty
  refine ⟨⟨⟨m.tree.tree, ntMerge m.tree.md (initParamsB o names false), m.tree.ty⟩,
    ⟨⟨m.tree.tree, ntMerge (ntMerge m.tree.md (initParamsB o names true)) (initParamsB o names false),
      m.tree.ty⟩, m.cost, m.loss, fresh, m.ref, b2⟩,
    by simp only [stripB, withInitB, if_pos hty]; rfl,
    by simp only [embedMember, stripMember, embedB, stripB, withInitB, if_pos hty, pureOk, okBind],
    ?_, rfl, rfl, rfl, rfl, rfl⟩,
    fun f ms ys h => by simpa [mapMembers] using mapM_length _ _ ys h⟩
  exact ntMerge_twice _ _ _ (initParams_keys o names true false) (initParams_nodup o names false hnd)

/-! ## Template builder hooks -/

/-- A template as built: inner trees and inner metadata in key order, and its metadata. -/
structure TB where
  trees : List (Tree JF)
  inners : List NT
  md : NT

/-- `sort_params(::Type{<:TemplateExpression})`, `src/TemplateExpression.jl:703-705`. -/
def sortT (raw : NT) : NT :=
  ["structure", "operators", "variable_names", "parameters"].map fun k => (k, (raw.lookup k).getD .nothing)

/-- The inner metadata built by `_build_inner_template_expressions`,
`src/TemplateExpression.jl:571-590,604-606`. -/
def innerMeta (o : BOpts) (names : MV) (embed : Bool) : NT :=
  [("operators", o.ops), ("variable_names", if embed then names else .nothing), ("eval_context", .val 0)]

/-- The template `init_params`, with `extra_init_params` `(; options.operators,
options.expression_options..., parameters)`, `src/TemplateExpression.jl:619,622-649`. -/
def tmplRaw (o : BOpts) (names : MV) (params : MV) (embed : Bool) : NT :=
  ntMerge [("operators", if embed then o.ops else .nothing), ("variable_names", if embed then names else .nothing)]
    (ntMerge (ntMerge [("operators", o.ops)] o.eo) [("parameters", params)])

/-- `create_expression` for templates, `src/TemplateExpression.jl:592-621`: one copy of `t` per
key; the keyword constructor (lines 346-397) takes `variable_names` from the first inner
expression when absent. -/
def tmplCreate (o : BOpts) (names : MV) (keys : List String) (t : Tree JF) (params : MV) (embed : Bool) : TB :=
  let m := sortT (tmplRaw o names params embed)
  let vn := match (m.lookup "variable_names").getD .nothing with
    | .nothing => ((innerMeta o names embed).lookup "variable_names").getD .nothing
    | v => v
  ⟨keys.map fun _ => t, keys.map fun _ => innerMeta o names embed,
    m.map fun p => if p.1 = "variable_names" then (p.1, vn) else p⟩

/-- `embed_metadata(::TemplateExpression)`: `with_metadata` on the template metadata only;
the prototype's parameters are copied (`_copy`, line 643). -/
def tmplEmbed (o : BOpts) (names : MV) (params : MV) (ex : TB) : TB :=
  ⟨ex.trees, ex.inners, ntMerge ex.md (sortT (tmplRaw o names params true))⟩

/-- `TemplateExpressionSpec` options. -/
def tmplOpts (ops st : MV) : BOpts :=
  ⟨ops, [("structure", st), ("inner_expression_type", .val 2), ("inner_expression_options", .val 3),
    ("parameter_initializer", .nothing)], 2⟩

/-- A template created by `create_expression` from template-spec options holds one copy of the
seed tree per key and the options' operators in the template and every inner expression whether
or not metadata is embedded; the template metadata is `(structure, operators, variable_names,
parameters)`, with the dataset's names exactly when embedded. -/
def tmplCreateShape : Prop :=
  ∀ (ops st names : MV) (keys : List String) (t : Tree JF) (params : MV) (embed : Bool),
    let ex := tmplCreate (tmplOpts ops st) names keys t params embed
    ex.trees = keys.map (fun _ => t) ∧
    (∀ m ∈ ex.inners, m.lookup "operators" = some ops ∧
      m.lookup "variable_names" = some (if embed then names else .nothing)) ∧
    ex.md = [("structure", st), ("operators", ops),
      ("variable_names", if embed then names else .nothing), ("parameters", params)]

theorem tmplCreateShape_holds : tmplCreateShape := by
  intro ops st names keys t params embed
  refine ⟨rfl, fun m hm => ?_, ?_⟩
  · simp only [tmplCreate, List.mem_map] at hm
    obtain ⟨_, _, rfl⟩ := hm
    cases embed <;> simp [innerMeta, tmplOpts, List.lookup]
  · cases embed <;> cases names <;>
      simp [tmplCreate, tmplRaw, tmplOpts, sortT, ntMerge, ntOver, ntNew, innerMeta, List.lookup]

/-- Embedding the metadata of a created template should give the template created with
embedded metadata. -/
def tmplEmbedCreate : Prop :=
  ∀ (o : BOpts) (names : MV) (keys : List String) (t : Tree JF) (params : MV),
    (tmplEmbed o names params (tmplCreate o names keys t params false)).inners =
      (tmplCreate o names keys t params true).inners

theorem tmplEmbedCreate_refuted : ¬ tmplEmbedCreate := by
  intro h
  have := h (tmplOpts (.ops 0) (.val 1)) (.names ["z"]) ["f"] (.const (.fin 1)) .nothing
  simp [tmplEmbed, tmplCreate, innerMeta] at this

/-! ## Expression specs -/

/-- The expression type a spec selects. -/
inductive ETy where
  | expression
  | template
  deriving DecidableEq, Repr

/-- What `get_expression_type`, `get_expression_options` and `get_node_type` return. -/
structure SpecInfo where
  ty : ETy
  options : NT
  nodeType : String

/-- `ExpressionSpec(; node_type=Node)`, `src/ExpressionSpec.jl:12-19`. -/
def exprSpec (nodeType : String := "Node") : SpecInfo := ⟨.expression, [], nodeType⟩

/-- `TemplateExpressionSpec(; structure, inner_expression_type=ComposableExpression,
inner_expression_options=(;), parameter_initializer=nothing)`, `src/TemplateExpression.jl:1192-1257`. -/
def tmplSpec (st : MV) (iet : MV := .val 0) (ieo : MV := .val 1) (pinit : MV := .nothing) : SpecInfo :=
  ⟨.template, [("structure", st), ("inner_expression_type", iet),
    ("inner_expression_options", ieo), ("parameter_initializer", pinit)], "Node"⟩

def specDefaults : Prop :=
  ∀ (nodeType : String) (st iet ieo pinit : MV),
    (exprSpec nodeType).ty = .expression ∧ (exprSpec nodeType).nodeType = nodeType ∧
    (exprSpec nodeType).options = [] ∧
    (tmplSpec st iet ieo pinit).ty = .template ∧ (tmplSpec st iet ieo pinit).nodeType = "Node" ∧
    (tmplSpec st iet ieo pinit).options =
      [("structure", st), ("inner_expression_type", iet),
       ("inner_expression_options", ieo), ("parameter_initializer", pinit)]

theorem specDefaults_holds : specDefaults := by
  intro nodeType st iet ieo pinit
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Composable construction and call-time buffers -/

/-- An `EvalContext`; `buffer` is the identity of an `ArrayBuffer`, if any. -/
structure ECtx where
  turbo : Bool
  bumper : Bool
  earlyExit : Bool
  buffer : Option Nat
  useFused : Bool

/-- The `eval_context` stored by the keyword `ComposableExpression` constructor,
`src/ComposableExpression.jl:64-83` (after `_process_eval_options`). -/
def composableCtx (kws : List String) (ctx : Option ECtx) : Jl (Option ECtx) :=
  if kws.all (· = "eval_options") then
    match ctx with
    | some c => if c.buffer.isSome then
        throw (.argumentError "ComposableExpression metadata cannot contain an evaluation buffer.")
      else pure (some c)
    | none => pure none
  else throw (.argumentError "Invalid keyword argument(s)")

/-- `_with_call_time_buffer` on one inner expression, `src/TemplateExpression.jl:835-851`;
`dflt` is `EvalContext()` (`get_eval_context`, `src/ComposableExpression.jl:180-182`). -/
def withCallBuffer (dflt : ECtx) (stored : Option ECtx) (call : Option ECtx) : Option ECtx :=
  match call with
  | none => stored
  | some c => match c.buffer with
    | none => stored
    | some b =>
      let s := stored.getD dflt
      if s.bumper then stored else some { s with buffer := some b }

/-- The constructor never stores an evaluation buffer and rejects unknown keywords; template
evaluation lends the call's buffer to every inner expression without Bumper, keeping its other
settings, and leaves inner expressions unchanged without a call buffer or with Bumper. -/
def composableBuffer : Prop :=
  ∀ (dflt : ECtx) (kws : List String) (ctx stored : Option ECtx) (call : ECtx) (b : Nat),
    (∀ c, composableCtx kws ctx = .ok (some c) → c.buffer = none) ∧
    (¬ kws.all (· = "eval_options") → composableCtx kws ctx = .error (.argumentError "Invalid keyword argument(s)")) ∧
    withCallBuffer dflt stored none = stored ∧
    (call.buffer = none → withCallBuffer dflt stored (some call) = stored) ∧
    (call.buffer = some b → (stored.getD dflt).bumper = false →
      withCallBuffer dflt stored (some call) = some { stored.getD dflt with buffer := some b }) ∧
    (call.buffer = some b → (stored.getD dflt).bumper = true → withCallBuffer dflt stored (some call) = stored)

theorem composableBuffer_holds : composableBuffer := by
  intro dflt kws ctx stored call b
  refine ⟨fun c h => ?_, fun h => by simp [composableCtx, h]; rfl, rfl,
    fun h => by simp [withCallBuffer, h], fun h hb => by simp [withCallBuffer, h, hb],
    fun h hb => by simp [withCallBuffer, h, hb]⟩
  unfold composableCtx at h
  split at h
  · cases ctx with
    | none => cases h
    | some c' =>
      simp only at h
      split at h
      · cases h
      · cases h; rename_i hn; simpa using hn
  · cases h

end SymReg.Templates
