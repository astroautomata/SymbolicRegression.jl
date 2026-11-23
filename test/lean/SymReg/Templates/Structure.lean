import DynExpr.Runtime.Errors

/-!
`TemplateStructure` construction and `num_features` inference,
`src/TemplateExpression.jl:110-264`. NamedTuples are association lists in key order.
-/

namespace SymReg.Templates
open DynExpr

@[simp] theorem okBind {α β : Type} (v : α) (f : α → Jl β) :
    ((Except.ok v : Jl α) >>= f) = f v := rfl
@[simp] theorem errBind {α β : Type} (e : JlError) (f : α → Jl β) :
    ((Except.error e : Jl α) >>= f) = .error e := rfl
@[simp] theorem pureOk {α : Type} (v : α) : (pure v : Jl α) = .ok v := rfl

/-- `issetequal` on NamedTuple keys. -/
def setEq (a b : List String) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

/-- `getproperty(nt, k)` on a NamedTuple. -/
def field {α : Type} (nt : List (String × α)) (k : String) : Jl α :=
  match nt.lookup k with
  | some v => .ok v
  | none => .error (.errorException s!"type NamedTuple has no field {k}")

/-- `TemplateStructure{K,Kp,E,NF,NP}` fields after construction,
`src/TemplateExpression.jl:110-114`; the combiner is kept abstractly by the expression. -/
structure TStructure where
  keys : List String
  pkeys : List String
  numFeatures : List Int
  numParams : List Int
  deriving DecidableEq, Repr

/-- `has_params`, `src/TemplateExpression.jl:173`. -/
-- Source: src/TemplateExpression.jl:171-171
/-
get_parameter_keys(::TemplateStructure{<:Any,Kp}) where {Kp} = Kp
-/
def getParameterKeys (s : TStructure) : List String := s.pkeys

def TStructure.hasParams (s : TStructure) : Bool := !(getParameterKeys s).isEmpty

/-- `num_features[k]` / `num_parameters[k]` lookup by key. -/
def TStructure.nf (s : TStructure) (k : String) : Jl Int := field (s.keys.zip s.numFeatures) k

/-- Observable behaviour of the user's `combine` on the dummy arguments built by
`infer_variable_constraints` (`src/TemplateExpression.jl:229-264`): whether `applicable`
holds, the ordered calls `(key, number of arguments)` it makes on the `ArgumentRecorder`s
(each forwards to `_record_composable_expression!`, lines 176-191), and how it ends after
those calls (normal return or a user exception). -/
structure CombineRun where
  applicable : Bool
  calls : List (String × Nat)
  outcome : Jl Unit

/-- `_record_composable_expression!`, `src/TemplateExpression.jl:176-186`, on the `Ref(-1)`
table. -/
def record (tbl : List (String × Int)) (k : String) (n : Nat) : Jl (List (String × Int)) := do
  let vc ← field tbl k
  if vc = -1 then pure (tbl.map fun p => if p.1 = k then (k, (n : Int)) else p)
  else if vc ≠ n then throw (.argumentError s!"Inconsistent number of arguments passed to {k}")
  else pure tbl

/-- `infer_variable_constraints`, `src/TemplateExpression.jl:229-264`; `run hasParams`
is the combiner called with or without the `ParamVector` NamedTuple. -/
def infer (K : List String) (numParams : List (String × Int)) (run : Bool → CombineRun) :
    Jl (List (String × Int)) := do
  let r := run (!numParams.isEmpty)
  if !r.applicable then
    throw (.argumentError "Your template structure's `combine` function must accept ...")
  let tbl ← r.calls.foldlM (fun t c => record t c.1 c.2) (K.map fun k => (k, -1))
  r.outcome
  let inferred ← K.mapM fun k => do pure (k, ← field tbl k)
  let failed := K.filter fun k => (inferred.lookup k) = some (-1)
  if !failed.isEmpty then
    throw (.argumentError s!"Failed to infer number of features used by {failed}")
  pure inferred

/-- `TemplateStructure{K,Kp}(combine, _deprecated_num_features; num_features,
num_parameters, prototype)`, `src/TemplateExpression.jl:127-163`. The deprecation warning has no
effect on the result. `@something` evaluates the inference only when both feature
arguments are `nothing`. -/
def mkStructure (K Kp : List String) (deprecated nf np : Option (List (String × Int)))
    (run : Bool → CombineRun) : Jl TStructure := do
  if K.any (· ∈ Kp) then
    throw (.argumentError "Template expression and parameter names must be disjoint")
  if !Kp.isEmpty && np.isNone then
    throw (.assertionError "Expected `num_parameters` to be provided")
  let np := np.getD []
  if !setEq (np.map Prod.fst) Kp then throw (.argumentError s!"`num_parameters` keys must match")
  let npv ← Kp.mapM (field np)
  let nfs ← match nf, deprecated with
    | some x, _ => pure x
    | none, some x => pure x
    | none, none => infer K (Kp.zip npv) run
  if !setEq (nfs.map Prod.fst) K then throw (.argumentError s!"`num_features` keys must match")
  let nfv ← K.mapM (field nfs)
  pure ⟨K, Kp, nfv, npv⟩

/-! ## Properties -/

/-- Construction fails, before inference, on overlapping names, missing parameter counts
for declared parameters, or parameter-count keys that differ from `Kp`. -/
def structureChecks : Prop :=
  ∀ K Kp deprecated nf np run,
    (∃ k ∈ K, k ∈ Kp) ∨ (Kp ≠ [] ∧ np = none) ∨ (np.isSome ∧ setEq ((np.getD []).map Prod.fst) Kp = false) →
    ∃ e, mkStructure K Kp deprecated nf np run = .error e

theorem field_ok {α : Type} (nt : List (String × α)) (k : String) (h : k ∈ nt.map Prod.fst) :
    ∃ v, field nt k = .ok v ∧ nt.lookup k = some v := by
  induction nt with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk; exact ⟨b, by simp [field, List.lookup], by simp [List.lookup]⟩
    · simp only [List.map_cons, List.mem_cons, hk, false_or] at h
      obtain ⟨v, h1, h2⟩ := ih h
      have hne : (k == a) = false := by simp [hk]
      exact ⟨v, by simp [field, List.lookup, hne, h2], by simp [List.lookup, hne, h2]⟩

theorem structureChecks_holds : structureChecks := by
  intro K Kp deprecated nf np run h
  unfold mkStructure
  by_cases h1 : K.any (· ∈ Kp) = true
  · exact ⟨_, by simp [h1]; rfl⟩
  have h1' : ¬ ∃ k ∈ K, k ∈ Kp := by simpa using h1
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!Kp.isEmpty && np.isNone) = true
  · exact ⟨_, by simp [h2]; rfl⟩
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  have h3 : setEq ((np.getD []).map Prod.fst) Kp = false := by
    rcases h with h | ⟨hk, hn⟩ | ⟨_, hs⟩
    · exact absurd h h1'
    · cases Kp with
      | nil => exact absurd rfl hk
      | cons _ _ => subst hn; simp at h2
    · exact hs
  exact ⟨_, by simp [h3]; rfl⟩

example : structureChecks := structureChecks_holds

/-- Explicit `num_features` take precedence over the deprecated positional argument and
the combiner is never run; the counts are reordered to the key order `K`. -/
def structureExplicit : Prop :=
  ∀ K Kp deprecated nf np (run run' : Bool → CombineRun),
    (∀ k ∈ K, k ∉ Kp) → (Kp = [] ∨ np.isSome) → setEq ((np.getD []).map Prod.fst) Kp = true →
    setEq (nf.map Prod.fst) K = true →
    mkStructure K Kp deprecated (some nf) np run = mkStructure K Kp none (some nf) np run' ∧
    ∃ s, mkStructure K Kp deprecated (some nf) np run = .ok s ∧ s.keys = K ∧ s.pkeys = Kp ∧
      s.numFeatures.length = K.length ∧
      ∀ k ∈ K, ∃ v, nf.lookup k = some v ∧ s.nf k = .ok v

theorem mapM_field_ok {α : Type} (nt : List (String × α)) (K : List String)
    (h : ∀ k ∈ K, k ∈ nt.map Prod.fst) :
    ∃ vs, K.mapM (field nt) = .ok vs ∧ vs.length = K.length ∧
      ∀ k ∈ K, ∃ v, nt.lookup k = some v ∧ field (K.zip vs) k = .ok v := by
  induction K with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons k ks ih =>
    obtain ⟨v, hv, hl⟩ := field_ok nt k (h k (by simp))
    obtain ⟨vs, hvs, hlen, hall⟩ := ih (fun k hk => h k (by simp [hk]))
    refine ⟨v :: vs, ?_, by simp [hlen], ?_⟩
    · simp [List.mapM_cons, hv, hvs]
    · intro k' hk'
      by_cases he : k' = k
      · subst he; exact ⟨v, hl, by simp [field, List.lookup]⟩
      · have hm : k' ∈ ks := by simpa [he] using hk'
        obtain ⟨w, hw1, hw2⟩ := hall k' hm
        have hne : (k' == k) = false := by simp [he]
        exact ⟨w, hw1, by simpa [field, List.lookup, hne] using hw2⟩

theorem setEq_mem {a b : List String} (h : setEq a b = true) : ∀ k ∈ b, k ∈ a := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem structureExplicit_holds : structureExplicit := by
  intro K Kp deprecated nf np run run' hd hp hs hf
  have h1 : K.any (· ∈ Kp) = false := by simpa using hd
  have h2 : (!Kp.isEmpty && np.isNone) = false := by
    rcases hp with rfl | h <;> simp [*]
  obtain ⟨npv, hnpv, _, _⟩ := mapM_field_ok (np.getD []) Kp (setEq_mem hs)
  obtain ⟨nfv, hnfv, hlen, hall⟩ := mapM_field_ok nf K (setEq_mem hf)
  have heq : ∀ dep (r : Bool → CombineRun),
      mkStructure K Kp dep (some nf) np r = .ok ⟨K, Kp, nfv, npv⟩ := by
    intro dep r
    simp [mkStructure, h1, h2, hs, hnpv, hf, hnfv]
  refine ⟨by rw [heq, heq], ⟨K, Kp, nfv, npv⟩, heq _ _, rfl, rfl, hlen, ?_⟩
  intro k hk
  obtain ⟨v, h1, h2⟩ := hall k hk
  exact ⟨v, h1, h2⟩

example : setEq ([("f", (1 : Int))].map Prod.fst) ["f"] = true ∧
    setEq (([] : List (String × Int)).map Prod.fst) [] = true := by decide


/-- The `Ref(-1)` table as a function of the key, `src/TemplateExpression.jl:237`. -/
def tblOf (K : List String) (st : String → Int) : List (String × Int) := K.map fun k => (k, st k)

theorem field_tblOf (K : List String) (st : String → Int) (k : String) :
    field (tblOf K st) k = if k ∈ K then .ok (st k) else
      .error (.errorException s!"type NamedTuple has no field {k}") := by
  induction K with
  | nil => simp [tblOf, field, List.lookup]
  | cons k' ks ih =>
    by_cases he : k = k'
    · subst he; simp [tblOf, field, List.lookup]
    · have hne : (k == k') = false := by simp [he]
      simp only [tblOf, field, List.map_cons, List.lookup, hne] at ih ⊢
      simp [ih, he]

theorem lookup_tblOf (K : List String) (st : String → Int) (k : String) (hk : k ∈ K) :
    (tblOf K st).lookup k = some (st k) := by
  have h := field_tblOf K st k
  simp only [hk, ↓reduceIte, field] at h
  split at h <;> simp_all

theorem record_new (K : List String) (st : String → Int) (k : String) (n : Nat)
    (hk : k ∈ K) (hv : st k = -1) :
    record (tblOf K st) k n = .ok (tblOf K fun k' => if k' = k then (n : Int) else st k') := by
  unfold record
  rw [field_tblOf, if_pos hk, okBind, if_pos hv, pureOk]
  congr 1
  simp only [tblOf, List.map_map]
  apply List.map_congr_left
  intro k' _
  by_cases h' : k' = k
  · subst h'; simp
  · simp [h']

theorem record_same (K : List String) (st : String → Int) (k : String) (n : Nat)
    (hk : k ∈ K) (hv : st k = n) : record (tblOf K st) k n = .ok (tblOf K st) := by
  unfold record
  have h1 : st k ≠ -1 := by rw [hv]; omega
  rw [field_tblOf, if_pos hk, okBind, if_neg h1, if_neg (by simpa using hv), pureOk]

theorem record_conflict (K : List String) (st : String → Int) (k : String) (n : Nat)
    (hk : k ∈ K) (h1 : st k ≠ -1) (h2 : st k ≠ n) : ∃ e, record (tblOf K st) k n = .error e := by
  unfold record
  rw [field_tblOf, if_pos hk, okBind, if_neg h1, if_pos h2]
  exact ⟨_, rfl⟩

theorem record_missing (K : List String) (st : String → Int) (k : String) (n : Nat)
    (hk : k ∉ K) : ∃ e, record (tblOf K st) k n = .error e := by
  unfold record
  rw [field_tblOf, if_neg hk, errBind]
  exact ⟨_, rfl⟩

/-- What a successful recording pass leaves in the table: every called key holds the arity
of its calls, already-set keys keep their value, and never-called keys are untouched. -/
theorem record_fold (K : List String) :
    ∀ (calls : List (String × Nat)) (st : String → Int) t,
      calls.foldlM (fun t c => record t c.1 c.2) (tblOf K st) = .ok t →
      ∃ stf, t = tblOf K stf ∧ (∀ k ∈ K, st k ≠ -1 → stf k = st k) ∧
        (∀ k, (∀ c ∈ calls, c.1 ≠ k) → stf k = st k) ∧
        ∀ c ∈ calls, c.1 ∈ K ∧ stf c.1 = c.2 := by
  intro calls
  induction calls with
  | nil => intro st t h; cases h; exact ⟨st, rfl, by simp, by simp, by simp⟩
  | cons c rest ih =>
    intro st t h
    obtain ⟨k, n⟩ := c
    simp only [List.foldlM_cons] at h
    by_cases hk : k ∈ K
    · by_cases hv : st k = -1
      · let st' := fun k' => if k' = k then (n : Int) else st k'
        rw [record_new K st k n hk hv, okBind] at h
        obtain ⟨stf, rfl, hkeep, huntouched, hcalls⟩ := ih st' t h
        have hn : st' k ≠ -1 := by simp [st']
        refine ⟨stf, rfl, ?_, ?_, ?_⟩
        · intro k' hk' hne
          have hk'k : k' ≠ k := by intro he; subst he; exact hne hv
          rw [hkeep k' hk' (by simpa [st', hk'k] using hne)]; simp [st', hk'k]
        · intro k' hall
          have hk'k : k ≠ k' := hall (k, n) (by simp)
          rw [huntouched k' (fun c hc => hall c (by simp [hc]))]
          simp [st', Ne.symm hk'k]
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨hk, by rw [hkeep k hk hn]; simp [st']⟩
          · exact hcalls c hc
      · by_cases hne : st k = (n : Int)
        · rw [record_same K st k n hk hne, okBind] at h
          obtain ⟨stf, rfl, hkeep, huntouched, hcalls⟩ := ih st t h
          refine ⟨stf, rfl, hkeep, fun k' hall => huntouched k' (fun c hc => hall c (by simp [hc])), ?_⟩
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨hk, by rw [hkeep k hk hv, hne]⟩
          · exact hcalls c hc
        · obtain ⟨e, he⟩ := record_conflict K st k n hk hv hne
          rw [he, errBind] at h; cases h
    · obtain ⟨e, he⟩ := record_missing K st k n hk
      rw [he, errBind] at h; cases h

theorem mapM_field_tblOf (K : List String) (st : String → Int) :
    K.mapM (fun k => do pure (k, ← field (tblOf K st) k)) = .ok (tblOf K st) := by
  have : ∀ L : List String, (∀ k ∈ L, k ∈ K) →
      L.mapM (fun k => do pure (k, ← field (tblOf K st) k)) = .ok (tblOf L st) := by
    intro L hL
    induction L with
    | nil => rfl
    | cons k ks ih =>
      rw [List.mapM_cons, field_tblOf, if_pos (hL k (by simp)), okBind, pureOk, okBind,
        ih (fun k' h => hL k' (by simp [h])), okBind, pureOk]
      rfl
  exact this K (fun _ h => h)

theorem mapM_field_tblOf' (K : List String) (st : String → Int) :
    K.mapM (field (tblOf K st)) = .ok (K.map st) := by
  have : ∀ L : List String, (∀ k ∈ L, k ∈ K) → L.mapM (field (tblOf K st)) = .ok (L.map st) := by
    intro L hL
    induction L with
    | nil => rfl
    | cons k ks ih =>
      rw [List.mapM_cons, field_tblOf, if_pos (hL k (by simp)), okBind,
        ih (fun k' h => hL k' (by simp [h])), okBind, pureOk]
      rfl
  exact this K (fun _ h => h)

/-- `infer` once the recording pass and the combiner have finished normally. -/
theorem infer_after (K : List String) numParams (run : Bool → CombineRun) (stf : String → Int)
    (happ : (run (!numParams.isEmpty)).applicable = true)
    (ht : (run (!numParams.isEmpty)).calls.foldlM (fun t c => record t c.1 c.2)
      (tblOf K fun _ => -1) = .ok (tblOf K stf))
    (hout : (run (!numParams.isEmpty)).outcome = .ok ()) :
    infer K numParams run =
      if !(K.filter fun k => (tblOf K stf).lookup k = some (-1)).isEmpty then
        .error (.argumentError
          s!"Failed to infer number of features used by {K.filter fun k => (tblOf K stf).lookup k = some (-1)}")
      else .ok (tblOf K stf) := by
  have hinit : (K.map fun k => (k, (-1 : Int))) = tblOf K fun _ => -1 := rfl
  unfold infer
  simp only [happ, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hinit, ht, okBind, hout, okBind, mapM_field_tblOf, okBind]
  split <;> rfl

/-- Successful inference: if `combine` accepts the dummy arguments, calls only template keys,
calls every key with one fixed arity `a k`, and returns normally, the inferred counts are
exactly those arities, in key order. -/
def inferSpec : Prop :=
  ∀ (K : List String) numParams (run : Bool → CombineRun) (a : String → Nat),
    (run (!numParams.isEmpty)).applicable = true →
    (run (!numParams.isEmpty)).outcome = .ok () →
    (∀ c ∈ (run (!numParams.isEmpty)).calls, c.1 ∈ K ∧ c.2 = a c.1) →
    (∀ k ∈ K, ∃ n, (k, n) ∈ (run (!numParams.isEmpty)).calls) →
    infer K numParams run = .ok (K.map fun k => (k, (a k : Int)))

/-- The recording pass with consistent arities succeeds. -/
theorem record_fold_ok (K : List String) (a : String → Nat) :
    ∀ (calls : List (String × Nat)) (st : String → Int),
      (∀ c ∈ calls, c.1 ∈ K ∧ c.2 = a c.1) → (∀ k, st k = -1 ∨ st k = a k) →
      ∃ t, calls.foldlM (fun t c => record t c.1 c.2) (tblOf K st) = .ok t := by
  intro calls
  induction calls with
  | nil => intro st _ _; exact ⟨_, rfl⟩
  | cons c rest ih =>
    intro st hc hst
    obtain ⟨k, n⟩ := c
    obtain ⟨hk, hn⟩ := hc (k, n) (by simp)
    simp only at hk hn; subst hn
    simp only [List.foldlM_cons]
    rcases hst k with hv | hv
    · rw [record_new K st k (a k) hk hv, okBind]
      apply ih _ (fun c h => hc c (by simp [h]))
      intro k'; by_cases h' : k' = k
      · subst h'; right; simp
      · simpa [h'] using hst k'
    · rw [record_same K st k (a k) hk hv, okBind]
      exact ih st (fun c h => hc c (by simp [h])) hst

theorem inferSpec_holds : inferSpec := by
  intro K numParams run a happ hout hcalls hall
  obtain ⟨t, ht⟩ := record_fold_ok K a _ (fun _ => -1) hcalls (fun _ => .inl rfl)
  obtain ⟨stf, rfl, _, _, hc⟩ := record_fold K _ _ t ht
  have hstf : ∀ k ∈ K, stf k = a k := by
    intro k hk
    obtain ⟨n, hn⟩ := hall k hk
    have h1 := (hc _ hn).2
    have h2 := (hcalls _ hn).2
    simp only at h1 h2; rw [h1, h2]
  have hfail : (K.filter fun k => (tblOf K stf).lookup k = some (-1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k hk
    rw [lookup_tblOf K stf k hk, hstf k hk]; simp
  rw [infer_after K numParams run stf happ ht hout, hfail]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.map_congr_left; intro k hk; simp [hstf k hk]

example : inferSpec := inferSpec_holds

/-- Any key called with two different numbers of arguments makes inference throw, whatever
the rest of the call trace. -/
def inferInconsistent : Prop :=
  ∀ (K : List String) numParams (run : Bool → CombineRun) k n m,
    k ∈ K → (run (!numParams.isEmpty)).applicable = true →
    (k, n) ∈ (run (!numParams.isEmpty)).calls → (k, m) ∈ (run (!numParams.isEmpty)).calls →
    n ≠ m → ∃ e, infer K numParams run = .error e

theorem inferInconsistent_holds : inferInconsistent := by
  intro K numParams run k n m hk happ hn hm hnm
  have hinit : (K.map fun k => (k, (-1 : Int))) = tblOf K fun _ => -1 := rfl
  unfold infer
  simp only [happ, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hinit]
  cases hf : (run (!numParams.isEmpty)).calls.foldlM (fun t c => record t c.1 c.2)
      (tblOf K fun _ => -1) with
  | error e => exact ⟨e, rfl⟩
  | ok t =>
    obtain ⟨stf, _, _, _, hc⟩ := record_fold K _ _ t hf
    have h1 := (hc _ hn).2
    have h2 := (hc _ hm).2
    simp only at h1 h2
    rw [h1] at h2; exact absurd (by exact_mod_cast h2) hnm

/-- A template key the combiner never calls makes inference throw (an `ArgumentError` when
nothing else fails first), so its feature count is never silently defaulted. -/
def inferUncalled : Prop :=
  ∀ (K : List String) numParams (run : Bool → CombineRun) k,
    k ∈ K → (∀ c ∈ (run (!numParams.isEmpty)).calls, c.1 ≠ k) →
    ∃ e, infer K numParams run = .error e

theorem inferUncalled_holds : inferUncalled := by
  intro K numParams run k hk hnot
  have hinit : (K.map fun k => (k, (-1 : Int))) = tblOf K fun _ => -1 := rfl
  by_cases happ : (run (!numParams.isEmpty)).applicable = true
  · cases hf : (run (!numParams.isEmpty)).calls.foldlM (fun t c => record t c.1 c.2)
        (tblOf K fun _ => -1) with
    | error e =>
      refine ⟨e, ?_⟩
      unfold infer
      simp only [happ, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hinit, hf, errBind]
    | ok t =>
      obtain ⟨stf, rfl, _, hu, _⟩ := record_fold K _ _ _ hf
      have hk1 : stf k = -1 := hu k hnot
      cases ho : (run (!numParams.isEmpty)).outcome with
      | error e =>
        refine ⟨e, ?_⟩
        unfold infer
        simp only [happ, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hinit, hf, okBind, ho, errBind]
      | ok u =>
        cases u
        have hne : (K.filter fun k => (tblOf K stf).lookup k = some (-1)).isEmpty = false := by
          rw [List.isEmpty_eq_false_iff_exists_mem]
          exact ⟨k, List.mem_filter.mpr ⟨hk, by rw [lookup_tblOf K stf k hk, hk1]; simp⟩⟩
        rw [infer_after K numParams run stf happ hf ho, hne]
        exact ⟨_, rfl⟩
  · unfold infer
    simp only [Bool.not_eq_true] at happ
    simp only [happ, Bool.not_false, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- A combiner that does not accept the dummy arguments is rejected with an `ArgumentError`
before it is called. -/
def inferNotApplicable : Prop :=
  ∀ (K : List String) numParams (run : Bool → CombineRun),
    (run (!numParams.isEmpty)).applicable = false →
    ∃ msg, infer K numParams run = .error (.argumentError msg)

theorem inferNotApplicable_holds : inferNotApplicable := by
  intro K numParams run h
  unfold infer
  simp only [h, Bool.not_false, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- Successful construction without explicit counts stores exactly the inferred arities. -/
def structureInferred : Prop :=
  ∀ K Kp np (run : Bool → CombineRun) (a : String → Nat),
    (∀ k ∈ K, k ∉ Kp) → (Kp = [] ∨ np.isSome) → setEq ((np.getD []).map Prod.fst) Kp = true →
    (run (!Kp.isEmpty)).applicable = true → (run (!Kp.isEmpty)).outcome = .ok () →
    (∀ c ∈ (run (!Kp.isEmpty)).calls, c.1 ∈ K ∧ c.2 = a c.1) →
    (∀ k ∈ K, ∃ n, (k, n) ∈ (run (!Kp.isEmpty)).calls) →
    ∃ s, mkStructure K Kp none none np run = .ok s ∧ s.keys = K ∧ s.pkeys = Kp ∧
      s.numFeatures = K.map fun k => (a k : Int)

theorem structureInferred_holds : structureInferred := by
  intro K Kp np run a hd hp hs happ hout hc hall
  have h1 : K.any (· ∈ Kp) = false := by simpa using hd
  have h2 : (!Kp.isEmpty && np.isNone) = false := by
    rcases hp with rfl | h <;> simp [*]
  obtain ⟨npv, hnpv, hlen, _⟩ := mapM_field_ok (np.getD []) Kp (setEq_mem hs)
  have hz : (Kp.zip npv).isEmpty = Kp.isEmpty := by
    cases Kp <;> cases npv <;> simp_all
  have hinf : infer K (Kp.zip npv) run = .ok (tblOf K fun k => (a k : Int)) :=
    inferSpec_holds K (Kp.zip npv) run a (by rw [hz]; exact happ) (by rw [hz]; exact hout)
      (by rw [hz]; exact hc) (by rw [hz]; exact hall)
  have hkeys : (tblOf K fun k => (a k : Int)).map Prod.fst = K := by
    simp [tblOf, Function.comp_def]
  have hsetK : setEq K K = true := by simp [setEq]
  refine ⟨⟨K, Kp, K.map fun k => (a k : Int), npv⟩, ?_, rfl, rfl, rfl⟩
  unfold mkStructure
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, hs, Bool.not_true]
  rw [hnpv, okBind, hinf, okBind, hkeys, hsetK]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [mapM_field_tblOf', okBind, pureOk]
def parameterKeyOrder : Prop := ∀ k kp depr nf np run s,
  mkStructure k kp depr nf np run = .ok s → getParameterKeys s = kp

theorem parameterKeyOrder_holds : parameterKeyOrder := by
  intro k kp depr nf np run s h
  simp only [mkStructure, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' first | (solve | cases h; rfl) | (solve | contradiction) | split at h

end SymReg.Templates
