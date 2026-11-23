import SymReg.Population.Tournament

/-!
Model of the `Population` constructors, `copy`, `finalize_costs` and `best_sub_pop` of
`src/Population.jl` (SymbolicRegression.jl `upstream/master` daae84e5).

Population members are object identities (`Nat`) with their mutable fields held in store
functions; fresh identities come from an allocation counter. Trees, plugins, losses and the
random tree generator are abstract and quantified over.
-/

namespace SymReg.Population
open DynExpr

/-! ## Constructors -/

/-- A member built by `constructorof(PM)(dataset, tree, options; parent=-1, deterministic)`
(`src/Population.jl:77-83,88-94,105-111`), with the fields the constructors set: the tree, the
parent reference, and the object identity (here the index of the `_init_tree` call). -/
structure NewMember (τ : Type) where
  tree : τ
  parent : Int
  id : Nat

/- Source: src/Plugin.jl:398-402
@inline function resolve_init_member(states::Tuple, plugins::Tuple, dataset, options)
    candidates = strictmap((s, p) -> init_member(s, p, dataset, options), states, plugins)
    count(!isnothing, candidates) > 1 && _init_member_conflict(plugins, candidates)
    return _first_non_nothing(candidates)
end
-/
private def collectCandidates {P S τ W : Type} (provider : S → P → W → Jl (Option τ) × W) :
    List (S × P) → W → Jl (List (Option τ)) × W
  | [], w => (.ok [], w)
  | (s, p) :: pairs, w =>
    match provider s p w with
    | (.error e, w') => (.error e, w')
    | (.ok result, w') =>
      let (tail, w'') := collectCandidates provider pairs w'
      (tail.map (List.cons result), w'')

def candidateResult {τ : Type} (cands : List (Option τ)) : Jl (Option τ) :=
  if 1 < (cands.filter Option.isSome).length then .error (.argumentError "init_member conflict")
  else .ok (cands.findSome? id)

/- Source: src/Population.jl:47-54
function _init_tree(
    dataset, options, nlength::Int, nfeatures::Int, ::Type{T}, plugin_states::Tuple
) where {T}
    return @something(
        resolve_init_member(plugin_states, options.plugins, dataset, options),
        gen_random_tree(nlength, options, nfeatures, T),
    )
end
-/
def initTree {τ W : Type} (collect : W → Jl (List (Option τ)) × W)
    (gen : W → Jl τ × W) (w : W) : Jl τ × W :=
  match collect w with
  | (.error e, w') => (.error e, w')
  | (.ok cands, w') =>
    match candidateResult cands with
    | .error e => (.error e, w')
    | .ok (some t) => (.ok t, w')
    | .ok none => gen w'

def initMemberTree {P S O D τ W : Type} (provider : S → P → D → O → W → Jl (Option τ) × W)
    (states : List S) (plugins : List P) (dataset : D) (options : O)
    (gen : W → Jl τ × W) (w : W) : Jl τ × W :=
  initTree
    (fun w' => if states.length ≠ plugins.length then
      (.error (.dimensionMismatch "collections must have equal lengths"), w')
    else collectCandidates (fun s p => provider s p dataset options) (states.zip plugins) w')
    gen w

/-- One member construction from `_init_tree` call number `c`: `cands c` are the plugins'
`init_member` results of that call and `gen nl c` the `gen_random_tree(nl, ...)` result it
would draw. -/
def mkMember {τ : Type} (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ) (nl c : Nat) :
    Jl (NewMember τ) := do
  let t ← (initTree (fun _ : Unit => (.ok (cands c), ())) (fun _ => (.ok (gen nl c), ())) ()).1
  pure { tree := t, parent := -1, id := c }

/-- `@assert (population_size !== nothing) ⊻ (npop !== nothing)` of `src/Population.jl:72,136`. -/
def assertXor (size npop : Option Nat) : Jl Unit :=
  if size.isSome != npop.isSome then pure () else throw (.assertionError "xor")

/-- `Population(dataset; options, population_size, nlength=3, nfeatures, npop, plugin_states)`,
`src/Population.jl:63-101`: `first_member` is built first (call 0), then the comprehension
`for i in 1:population_size` reuses it for `i == 1` and builds call `i - 1` otherwise. Returns
the members and `n`. -/
def popDataset {τ : Type} (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ)
    (size npop : Option Nat) (nl : Nat) : Jl (List (NewMember τ) × Nat) := do
  assertXor size npop
  let s := (size.or npop).getD 0
  let first ← mkMember cands gen nl 0
  let members ← (List.range s).mapM fun i => if i = 0 then pure first else mkMember cands gen nl i
  pure (members, s)

/-- `Population(X, y; population_size, nlength=3, options, nfeatures, loss_type, npop,
plugin_states)`, `src/Population.jl:125-145`. Dataset construction and
`update_baseline_loss!` only affect member costs, which are not modelled. The final call
`Population(dataset; population_size, options, nfeatures, plugin_states)` (line 144) does not
pass `nlength`, so the callee's default `nlength=3` is used. -/
def popMatrix {τ : Type} (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ)
    (size npop : Option Nat) (_nlength : Nat) : Jl (List (NewMember τ) × Nat) := do
  assertXor size npop
  let s := if npop.isNone then size else npop
  popDataset cands gen s none 3

/-- `_population_without_plugins(dataset; options, nlength=3, nfeatures)`,
`src/Population.jl:103-115`: one member from `gen_random_tree(nlength, ...)` (no plugin is
consulted), wrapped by `Population([member])` (`n = 1`). -/
def popWithoutPlugins {τ : Type} (gen : Nat → Nat → τ) (nl : Nat) : List (NewMember τ) × Nat :=
  ([{ tree := gen nl 0, parent := -1, id := 0 }], 1)

/-- At most one plugin provides an initial tree per call (otherwise `_init_tree` throws). -/
def AtMostOneProvider {τ : Type} (cands : Nat → List (Option τ)) : Prop :=
  ∀ c, ((cands c).filter Option.isSome).length ≤ 1

/-- Property `pop-init-tree`: `_init_tree` throws an `ArgumentError` when two or more plugins
return an initial tree, returns the provided tree when exactly one does, and otherwise returns
the `gen_random_tree` result. -/
def init_tree_spec : Prop :=
  ∀ (τ : Type) (cands : List (Option τ)) (gen : τ),
    (1 < (cands.filter Option.isSome).length →
      (initTree (fun _ : Unit => (.ok cands, ())) (fun _ => (.ok gen, ())) ()).1 =
        .error (.argumentError "init_member conflict")) ∧
    (∀ t, (cands.filter Option.isSome) = [some t] →
      (initTree (fun _ : Unit => (.ok cands, ())) (fun _ => (.ok gen, ())) ()).1 = .ok t) ∧
    ((∀ o ∈ cands, o = none) →
      (initTree (fun _ : Unit => (.ok cands, ())) (fun _ => (.ok gen, ())) ()).1 = .ok gen)

theorem findSome_of_filter {τ : Type} :
    ∀ (cands : List (Option τ)) (t : τ), cands.filter Option.isSome = [some t] →
      cands.findSome? id = some t := by
  intro cands
  induction cands with
  | nil => intro t h; simp at h
  | cons o os ih =>
    intro t h
    cases o with
    | none => simp at h ⊢; exact ih t h
    | some x =>
      simp at h ⊢
      exact h.1

theorem findSome_none {τ : Type} :
    ∀ (cands : List (Option τ)), (∀ o ∈ cands, o = none) → cands.findSome? id = none := by
  intro cands h
  induction cands with
  | nil => rfl
  | cons o os ih =>
    have := h o (by simp); subst this
    exact ih (fun o' ho' => h o' (by simp [ho']))

theorem init_tree_spec_holds : init_tree_spec := by
  intro τ cands gen
  refine ⟨fun h => by simp [initTree, candidateResult, h], fun t h => ?_, fun h => ?_⟩
  · simp [initTree, candidateResult, h, findSome_of_filter cands t h]
  · have h0 : (cands.filter Option.isSome).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro o ho; simp [h o ho]
    simp [initTree, candidateResult, h0, findSome_none cands h]

inductive ProviderRun {P S τ W : Type} (call : S → P → W → Jl (Option τ) × W) :
    List (S × P) → W → Jl (List (Option τ)) → W → Prop where
  | nil : ProviderRun call [] w (.ok []) w
  | throws : call s p w = (.error e, w') →
      ProviderRun call ((s,p) :: pairs) w (.error e) w'
  | next : call s p w = (.ok candidate, w') → ProviderRun call pairs w' tail w'' →
      ProviderRun call ((s,p) :: pairs) w (tail.map (List.cons candidate)) w''

def member_resolution : Prop := ∀ (P S O D τ W : Type)
    (provider : S → P → D → O → W → Jl (Option τ) × W)
    (states : List S) (plugins : List P) dataset options gen w,
  let out := initMemberTree provider states plugins dataset options gen w
  (states.length ≠ plugins.length →
    out = (.error (.dimensionMismatch "collections must have equal lengths"), w)) ∧
  (states.length = plugins.length → ∃ candidates w',
    ProviderRun (fun s p => provider s p dataset options) (states.zip plugins) w candidates w' ∧
    (∀ e, candidates = .error e → out = (.error e, w')) ∧
    ∀ cs, candidates = .ok cs →
      (1 < (cs.filter Option.isSome).length → out = (.error (.argumentError "init_member conflict"), w')) ∧
      (∀ t, cs.filter Option.isSome = [some t] → out = (.ok t, w')) ∧
      ((∀ c ∈ cs, c = none) → out = gen w'))

private theorem collectCandidates_run {P S τ W : Type}
    (call : S → P → W → Jl (Option τ) × W) (pairs : List (S × P)) (w : W) :
    let (candidates, w') := collectCandidates call pairs w
    ProviderRun call pairs w candidates w' := by
  induction pairs generalizing w with
  | nil => exact .nil
  | cons pair pairs ih =>
    obtain ⟨s, p⟩ := pair
    obtain ⟨result, w', he⟩ := Prod.exists.mp ⟨call s p w, rfl⟩
    cases result with
    | error e =>
      simpa [collectCandidates, he] using
        (ProviderRun.throws (call := call) (pairs := pairs) he)
    | ok candidate =>
      specialize ih w'
      cases ht : collectCandidates call pairs w' with
      | mk tail w'' =>
        rw [ht] at ih
        simpa [collectCandidates, he, ht] using ProviderRun.next (call := call) he ih

theorem member_resolution_holds : member_resolution := by
  intro P S O D τ W provider states plugins dataset options gen w
  constructor
  · intro h; simp [initMemberTree, initTree, h]
  · intro h
    let call := fun s p => provider s p dataset options
    have trace := collectCandidates_run call (states.zip plugins) w
    cases he : collectCandidates call (states.zip plugins) w with
    | mk candidates w' =>
      rw [he] at trace
      dsimp only [call] at he
      refine ⟨candidates, w', trace, ?_, ?_⟩
      · intro e he'
        simp [initMemberTree, initTree, h, he, he']
      · intro cs hc
        have run : initMemberTree provider states plugins dataset options gen w =
            (match candidateResult cs with
            | .error e => (.error e, w')
            | .ok (some t) => (.ok t, w')
            | .ok none => gen w') := by
          simp [initMemberTree, initTree, h, he, hc]
        refine ⟨fun conflict => by simp [run, candidateResult, conflict], ?_, ?_⟩
        · intro t ht; simp [run, candidateResult, ht, findSome_of_filter cs t ht]
        · intro hn
          have hz : (cs.filter Option.isSome).length = 0 := by
            rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro c hc; simp [hn c hc]
          simp [run, candidateResult, hz, findSome_none cs hn]

theorem mkMember_ok {τ : Type} (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ)
    (h : AtMostOneProvider cands) (nl c : Nat) :
    mkMember cands gen nl c =
      .ok { tree := ((cands c).findSome? id).getD (gen nl c), parent := -1, id := c } := by
  have := h c
  simp only [mkMember, initTree, candidateResult,
    show ¬ (1 < ((cands c).filter Option.isSome).length) by omega,
    if_false]
  cases (cands c).findSome? id <;> rfl

/-- Property `pop-ctor-size`: `Population(dataset; population_size=s)` (or `npop=s`), when at
most one plugin provides each initial tree, returns `n = s` and exactly `s` distinct new members,
each with `parent = -1`; member `j` (0-based) has the tree `_init_tree` built in call `j`: the
plugin-provided tree if any, else `gen_random_tree(nlength, ...)`. -/
def ctor_size : Prop :=
  ∀ (τ : Type) (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ) (s nl : Nat)
    (size npop : Option Nat),
    AtMostOneProvider cands → (size = some s ∧ npop = none ∨ size = none ∧ npop = some s) →
    ∃ ms, popDataset cands gen size npop nl = .ok (ms, s) ∧ ms.length = s ∧
      (ms.map NewMember.id).Nodup ∧
      ∀ j, j < s → ∃ m, ms[j]? = some m ∧ m.parent = -1 ∧ m.id = j ∧
        m.tree = ((cands j).findSome? id).getD (gen nl j)

theorem mapM_members {τ : Type} (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ)
    (h : AtMostOneProvider cands) (nl : Nat) (first : NewMember τ)
    (hf : first = { tree := ((cands 0).findSome? id).getD (gen nl 0), parent := -1, id := 0 }) :
    ∀ s, (List.range s).mapM (fun i => if i = 0 then pure first else mkMember cands gen nl i) =
      .ok ((List.range s).map fun j =>
        { tree := ((cands j).findSome? id).getD (gen nl j), parent := -1, id := j }) := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [List.range_succ, List.mapM_append, ih]
    simp only [List.mapM_cons, List.mapM_nil]
    by_cases hs : s = 0
    · subst hs; subst hf; simp; rfl
    · simp only [hs, if_false, mkMember_ok cands gen h nl s]
      simp [List.map_append]
      rfl

theorem ctor_size_holds : ctor_size := by
  intro τ cands gen s nl size npop h hk
  have hx : assertXor size npop = .ok () := by
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hs : (size.or npop).getD 0 = s := by
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  refine ⟨(List.range s).map fun j =>
    { tree := ((cands j).findSome? id).getD (gen nl j), parent := -1, id := j }, ?_, by simp, ?_, ?_⟩
  · simp only [popDataset, hx, hs, bind, Except.bind, mkMember_ok cands gen h nl 0]
    rw [mapM_members cands gen h nl _ rfl s]
    rfl
  · simp only [List.map_map]
    have : ((fun (m : NewMember τ) => m.id) ∘ fun j =>
        ({ tree := ((cands j).findSome? id).getD (gen nl j), parent := -1, id := j } : NewMember τ))
        = id := rfl
    rw [this, List.map_id]
    exact List.nodup_range
  · intro j hj
    exact ⟨{ tree := ((cands j).findSome? id).getD (gen nl j), parent := -1, id := j },
      by simp [hj], rfl, rfl, rfl⟩

/-- Property `pop-ctor-keywords`: both population constructors (`Population(dataset; ...)` and
`Population(X, y; ...)`) throw an `AssertionError` unless exactly one of `population_size` and
`npop` is given. -/
def ctor_keywords : Prop :=
  ∀ (τ : Type) (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ) (nl : Nat)
    (size npop : Option Nat), size.isSome = npop.isSome →
    popDataset cands gen size npop nl = .error (.assertionError "xor") ∧
    popMatrix cands gen size npop nl = .error (.assertionError "xor")

theorem ctor_keywords_holds : ctor_keywords := by
  intro τ cands gen nl size npop h
  have : assertXor size npop = .error (.assertionError "xor") := by
    simp [assertXor, h]; rfl
  simp [popDataset, popMatrix, this, bind, Except.bind]

/-- Property `pop-ctor-matrix-nlength`: `Population(X, y; population_size=s, nlength=l, ...)`
(no plugin providing trees) builds every member from `gen_random_tree(l, ...)`, the
`nlength` it was given. -/
def ctor_matrix_nlength : Prop :=
  ∀ (τ : Type) (cands : Nat → List (Option τ)) (gen : Nat → Nat → τ) (s nl : Nat)
    (ms : List (NewMember τ)) (n : Nat),
    (∀ c, ∀ o ∈ cands c, o = none) →
    popMatrix cands gen (some s) none nl = .ok (ms, n) → ∀ m ∈ ms, m.tree = gen nl m.id

theorem ctor_matrix_nlength_refuted : ¬ ctor_matrix_nlength := by
  intro h
  have := h Nat (fun _ => []) (fun nl _ => nl) 1 5 [{ tree := 3, parent := -1, id := 0 }] 1
    (by simp) rfl { tree := 3, parent := -1, id := 0 } (by simp)
  simp at this

/-- Property `pop-without-plugins`: `_population_without_plugins` returns a one-member
population (`n = 1 = length(members)`) whose member has `parent = -1` and the
`gen_random_tree(nlength, ...)` tree; no plugin's `init_member` is consulted. -/
def without_plugins : Prop :=
  ∀ (τ : Type) (gen : Nat → Nat → τ) (nl : Nat),
    (popWithoutPlugins gen nl).2 = (popWithoutPlugins gen nl).1.length ∧
    (popWithoutPlugins gen nl).2 = 1 ∧
    ∀ m ∈ (popWithoutPlugins gen nl).1, m.parent = -1 ∧ m.tree = gen nl 0

theorem without_plugins_holds : without_plugins := by
  intro τ gen nl
  simp [popWithoutPlugins]

example : AtMostOneProvider (fun _ => ([none, some 7] : List (Option Nat))) := by
  intro c; simp

/-! ## `copy` -/

/-- `Base.copy(pop)`, `src/Population.jl:147-153`: for `i in 1:pop.n`, `copied_members[i] =
copy(pop.members[i])` (checked indexing), then `Population(copied_members)` (`n =
length(copied_members)`, `src/Population.jl:34-36`). `copy(member)` (`src/PopMember.jl:170-179`)
allocates the fresh identity `next` holding a copy of the member's fields (`fields : Nat → φ`,
e.g. tree, cost, loss, birth, references). Returns the members, the field store and the next
free identity. The member type is unchanged (`::P`, so `popmember_type` is the same). -/
def copyPop {φ : Type} (fields : Nat → φ) (members : List Nat) (n next : Nat) :
    Jl (List Nat × (Nat → φ) × Nat) := do
  let rec go : Nat → List Nat → (Nat → φ) → Nat → Jl (List Nat × (Nat → φ) × Nat)
    | 0, acc, f, nx => pure (acc, f, nx)
    | k + 1, acc, f, nx => do
      let m ← at1 members (acc.length + 1)
      go k (acc ++ [nx]) (fun x => if x = nx then f m else f x) (nx + 1)
  go n [] fields next

/-- Property `pop-copy`: for a population with `n = length(members)`, `copy(pop)` returns a
population with the same `n`, whose members are distinct objects that are all newly allocated
(none is a member of the original), member `i` carrying the fields of original member `i`; the
original objects' fields are unchanged. -/
def copy_spec : Prop :=
  ∀ (φ : Type) (fields : Nat → φ) (members : List Nat) (next : Nat),
    (∀ x ∈ members, x < next) →
    ∃ ms f' nx, copyPop fields members members.length next = .ok (ms, f', nx) ∧
      ms.length = members.length ∧ ms.Nodup ∧ (∀ x ∈ ms, next ≤ x ∧ x ∉ members) ∧
      (∀ i, i < members.length → ∀ a b, ms[i]? = some a → members[i]? = some b → f' a = fields b) ∧
      (∀ x, x < next → f' x = fields x)

theorem copy_go {φ : Type} (members : List Nat) (next : Nat) (hmem : ∀ x ∈ members, x < next) :
    ∀ k (acc : List Nat) (f : Nat → φ) (fields : Nat → φ),
      acc.length + k = members.length → acc = List.range' next acc.length →
      (∀ i, i < acc.length → ∀ b, members[i]? = some b → f (next + i) = fields b) →
      (∀ x, x < next → f x = fields x) →
      ∃ ms f' nx, copyPop.go members k acc f (next + acc.length) = .ok (ms, f', nx) ∧
        ms = List.range' next members.length ∧
        (∀ i, i < members.length → ∀ b, members[i]? = some b → f' (next + i) = fields b) ∧
        (∀ x, x < next → f' x = fields x) := by
  intro k
  induction k with
  | zero =>
    intro acc f fields hl ha hf hfx
    refine ⟨acc, f, _, rfl, by rw [ha]; simp at hl; rw [hl], fun i hi b hb => hf i (by omega) b hb, hfx⟩
  | succ k ih =>
    intro acc f fields hl ha hf hfx
    have hlt : acc.length < members.length := by omega
    simp only [copyPop.go, at1_ok members (acc.length + 1) (by omega) (by omega), bind,
      Except.bind]
    simp only [Nat.add_sub_cancel]
    have := ih (acc ++ [next + acc.length])
      (fun x => if x = next + acc.length then f members[acc.length] else f x) fields
      (by simp; omega) (by rw [ha]; simp [List.range'_concat]) ?_ ?_
    · simpa [Nat.add_assoc] using this
    · intro i hi b hb
      simp at hi
      by_cases hie : i = acc.length
      · subst hie
        rw [List.getElem?_eq_getElem hlt] at hb
        simp at hb
        subst hb
        simp
        exact hfx _ (hmem _ (List.getElem_mem hlt))
      · have : next + i ≠ next + acc.length := by omega
        simp [hie]
        exact hf i (by omega) b hb
    · intro x hx
      have : x ≠ next + acc.length := by omega
      simp [this]
      exact hfx x hx

theorem copy_spec_holds : copy_spec := by
  intro φ fields members next hlt
  obtain ⟨ms, f', nx, h, hms, hf, hfx⟩ :=
    copy_go members next hlt members.length [] fields fields (by simp) rfl (by simp) (fun _ _ => rfl)
  refine ⟨ms, f', nx, by simpa [copyPop] using h, by simp [hms], ?_, ?_, ?_, hfx⟩
  · rw [hms]; exact List.nodup_range'
  · intro x hx
    rw [hms, List.mem_range'_1] at hx
    exact ⟨hx.1, fun hm => by have := hlt x hm; omega⟩
  · intro i hi a b ha hb
    rw [hms, List.getElem?_eq_getElem (by simp; omega)] at ha
    simp at ha
    rw [← ha]
    exact hf i hi b hb

/-! ## `finalize_costs` -/

/-- `finalize_costs(dataset, pop, options)`, `src/Population.jl:236-250`. When
`use_batching(options, dataset)` holds, every member (in order) gets
`cost, loss = eval_cost(dataset, member, options)`, i.e. `loss = evalLoss m` (the full-data
loss of the member's tree) and `cost = loss_to_cost(loss, ...)` (`src/LossFunctions.jl:226-246`,
here `toCost m loss`, which depends on the member's tree and complexity only); `num_evals` is
`pop.n`. Otherwise nothing changes and `num_evals = 0`. Mutation is in place: the population
and member objects are the same. -/
def finalizeCosts {L : Type} (batching : Bool) (members : List Nat) (cost loss : Nat → L)
    (evalLoss : Nat → L) (toCost : Nat → L → L) : (Nat → L) × (Nat → L) × Nat :=
  if batching then
    let r := members.foldl (fun (acc : (Nat → L) × (Nat → L)) m =>
      ((fun x => if x = m then toCost m (evalLoss m) else acc.1 x),
       (fun x => if x = m then evalLoss m else acc.2 x))) (cost, loss)
    (r.1, r.2, members.length)
  else (cost, loss, 0)

/-- Property `pop-finalize-costs`: with batching, after `finalize_costs` every member has
`loss` equal to its full-data loss and `cost = loss_to_cost(loss, ...)`, every other object is
unchanged, and `num_evals = pop.n`; without batching nothing changes and `num_evals = 0`. -/
def finalize_costs_spec : Prop :=
  ∀ (L : Type) (batching : Bool) (members : List Nat) (cost loss evalLoss : Nat → L)
    (toCost : Nat → L → L),
    (batching = true → ∀ x,
      (finalizeCosts batching members cost loss evalLoss toCost).1 x =
        (if x ∈ members then toCost x (evalLoss x) else cost x) ∧
      (finalizeCosts batching members cost loss evalLoss toCost).2.1 x =
        (if x ∈ members then evalLoss x else loss x)) ∧
    (batching = true → (finalizeCosts batching members cost loss evalLoss toCost).2.2 = members.length) ∧
    (batching = false → finalizeCosts batching members cost loss evalLoss toCost = (cost, loss, 0))

theorem finalize_fold {L : Type} (evalLoss : Nat → L) (toCost : Nat → L → L) :
    ∀ (members : List Nat) (c l : Nat → L) x,
      (members.foldl (fun (acc : (Nat → L) × (Nat → L)) m =>
        ((fun x => if x = m then toCost m (evalLoss m) else acc.1 x),
         (fun x => if x = m then evalLoss m else acc.2 x))) (c, l)).1 x =
        (if x ∈ members then toCost x (evalLoss x) else c x) ∧
      (members.foldl (fun (acc : (Nat → L) × (Nat → L)) m =>
        ((fun x => if x = m then toCost m (evalLoss m) else acc.1 x),
         (fun x => if x = m then evalLoss m else acc.2 x))) (c, l)).2 x =
        (if x ∈ members then evalLoss x else l x) := by
  intro members
  induction members with
  | nil => intro c l x; simp
  | cons m ms ih =>
    intro c l x
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih _ _ x
    rw [h1, h2]
    by_cases hx : x = m
    · subst hx; simp
    · simp [hx]

theorem finalize_costs_spec_holds : finalize_costs_spec := by
  intro L batching members cost loss evalLoss toCost
  refine ⟨fun hb x => ?_, fun hb => by simp [finalizeCosts, hb], fun hb => by simp [finalizeCosts, hb]⟩
  simp only [finalizeCosts, hb, if_true]
  exact finalize_fold evalLoss toCost members cost loss x

/-! ## `best_sub_pop` -/

/-- Contract of `sortperm(v)` (Julia Base, default `isless` order): a permutation of
`1:length(v)` along which `v` is sorted. -/
def SortPerm (v : List JF) (perm : List Nat) : Prop :=
  perm.Perm (List.range' 1 v.length) ∧
  perm.Pairwise fun i j => isless (v.getD (j - 1) .nan) (v.getD (i - 1) .nan) = false

/-- `_get_cost(member) = member.cost`, `src/Population.jl:214`: the cost field. -/
def getCost {ι : Type} (cost : ι → JF) (m : ι) : JF := cost m

/-- `best_sub_pop(pop; topn=10)`, `src/Population.jl:253-258`: `best_idx =
sortperm([pop.members[i].cost for i in 1:pop.n])` (here any `perm` meeting the `sortperm`
contract), `actual_topn = min(topn, pop.n)`, and `Population(pop.members[best_idx[1:actual_topn]])`
(the population's own members, `n = length`). `1:k` is empty for `k ≤ 0`. -/
def bestSubPop {ι : Type} (members : List ι) (perm : List Nat) (topn : Int) : Jl (List ι × Nat) := do
  let k := (min topn (members.length : Int)).toNat
  let sel ← (perm.take k).mapM (at1 members)
  pure (sel, sel.length)

/-- Property `pop-best-sub-pop`: `best_sub_pop(pop; topn)` returns `max(0, min(topn, pop.n))`
of the population's own members, ranked by `member.cost` (`_get_cost`): no returned member's
cost is `isless`-greater than any member left out (NaN costs come last), and the returned
members are distinct positions of the population. -/
def best_sub_pop_spec : Prop :=
  ∀ (ι : Type) (members : List ι) (cost : ι → JF) (perm : List Nat) (topn : Int),
    SortPerm (members.map (getCost cost)) perm →
    ∃ sel, bestSubPop members perm topn = .ok (sel, sel.length) ∧
      sel.length = (min topn (members.length : Int)).toNat ∧
      (∀ i ∈ perm.take (min topn (members.length : Int)).toNat,
        ∀ j, 1 ≤ j → j ≤ members.length → j ∉ perm.take (min topn (members.length : Int)).toNat →
          ∀ a b, members[i - 1]? = some a → members[j - 1]? = some b →
            isless (getCost cost b) (getCost cost a) = false) ∧
      sel = (perm.take (min topn (members.length : Int)).toNat).filterMap fun i => members[i - 1]?

theorem mapM_at1_filterMap {α : Type} (xs : List α) :
    ∀ (is : List Nat), (∀ i ∈ is, 1 ≤ i ∧ i ≤ xs.length) →
      is.mapM (at1 xs) = .ok (is.filterMap fun i => xs[i - 1]?) := by
  intro is
  induction is with
  | nil => intro _; rfl
  | cons i is ih =>
    intro h
    have hi := h i (by simp)
    rw [List.mapM_cons, at1_ok xs i hi.1 hi.2, ih (fun x hx => h x (by simp [hx]))]
    simp [List.getElem?_eq_getElem (show i - 1 < xs.length by omega)]
    rfl

theorem best_sub_pop_spec_holds : best_sub_pop_spec := by
  intro ι members cost perm topn ⟨hperm, hsorted⟩
  have hmem : ∀ i, i ∈ perm ↔ 1 ≤ i ∧ i ≤ members.length := by
    intro i
    rw [hperm.mem_iff, List.mem_range'_1]
    simp; omega
  have hlenp : perm.length = members.length := by simpa using hperm.length_eq
  obtain ⟨k, hk⟩ : ∃ k, k = (min topn (members.length : Int)).toNat := ⟨_, rfl⟩
  rw [← hk]
  have hkle : k ≤ members.length := by omega
  have hb : ∀ i ∈ perm.take k, 1 ≤ i ∧ i ≤ members.length :=
    fun i hi => (hmem i).1 (List.mem_of_mem_take hi)
  have hsel := mapM_at1_filterMap members (perm.take k) hb
  have hlsel : ((perm.take k).filterMap fun i => members[i - 1]?).length = k := by
    obtain ⟨smp, hs, hl, -⟩ := mapM_at1 members (perm.take k) hb
    rw [hsel] at hs
    cases hs
    rw [hl]; simp; omega
  refine ⟨(perm.take k).filterMap fun i => members[i - 1]?, ?_, hlsel, ?_, rfl⟩
  · simp only [bestSubPop]; rw [← hk, hsel]; rfl
  · intro i hi j hj1 hj2 hj a b ha hb'
    have hjd : j ∈ perm.drop k := by
      have hjp := (hmem j).2 ⟨hj1, hj2⟩
      rw [← List.take_append_drop k perm, List.mem_append] at hjp
      exact hjp.resolve_left hj
    rw [← List.take_append_drop k perm, List.pairwise_append] at hsorted
    have := hsorted.2.2 i hi j hjd
    have hi' := hb i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, ha, hb', Option.map_some,
      Option.getD_some] at this
    exact this

/-! ## Satisfiable preconditions -/

example : (∀ x ∈ [3, 5], x < 6) ∧
    SortPerm ([JF.fin 2, .nan, .fin 1].map (getCost id)) [3, 1, 2] := by
  refine ⟨by decide, ?_, by decide⟩
  decide

end SymReg.Population
