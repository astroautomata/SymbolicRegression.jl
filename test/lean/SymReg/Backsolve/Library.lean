import SymReg.Backsolve.EvalInverse
import SymReg.Backsolve.Fit
import SymReg.Options.Constructor
import DynExpr.NodeBase.TreeOps

/-!
Model of the library, weighted-sum and driver parts of `src/Backsolve.jl`:
`configured_backsolve`, `weighted_sum_costs`, `combine_trees_weighted_sum`,
`_has_weighted_sum_operators`, `build_basis_library` (with `BasisLibrary`),
`prepare_backsolve_setup` (with `BacksolveSetup`) and `fit_sparse_expression`.

Trees are DE's pure `Tree JF`; `compute_complexity(tree, options)` is an arbitrary function
`cx`, `eval_tree_array(tree, dataset.X, options.operators)` an arbitrary function `ev`
returning the values and the success flag, and `hash` an arbitrary function. The binary
operator list `options.operators.binops` is a list of the operators of `Inverse.lean`, where
`op === (+)` is `.b .plus` and `op === (*)` is `.b .mult`. Fitted targets and evaluated
columns enter the numerical core of `Fit.lean` as exact rationals (the finite values that the
code admits; a target entry of a row that the mask excludes is never read, so it is modelled
by an arbitrary rational). The `BacksolveMutation` fields are those of `src/Mutations.jl:113-118`.
-/

namespace SymReg.Backsolve
open DynExpr DynExpr.NodeBase SymReg.Options

/-! ## `configured_backsolve` -/

/-- `mutation isa BacksolveMutation && weight > 0.0` (`src/Backsolve.jl:14`). -/
def enabledBacksolve (p : MutationInstance × JF) : Bool :=
  p.1.kind == .backsolve && jlt (.fin 0) p.2

/-- The `configured_backsolve` error message (`src/Backsolve.jl:16`). -/
def notEnabledMsg : String := "BacksolveMutation is not enabled in `options.mutations`."

/-- `configured_backsolve(options)` (`src/Backsolve.jl:13-17`) on `options.mutations`. -/
def configuredBacksolve : List (MutationInstance × JF) → Jl MutationInstance
  | [] => throw (.argumentError notEnabledMsg)
  | p :: rest => if enabledBacksolve p then pure p.1 else configuredBacksolve rest

/-- `configured_backsolve` returns the first `BacksolveMutation` with a positive weight
(`NaN` is not positive) and throws `ArgumentError` exactly when there is none
(`src/Backsolve.jl:13-17`). -/
def configuredSpec : Prop :=
  ∀ ms : List (MutationInstance × JF),
    (∀ m, configuredBacksolve ms = .ok m ↔ ∃ pre w rest, ms = pre ++ (m, w) :: rest ∧
      enabledBacksolve (m, w) = true ∧ ∀ p ∈ pre, enabledBacksolve p = false) ∧
    (∀ e, configuredBacksolve ms = .error e ↔
      e = .argumentError notEnabledMsg ∧ ∀ p ∈ ms, enabledBacksolve p = false)

theorem configured_fwd : ∀ (ms : List (MutationInstance × JF)) (m : MutationInstance),
    configuredBacksolve ms = .ok m → ∃ pre w rest, ms = pre ++ (m, w) :: rest ∧
      enabledBacksolve (m, w) = true ∧ ∀ p ∈ pre, enabledBacksolve p = false := by
  intro ms
  induction ms with
  | nil => intro m h; cases h
  | cons p rest ih =>
    intro m h
    unfold configuredBacksolve at h
    by_cases hp : enabledBacksolve p = true
    · rw [if_pos hp] at h
      cases h
      exact ⟨[], p.2, rest, rfl, hp, by simp⟩
    · rw [if_neg hp] at h
      obtain ⟨pre, w, r, h1, h2, h3⟩ := ih m h
      refine ⟨p :: pre, w, r, by simp [h1], h2, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simpa using hp
      · exact h3 q hq

theorem configured_bwd : ∀ (pre : List (MutationInstance × JF)) (m : MutationInstance) (w : JF)
    (rest : List (MutationInstance × JF)), enabledBacksolve (m, w) = true →
    (∀ p ∈ pre, enabledBacksolve p = false) → configuredBacksolve (pre ++ (m, w) :: rest) = .ok m := by
  intro pre
  induction pre with
  | nil => intro m w rest h _; simp [configuredBacksolve, h, pure, Except.pure]
  | cons q pre ih =>
    intro m w rest h hpre
    simp only [List.cons_append, configuredBacksolve]
    rw [if_neg (by simp [hpre q (by simp)])]
    exact ih m w rest h (fun p hp => hpre p (by simp [hp]))

theorem configured_err : ∀ (ms : List (MutationInstance × JF)) (e : JlError),
    configuredBacksolve ms = .error e ↔
      e = .argumentError notEnabledMsg ∧ ∀ p ∈ ms, enabledBacksolve p = false := by
  intro ms
  induction ms with
  | nil => intro e; simp [configuredBacksolve, throw, throwThe, MonadExceptOf.throw, Except.error.injEq]; exact eq_comm
  | cons p rest ih =>
    intro e
    unfold configuredBacksolve
    by_cases hp : enabledBacksolve p = true
    · rw [if_pos hp]
      simp [pure, Except.pure, hp]
    · rw [if_neg hp, ih e]
      simp only [List.mem_cons, forall_eq_or_imp]
      simp at hp
      simp [hp]

theorem configuredSpec_holds : configuredSpec := by
  intro ms
  refine ⟨fun m => ⟨configured_fwd ms m, ?_⟩, configured_err ms⟩
  rintro ⟨pre, w, rest, rfl, h1, h2⟩
  exact configured_bwd pre m w rest h1 h2

example : configuredBacksolve [({ kind := .backsolve }, .fin 1)] = .ok { kind := .backsolve } ∧
    configuredBacksolve [] = .error (.argumentError notEnabledMsg) := ⟨rfl, rfl⟩

/-! ## Weighted sums -/

/-- `op === (+)`. -/
def isPlus : Op → Bool
  | .b .plus => true
  | _ => false

/-- `op === (*)`. -/
def isMult : Op → Bool
  | .b .mult => true
  | _ => false

/-- `findfirst(p, binops)`, one-based. -/
def findIdx1 (p : Op → Bool) (bin : List Op) : Option Nat := (bin.findIdx? p).map (· + 1)

/-- `_has_weighted_sum_operators(options)` (`src/Backsolve.jl:381-383`). -/
def hasWS (bin : List Op) : Bool := bin.any isPlus && bin.any isMult

/-- `something(nothing)` throws `ArgumentError`. -/
def somethingMsg : String := "No value arguments present"

-- Source: src/Backsolve.jl:158-169
-- add_idx = something(findfirst(op -> op === (+), options.operators.binops))
-- mult_idx = something(findfirst(op -> op === (*), options.operators.binops))
--
-- c1 = constructorof(N)(; val=one(T))
-- c2 = constructorof(N)(; val=one(T))
-- constant_cost = compute_complexity(c1, options)
-- mult_cost =
--     compute_complexity(constructorof(N)(; op=mult_idx, children=(c1, c2)), options) -
--     2 * constant_cost
-- join_cost =
--     compute_complexity(constructorof(N)(; op=add_idx, children=(c1, c2)), options) -
--     2 * constant_cost
/-- Operator lookup and per-addend costs: `(join_cost, addend_overhead)`. -/
def wscHeader (cx : Tree JF → Int) (bin : List Op) : Jl (Int × Int) :=
  match findIdx1 isPlus bin with
  | none => throw (.argumentError somethingMsg)
  | some addIdx =>
    match findIdx1 isMult bin with
    | none => throw (.argumentError somethingMsg)
    | some multIdx =>
      let c1 : Tree JF := .const (.fin 1)
      let c2 : Tree JF := .const (.fin 1)
      let cc := cx c1
      let mc := cx (.branch multIdx [c1, c2]) - 2 * cc
      let jc := cx (.branch addIdx [c1, c2]) - 2 * cc
      pure (jc, cc + mc)

/-- `weighted_sum_costs(terms, tree_prototype, options)` (`src/Backsolve.jl:150-177`). -/
def weightedSumCosts (cx : Tree JF → Int) (bin : List Op) (terms : List (Tree JF)) :
    Jl (List Int × Int × Int) :=
  wscHeader cx bin >>= fun h => pure (terms.map (fun t => cx t + h.2), h.1, h.2)

-- Source: src/Backsolve.jl:428-449
-- R = typeof(float(real(zero(T))))
-- tol = eps(R)
-- active_indices = findall(abs.(coefficients) .> tol * 100)
-- isempty(active_indices) && return nothing
-- active_trees = trees[active_indices]
-- active_coeffs = coefficients[active_indices]
-- if abs(coeff - one(T)) < tol * 100
--     return tree
-- end
/-- Dispatched operations for the coefficient type, including the result of
`eps(R) * 100` in its real component type. -/
structure CoefficientOps (T : Type) where
  cutoff : JF
  magnitude : T → JF
  subOne : T → T

def coefficientTolerance (p : SymReg.Loss.LossPrecision) : JF :=
  let eps : Rat := match p with
    | .float16 => 1 / 1024
    | .float32 => 1 / 8388608
    | .float64 => epsF
  p.round (.fin (eps * 100))

def realCoefficients (p : SymReg.Loss.LossPrecision) : CoefficientOps JF where
  cutoff := coefficientTolerance p
  magnitude
    | .fin q => .fin (rabs q)
    | .negInf => .posInf
    | x => x
  subOne x := p.round (x - .fin 1)

def weightedTerm {T : Type} (ops : CoefficientOps T) (multIdx : Nat) (t : Tree T) (c : T) :
    Tree T :=
  if jlt (ops.magnitude (ops.subOne c)) ops.cutoff then t
  else .branch multIdx [.const c, t]

/-- Gather the active tree positions before constructing any new nodes. -/
def activeTerms {T : Type} (ops : CoefficientOps T) (trees : List (Tree T)) (coeffs : List T) :
    Jl (List (Tree T × T)) :=
  let active := coeffs.zipIdx.filter (fun (c, _) => jlt ops.cutoff (ops.magnitude c))
  active.mapM fun (c, i) =>
    match trees[i]? with
    | none => .error .boundsError
    | some t => .ok (t, c)

-- Source: src/Backsolve.jl:421-471
def combine {T : Type} (ops : CoefficientOps T) (bin : List Op) (trees : List (Tree T)) (coeffs : List T) :
    Jl (Option (Tree T)) :=
  if !hasWS bin then pure none
  else
    match findIdx1 isPlus bin, findIdx1 isMult bin with
    | some addIdx, some multIdx => do
      let active ← activeTerms ops trees coeffs
      match active.map (fun (t, c) => weightedTerm ops multIdx t c) with
      | [] => pure none
      | w :: ws => pure (some (ws.foldl (fun acc t => .branch addIdx [acc, t]) w))
    | _, _ => throw (.argumentError somethingMsg)

/-- `compute_complexity` adds node weights: constants cost `cc`, a binary node `w op` plus its
children (the default and `ComplexityMapping` complexities; `src/Complexity.jl:25-70`). -/
def Additive (cx : Tree JF → Int) (cc : Int) (w : Nat → Int) : Prop :=
  (∀ v, cx (.const v) = cc) ∧ ∀ o a b, cx (.branch o [a, b]) = w o + cx a + cx b

theorem foldl_cx (cx : Tree JF → Int) (cc : Int) (w : Nat → Int) (hA : Additive cx cc w) (a : Nat) :
    ∀ (ws : List (Tree JF)) (acc : Tree JF),
      cx (ws.foldl (fun acc t => .branch a [acc, t]) acc) = cx acc + (ws.map (fun t => w a + cx t)).sum := by
  intro ws
  induction ws with
  | nil => intro acc; simp
  | cons t ws ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, hA.2]
    omega

theorem sum_map_add {A : Type} (k : Int) (f : A → Int) :
    ∀ l : List A, (l.map (fun p => k + f p)).sum = (l.map f).sum + k * l.length := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    grind

/-- `weighted_sum_costs` prices every addend of `combine_trees_weighted_sum` exactly
(`src/Backsolve.jl:150-177,394-457`): with an additive complexity, `join_cost` is the weight of
`+`, `addend_overhead` the constant's cost plus the weight of `*`, every term cost is the term's
complexity plus that overhead, and the combined tree's complexity is the sum of the active
terms' costs, minus the overhead for every coefficient within `100 eps` of one (which is
dropped), plus one `join_cost` per additional term. -/
def weightedSumCostsExact : Prop :=
  ∀ (cx : Tree JF → Int) (cc : Int) (w : Nat → Int) (bin : List Op) (terms : List (Tree JF))
    (ops : CoefficientOps JF) (coeffs : List JF) (tc : List Int) (jc ov : Int) (u : Tree JF),
    Additive cx cc w → weightedSumCosts cx bin terms = .ok (tc, jc, ov) →
    (∃ addIdx multIdx, findIdx1 isPlus bin = some addIdx ∧ findIdx1 isMult bin = some multIdx ∧
      jc = w addIdx ∧ ov = cc + w multIdx) ∧
    tc = terms.map (fun t => cx t + ov) ∧
    (∀ active, activeTerms ops terms coeffs = .ok active → combine ops bin terms coeffs = .ok (some u) →
      cx u = (active.map (fun p =>
          cx p.1 + ov - (if jlt (ops.magnitude (ops.subOne p.2))
            ops.cutoff then ov else 0))).sum +
        jc * ((active.length : Int) - 1))

theorem weightedSumCostsExact_holds : weightedSumCostsExact := by
  intro cx cc w bin terms ops coeffs tc jc ov u hA hw
  unfold weightedSumCosts wscHeader at hw
  cases ha : findIdx1 isPlus bin with
  | none => rw [ha] at hw; cases hw
  | some addIdx =>
    cases hm : findIdx1 isMult bin with
    | none => rw [ha, hm] at hw; cases hw
    | some multIdx =>
      rw [ha, hm] at hw
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨h1, h2, h3⟩ := hw
      have hjc : jc = w addIdx := by rw [← h2, hA.2, hA.1]; omega
      have hov : ov = cc + w multIdx := by rw [← h3, hA.2, hA.1]; omega
      refine ⟨⟨addIdx, multIdx, rfl, rfl, hjc, hov⟩, by rw [← h1, h3], ?_⟩
      intro act ha' hc
      have hW : ∀ p : Tree JF × JF, cx (weightedTerm ops multIdx p.1 p.2) =
          cx p.1 + ov - (if jlt (ops.magnitude (ops.subOne p.2))
            ops.cutoff then ov else 0) := by
        intro p
        unfold weightedTerm
        by_cases hb : jlt (ops.magnitude (ops.subOne p.2)) ops.cutoff = true
        · simp only [hb, ↓reduceIte]; omega
        · simp only [hb, Bool.false_eq_true, ite_false, hA.2, hA.1]; omega
      unfold combine at hc
      have hws : hasWS bin = true := by
        cases hh : hasWS bin
        · rw [hh] at hc; cases hc
        · rfl
      rw [hws, ha, hm] at hc
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ha', bind, Except.bind,
        pure, Except.pure] at hc
      match act, hc with
      | p :: rest, hc =>
        simp only [List.map_cons, Except.ok.injEq, Option.some.injEq] at hc
        subst hc
        rw [foldl_cx cx cc w hA addIdx, hW]
        simp only [List.map_map, List.map_cons, List.sum_cons, List.length_cons]
        have := sum_map_add (w addIdx) (fun p => cx (weightedTerm ops multIdx p.1 p.2)) rest
        simp only [Function.comp_def] at this ⊢
        rw [this]
        simp only [hW]
        rw [hjc]
        push_cast
        rw [show ((rest.length : Int) + 1 - 1) = rest.length by omega]
        omega

/-- `combine_trees_weighted_sum` returns `nothing` exactly when `+` or `*` is missing or no
coefficient exceeds `100 eps` in magnitude (`src/Backsolve.jl:411-419`). -/
def combineNone : Prop :=
  ∀ (T : Type) (ops : CoefficientOps T) (bin : List Op) (terms : List (Tree T)) (coeffs : List T),
    (combine ops bin terms coeffs = .ok none ↔ hasWS bin = false ∨
      ∀ c ∈ coeffs, jlt ops.cutoff (ops.magnitude c) = false) ∧
    (combine ops bin terms coeffs = .error .boundsError ↔ hasWS bin = true ∧
      ∃ (i : Nat) (c : T), coeffs[i]? = some c ∧ terms.length ≤ i ∧
        jlt ops.cutoff (ops.magnitude c) = true)

theorem findIdx1_isSome (p : Op → Bool) (bin : List Op) :
    (findIdx1 p bin).isSome = bin.any p := by
  unfold findIdx1
  rw [Option.isSome_map]
  induction bin with
  | nil => rfl
  | cons o bin ih =>
    rw [List.findIdx?_cons, List.any_cons]
    cases hp : p o
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_map, Bool.false_or]; exact ih
    · simp

private theorem activeTermsFacts {T : Type} (terms : List (Tree T)) (active : List (T × Nat)) :
    let picked := active.mapM fun (c, i) =>
      match terms[i]? with
      | none => (.error .boundsError : Jl _)
      | some t => .ok (t, c)
    (picked = .ok [] ↔ active = []) ∧
    (picked = .error .boundsError ↔ ∃ p ∈ active, terms.length ≤ p.2) ∧
    (picked = .ok [] ∨ picked = .error .boundsError ∨ ∃ p rest, picked = .ok (p :: rest)) := by
  induction active with
  | nil => simp [pure, Except.pure]
  | cons p ps ih =>
    obtain ⟨c, i⟩ := p
    simp only [List.mapM_cons]
    cases h : terms[i]? with
    | none =>
      have hi := List.getElem?_eq_none_iff.mp h
      simp [h, bind, Except.bind, List.mem_cons, hi]
    | some t =>
      have hi := (List.getElem?_eq_some_iff.mp h).1
      rcases ih with ⟨_, herr, hempty | he | ⟨p, rest, hp⟩⟩
      · simp [h, hempty, bind, Except.bind, pure, Except.pure, List.mem_cons, show ¬ terms.length ≤ i by omega, ← herr]
      · simp [h, he, bind, Except.bind, List.mem_cons, show ¬ terms.length ≤ i by omega, ← herr]
      · simp [h, hp, bind, Except.bind, pure, Except.pure, List.mem_cons, show ¬ terms.length ≤ i by omega, ← herr]

theorem combineNone_holds : combineNone := by
  intro T ops bin terms coeffs
  unfold combine
  cases hws : hasWS bin
  · simp [pure, Except.pure]
  · have h1 := findIdx1_isSome isPlus bin
    have h2 := findIdx1_isSome isMult bin
    have ⟨hp, hm⟩ : bin.any isPlus = true ∧ bin.any isMult = true := by
      simpa only [hasWS, Bool.and_eq_true] using hws
    cases ha : findIdx1 isPlus bin with
    | none => simp [ha, hp] at h1
    | some a =>
      cases hb : findIdx1 isMult bin with
      | none => simp [hb, hm] at h2
      | some m =>
        let active := coeffs.zipIdx.filter (fun (c, _) => jlt ops.cutoff (ops.magnitude c))
        have facts := activeTermsFacts terms active
        change (activeTerms ops terms coeffs = .ok [] ↔ active = []) ∧
          (activeTerms ops terms coeffs = .error .boundsError ↔ ∃ p ∈ active, terms.length ≤ p.2) ∧
          (activeTerms ops terms coeffs = .ok [] ∨ activeTerms ops terms coeffs = .error .boundsError ∨
            ∃ p rest, activeTerms ops terms coeffs = .ok (p :: rest)) at facts
        obtain ⟨hn, he, hr⟩ := facts
        have empty : active = [] ↔ ∀ c ∈ coeffs,
            jlt ops.cutoff (ops.magnitude c) = false := by
          simp only [active, List.filter_eq_nil_iff, List.mem_zipIdx_iff_getElem?, Bool.not_eq_true]
          constructor
          · intro h c hc
            obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
            exact h (c, i) (by simpa using hi)
          · intro h p hp
            exact h p.1 (List.mem_iff_getElem?.mpr ⟨p.2, by simpa using hp⟩)
        have bad : (∃ p ∈ active, terms.length ≤ p.2) ↔
            ∃ (i : Nat) (c : T), coeffs[i]? = some c ∧ terms.length ≤ i ∧
              jlt ops.cutoff (ops.magnitude c) = true := by
          simp only [active, List.mem_filter, List.mem_zipIdx_iff_getElem?]
          constructor
          · rintro ⟨⟨c, i⟩, ⟨hx, ha⟩, hi⟩
            exact ⟨i, c, by simpa using hx, hi, ha⟩
          · rintro ⟨i, c, hx, hi, ha⟩
            exact ⟨(c, i), ⟨by simpa using hx, ha⟩, hi⟩
        rcases hr with hn' | he' | ⟨p, rest, hs⟩
        · simp [hn', bind, Except.bind, pure, Except.pure, ← empty, ← bad, ← hn, ← he]
        · simp [he', bind, Except.bind, ← empty, ← bad, ← hn, ← he]
        · simp [hs, bind, Except.bind, pure, Except.pure, ← empty, ← bad, ← hn, ← he]

/-! ## The basis library -/

/-- A population member: its loss and tree. -/
structure Member where
  loss : JF
  tree : Tree JF

/-- `isless(a, b)` on `Float64`: `NaN` sorts after every other value. -/
def jisless : JF → JF → Bool
  | .nan, _ => false
  | _, .nan => true
  | a, b => jlt a b

/-- The seed terms (`src/Backsolve.jl:348-354`): the constant `1` and the features
`1:nfeatures`. -/
def baseTerms (nf : Int) : List (Tree JF) :=
  .const (.fin 1) :: (List.range nf.toNat).map (fun i => .feature (i + 1))

/-- The population subtrees (`src/Backsolve.jl:356-363`): `collect` (preorder) of every tree of
the `top_k` lowest-loss members, after a stable `sort` by `isless` on the loss. -/
def popSubtrees (topK : Int) : Option (List Member) → List (Tree JF)
  | none => []
  | some ms =>
    ((ms.mergeSort (fun a b => !jisless b.loss a.loss)).take (min topK ms.length).toNat).flatMap
      (fun m => preorder m.tree)

/-- The library candidates (`src/Backsolve.jl:345-368`): the seed terms, then the first
population subtrees, up to `max_library_size` terms in all. -/
def candidates (nf maxSize topK : Int) (pop : Option (List Member)) : List (Tree JF) :=
  baseTerms nf ++ (popSubtrees topK pop).take
    (min ((popSubtrees topK pop).length : Int) (maxSize - (baseTerms nf).length)).toNat

/-- The evaluated columns and the hash dictionary. -/
structure LibState where
  terms : List (Tree JF)
  cols : List (List JF)
  hmap : Nat → Nat

/-- `eval_tree_array` succeeded with no `NaN` or `Inf` (`src/Backsolve.jl:377`). -/
def finiteEval (r : List JF × Bool) : Bool := r.2 && r.1.all JF.valid

-- Source: src/Backsolve.jl:369–390
-- for term in candidate_terms
--     col, success = eval_tree_array(term, dataset.X, options.operators)
--     if success && !any(isnan, col) && !any(isinf, col)
--         hv = hash(col)
--         j = get(seen_columns, hv, 0)
--         if j == 0 || evaluated_cols[j] != col
--             push!(valid_terms, term)
--             push!(evaluated_cols, col)
--             seen_columns[hv] = length(evaluated_cols)
--         end
--     end
-- end
abbrev BasisEval := Tree JF → Jl (List JF × Bool)

def addTerms (ev : BasisEval) (hash : List JF → Nat) :
    List (Tree JF) → LibState → Jl LibState
  | [], s => pure s
  | t :: ts, s => ev t >>= fun r =>
    if finiteEval r then
      let v := r.1
      let j := s.hmap (hash v)
      if j ≠ 0 ∧ s.cols.getD (j - 1) [] = v then addTerms ev hash ts s
      else addTerms ev hash ts
        ⟨s.terms ++ [t], s.cols ++ [v],
          fun k => if k = hash v then s.cols.length + 1 else s.hmap k⟩
    else addTerms ev hash ts s

/-- `build_basis_library` (`src/Backsolve.jl:296–392`), with the constructor shape
check (`src/Backsolve.jl:63–71`). -/
def buildLibrary (ev : BasisEval) (hash : List JF → Nat) (nf maxSize topK : Int)
    (pop : Option (List Member)) : Jl (List (Tree JF) × List (List JF) × Nat) :=
  if maxSize < 1 + nf then
    .error (.argumentError "build_basis_library requires max_library_size >= 1 + nfeatures")
  else do
    let cands := candidates nf maxSize topK pop
    let s ← addTerms ev hash cands ⟨[], [], fun _ => 0⟩
    if s.cols.length ≠ s.terms.length then
      .error (.argumentError "BasisLibrary requires one evaluated_terms column per term.")
    else pure (s.terms, s.cols, cands.length)


theorem finiteEval_iff (r : List JF × Bool) :
    finiteEval r = true ↔ r.2 = true ∧ ∀ v ∈ r.1, v.valid = true := by
  simp [finiteEval, List.all_eq_true]

/-- Ordered candidate decisions. The dictionary records the most recent retained
column at each hash, so a collision alone cannot skip a distinct column. -/
inductive BasisRun (ev : BasisEval) (hash : List JF → Nat) :
    List (Tree JF) → LibState → Jl LibState → Prop
  | stop (s) : BasisRun ev hash [] s (.ok s)
  | raises {t ts s e} : ev t = .error e →
      BasisRun ev hash (t :: ts) s (.error e)
  | skipBad {t ts s v r} : ev t = .ok v → finiteEval v = false →
      BasisRun ev hash ts s r → BasisRun ev hash (t :: ts) s r
  | skipDuplicate {t ts s v r j} : ev t = .ok (v, true) →
      (∀ a ∈ v, a.valid = true) → s.hmap (hash v) = j → j ≠ 0 →
      s.cols.getD (j - 1) [] = v →
      BasisRun ev hash ts s r → BasisRun ev hash (t :: ts) s r
  | keep {t ts s v r} : ev t = .ok (v, true) → (∀ a ∈ v, a.valid = true) →
      (s.hmap (hash v) = 0 ∨ s.cols.getD (s.hmap (hash v) - 1) [] ≠ v) →
      BasisRun ev hash ts
        ⟨s.terms ++ [t], s.cols ++ [v],
          fun k => if k = hash v then s.cols.length + 1 else s.hmap k⟩ r →
      BasisRun ev hash (t :: ts) s r

theorem basisRun_outcome {ev hash ts s r} (h : BasisRun ev hash ts s r) :
    addTerms ev hash ts s = r := by
  induction h with
  | stop => rfl
  | raises he => simp [addTerms, he, bind, Except.bind]
  | skipBad he hf _ ih => simpa [addTerms, he, hf, bind, Except.bind] using ih
  | @skipDuplicate t ts s v r j he hv hj hn heq _ ih =>
    have hf := (finiteEval_iff (v, true)).mpr ⟨rfl, hv⟩
    simp only [addTerms, he, hf, bind, Except.bind, ite_true, hj]
    rw [if_pos ⟨hn, heq⟩]
    exact ih
  | @keep t ts s v r he hv hk _ ih =>
    have hf := (finiteEval_iff (v, true)).mpr ⟨rfl, hv⟩
    simp only [addTerms, he, hf, bind, Except.bind, ite_true]
    rw [if_neg (fun h => hk.elim (fun hz => h.1 hz) (fun hn => hn h.2))]
    exact ih

theorem basisRun_exists (ev : BasisEval) (hash : List JF → Nat) :
    ∀ ts s, ∃ r, BasisRun ev hash ts s r
  | [], s => ⟨.ok s, .stop s⟩
  | t :: ts, s => by
    cases he : ev t with
    | error e => exact ⟨.error e, .raises he⟩
    | ok v =>
      by_cases hf : finiteEval v = true
      · obtain ⟨hcomplete, hfinite⟩ := (finiteEval_iff _).mp hf
        obtain ⟨col, complete⟩ := v
        simp only at hcomplete hfinite
        subst complete
        by_cases hd : s.hmap (hash col) ≠ 0 ∧
            s.cols.getD (s.hmap (hash col) - 1) [] = col
        · obtain ⟨r, hr⟩ := basisRun_exists ev hash ts s
          exact ⟨r, .skipDuplicate he hfinite rfl hd.1 hd.2 hr⟩
        · have hn : s.hmap (hash col) = 0 ∨
              s.cols.getD (s.hmap (hash col) - 1) [] ≠ col := by
              by_cases hz : s.hmap (hash col) = 0
              · exact .inl hz
              · exact .inr (fun hh => hd ⟨hz, hh⟩)
          obtain ⟨r, hr⟩ := basisRun_exists ev hash ts _
          exact ⟨r, .keep he hfinite hn hr⟩
      · obtain ⟨r, hr⟩ := basisRun_exists ev hash ts s
        exact ⟨r, .skipBad he (by simpa using hf) hr⟩

theorem BasisRun.shape {ev hash ts s t}
    (h : BasisRun ev hash ts s (.ok t)) (hs : s.cols.length = s.terms.length) :
    t.cols.length = t.terms.length := by
  generalize e : Except.ok t = r at h
  induction h generalizing t with
  | stop => cases e; exact hs
  | raises => cases e
  | skipBad _ _ _ ih | skipDuplicate _ _ _ _ _ _ ih => exact ih hs e
  | keep _ _ _ _ ih => apply ih _ e; simp [hs]

def basisLibrary : Prop :=
  ∀ (ev : BasisEval) (hash : List JF → Nat) (nf maxSize topK : Int)
    (pop : Option (List Member)),
    (maxSize < 1 + nf → buildLibrary ev hash nf maxSize topK pop =
      .error (.argumentError "build_basis_library requires max_library_size >= 1 + nfeatures")) ∧
    (1 + nf ≤ maxSize →
      (∀ e, buildLibrary ev hash nf maxSize topK pop = .error e ↔
        BasisRun ev hash (candidates nf maxSize topK pop) ⟨[], [], fun _ => 0⟩ (.error e)) ∧
      ∀ ts cs n, buildLibrary ev hash nf maxSize topK pop = .ok (ts, cs, n) ↔
        n = (candidates nf maxSize topK pop).length ∧
        ∃ s, BasisRun ev hash (candidates nf maxSize topK pop) ⟨[], [], fun _ => 0⟩ (.ok s) ∧
          s.terms = ts ∧ s.cols = cs)
theorem candidates_length (nf maxSize topK : Int) (pop : Option (List Member)) (hnf : 0 ≤ nf)
    (h : 1 + nf ≤ maxSize) : ((candidates nf maxSize topK pop).length : Int) ≤ maxSize := by
  unfold candidates
  have hb : ((baseTerms nf).length : Int) = 1 + nf := by
    simp only [baseTerms, List.length_cons, List.length_map, List.length_range]
    push_cast
    rw [Int.toNat_of_nonneg hnf]
    omega
  generalize popSubtrees topK pop = S
  rw [List.length_append, List.length_take]
  generalize (baseTerms nf).length = B at hb ⊢
  have h4 : ((min (S.length : Int) (maxSize - B)).toNat : Int) = min (S.length : Int) (maxSize - B) :=
    Int.toNat_of_nonneg (by omega)
  generalize (min (S.length : Int) (maxSize - B)).toNat = k at h4 ⊢
  have hm : min k S.length ≤ k := Nat.min_le_left _ _
  omega

theorem basisLibrary_holds : basisLibrary := by
  intro ev hash nf maxSize topK pop
  refine ⟨fun h => by simp [buildLibrary, h], fun h => ?_⟩
  let cand := candidates nf maxSize topK pop
  let start : LibState := ⟨[], [], fun _ => 0⟩
  obtain ⟨r, hr⟩ := basisRun_exists ev hash cand start
  have he := basisRun_outcome hr
  have hn : ¬ maxSize < 1 + nf := by omega
  simp only [buildLibrary, if_neg hn]
  change (∀ _, (_ >>= _) = _ ↔ _) ∧ ∀ _ _ _, (_ >>= _) = _ ↔ _
  constructor
  · intro e
    constructor
    · intro hh
      cases r with
      | error er =>
        change (addTerms ev hash cand start >>= _) = .error e at hh
        rw [he] at hh
        cases hh
        exact hr
      | ok s =>
        change (addTerms ev hash cand start >>= _) = .error e at hh
        rw [he] at hh
        simp [bind, Except.bind, hr.shape rfl, pure, Except.pure] at hh
    · intro hh
      change (addTerms ev hash cand start >>= _) = .error e
      rw [basisRun_outcome hh]
      rfl
  · intro ts cs n
    constructor
    · intro hh
      cases r with
      | error er =>
        change (addTerms ev hash cand start >>= _) = .ok (ts, cs, n) at hh
        rw [he] at hh
        cases hh
      | ok s =>
        change (addTerms ev hash cand start >>= _) = .ok (ts, cs, n) at hh
        rw [he] at hh
        simp [bind, Except.bind, hr.shape rfl, pure, Except.pure] at hh
        obtain ⟨rfl, rfl, rfl⟩ := hh
        exact ⟨rfl, s, hr, rfl, rfl⟩
    · rintro ⟨rfl, s, hrel, rfl, rfl⟩
      change (addTerms ev hash cand start >>= _) = .ok (s.terms, s.cols, cand.length)
      rw [basisRun_outcome hrel]
      simp [cand, bind, Except.bind, hrel.shape rfl, pure, Except.pure]

/-! ## `fit_sparse_expression` -/

/-- The functions `fit_sparse_expression` depends on: the binary operators, `eval_tree_array`
on the dataset, `compute_complexity`, `hash`, `sqrt`, and the Cholesky solve. -/
structure FitEnv where
  bin : List Op
  ev : BasisEval
  cx : Tree JF → Int
  hash : List JF → Nat
  sq : Rat → Rat
  ch : Chol

/-- The `BacksolveMutation` fields (`src/Mutations.jl:113-118`). -/
structure BacksolveCfg where
  maxLibrarySize : Int
  maxTerms : Int
  minImprovement : Rat
  nodeAttempts : Int

/-- The value of a finite scalar. -/
def toRat : JF → Rat
  | .fin q => q
  | _ => 0

/-- `BacksolveSetup(basis, gram, term_costs, join_cost, addend_overhead)` (`src/Backsolve.jl:459-475`). -/
structure Setup where
  terms : List (Tree JF)
  cols : List (List JF)
  nEval : Nat
  gram : Mat
  tc : List Int
  join : Int
  ov : Int

/-- `prepare_backsolve_setup(...; max_library_size, top_k)` (`src/Backsolve.jl:477-509`). -/
def prepareSetup (E : FitEnv) (nf maxSize topK : Int) (pop : Option (List Member)) : Jl Setup :=
  buildLibrary E.ev E.hash nf maxSize topK pop >>= fun b =>
  weightedSumCosts E.cx E.bin b.1 >>= fun c =>
  pure ⟨b.1, b.2.1, b.2.2, gramOf (b.2.1.map (·.map toRat)), c.1, c.2.1, c.2.2⟩

/-- `count(valid_mask) < min(10, n_rows)` (`src/Backsolve.jl:577-580`). -/
def tooFewRows (mask : Option (List Bool)) (n : Nat) : Bool :=
  match mask with
  | some m => decide (m.count true < min 10 n)
  | none => false

/-- The extra term's values (`src/Backsolve.jl:597-604`): `some none` without an extra term,
`none` when its evaluation fails or is not finite (the fit returns `nothing`). -/
def extraVals (E : FitEnv) : Option (Tree JF) → Jl (Option (Option Vec))
  | none => pure (some none)
  | some e => do
    let r ← E.ev e
    pure (if finiteEval r then some (some (r.1.map toRat)) else none)

/-- `target_fit[.!valid_mask] .= extra_values[.!valid_mask]` (`src/Backsolve.jl:608-611`). -/
def replaceInvalid (m : List Bool) (t e : Vec) : Vec :=
  List.zipWith (fun b p => if b then p.1 else p.2) m (t.zip e)

/-- The Gram matrix extended by the extra column (`src/Backsolve.jl:635-643`). -/
def extendGram (base : Mat) (theta : List Vec) (e : Vec) : Mat :=
  List.zipWith (fun row th => row ++ [dotR th e]) base theta ++
    [theta.map (fun th => dotR th e) ++ [sumSq e]]

/-- `G`, `g` and `yy` of the fit (`src/Backsolve.jl:606-650`); `theta` is the list of library
columns and `gramS` the setup's Gram matrix. -/
def fitGram (theta : List Vec) (gramS : Option Mat) (target : Vec) (mask : Option (List Bool))
    (exv : Option Vec) : Mat × Vec × Rat :=
  if mask.isSome && exv.isNone then
    let m := mask.getD []
    let thM := theta.map (sel m)
    let tM := sel m target
    (gramOf thM, thM.map (fun c => dotR c tM), sumSq tM)
  else
    let tf := match mask, exv with
      | some m, some e => if m.all id then target else replaceInvalid m target e
      | _, _ => target
    let gfull := theta.map (fun c => dotR c tf)
    let base := gramS.getD (gramOf theta)
    match exv with
    | none => (base, gfull, sumSq tf)
    | some e => (extendGram base theta e, gfull ++ [dotR e tf], sumSq tf)

/-- `term_costs, join_cost` (`src/Backsolve.jl:654-665`). -/
def fitCosts (E : FitEnv) (terms : List (Tree JF)) (setup : Option Setup) (extra : Option (Tree JF)) :
    Jl (List Int × Int) :=
  match setup with
  | none => weightedSumCosts E.cx E.bin (terms ++ extra.toList) >>= fun r => pure (r.1, r.2.1)
  | some s => pure (match extra with
    | none => (s.tc, s.join)
    | some e => (s.tc ++ [E.cx e + s.ov], s.join))

/-- `max_complexity !== nothing && c > max_complexity`. -/
def overBudget (maxC : Option Int) (c : Int) : Bool :=
  match maxC with
  | some mc => decide (mc < c)
  | none => false

/-- The checks on the combined tree (`src/Backsolve.jl:692-704`): its complexity against
`max_complexity`, then a finite evaluation. -/
def finalCheck (E : FitEnv) (maxC : Option Int) (u : Tree JF) : Jl (Option (Tree JF)) :=
  if overBudget maxC (E.cx u) then pure none
  else do
    let r ← E.ev u
    pure (if finiteEval r then some u else none)

/-- The selection, combination and final checks (`src/Backsolve.jl:667-704`). -/
def fitTail (E : FitEnv) (cfg : BacksolveCfg) (termsFit : List (Tree JF)) (G : Mat) (g : Vec)
    (yy : Rat) (tc : List Int) (jc : Int) (maxC : Option Int) : Jl (Option (Tree JF)) :=
  let r := greedyGram E.sq E.ch G g yy tc jc maxC cfg.maxTerms cfg.minImprovement
  if r.2 then do
    match ← combine (realCoefficients .float64) E.bin termsFit (r.1.map JF.fin) with
    | none => pure none
    | some u => finalCheck E maxC u
  else pure none

/-- Everything after the basis library (`src/Backsolve.jl:594-704`). -/
def fitAfter (E : FitEnv) (cfg : BacksolveCfg) (terms : List (Tree JF)) (theta : List Vec)
    (gramS : Option Mat) (costs : Jl (List Int × Int)) (target : Vec) (mask : Option (List Bool))
    (extra : Option (Tree JF)) (maxC : Option Int) : Jl (Option (Tree JF)) := do
  match ← extraVals E extra with
  | none => pure none
  | some exv =>
    let G := fitGram theta gramS target mask exv
    let c ← costs
    fitTail E cfg (terms ++ extra.toList) G.1 G.2.1 G.2.2 c.1 c.2 maxC

/-- `fit_sparse_expression(tree_prototype, target_values, dataset, options, nfeatures;
backsolve_options, population_for_backsolve, valid_mask, setup, extra_term, max_complexity)`
(`src/Backsolve.jl:511-705`); without a setup the library uses the default `top_k = 10`. -/
def fitSparse (E : FitEnv) (cfg : BacksolveCfg) (nf : Int) (pop : Option (List Member))
    (target : Vec) (mask : Option (List Bool)) (setup : Option Setup) (extra : Option (Tree JF))
    (maxC : Option Int) : Jl (Option (Tree JF)) :=
  if !hasWS E.bin then pure none
  else if tooFewRows mask target.length then pure none
  else
    (match setup with
      | none => buildLibrary E.ev E.hash nf cfg.maxLibrarySize 10 pop >>= fun b => pure (b.1, b.2.1)
      | some s => pure (s.terms, s.cols)) >>= fun tc =>
    fitAfter E cfg tc.1 (tc.2.map (·.map toRat)) (setup.map (·.gram)) (fitCosts E tc.1 setup extra)
      target mask extra maxC

-- Source: src/Backsolve.jl:575–587
-- backsolve_options::BacksolveMutation=configured_backsolve(options),
def fitSparseCall (E : FitEnv) (ms : List (MutationInstance × JF))
    (fields : MutationInstance → BacksolveCfg) (kw : Option BacksolveCfg)
    (nf : Int) (pop : Option (List Member)) (target : Vec) (mask : Option (List Bool))
    (setup : Option Setup) (extra : Option (Tree JF)) (maxC : Option Int) : Jl (Option (Tree JF)) := do
  let cfg ← match kw with
    | some cfg => pure cfg
    | none => (configuredBacksolve ms).map fields
  fitSparse E cfg nf pop target mask setup extra maxC

theorem bind_ok {α β : Type} {x : Jl α} {f : α → Jl β} {v : β} (h : (x >>= f) = .ok v) :
    ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩


def fitGuardedCall : Prop :=
  (∀ (E : FitEnv) (ms : List (MutationInstance × JF)) (fields : MutationInstance → BacksolveCfg)
    (kw : Option BacksolveCfg) (nf : Int) (pop : Option (List Member)) (target : Vec)
    (mask : Option (List Bool)) (setup : Option Setup) (extra : Option (Tree JF))
    (maxC : Option Int),
    (kw = none → (∀ p ∈ ms, enabledBacksolve p = false) →
      fitSparseCall E ms fields kw nf pop target mask setup extra maxC =
        .error (.argumentError notEnabledMsg)) ∧
    ((kw.isSome = true ∨ ∃ m, configuredBacksolve ms = .ok m) →
      (hasWS E.bin = false ∨ tooFewRows mask target.length = true) →
      fitSparseCall E ms fields kw nf pop target mask setup extra maxC = .ok none)) ∧
  (∀ (E : FitEnv) (cfg : BacksolveCfg) (ts : List (Tree JF)) (G : Mat)
    (g : Vec) (yy : Rat) (tc : List Int) (jc : Int) (maxC : Option Int) (u : Tree JF),
    let (cs, success) := greedyGram E.sq E.ch G g yy tc jc maxC cfg.maxTerms cfg.minImprovement
    success = true → combine (realCoefficients .float64) E.bin ts (cs.map JF.fin) = .ok (some u) →
    ((∃ mc, maxC = some mc ∧ mc < E.cx u) → fitTail E cfg ts G g yy tc jc maxC = .ok none) ∧
    ((∀ mc, maxC = some mc → E.cx u ≤ mc) →
      (∀ e, E.ev u = .error e → fitTail E cfg ts G g yy tc jc maxC = .error e) ∧
      (∀ vs complete, E.ev u = .ok (vs, complete) →
        (fitTail E cfg ts G g yy tc jc maxC = .ok (some u) ↔
          complete = true ∧ ∀ v ∈ vs, v.valid = true))))

theorem fitGuardedCall_holds : fitGuardedCall := by
  constructor
  · intro E ms fields kw nf pop target mask setup extra maxC
    constructor
    · rintro rfl h
      have he := ((configuredSpec_holds ms).2 (.argumentError notEnabledMsg)).mpr ⟨rfl, h⟩
      simp [fitSparseCall, he, bind, Except.bind, Except.map]
    · intro h ha
      have guard (cfg : BacksolveCfg) :
          fitSparse E cfg nf pop target mask setup extra maxC = .ok none :=
        ha.elim (fun h => by simp [fitSparse, h, pure, Except.pure])
          (fun h => by cases hw : hasWS E.bin <;> simp [fitSparse, hw, h, pure, Except.pure])
      cases kw with
      | some cfg => simpa [fitSparseCall, pure, Except.pure, bind, Except.bind] using guard cfg
      | none =>
        rcases h with h | ⟨m, hm⟩
        · cases h
        · simpa [fitSparseCall, hm, bind, Except.bind, Except.map] using guard (fields m)
  · intro E cfg ts G g yy tc jc maxC u
    dsimp only
    intro hs hu
    refine ⟨?_, ?_⟩
    · rintro ⟨mc, rfl, hb⟩
      simp [fitTail, hs, hu, finalCheck, overBudget, hb, pure, Except.pure, bind, Except.bind]
    · intro hb
      have hn : overBudget maxC (E.cx u) = false := by
        cases maxC with
        | none => rfl
        | some mc => have := hb mc rfl; simp [overBudget]; omega
      constructor
      · intro e he
        simp [fitTail, hs, hu, finalCheck, hn, he, bind, Except.bind]
      · intro vs complete he
        by_cases hf : finiteEval (vs, complete) = true
        · have h := (finiteEval_iff (vs, complete)).mp hf
          simpa [fitTail, hs, hu, finalCheck, hn, he, hf, bind, Except.bind, pure, Except.pure] using h
        · have h : ¬ (complete = true ∧ ∀ v ∈ vs, v.valid = true) :=
            fun h => hf ((finiteEval_iff (vs, complete)).mpr h)
          simp [fitTail, hs, hu, finalCheck, hn, he, hf, h, bind, Except.bind, pure, Except.pure]

theorem wsc_append (cx : Tree JF → Int) (bin : List Op) (terms more : List (Tree JF))
    (tc : List Int) (jc ov : Int) (h : weightedSumCosts cx bin terms = .ok (tc, jc, ov)) :
    weightedSumCosts cx bin (terms ++ more) = .ok (tc ++ more.map (fun t => cx t + ov), jc, ov) := by
  unfold weightedSumCosts at h ⊢
  cases hh : wscHeader cx bin with
  | error e => rw [hh] at h; cases h
  | ok p =>
    rw [hh] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3
    simp

theorem fitGram_setup (theta : List Vec) (target : Vec) (mask : Option (List Bool))
    (exv : Option Vec) :
    fitGram theta (some (gramOf theta)) target mask exv = fitGram theta none target mask exv := by
  unfold fitGram
  split <;> rfl

/-- Reusing a setup is an optimisation only (`src/Backsolve.jl:459-475,545-547`): fitting with
the setup `prepare_backsolve_setup` builds from the same population with
`max_library_size = backsolve_options.max_library_size` and the default `top_k = 10` returns the
same result as fitting without a setup. -/
def fitSetupTransparent : Prop :=
  ∀ (E : FitEnv) (cfg : BacksolveCfg) (nf : Int) (pop : Option (List Member)) (target : Vec)
    (mask : Option (List Bool)) (extra : Option (Tree JF)) (maxC : Option Int) (s : Setup),
    prepareSetup E nf cfg.maxLibrarySize 10 pop = .ok s →
    fitSparse E cfg nf pop target mask (some s) extra maxC =
      fitSparse E cfg nf pop target mask none extra maxC

theorem fitSetupTransparent_holds : fitSetupTransparent := by
  intro E cfg nf pop target mask extra maxC s hs
  unfold prepareSetup at hs
  obtain ⟨b, hb, hs⟩ := bind_ok hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  simp only [pure, Except.pure, Except.ok.injEq] at hs
  subst hs
  obtain ⟨terms, cols, n⟩ := b
  obtain ⟨tc, jc, ov⟩ := c
  unfold fitSparse
  split
  · rfl
  · split
    · rfl
    · simp only [hb, bind, Except.bind, pure, Except.pure, Option.map_some]
      have hcost : fitCosts E terms (some ⟨terms, cols, n, gramOf (cols.map (·.map toRat)), tc, jc, ov⟩)
          extra = fitCosts E terms none extra := by
        unfold fitCosts
        rw [wsc_append E.cx E.bin terms extra.toList tc jc ov hc]
        cases extra <;> simp [bind, Except.bind, pure, Except.pure]
      rw [hcost]
      unfold fitAfter
      cases he : extraVals E extra with
      | error e => rfl
      | ok o =>
        cases o with
        | none => rfl
        | some exv => simp [bind, Except.bind, fitGram_setup]

/-- The environment of the satisfiability witnesses: one row, `+` and `*`, every tree evaluating
to `1`. -/
noncomputable def env1 : FitEnv :=
  { bin := [.b .plus, .b .mult], ev := fun _ => .ok ([.fin 1], true), cx := fun _ => 1,
    hash := fun _ => 0, sq := sqC, ch := chol1 }

/-- The configuration of the satisfiability witnesses. -/
def cfg1 : BacksolveCfg :=
  { maxLibrarySize := 1, maxTerms := 1, minImprovement := 1 / 1000, nodeAttempts := 1 }

example : (match fitSparse env1 cfg1 0 none [1] none none none none with
    | .ok (some _) => true | _ => false) = true := by decide +kernel

example : (match prepareSetup env1 0 cfg1.maxLibrarySize 10 none with
    | .ok _ => true | _ => false) = true := by decide +kernel

end SymReg.Backsolve
