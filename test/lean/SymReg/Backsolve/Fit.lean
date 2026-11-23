/-!
Model of the numerical core of `src/Backsolve.jl`: `_solve_gram`, `stlsq`/`_stlsq_gram` and
`greedy_forward_selection_gram`.

Scalars are exact rationals: the inputs are finite (the library columns and the fitted targets
are filtered for finiteness by every caller, `src/Backsolve.jl:377,585,600-603`), and the model
has no rounding or overflow. `T` is real (`Float64`); the `Complex` element types admitted by
`STLSQ_DATA_TYPE` are outside the model. `eps(Float64) = 2^-52` is exact; the ridge constants
`1e-10`, `1e-8`, `1e-6` are their decimal values. Base `sqrt` is an arbitrary function `sq`, and
`cholesky(Hermitian(A)) \ b` is an arbitrary solver `ch` returning `none` for
`PosDefException`; properties that need facts about them state those facts as hypotheses.
Vectors are lists, matrices lists of rows, and indices inside the model are zero-based.
-/

namespace SymReg.Backsolve

/-- A real vector. -/
abbrev Vec := List Rat
/-- A real matrix, as its list of rows. -/
abbrev Mat := List (List Rat)

/-- `dot(a, b)` on real vectors. -/
def dotR (a b : Vec) : Rat := (List.zipWith (· * ·) a b).sum

/-- `A * x`. -/
def mulVec (A : Mat) (x : Vec) : Vec := A.map (fun row => dotR row x)

/-- `sum(abs2, v)`. -/
def sumSq (v : Vec) : Rat := dotR v v

/-- `abs(q)`. -/
def rabs (q : Rat) : Rat := if q < 0 then -q else q

/-- `eps(Float64)`. -/
def epsF : Rat := 1 / 4503599627370496

/-- `typemax(Int)`. -/
def typemaxInt : Int := 9223372036854775807

/-- `cholesky(Hermitian(A)) \ b`; `none` is a `PosDefException`. -/
abbrev Chol := Mat → Vec → Option Vec

/-- An exact solver: whatever it returns solves the system. -/
def CholSound (ch : Chol) : Prop :=
  ∀ A b x, ch A b = some x → mulVec A x = b ∧ x.length = b.length

/-- `G ./ (col_norms * col_norms')`. -/
def normMat (G : Mat) (cn : Vec) : Mat :=
  List.zipWith (fun row ci => List.zipWith (fun gij cj => gij / (ci * cj)) row cn) G cn

/-- `g ./ col_norms`. -/
def normVec (g cn : Vec) : Vec := List.zipWith (· / ·) g cn

/-- `A + ridge * I`. -/
def addRidge (A : Mat) (r : Rat) : Mat :=
  A.mapIdx (fun i row => row.mapIdx (fun j a => if i = j then a + r else a))

/-- The escalating ridges `1e-10`, `1e-8`, `1e-6` (`src/Backsolve.jl:43-52`). -/
def ridges : List Rat := [1 / 10000000000, 1 / 100000000, 1 / 1000000]

/-- The ridge loop of `_solve_gram` (`src/Backsolve.jl:43-53`): the first ridge whose
factorisation succeeds, else `zeros(T, length(b))`. -/
def tryRidges (ch : Chol) (A : Mat) (b : Vec) : List Rat → Vec
  | [] => List.replicate b.length 0
  | r :: rs => match ch (addRidge A r) b with
    | some x => x
    | none => tryRidges ch A b rs

/-- `_solve_gram(G, g, col_norms)` (`src/Backsolve.jl:32-54`). -/
def solveGram (ch : Chol) (G : Mat) (g cn : Vec) : Vec :=
  match ch (normMat G cn) (normVec g cn) with
  | some x => x
  | none => tryRidges ch (normMat G cn) (normVec g cn) ridges

/-! ## Index helpers -/

/-- `x[mask]`. -/
def sel {α : Type} : List Bool → List α → List α
  | b :: bs, x :: xs => if b then x :: sel bs xs else sel bs xs
  | _, _ => []

/-- `G[mask, mask]`. -/
def subMat (m : List Bool) (G : Mat) : Mat := (sel m G).map (sel m)

/-- `v = zeros(T, n); v[mask] = vals`. -/
def scatter : List Bool → Vec → Vec
  | true :: bs, v :: vs => v :: scatter bs vs
  | true :: bs, [] => 0 :: scatter bs []
  | false :: bs, vs => 0 :: scatter bs vs
  | [], _ => []

/-- `x[is]` for a list of (zero-based) indices. -/
def pick {α : Type} (xs : List α) (is : List Nat) (d : α) : List α := is.map (xs.getD · d)

/-- `G[is, is]`. -/
def subIdx (G : Mat) (is : List Nat) : Mat := (pick G is []).map (fun row => pick row is 0)

/-- `c[is] = vs`. -/
def setAt : Vec → List Nat → Vec → Vec
  | c, i :: is, v :: vs => setAt (c.set i v) is vs
  | c, _, _ => c

/-- `theta' * theta` for the columns of `theta`. -/
def gramOf (cols : List Vec) : Mat := cols.map (fun ci => cols.map (fun cj => dotR ci cj))

/-- `sqrt.(max.(real.(diag(G)), zero(R)))` (`src/Backsolve.jl:117,215`). -/
def rawNorms (sq : Rat → Rat) (G : Mat) (n : Nat) : Vec :=
  (List.range n).map (fun i => sq (max ((G.getD i []).getD i 0) 0))

/-! ## Sequential thresholded least squares -/

/-- `abs.(coefficients) .< threshold` negated: the active terms (`src/Backsolve.jl:123-124`). -/
def threshMask (thr : Rat) (c : Vec) : List Bool := c.map (fun q => !(decide (rabs q < thr)))

/-- The iteration loop of `_stlsq_gram` (`src/Backsolve.jl:122-142`); `none` is the early
return when every term is thresholded away. -/
def stlsqLoop (sq : Rat → Rat) (ch : Chol) (G : Mat) (g cn : Vec) (thr : Rat) :
    Nat → Vec → Option Vec
  | 0, c => some c
  | k + 1, c =>
    let act := threshMask thr c
    if !(act.any id) then none
    else
      let cnew := scatter act (solveGram ch (subMat act G) (sel act g) (sel act cn))
      if decide (sq (sumSq (List.zipWith (· - ·) cnew c)) < epsF * 10) then some cnew
      else stlsqLoop sq ch G g cn thr k cnew

/-- The column norms of `_stlsq_gram` (`src/Backsolve.jl:117-118`). -/
def stlsqNorms (sq : Rat → Rat) (G : Mat) (g : Vec) : Vec :=
  (rawNorms sq G g.length).map (fun c => max c epsF)

/-- `_stlsq_gram(G, g; lambda, max_iter)` (`src/Backsolve.jl:108-148`). -/
def stlsqGram (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (lambda : Rat) (maxIter : Int) :
    Vec × Bool :=
  let cn := stlsqNorms sq G g
  match stlsqLoop sq ch G g cn lambda maxIter.toNat (solveGram ch G g cn) with
  | none => (List.replicate g.length 0, false)
  | some c =>
    let c' := List.zipWith (· / ·) c cn
    (c', c'.any (fun q => decide (epsF * 100 < rabs q)))

/-- `stlsq(theta, y; lambda, max_iter)` (`src/Backsolve.jl:93-106`) for the `ns x cols.length`
matrix with columns `cols`. -/
def stlsq (sq : Rat → Rat) (ch : Chol) (ns : Nat) (cols : List Vec) (y : Vec) (lambda : Rat)
    (maxIter : Int) : Vec × Bool :=
  if y.length ≠ ns then (List.replicate cols.length 0, false)
  else stlsqGram sq ch (gramOf cols) (cols.map (fun c => dotR c y)) lambda maxIter

/-! ## Greedy forward selection -/

/-- Loop state of `greedy_forward_selection_gram`. `norms` records the initial residual norm
and the residual norm after every accepted addition (an observation of the loop, not a Julia
variable). -/
structure GState where
  active : List Nat
  x : Vec
  rnorm : Rat
  remaining : Int
  corr : Vec
  norms : List Rat

/-- The candidate scan (`src/Backsolve.jl:226-237`): the one-based index of the first usable,
inactive, affordable column with the largest `abs(corr_resid[j])`, strictly above zero; `0` for
none. -/
def selectBest (usable : List Bool) (active : List Nat) (costs : List Int) (extra remaining : Int)
    (corr : Vec) (n : Nat) : Nat × Rat :=
  (List.range n).foldl (fun acc j =>
    if usable.getD j false && !(active.contains j) && decide (costs.getD j 0 + extra ≤ remaining)
    then if acc.2 < rabs (corr.getD j 0) then (j + 1, rabs (corr.getD j 0)) else acc
    else acc) (0, 0)

/-- Fixed data of one greedy run. -/
structure GCtx where
  sq : Rat → Rat
  ch : Chol
  G : Mat
  g : Vec
  Gn : Mat
  gn : Vec
  cn : Vec
  usable : List Bool
  costs : List Int
  join : Int
  maxTerms : Int
  minImpr : Rat
  yy : Rat
  yscale : Rat
  n : Nat

/-- One accepted addition: the refit and its residual norm (`src/Backsolve.jl:240-251`). -/
def GCtx.trialFit (c : GCtx) (trial : List Nat) : Vec × Rat :=
  let xt := solveGram c.ch (subIdx c.G trial) (pick c.g trial 0) (pick c.cn trial 0)
  (xt, c.sq (max (c.yy - 2 * dotR xt (pick c.gn trial 0) + dotR xt (mulVec (subIdx c.Gn trial) xt)) 0))

/-- The state after accepting `trial` with refit `fit` and estimated cost `cost`
(`src/Backsolve.jl:255-258`). -/
def GState.accept (st : GState) (trial : List Nat) (fit : Vec × Rat) (cost : Int) : GState :=
  { active := trial, x := fit.1, rnorm := fit.2, remaining := st.remaining - cost,
    corr := st.corr, norms := st.norms ++ [fit.2] }

/-- The state before the loop (`src/Backsolve.jl:216-222`). -/
def GState.init (r0 : Rat) (rem : Int) (corr : Vec) : GState :=
  { active := [], x := [], rnorm := r0, remaining := rem, corr, norms := [r0] }

/-- `extra = isempty(active) ? 0 : join_cost` (`src/Backsolve.jl:225`). -/
def GCtx.extra (c : GCtx) (st : GState) : Int := if st.active.isEmpty then 0 else c.join

/-- The `while` loop (`src/Backsolve.jl:224-260`); the fuel `max_terms` bounds it because every
continuing iteration adds one term. The breaks `best_j == 0`,
`!(improvement >= min_improvement)` and `residual_norm <= tol * 100 * y_scale` return the
current state. -/
def greedyLoop (c : GCtx) : Nat → GState → GState
  | 0, st => st
  | k + 1, st =>
    if (st.active.length : Int) < c.maxTerms then
      let extra := c.extra st
      let bj := (selectBest c.usable st.active c.costs extra st.remaining st.corr c.n).1
      if bj = 0 then st
      else
        let j := bj - 1
        let trial := st.active ++ [j]
        let fit := c.trialFit trial
        if c.minImpr ≤ (st.rnorm - fit.2) / max st.rnorm (epsF * c.yscale) then
          let st' := st.accept trial fit (c.costs.getD j 0 + extra)
          if fit.2 ≤ epsF * 100 * c.yscale then st'
          else greedyLoop c k { st' with
            corr := List.zipWith (· - ·) c.gn (c.Gn.map (fun row => dotR (pick row trial 0) fit.1)) }
        else st
    else st

/-- The setup of `greedy_forward_selection_gram` (`src/Backsolve.jl:204-222`) and the final
loop state; `none` for the early `return coefficients, false` exits. -/
def greedyRun (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (yy : Rat) (costs : List Int)
    (join : Int) (budget : Option Int) (maxTerms : Int) (minImpr : Rat) :
    Option (GCtx × GState) :=
  let n := g.length
  if !(decide (0 < n) && G.length == n && G.all (·.length == n)) then none
  else
    let cn0 := rawNorms sq G n
    let usable := cn0.map (fun c => decide (epsF < c))
    if !(usable.any id) then none
    else
      let cn := cn0.map (fun c => max c epsF)
      let r0 := sq (max yy 0)
      let ctx : GCtx :=
        { sq, ch, G, g, Gn := normMat G cn, gn := normVec g cn, cn, usable, costs,
          join, maxTerms, minImpr, yy, yscale := max r0 1, n }
      some (ctx, greedyLoop ctx maxTerms.toNat
        (GState.init r0 (budget.getD typemaxInt) (normVec g cn)))

/-- `greedy_forward_selection_gram(G, g, yy; term_costs, join_cost, budget, max_terms,
min_improvement)` (`src/Backsolve.jl:193-266`). -/
def greedyGram (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (yy : Rat) (costs : List Int)
    (join : Int) (budget : Option Int) (maxTerms : Int) (minImpr : Rat) : Vec × Bool :=
  match greedyRun sq ch G g yy costs join budget maxTerms minImpr with
  | none => (List.replicate g.length 0, false)
  | some (ctx, st) =>
    if st.active.isEmpty then (List.replicate g.length 0, false)
    else
      let c := setAt (List.replicate g.length 0) st.active
        (List.zipWith (· / ·) st.x (pick ctx.cn st.active 0))
      (c, c.any (fun q => decide (epsF * 100 < rabs q)))

/-! ## `_solve_gram` solves the normal equations -/

theorem tryRidges_spec (ch : Chol) (hch : CholSound ch) (A : Mat) (b : Vec) :
    ∀ rs : List Rat, tryRidges ch A b rs = List.replicate b.length 0 ∨
      ∃ r ∈ rs, mulVec (addRidge A r) (tryRidges ch A b rs) = b := by
  intro rs
  induction rs with
  | nil => exact Or.inl rfl
  | cons r rs ih =>
    unfold tryRidges
    cases h : ch (addRidge A r) b with
    | some x => exact Or.inr ⟨r, by simp, (hch _ _ _ h).1⟩
    | none =>
      simp only
      rcases ih with h1 | ⟨r', hr', h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨r', by simp [hr'], h2⟩

theorem dotR_nil_left (x : Vec) : dotR [] x = 0 := rfl

theorem dotR_cons (a : Rat) (as : Vec) (b : Rat) (bs : Vec) :
    dotR (a :: as) (b :: bs) = a * b + dotR as bs := by
  simp [dotR]

/-- One row of the normalised system: `sum_j G_ij / (c_i c_j) x_j = (sum_j G_ij (x_j / c_j)) / c_i`. -/
theorem dot_norm_row (ci : Rat) (hci : ci ≠ 0) :
    ∀ (row cn x : Vec), row.length = cn.length → x.length = cn.length → (∀ c ∈ cn, c ≠ 0) →
      dotR (List.zipWith (fun gij cj => gij / (ci * cj)) row cn) x =
        dotR row (List.zipWith (· / ·) x cn) / ci := by
  intro row
  induction row with
  | nil => intro cn x _ _ _; show (0 : Rat) = 0 / ci; grind
  | cons a as ih =>
    intro cn x h1 h2 h3
    match cn, x, h1, h2 with
    | c :: cs, y :: ys, h1, h2 =>
      have hc : c ≠ 0 := h3 c (by simp)
      have hrest := ih cs ys (by simpa using h1) (by simpa using h2)
        (fun c' hc' => h3 c' (by simp [hc']))
      simp only [List.zipWith_cons_cons, dotR_cons, hrest]
      grind

/-- A solution of the column-normalised system, rescaled by the column norms, solves `G z = g`. -/
theorem normal_eq (cn x : Vec) (hcn : ∀ c ∈ cn, c ≠ 0) (hx : x.length = cn.length) :
    ∀ (G : Mat) (g cs : Vec), (∀ row ∈ G, row.length = cn.length) → G.length = g.length →
      G.length = cs.length → (∀ c ∈ cs, c ≠ 0) →
      mulVec (List.zipWith (fun row ci => List.zipWith (fun gij cj => gij / (ci * cj)) row cn) G cs) x =
        List.zipWith (· / ·) g cs →
      mulVec G (List.zipWith (· / ·) x cn) = g := by
  intro G
  induction G with
  | nil => intro g cs _ h1 _ _ _; match g, h1 with | [], _ => rfl
  | cons r G ih =>
    intro g cs hrows h1 h2 hcs h
    match g, cs, h1, h2 with
    | g0 :: gs, c0 :: css, h1, h2 =>
      have hc0 : c0 ≠ 0 := hcs c0 (by simp)
      simp only [List.zipWith_cons_cons, mulVec, List.map_cons, List.cons.injEq] at h
      obtain ⟨hh, ht⟩ := h
      rw [dot_norm_row c0 hc0 r cn x (hrows r (by simp)) hx hcn] at hh
      have hrest := ih gs css (fun row hr => hrows row (by simp [hr])) (by simpa using h1)
        (by simpa using h2) (fun c hc => hcs c (by simp [hc])) ht
      simp only [mulVec, List.map_cons, List.cons.injEq]
      refine ⟨?_, hrest⟩
      have : dotR r (List.zipWith (· / ·) x cn) = dotR r (List.zipWith (· / ·) x cn) / c0 * c0 := by
        grind
      rw [this, hh]
      grind

/-- `_solve_gram` (`src/Backsolve.jl:20-54`): with an exact solver, the result solves the
normalised system `A x = b` (`A = G ./ (c c')`, `b = g ./ c`), a ridged system
`(A + r I) x = b` for one of the three escalating ridges, or is the all-zero vector; when the
unridged factorisation succeeds its solution is returned, and rescaling it by the column norms
solves the normal equations `G z = g` (square `n x n` system, nonzero column norms). -/
def solveGramSpec : Prop :=
  ∀ (ch : Chol) (G : Mat) (g cn : Vec), CholSound ch →
    (solveGram ch G g cn = List.replicate (normVec g cn).length 0 ∨
      mulVec (normMat G cn) (solveGram ch G g cn) = normVec g cn ∨
      ∃ r ∈ ridges, mulVec (addRidge (normMat G cn) r) (solveGram ch G g cn) = normVec g cn) ∧
    (∀ x0, ch (normMat G cn) (normVec g cn) = some x0 → solveGram ch G g cn = x0 ∧
      ((∀ row ∈ G, row.length = cn.length) → G.length = g.length → g.length = cn.length →
        (∀ c ∈ cn, c ≠ 0) → mulVec G (List.zipWith (· / ·) x0 cn) = g))

theorem solveGramSpec_holds : solveGramSpec := by
  intro ch G g cn hch
  refine ⟨?_, ?_⟩
  · unfold solveGram
    cases h : ch (normMat G cn) (normVec g cn) with
    | some x => exact Or.inr (Or.inl (hch _ _ _ h).1)
    | none =>
      simp only
      rcases tryRidges_spec ch hch (normMat G cn) (normVec g cn) ridges with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
  · intro x0 h0
    refine ⟨by unfold solveGram; rw [h0], fun hrows hG hg hcn => ?_⟩
    obtain ⟨hsol, hlen⟩ := hch _ _ _ h0
    have hxl : x0.length = cn.length := by
      rw [hlen]; simp [normVec, hg]
    exact normal_eq cn x0 hcn hxl G g cn hrows hG (by omega) hcn hsol

/-- A one-by-one exact solver, used to witness the hypotheses. -/
def chol1 : Chol := fun A b =>
  match A, b with
  | [[a]], [b0] => if a = 0 then none else some [b0 / a]
  | _, _ => none

theorem chol1_sound : CholSound chol1 := by
  intro A b x h
  unfold chol1 at h
  split at h
  · rename_i a b0
    by_cases ha : a = 0
    · rw [if_pos ha] at h; cases h
    · rw [if_neg ha] at h
      cases h
      refine ⟨?_, rfl⟩
      simp only [mulVec, dotR, List.map_cons, List.map_nil, List.zipWith_cons_cons,
        List.zipWith_nil_left, List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
      grind
  · cases h

example : CholSound chol1 ∧ chol1 [[2]] [4] = some [2] := ⟨chol1_sound, by with_unfolding_all decide⟩

/-! ## Thresholded least squares -/

theorem stlsqLoop_spec (sq : Rat → Rat) (ch : Chol) (G : Mat) (g cn : Vec) (thr : Rat) :
    ∀ (k : Nat) (c c' : Vec), stlsqLoop sq ch G g cn thr k c = some c' →
      c' = c ∨ ∃ cPrev, (threshMask thr cPrev).any id = true ∧
        c' = scatter (threshMask thr cPrev)
          (solveGram ch (subMat (threshMask thr cPrev) G) (sel (threshMask thr cPrev) g)
            (sel (threshMask thr cPrev) cn)) := by
  intro k
  induction k with
  | zero => intro c c' h; cases h; exact Or.inl rfl
  | succ k ih =>
    intro c c' h
    unfold stlsqLoop at h
    by_cases hany : (threshMask thr c).any id = true
    · rw [if_neg (by simp [hany])] at h
      simp only at h
      split at h
      · cases h; exact Or.inr ⟨c, hany, rfl⟩
      · rcases ih _ c' h with h1 | h2
        · exact Or.inr ⟨c, hany, h1⟩
        · exact Or.inr h2
    · rw [if_pos (by simp [hany])] at h; cases h

/-- `stlsq` and `_stlsq_gram` (`src/Backsolve.jl:56-148`): a length mismatch returns all zeros
and `false`; otherwise the result is all zeros with `false` (every term thresholded away), the
rescaled initial least-squares solution (`max_iter <= 0`), or the rescaled refit
`_solve_gram` on the terms whose preceding estimate reached the threshold, zero elsewhere; and
`success` holds only if some returned coefficient exceeds `100 eps` in magnitude. -/
def stlsqFit : Prop :=
  ∀ (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (lambda : Rat) (maxIter : Int),
    let r := stlsqGram sq ch G g lambda maxIter
    let cn := stlsqNorms sq G g
    (r.2 = true → ∃ q ∈ r.1, epsF * 100 < rabs q) ∧
    (r = (List.replicate g.length 0, false) ∨
      r.1 = List.zipWith (· / ·) (solveGram ch G g cn) cn ∨
      ∃ cPrev, (threshMask lambda cPrev).any id = true ∧
        r.1 = List.zipWith (· / ·) (scatter (threshMask lambda cPrev)
          (solveGram ch (subMat (threshMask lambda cPrev) G) (sel (threshMask lambda cPrev) g)
            (sel (threshMask lambda cPrev) cn))) cn) ∧
    (∀ (ns : Nat) (cols : List Vec) (y : Vec), y.length ≠ ns →
      stlsq sq ch ns cols y lambda maxIter = (List.replicate cols.length 0, false)) ∧
    (∀ (ns : Nat) (cols : List Vec) (y : Vec), y.length = ns →
      stlsq sq ch ns cols y lambda maxIter =
        stlsqGram sq ch (gramOf cols) (cols.map (fun c => dotR c y)) lambda maxIter)

theorem stlsqFit_holds : stlsqFit := by
  intro sq ch G g lambda maxIter
  dsimp only
  have hs1 : ∀ (ns : Nat) (cols : List Vec) (y : Vec), y.length ≠ ns →
      stlsq sq ch ns cols y lambda maxIter = (List.replicate cols.length 0, false) := by
    intro ns cols y h; simp [stlsq, h]
  have hs2 : ∀ (ns : Nat) (cols : List Vec) (y : Vec), y.length = ns →
      stlsq sq ch ns cols y lambda maxIter =
        stlsqGram sq ch (gramOf cols) (cols.map (fun c => dotR c y)) lambda maxIter := by
    intro ns cols y h; simp [stlsq, h]
  cases hloop : stlsqLoop sq ch G g (stlsqNorms sq G g) lambda maxIter.toNat
      (solveGram ch G g (stlsqNorms sq G g)) with
  | none =>
    dsimp only [stlsqGram]; rw [hloop]; dsimp only
    exact ⟨(fun h => by cases h), Or.inl rfl, hs1, hs2⟩
  | some c =>
    dsimp only [stlsqGram]; rw [hloop]; dsimp only
    refine ⟨(fun h => by simpa using h), ?_, hs1, hs2⟩
    rcases stlsqLoop_spec sq ch G g _ lambda _ _ c hloop with h1 | ⟨cp, ha, hcp⟩
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inr (Or.inr ⟨cp, ha, by rw [hcp]⟩)

/-! ## Greedy selection: budget and term limits -/

/-- Complexity of the weighted sum of the terms `A` as estimated by the selection: their costs
plus one join per additional term (`src/Backsolve.jl:175-176,229,255`). -/
def spent (costs : List Int) (join : Int) (A : List Nat) : Int :=
  if A = [] then 0 else (A.map (costs.getD · 0)).sum + join * ((A.length : Int) - 1)

theorem spent_snoc (costs : List Int) (join : Int) (A : List Nat) (j : Nat) :
    spent costs join (A ++ [j]) =
      spent costs join A + (costs.getD j 0 + if A.isEmpty then 0 else join) := by
  unfold spent
  cases A with
  | nil => simp
  | cons a as =>
    simp only [List.cons_append, reduceCtorEq, if_false, List.map_cons, List.map_append,
      List.sum_cons, List.sum_append, List.map_nil, List.sum_nil, List.length_cons,
      List.length_append, List.isEmpty_cons, Bool.false_eq_true]
    push_cast
    grind

theorem selectBest_spec (usable : List Bool) (active : List Nat) (costs : List Int)
    (extra remaining : Int) (corr : Vec) (n : Nat) :
    let bj := (selectBest usable active costs extra remaining corr n).1
    bj = 0 ∨ (bj - 1 < n ∧ usable.getD (bj - 1) false = true ∧ (bj - 1) ∉ active ∧
      costs.getD (bj - 1) 0 + extra ≤ remaining) := by
  let P : Nat × Rat → Prop := fun acc => acc.1 = 0 ∨ (acc.1 - 1 < n ∧
    usable.getD (acc.1 - 1) false = true ∧ (acc.1 - 1) ∉ active ∧
    costs.getD (acc.1 - 1) 0 + extra ≤ remaining)
  have key : ∀ (l : List Nat) (acc : Nat × Rat), (∀ j ∈ l, j < n) → P acc →
      P (l.foldl (fun acc j =>
        if usable.getD j false && !(active.contains j) && decide (costs.getD j 0 + extra ≤ remaining)
        then if acc.2 < rabs (corr.getD j 0) then (j + 1, rabs (corr.getD j 0)) else acc
        else acc) acc) := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons j l ih =>
      intro acc hl hacc
      simp only [List.foldl_cons]
      apply ih _ (fun j' hj' => hl j' (by simp [hj']))
      split
      · rename_i hc
        split
        · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
          obtain ⟨⟨h1, h2⟩, h3⟩ := hc
          refine Or.inr ⟨by simpa using hl j (by simp), by simpa using h1, ?_, by simpa using h3⟩
          simpa using h2
        · exact hacc
      · exact hacc
  exact key (List.range n) (0, 0) (fun j hj => by simpa using hj) (Or.inl rfl)

/-- The budget, term-count and usability invariant of the greedy loop. -/
def GInv (c : GCtx) (rem : Int) (st : GState) : Prop :=
  st.active.Nodup ∧ (st.active.length : Int) ≤ max c.maxTerms 0 ∧
  (∀ j ∈ st.active, j < c.n ∧ c.usable.getD j false = true) ∧
  spent c.costs c.join st.active + st.remaining = rem ∧
  (st.active ≠ [] → 0 ≤ st.remaining)

theorem accept_inv (c : GCtx) (rem : Int) (st : GState) (j : Nat) (fit : Vec × Rat)
    (h : GInv c rem st) (hlen : (st.active.length : Int) < c.maxTerms) (hn : j < c.n)
    (hu : c.usable.getD j false = true) (hna : j ∉ st.active)
    (hcost : c.costs.getD j 0 + c.extra st ≤ st.remaining) :
    GInv c rem (st.accept (st.active ++ [j]) fit (c.costs.getD j 0 + c.extra st)) := by
  obtain ⟨hnd, _, hus, hsp, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb hab => hna ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb; subst hab; exact ha
  · simp only [GState.accept, List.length_append, List.length_singleton]; push_cast; omega
  · intro j' hj
    simp only [GState.accept, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact hus j' hj
    · exact ⟨hn, hu⟩
  · simp only [GState.accept]; rw [spent_snoc]; unfold GCtx.extra at hcost ⊢; omega
  · intro _; simp only [GState.accept]; omega

theorem greedyLoop_inv (c : GCtx) (rem : Int) :
    ∀ (k : Nat) (st : GState), GInv c rem st → GInv c rem (greedyLoop c k st) := by
  intro k
  induction k with
  | zero => intro st h; exact h
  | succ k ih =>
    intro st h
    rw [greedyLoop]
    split
    · rename_i hlen
      dsimp only
      have hsel := selectBest_spec c.usable st.active c.costs
        (c.extra st) st.remaining st.corr c.n
      dsimp only at hsel
      split
      · exact h
      · rename_i hbj
        obtain ⟨hn, hu, hna, hcost⟩ := hsel.resolve_left hbj
        have hnew := accept_inv c rem st _ (c.trialFit (st.active ++ [(selectBest c.usable st.active
          c.costs (c.extra st) st.remaining st.corr c.n).1 - 1]))
          h hlen hn hu hna hcost
        split
        · split
          · exact hnew
          · exact ih _ hnew
        · exact h
    · exact h

theorem setAt_getD_of_not_mem :
    ∀ (is : List Nat) (c vs : Vec) (j : Nat), j ∉ is → (setAt c is vs).getD j 0 = c.getD j 0 := by
  intro is
  induction is with
  | nil => intro c vs j _; cases vs <;> rfl
  | cons i is ih =>
    intro c vs j hj
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [setAt]
      rw [ih _ _ j (fun h => hj (by simp [h]))]
      have hij : i ≠ j := fun h => hj (by simp [h])
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

theorem setAt_length :
    ∀ (is : List Nat) (c vs : Vec), (setAt c is vs).length = c.length := by
  intro is
  induction is with
  | nil => intro c vs; cases vs <;> rfl
  | cons i is ih =>
    intro c vs
    cases vs with
    | nil => rfl
    | cons v vs => simp only [setAt]; rw [ih]; simp

/-- `greedy_forward_selection_gram` respects its limits (`src/Backsolve.jl:150-266`): the
returned coefficients have length `n` and vanish outside a list `A` of distinct zero-based
indices of usable columns (`col_norms[j] > eps`), with at most `max_terms` entries, and when
`A` is nonempty its estimated weighted-sum complexity (term costs plus one `join_cost` per
additional term) is at most the budget (`typemax(Int)` when `nothing`); `success` implies `A`
is nonempty. -/
def greedyBudget : Prop :=
  ∀ (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (yy : Rat) (costs : List Int) (join : Int)
    (budget : Option Int) (maxTerms : Int) (minImpr : Rat),
    let r := greedyGram sq ch G g yy costs join budget maxTerms minImpr
    r.1.length = g.length ∧
    ∃ A : List Nat, A.Nodup ∧ (A.length : Int) ≤ max maxTerms 0 ∧
      (∀ j ∈ A, j < g.length ∧ epsF < (rawNorms sq G g.length).getD j 0) ∧
      (∀ j, j ∉ A → r.1.getD j 0 = 0) ∧
      (A ≠ [] → spent costs join A ≤ budget.getD typemaxInt) ∧
      (r.2 = true → A ≠ [])

theorem replicate_getD (n j : Nat) : (List.replicate n (0 : Rat)).getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem greedyBudget_holds : greedyBudget := by
  intro sq ch G g yy costs join budget maxTerms minImpr
  dsimp only
  have hz : ∀ j, j ∉ ([] : List Nat) → (List.replicate g.length (0 : Rat)).getD j 0 = 0 :=
    fun j _ => replicate_getD _ _
  have hnil : (([] : List Nat).length : Int) ≤ max maxTerms 0 := by
    show ((0 : Nat) : Int) ≤ max maxTerms 0; omega
  cases hrun : greedyRun sq ch G g yy costs join budget maxTerms minImpr with
  | none =>
    simp only [greedyGram, hrun]
    exact ⟨by simp, [], List.nodup_nil, hnil, by simp, hz, by simp, by simp⟩
  | some p =>
    obtain ⟨ctx, st⟩ := p
    have hinv : GInv ctx (budget.getD typemaxInt) st ∧ ctx.n = g.length ∧
        ctx.usable = (rawNorms sq G g.length).map (fun c => decide (epsF < c)) ∧
        ctx.costs = costs ∧ ctx.join = join ∧ ctx.maxTerms = maxTerms := by
      unfold greedyRun at hrun; dsimp only at hrun
      split at hrun
      · cases hrun
      · split at hrun
        · cases hrun
        · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨hctx, hst⟩ := hrun
          subst hctx; subst hst
          refine ⟨greedyLoop_inv _ _ _ _ ⟨List.nodup_nil, ?_, by simp [GState.init],
            by simp [spent, GState.init], by simp [GState.init]⟩, rfl, rfl, rfl, rfl, rfl⟩
          show ((0 : Nat) : Int) ≤ max maxTerms 0; omega
    obtain ⟨⟨hnd, hl, hus, hsp, hrem⟩, hn, husable, hcosts, hjoin, hmt⟩ := hinv
    simp only [greedyGram, hrun]
    by_cases hne : st.active.isEmpty = true
    · simp only [hne, ↓reduceIte]
      exact ⟨by simp, [], List.nodup_nil, hnil, by simp, hz, by simp, by simp⟩
    · simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hA : st.active ≠ [] := by simpa using hne
      refine ⟨by rw [setAt_length]; simp, st.active, hnd, hmt ▸ hl, fun j hj => ?_,
        fun j hj => ?_, fun _ => ?_, fun _ => hA⟩
      · obtain ⟨h1, h2⟩ := hus j hj
        rw [hn] at h1; rw [husable] at h2
        refine ⟨h1, ?_⟩
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at h2 ⊢
        cases hx : (rawNorms sq G g.length)[j]? with
        | none => simp [hx] at h2
        | some v => simpa [hx] using h2
      · rw [setAt_getD_of_not_mem _ _ _ j hj]; exact replicate_getD _ _
      · have := hrem hA; rw [hcosts, hjoin] at hsp; omega

example : (greedyRun (fun _ => 1) chol1 [[1]] [1] 1 [1] 1 none 1 (1 / 1000)).isSome = true := by
  decide +kernel

/-! ## Greedy selection: every accepted addition improves the residual -/

/-- Consecutive residual norms `a, b` satisfy the acceptance test
`(a - b) / max(a, eps * y_scale) >= min_improvement` (`src/Backsolve.jl:252-253`). -/
def ImprChain (minImpr yscale : Rat) : List Rat → Prop
  | a :: b :: rest => minImpr ≤ (a - b) / max a (epsF * yscale) ∧ ImprChain minImpr yscale (b :: rest)
  | _ => True

/-- Strictly decreasing. -/
def DecChain : List Rat → Prop
  | a :: b :: rest => b < a ∧ DecChain (b :: rest)
  | _ => True

theorem imprChain_snoc (minImpr yscale : Rat) :
    ∀ (l : List Rat) (a b : Rat), ImprChain minImpr yscale (l ++ [a]) →
      minImpr ≤ (a - b) / max a (epsF * yscale) → ImprChain minImpr yscale (l ++ [a, b]) := by
  intro l
  induction l with
  | nil => intro a b _ h; exact ⟨h, trivial⟩
  | cons x l ih =>
    intro a b h1 h2
    match l, h1 with
    | [], h1 => exact ⟨h1.1, h2, trivial⟩
    | y :: l', h1 => exact ⟨h1.1, ih a b h1.2 h2⟩

theorem accept_chain (minImpr yscale : Rat) (st : GState) (x : Rat) (l : List Rat)
    (hl : st.norms = l ++ [st.rnorm]) (h2 : ImprChain minImpr yscale st.norms)
    (himp : minImpr ≤ (st.rnorm - x) / max st.rnorm (epsF * yscale)) :
    ImprChain minImpr yscale (st.norms ++ [x]) ∧ (st.norms ++ [x]).head? = st.norms.head? := by
  refine ⟨?_, ?_⟩
  · rw [hl, List.append_assoc]
    exact imprChain_snoc _ _ l _ _ (hl ▸ h2) himp
  · rw [hl]; cases l <;> simp

/-- The residual-norm invariant: `norms` ends with the current `rnorm`, starts with `h0`, and
every step passes the acceptance test. -/
def ChainInv (c : GCtx) (h0 : Option Rat) (st : GState) : Prop :=
  (∃ l, st.norms = l ++ [st.rnorm]) ∧ ImprChain c.minImpr c.yscale st.norms ∧
  st.norms.head? = h0

theorem greedyLoop_chain (c : GCtx) (h0 : Option Rat) :
    ∀ (k : Nat) (st : GState), ChainInv c h0 st → ChainInv c h0 (greedyLoop c k st) := by
  intro k
  induction k with
  | zero => intro st h; exact h
  | succ k ih =>
    intro st h
    rw [greedyLoop]
    split
    · dsimp only
      split
      · exact h
      · split
        · rename_i himp
          obtain ⟨⟨l, hl⟩, h2, h3⟩ := h
          obtain ⟨hc, hhd⟩ := accept_chain _ _ st _ l hl h2 himp
          have hnew : ChainInv c h0 (st.accept (st.active ++ [(selectBest c.usable st.active c.costs
              (c.extra st) st.remaining st.corr c.n).1 - 1])
              (c.trialFit (st.active ++ [(selectBest c.usable st.active c.costs
              (c.extra st) st.remaining st.corr c.n).1 - 1]))
              (c.costs.getD ((selectBest c.usable st.active c.costs
              (c.extra st) st.remaining st.corr c.n).1 - 1) 0 + c.extra st)) :=
            ⟨⟨st.norms, rfl⟩, hc, hhd.trans h3⟩
          split
          · exact hnew
          · exact ih _ hnew
        · exact h
    · exact h

theorem decChain_of_impr (minImpr yscale : Rat) (hm : 0 < minImpr) (hy : 0 < yscale) :
    ∀ l : List Rat, ImprChain minImpr yscale l → DecChain l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons a l ih =>
    intro h
    match l, h, ih with
    | [], _, _ => trivial
    | b :: rest, h, ih =>
      refine ⟨?_, ih h.2⟩
      have hpos : 0 < max a (epsF * yscale) := by
        have : 0 < epsF * yscale := Rat.mul_pos (by with_unfolding_all decide) hy
        grind
      have hh : minImpr ≤ (a - b) / max a (epsF * yscale) := h.1
      have h1 : 0 < (a - b) / max a (epsF * yscale) := by grind
      have h2 := (Rat.lt_div_iff hpos).mp h1
      grind

/-- Greedy forward selection only accepts additions that shrink the residual norm by at least
the relative factor `min_improvement` (`src/Backsolve.jl:180-182,252-253`): along the sequence
of residual norms (the initial `sqrt(yy)` and the norm after each accepted addition), every
step passes the acceptance test, and with `min_improvement > 0` the norms strictly decrease. -/
def greedyMonotone : Prop :=
  ∀ (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (yy : Rat) (costs : List Int) (join : Int)
    (budget : Option Int) (maxTerms : Int) (minImpr : Rat) (ctx : GCtx) (st : GState),
    greedyRun sq ch G g yy costs join budget maxTerms minImpr = some (ctx, st) →
    st.norms.head? = some (sq (max yy 0)) ∧ ImprChain minImpr ctx.yscale st.norms ∧
    (0 < minImpr → DecChain st.norms)

theorem greedyMonotone_holds : greedyMonotone := by
  intro sq ch G g yy costs join budget maxTerms minImpr ctx st h
  unfold greedyRun at h; dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hctx, hst⟩ := h
      subst hctx; subst hst
      obtain ⟨_, hc, hhd⟩ := greedyLoop_chain _ (some (sq (max yy 0))) maxTerms.toNat
        (GState.init (sq (max yy 0)) (budget.getD typemaxInt) _) ⟨⟨[], rfl⟩, trivial, rfl⟩
      refine ⟨hhd, hc, fun hm => decChain_of_impr _ _ hm ?_ _ hc⟩
      show 0 < max (sq (max yy 0)) 1
      grind

/-! ## Greedy selection is not scale invariant -/

/-- A square root that is exact on the squares of nonnegative rationals. -/
def SqrtExact (sq : Rat → Rat) : Prop := ∀ q : Rat, 0 ≤ q → sq (q * q) = q

/-- The docstring claim (`src/Backsolve.jl:184-187`): greedy selection "is invariant to the
scale of `y`". Scaling `y` by `s > 0` (so `g` by `s` and `yy` by `s^2`) scales the coefficients
by `s` and keeps `success`. -/
def greedyScaleInvariant : Prop :=
  ∀ (sq : Rat → Rat) (ch : Chol) (G : Mat) (g : Vec) (yy : Rat) (costs : List Int) (join : Int)
    (budget : Option Int) (maxTerms : Int) (minImpr s : Rat),
    SqrtExact sq → CholSound ch → 0 < s →
    greedyGram sq ch G (g.map (s * ·)) (s * s * yy) costs join budget maxTerms minImpr =
      let r := greedyGram sq ch G g yy costs join budget maxTerms minImpr
      (r.1.map (s * ·), r.2)

theorem sq_inj {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a = b * b) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by grind
  rcases Rat.mul_eq_zero.mp h1 with h2 | h2
  · grind
  · grind

/-- The nonnegative square root of a rational square, `0` elsewhere. -/
noncomputable def classicalSqrt (x : Rat) : Rat := by
  classical exact if h : ∃ q : Rat, 0 ≤ q ∧ q * q = x then Classical.choose h else 0

theorem classicalSqrt_exact : SqrtExact classicalSqrt := by
  intro q hq
  have h : ∃ r : Rat, 0 ≤ r ∧ r * r = q * q := ⟨q, hq, rfl⟩
  unfold classicalSqrt
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  exact sq_inj hs.1 hq hs.2

/-- Exact on the three values the counterexample takes square roots of. -/
noncomputable def sqC (x : Rat) : Rat :=
  if x = 0 then 0 else if x = 1 then 1 else if x = epsF * epsF then epsF else classicalSqrt x

theorem sqC_exact : SqrtExact sqC := by
  intro q hq
  unfold sqC
  by_cases h0 : q * q = 0
  · rw [if_pos h0]
    rcases Rat.mul_eq_zero.mp h0 with h | h <;> exact h.symm
  · rw [if_neg h0]
    by_cases h1 : q * q = 1
    · rw [if_pos h1]; exact (sq_inj hq (by with_unfolding_all decide) (by rw [h1]; with_unfolding_all decide)).symm
    · rw [if_neg h1]
      by_cases h2 : q * q = epsF * epsF
      · rw [if_pos h2]; exact (sq_inj hq (by with_unfolding_all decide) h2).symm
      · rw [if_neg h2]; exact classicalSqrt_exact q hq

theorem greedyScaleInvariant_refuted : ¬ greedyScaleInvariant := by
  intro h
  have := h sqC chol1 [[1]] [1] 1 [1] 1 none 1 (1 / 1000) epsF sqC_exact chol1_sound (by with_unfolding_all decide)
  have horig : greedyGram sqC chol1 [[1]] [1] 1 [1] 1 none 1 (1 / 1000) = ([1], true) := by
    decide +kernel
  have hscaled : greedyGram sqC chol1 [[1]] ([1].map (epsF * ·)) (epsF * epsF * 1) [1] 1 none 1
      (1 / 1000) = ([epsF], false) := by
    decide +kernel
  rw [hscaled, horig] at this
  simp at this

end SymReg.Backsolve
