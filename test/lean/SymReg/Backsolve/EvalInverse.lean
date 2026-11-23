import SymReg.Backsolve.Inverse
import DynExpr.Model.Tree
import DynExpr.Eval.Core

/-!
Model of `src/EvaluateInverse.jl`: masked inversion of a tree evaluation down to one node.

Trees are DE's pure `Tree JF` (plain `Node`, `preserve_sharing = false`). The inverted node is
identified by its path of one-based child indices from the root (`none` when the node is not
in the tree); for an alias-free tree this is exactly the object identity tested by `===` at
`src/EvaluateInverse.jl:168,253`. Node degrees are at most 2 (`Node{T,2}`, the default node
type and the only one `BacksolveMutation` accepts, `src/Mutate.jl:777`); a node of higher
degree is outside the model. The data matrix is the list of samples (`X[:, r]`), each a list
of feature values. Sibling subtrees use DE's constant-tree shortcut before rowwise
evaluation with `early_exit=false` (`src/EvaluateInverse.jl:27-60`); the evaluation buffer reset
(`_reset_eval_buffer!`) has no observable effect here.
-/

namespace SymReg.Backsolve
open DynExpr

/-- One sample: its feature values, one-based. -/
abbrev Row := List JF

/-- Operator enum: `ops[d - 1]` lists the degree-`d` operators, one-based. -/
abbrev Ops := List (List Op)

/-- Number of degree-`d` operators. -/
def nopsOf (ops : Ops) (d : Nat) : Nat := (ops[d - 1]?.getD []).length

/-- Operator selection of `inner_dispatch_degn_masked` (`src/EvaluateInverse.jl:186-223`):
with no operator of this degree it throws `ArgumentError`; otherwise `@nif` tests
`i == op_idx` for `i < nops` and falls through to operator `nops`. -/
def opDispatch (ops : Ops) (d o : Nat) : Jl Op :=
  if (ops[d - 1]?.getD []).length = 0 then
    throw (.argumentError "eval_inverse_tree_array cannot invert node degree with the configured operators.")
  else
    match (ops[d - 1]?.getD [])[(if 1 ≤ o ∧ o < (ops[d - 1]?.getD []).length then o
        else (ops[d - 1]?.getD []).length) - 1]? with
    | some op => pure op
    | none => throw .boundsError

/-- Feature access `X[i, row]`. -/
def featAt (row : Row) (i : Nat) : Jl JF :=
  if i = 0 then throw .boundsError
  else match row[i - 1]? with
    | some v => pure v
    | none => throw .boundsError

mutual
/-- Evaluation of a tree on one sample, children first (DE `eval_tree_array`). -/
def evalRow (L : Lib) (ops : Ops) (row : Row) : Tree JF → Jl JF
  | .const v => pure v
  | .feature i => featAt row i
  | .branch o cs => do
    let vs ← evalRows L ops row cs
    match (ops[cs.length - 1]?.getD [])[o - 1]? with
    | some op => op.eval L vs
    | none => throw .boundsError

/-- The children's values, left to right. -/
def evalRows (L : Lib) (ops : Ops) (row : Row) : List (Tree JF) → Jl (List JF)
  | [] => pure []
  | c :: cs => do
    let v ← evalRow L ops row c
    let vs ← evalRows L ops row cs
    pure (v :: vs)
end

-- Source: src/EvaluateInverse.jl:259–267; DE src/Evaluate.jl:315–328
-- elseif is_constant(tree)
--     const_result = dispatch_constant_tree(tree, operators, eval_context.early_exit)
--     return ResultOk(get_filled_array(eval_context.buffer, const_result.x, cX, axes(cX, 2)), true)
def evalArr (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) : Jl (List JF) :=
  if DynExpr.Eval.isConstant t then do
    let v ← evalRow L ops [] t
    pure (List.replicate X.length v)
  else X.mapM (fun row => evalRow L ops row t)

mutual
private theorem constantEvalRow (L : Lib) (ops : Ops) (row : Row) :
    ∀ t : Tree JF, DynExpr.Eval.isConstant t = true →
      evalRow L ops row t = evalRow L ops [] t
  | .const _, _ => rfl
  | .feature _, h => by simp [DynExpr.Eval.isConstant] at h
  | .branch _ cs, h => by
    simp only [DynExpr.Eval.isConstant] at h
    simp only [evalRow, constantEvalRows L ops row cs h]
private theorem constantEvalRows (L : Lib) (ops : Ops) (row : Row) :
    ∀ cs : List (Tree JF), DynExpr.Eval.isConstantL cs = true →
      evalRows L ops row cs = evalRows L ops [] cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [DynExpr.Eval.isConstantL, Bool.and_eq_true] at h
    simp only [evalRows, constantEvalRow L ops row c h.1, constantEvalRows L ops row cs h.2]
end

private theorem evalArr_ok {L : Lib} {ops : Ops} {X : List Row} {t : Tree JF} {out : List JF}
    (h : evalArr L ops X t = .ok out) : X.mapM (fun r => evalRow L ops r t) = .ok out := by
  unfold evalArr at h
  by_cases hc : DynExpr.Eval.isConstant t = true
  · rw [if_pos hc] at h
    cases hv : evalRow L ops [] t with
    | error e => simp [hv, bind, Except.bind] at h
    | ok v =>
      simp [hv, bind, Except.bind, pure, Except.pure] at h
      subst out
      have hv' (r : Row) : evalRow L ops r t = .ok v := (constantEvalRow L ops r t hc).trans hv
      induction X with
      | nil => rfl
      | cons r rs ih =>
        rw [List.mapM_cons, hv', ih, List.length_cons, List.replicate_succ]
        rfl
  · simpa [hc] using h

/-- `valid .&= isfinite.(x)` (`src/EvaluateInverse.jl:239,263,280`). -/
def andMask : List Bool → List JF → List Bool
  | b :: bs, v :: vs => (b && v.valid) :: andMask bs vs
  | _, _ => []

/-- `any(Base.Fix1(===, node_to_invert_at), get_child(tree, i))` (`src/EvaluateInverse.jl:253`). -/
def inChild : Option (List Nat) → Nat → Bool
  | some (j :: _), i => j == i
  | _, _ => false

/-- Location of the node inside child `i`. -/
def subLoc : Option (List Nat) → Nat → Option (List Nat)
  | some (j :: rest), i => if j = i then some rest else none
  | _, _ => none

/-- Argument tuple of `degn_invert!` at one row: `y[row]` at position `I`, sibling values
elsewhere (`src/EvaluateInverse.jl:303`). -/
def invArgs (d I : Nat) (sibs : List (List JF)) (r : Nat) (yr : JF) : List JF :=
  (List.range d).map (fun k => if k + 1 == I then yr else (sibs.getD k []).getD r .nan)

/-- The row loop of `degn_invert!` (`src/EvaluateInverse.jl:297-310`): row by row,
`approx_inverse(op, Val(I), args)`; `nothing` returns `false` with the rows done so far
overwritten; otherwise `y[row] = op_inv(y[row])`. -/
def degnInvertGo (L : Lib) (op : Op) (d I : Nat) (sibs : List (List JF)) :
    Nat → List JF → List JF → Jl (Bool × List JF)
  | _, done, [] => pure (true, done)
  | r, done, yr :: rest =>
    match approxInv L (route op I (invArgs d I sibs r yr)) with
    | none => pure (false, done ++ yr :: rest)
    | some g => g yr >>= fun v => degnInvertGo L op d I sibs (r + 1) (done ++ [v]) rest

/-- `degn_invert!(y, siblings, op, Val(degree), Val(I))`. -/
def degnInvert (L : Lib) (op : Op) (d I : Nat) (sibs : List (List JF)) (y : List JF) :
    Jl (Bool × List JF) :=
  degnInvertGo L op d I sibs 0 [] y

/-- Degree-1 branch of `dispatch_degn_masked` (`src/EvaluateInverse.jl:236-244`); `k` is the
recursive call on the child. -/
def uCase (L : Lib) (op : Op) (y : List JF) (valid : List Bool)
    (k : List JF → List Bool → Jl (List JF × List Bool)) : Jl (List JF × List Bool) :=
  degnInvert L op 1 1 [y] y >>= fun p =>
  if !p.1 then pure (p.2, List.replicate p.2.length false)
  else if !((andMask valid p.2).any id) then pure (p.2, andMask valid p.2)
  else k p.2 (andMask valid p.2)

/-- Degree-2 branch of `dispatch_degn_masked` (`src/EvaluateInverse.jl:245-291`): evaluate the
sibling `cSib`, mask, invert at position `c`, mask again, recurse with `k`. -/
def bCase (L : Lib) (ops : Ops) (X : List Row) (op : Op) (c : Nat) (cSib : Tree JF)
    (y : List JF) (valid : List Bool) (k : List JF → List Bool → Jl (List JF × List Bool)) :
    Jl (List JF × List Bool) :=
  evalArr L ops X cSib >>= fun sib =>
  if !((andMask valid sib).any id) then pure (y, andMask valid sib)
  else
    degnInvert L op 2 c (if c = 1 then [y, sib] else [sib, y]) y >>= fun p =>
    if !p.1 then pure (p.2, List.replicate y.length false)
    else if !((andMask (andMask valid sib) p.2).any id) then
      pure (p.2, andMask (andMask valid sib) p.2)
    else k p.2 (andMask (andMask valid sib) p.2)

/-- `_eval_inverse_tree_array_masked` (`src/EvaluateInverse.jl:158-183`) with the dispatch of
`src/EvaluateInverse.jl:186-292`: values and validity mask. -/
def invM (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (loc : Option (List Nat))
    (y : List JF) (valid : List Bool) : Jl (List JF × List Bool) :=
  if loc = some [] then pure (y, valid)
  else match t with
  | .const _ | .feature _ => pure (y, List.replicate y.length false)
  | .branch _ [] => pure (y, List.replicate y.length false)
  | .branch o [c1] =>
    opDispatch ops 1 o >>= fun op =>
    uCase L op y valid (fun y1 v1 => invM L ops X c1 (subLoc loc 1) y1 v1)
  | .branch o [c1, c2] =>
    opDispatch ops 2 o >>= fun op =>
    if inChild loc 1 then
      bCase L ops X op 1 c2 y valid (fun y1 v2 => invM L ops X c1 (subLoc loc 1) y1 v2)
    else
      bCase L ops X op 2 c1 y valid (fun y1 v2 => invM L ops X c2 (subLoc loc 2) y1 v2)
  | .branch _ (_ :: _ :: _ :: _) =>
    throw (.undefinedBehavior "node degree above 2 is outside the modelled Node{T,2}")

/-- `eval_inverse_tree_array_masked(tree, X, operators, node, y)` for a plain `Node`
(`src/EvaluateInverse.jl:121-141`): starts from `copy(y)` and `isfinite.(y)`. -/
def evalInverseMasked (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF)
    (loc : Option (List Nat)) (y : List JF) : Jl (List JF × List Bool) :=
  invM L ops X t loc y (y.map JF.valid)

/-- `eval_inverse_tree_array` (`src/EvaluateInverse.jl:80-100`) and the internal
`_eval_inverse_tree_array` (`src/EvaluateInverse.jl:143-155`, whose `ResultOk` carries the
same pair): the masked values with `all(valid)`. -/
def evalInverse (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF)
    (loc : Option (List Nat)) (y : List JF) : Jl (List JF × Bool) :=
  evalInverseMasked L ops X t loc y >>= fun r => pure (r.1, r.2.all id)

/-! ## Row specification -/

/-- One row of a unary inversion step. -/
def rowUn (L : Lib) (op : Op) (yv : JF) (k : JF → Jl (Option JF)) : Jl (Option JF) :=
  match approxInv L (route op 1 [yv]) with
  | none => pure none
  | some g => g yv >>= fun v => if v.valid then k v else pure none

/-- One row of a binary inversion step with sibling `cSib`, inverting at position `c`. -/
def rowBin (L : Lib) (ops : Ops) (op : Op) (c : Nat) (cSib : Tree JF) (row : Row) (yv : JF)
    (k : JF → Jl (Option JF)) : Jl (Option JF) :=
  evalRow L ops row cSib >>= fun s =>
  if !s.valid then pure none
  else match approxInv L (route op c (if c = 1 then [yv, s] else [s, yv])) with
    | none => pure none
    | some g => g yv >>= fun v => if v.valid then k v else pure none

/-- The per-row inversion: `some v` when every inverse step and every sibling value on the
path is finite, with `v` the inverted value at the node. -/
def rowInv (L : Lib) (ops : Ops) (t : Tree JF) (loc : Option (List Nat)) (row : Row) (yv : JF) :
    Jl (Option JF) :=
  if loc = some [] then pure (some yv)
  else match t with
  | .const _ | .feature _ => pure none
  | .branch _ [] => pure none
  | .branch o [c1] =>
    opDispatch ops 1 o >>= fun op => rowUn L op yv (rowInv L ops c1 (subLoc loc 1) row)
  | .branch o [c1, c2] =>
    opDispatch ops 2 o >>= fun op =>
    if inChild loc 1 then
      rowBin L ops op 1 c2 row yv (rowInv L ops c1 (subLoc loc 1) row)
    else
      rowBin L ops op 2 c1 row yv (rowInv L ops c2 (subLoc loc 2) row)
  | .branch _ (_ :: _ :: _ :: _) =>
    throw (.undefinedBehavior "node degree above 2 is outside the modelled Node{T,2}")

/-- The row specification of the masked inversion: the target must be finite. -/
def rowSpec (L : Lib) (ops : Ops) (t : Tree JF) (loc : Option (List Nat)) (row : Row) (yv : JF) :
    Jl (Option JF) :=
  if yv.valid then rowInv L ops t loc row yv else pure none

/-- Values and mask agree row by row with `R`, starting from `y` and `valid`. -/
@[reducible] def Spec (X : List Row) (R : Row → JF → Jl (Option JF)) (y : List JF)
    (valid : List Bool) (vals : List JF) (mask : List Bool) : Prop :=
  vals.length = X.length ∧ mask.length = X.length ∧
  ∀ r, r < X.length →
    (mask.getD r false = true ↔
      valid.getD r false = true ∧ ∃ v, R (X.getD r []) (y.getD r .nan) = .ok (some v)) ∧
    (mask.getD r false = true → R (X.getD r []) (y.getD r .nan) = .ok (some (vals.getD r .nan)))

/-! ## List lemmas -/

theorem andMask_length : ∀ (a : List Bool) (b : List JF), a.length = b.length →
    (andMask a b).length = a.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [andMask, List.length_cons]
    rw [andMask_length as bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem andMask_getD : ∀ (a : List Bool) (b : List JF) (r : Nat), a.length = b.length →
    (andMask a b).getD r false = (a.getD r false && (b.getD r .nan).valid)
  | [], [], r, _ => by simp [andMask]
  | x :: as, v :: bs, r, h => by
    cases r with
    | zero => simp [andMask]
    | succ r =>
      simp only [andMask, List.getD_cons_succ]
      exact andMask_getD as bs r (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem getD_of_any_false : ∀ (l : List Bool) (r : Nat), l.any id = false → l.getD r false = false
  | [], r, _ => by simp
  | b :: bs, r, h => by
    simp only [List.any_cons, id, Bool.or_eq_false_iff] at h
    cases r with
    | zero => simpa using h.1
    | succ r => simpa using getD_of_any_false bs r h.2

theorem getD_replicate_false (n r : Nat) : (List.replicate n false).getD r false = false := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    cases r with
    | zero => simp [List.replicate_succ]
    | succ r => simpa [List.replicate_succ] using ih r

theorem getD_map_valid : ∀ (y : List JF) (r : Nat),
    (y.map JF.valid).getD r false = (y.getD r .nan).valid
  | [], r => by simp [JF.valid]
  | a :: as, 0 => by simp
  | a :: as, r + 1 => by simpa using getD_map_valid as r

theorem mapM_ok {α β : Type} (f : α → Jl β) (d : α) (e : β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ r, r < xs.length → f (xs.getD r d) = .ok (ys.getD r e)
  | [], ys, h => by
    simp [List.mapM_nil, pure, Except.pure] at h
    subst h; simp
  | a :: as, ys, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | error err => simp [hfa, bind, Except.bind] at h
    | ok b =>
      cases hm : as.mapM f with
      | error err => simp [hfa, hm, bind, Except.bind] at h
      | ok bs =>
        simp [hfa, hm, bind, Except.bind, pure, Except.pure] at h
        subst h
        obtain ⟨hl, hr⟩ := mapM_ok f d e as bs hm
        refine ⟨by simp [hl], fun r hr' => ?_⟩
        cases r with
        | zero => simpa using hfa
        | succ r => simpa using hr r (by simp at hr'; omega)

theorem degnInvertGo_spec (L : Lib) (op : Op) (d I : Nat) (sibs : List (List JF)) :
    ∀ (ys : List JF) (r : Nat) (done out : List JF) (b : Bool),
      degnInvertGo L op d I sibs r done ys = .ok (b, out) →
      out.length = done.length + ys.length ∧
      (b = true → (∀ k, k < done.length → out.getD k .nan = done.getD k .nan) ∧
        ∀ k, k < ys.length → ∃ g,
          approxInv L (route op I (invArgs d I sibs (r + k) (ys.getD k .nan))) = some g ∧
          g (ys.getD k .nan) = .ok (out.getD (done.length + k) .nan)) ∧
      (b = false → ∃ k, k < ys.length ∧
        approxInv L (route op I (invArgs d I sibs (r + k) (ys.getD k .nan))) = none)
  | [], r, done, out, b, h => by
    simp only [degnInvertGo, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | yr :: rest, r, done, out, b, h => by
    simp only [degnInvertGo] at h
    cases ha : approxInv L (route op I (invArgs d I sibs r yr)) with
    | none =>
      simp only [ha, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, fun _ => ⟨0, by simp, by simpa using ha⟩⟩
    | some g =>
      simp only [ha] at h
      cases hg : g yr with
      | error err => simp [hg, bind, Except.bind] at h
      | ok v =>
        simp only [hg, bind, Except.bind] at h
        obtain ⟨hl, ht, hf⟩ := degnInvertGo_spec L op d I sibs rest (r + 1) (done ++ [v]) out b h
        refine ⟨by simp at hl ⊢; omega, fun hb => ?_, fun hb => ?_⟩
        · obtain ⟨hpre, hrows⟩ := ht hb
          refine ⟨fun k hk => ?_, fun k hk => ?_⟩
          · rw [hpre k (by simp; omega)]
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
          · cases k with
            | zero =>
              refine ⟨g, by simpa using ha, ?_⟩
              have := hpre done.length (by simp)
              simp only [List.getD_cons_zero, Nat.add_zero]
              rw [this]
              simpa [List.getD_eq_getElem?_getD] using hg
            | succ k =>
              obtain ⟨g', hg', hk'⟩ := hrows k (by simp at hk; omega)
              refine ⟨g', ?_, ?_⟩
              · have e : r + 1 + k = r + (k + 1) := by omega
                rw [e] at hg'
                simpa using hg'
              · have e : (done ++ [v]).length + k = done.length + (k + 1) := by simp; omega
                rw [e] at hk'
                simpa using hk'
        · obtain ⟨k, hk, hn⟩ := hf hb
          refine ⟨k + 1, by simp; omega, ?_⟩
          have e : r + 1 + k = r + (k + 1) := by omega
          rw [e] at hn
          simpa using hn

theorem degnInvert_spec (L : Lib) (op : Op) (d I : Nat) (sibs : List (List JF)) (y out : List JF)
    (b : Bool) (h : degnInvert L op d I sibs y = .ok (b, out)) :
    out.length = y.length ∧
    (b = true → ∀ r, r < y.length → ∃ g,
      approxInv L (route op I (invArgs d I sibs r (y.getD r .nan))) = some g ∧
      g (y.getD r .nan) = .ok (out.getD r .nan)) ∧
    (b = false → ∀ a, approxInv L (route op I a) = none) := by
  obtain ⟨hl, ht, hf⟩ := degnInvertGo_spec L op d I sibs y 0 [] out b h
  refine ⟨by simpa using hl, fun hb r hr => ?_, fun hb a => ?_⟩
  · obtain ⟨_, hrows⟩ := ht hb
    obtain ⟨g, hg, hv⟩ := hrows r hr
    exact ⟨g, by simpa using hg, by simpa using hv⟩
  · obtain ⟨k, _, hn⟩ := hf hb
    have hs := approxInv_route_isSome L op I (invArgs d I sibs (0 + k) (y.getD k .nan)) a
    rw [hn] at hs
    cases h' : approxInv L (route op I a) with
    | none => rfl
    | some _ => rw [h'] at hs; simp at hs

theorem invArgs_one (sibs : List (List JF)) (r : Nat) (yr : JF) :
    invArgs 1 1 sibs r yr = [yr] := by
  simp [invArgs, List.range_succ]

theorem invArgs_two (c : Nat) (hc : c = 1 ∨ c = 2) (y sib : List JF) (r : Nat) (yr : JF) :
    invArgs 2 c (if c = 1 then [y, sib] else [sib, y]) r yr =
      (if c = 1 then [yr, sib.getD r .nan] else [sib.getD r .nan, yr]) := by
  rcases hc with rfl | rfl <;> simp [invArgs, List.range_succ]

/-! ## The masked inversion agrees with the row specification -/

theorem finish_un (mk V c : Bool) (K : Jl (Option JF)) (w : JF)
    (hiff : mk = true ↔ ((V && c) = true ∧ ∃ v, K = .ok (some v)))
    (himp : mk = true → K = .ok (some w)) :
    (mk = true ↔ V = true ∧ ∃ v, (if c = true then K else pure none) = .ok (some v)) ∧
    (mk = true → (if c = true then K else pure none) = .ok (some w)) := by
  cases c with
  | false =>
    have hmk : mk = false := by
      cases mk
      · rfl
      · exact absurd (hiff.mp rfl).1 (by simp)
    subst hmk
    refine ⟨⟨fun h => ?_, fun ⟨_, v, hv⟩ => ?_⟩, fun h => ?_⟩
    · cases h
    · cases hv
    · cases h
  | true =>
    rw [if_pos rfl]
    simp only [Bool.and_true] at hiff
    exact ⟨hiff, himp⟩

theorem finish_bin (mk V s c : Bool) (K : Jl (Option JF)) (w : JF)
    (hiff : mk = true ↔ ((V && s && c) = true ∧ ∃ v, K = .ok (some v)))
    (himp : mk = true → K = .ok (some w)) :
    (mk = true ↔ V = true ∧ ∃ v, (if (!s) = true then pure none
      else if c = true then K else pure none) = .ok (some v)) ∧
    (mk = true → (if (!s) = true then pure none
      else if c = true then K else pure none) = .ok (some w)) := by
  cases s with
  | false =>
    have hmk : mk = false := by
      cases mk
      · rfl
      · exact absurd (hiff.mp rfl).1 (by simp)
    subst hmk
    refine ⟨⟨fun h => ?_, fun ⟨_, v, hv⟩ => ?_⟩, fun h => ?_⟩
    · cases h
    · cases hv
    · cases h
  | true =>
    rw [if_neg (by decide : ¬ ((!true) = true))]
    simp only [Bool.and_true] at hiff
    exact finish_un mk V c K w hiff himp

theorem finish_false {R : Jl (Option JF)} {V : Bool} (w : JF)
    (h : V = true → ∀ v, R ≠ .ok (some v)) :
    (false = true ↔ V = true ∧ ∃ v, R = .ok (some v)) ∧ (false = true → R = .ok (some w)) := by
  refine ⟨⟨fun h' => ?_, fun ⟨hV, v, hv⟩ => absurd hv (h hV v)⟩, fun h' => ?_⟩ <;> cases h'

theorem uCase_spec (L : Lib) (op : Op) (X : List Row) (y : List JF) (valid : List Bool)
    (vals : List JF) (mask : List Bool) (k : List JF → List Bool → Jl (List JF × List Bool))
    (kr R : Row → JF → Jl (Option JF)) (hR : ∀ row yv, R row yv = rowUn L op yv (kr row))
    (hy : y.length = X.length) (hv : valid.length = X.length)
    (hk : ∀ y1 v1 vals mask, y1.length = X.length → v1.length = X.length →
      k y1 v1 = .ok (vals, mask) → Spec X kr y1 v1 vals mask)
    (h : uCase L op y valid k = .ok (vals, mask)) :
    Spec X R y valid vals mask := by
  unfold uCase at h
  cases hd : degnInvert L op 1 1 [y] y with
  | error e => rw [hd] at h; cases h
  | ok p =>
    obtain ⟨b, y1⟩ := p
    rw [hd] at h
    change (if (!b) = true then pure (y1, List.replicate y1.length false)
      else if (!((andMask valid y1).any id)) = true then pure (y1, andMask valid y1)
      else k y1 (andMask valid y1)) = Except.ok (vals, mask) at h
    obtain ⟨hlen, htrue, hfalse⟩ := degnInvert_spec L op 1 1 [y] y y1 b hd
    have hl1 : y1.length = X.length := by omega
    cases b with
    | false =>
      rw [if_pos (by decide : (!false) = true)] at h
      cases h
      have hall := hfalse rfl
      refine ⟨hl1, by simp [hl1], fun r _ => ?_⟩
      rw [getD_replicate_false]
      refine finish_false _ (fun _ v hv' => ?_)
      rw [hR] at hv'
      unfold rowUn at hv'
      rw [hall] at hv'
      cases hv'
    | true =>
      rw [if_neg (by decide : ¬ ((!true) = true))] at h
      have hrow : ∀ r, r < X.length → ∀ kk : JF → Jl (Option JF),
          rowUn L op (y.getD r .nan) kk =
            (if (y1.getD r .nan).valid = true then kk (y1.getD r .nan) else pure none) := by
        intro r hr kk
        obtain ⟨g, hg, hgv⟩ := htrue rfl r (by omega)
        rw [invArgs_one] at hg
        unfold rowUn
        rw [hg]
        dsimp only
        rw [hgv]
        rfl
      have hm : ∀ r, (andMask valid y1).getD r false =
          (valid.getD r false && (y1.getD r .nan).valid) :=
        fun r => andMask_getD valid y1 r (by omega)
      have hml : (andMask valid y1).length = X.length := by
        rw [andMask_length valid y1 (by omega)]; exact hv
      by_cases hany : (andMask valid y1).any id = true
      · rw [if_neg (by rw [hany]; decide)] at h
        obtain ⟨h1, h2, h3⟩ := hk y1 (andMask valid y1) vals mask hl1 hml h
        refine ⟨h1, h2, fun r hr => ?_⟩
        obtain ⟨hiff, himp⟩ := h3 r hr
        rw [hm r] at hiff
        rw [hR, hrow r hr]
        exact finish_un _ _ _ _ _ hiff himp
      · have hf : (andMask valid y1).any id = false := by simpa using hany
        rw [if_pos (by rw [hf]; decide)] at h
        cases h
        refine ⟨hl1, hml, fun r hr => ?_⟩
        rw [getD_of_any_false _ r hf]
        refine finish_false _ (fun hV v hv' => ?_)
        have hz := getD_of_any_false _ r hf
        rw [hm r, hV] at hz
        simp only [Bool.true_and] at hz
        rw [hR, hrow r hr, if_neg (by rw [hz]; decide)] at hv'
        cases hv'

theorem bCase_spec (L : Lib) (ops : Ops) (op : Op) (c : Nat) (hc : c = 1 ∨ c = 2)
    (cSib : Tree JF) (X : List Row) (y : List JF) (valid : List Bool)
    (vals : List JF) (mask : List Bool) (k : List JF → List Bool → Jl (List JF × List Bool))
    (kr R : Row → JF → Jl (Option JF))
    (hR : ∀ row yv, R row yv = rowBin L ops op c cSib row yv (kr row))
    (hy : y.length = X.length) (hv : valid.length = X.length)
    (hk : ∀ y1 v1 vals mask, y1.length = X.length → v1.length = X.length →
      k y1 v1 = .ok (vals, mask) → Spec X kr y1 v1 vals mask)
    (h : bCase L ops X op c cSib y valid k = .ok (vals, mask)) :
    Spec X R y valid vals mask := by
  unfold bCase at h
  cases he : evalArr L ops X cSib with
  | error e => rw [he] at h; cases h
  | ok sib =>
    rw [he] at h
    change (if (!((andMask valid sib).any id)) = true then pure (y, andMask valid sib)
      else degnInvert L op 2 c (if c = 1 then [y, sib] else [sib, y]) y >>= fun p =>
        if (!p.1) = true then pure (p.2, List.replicate y.length false)
        else if (!((andMask (andMask valid sib) p.2).any id)) = true then
          pure (p.2, andMask (andMask valid sib) p.2)
        else k p.2 (andMask (andMask valid sib) p.2)) = Except.ok (vals, mask) at h
    obtain ⟨hsl, hsr⟩ := mapM_ok (fun row => evalRow L ops row cSib) [] .nan X sib (evalArr_ok he)
    have hm1 : ∀ r, (andMask valid sib).getD r false =
        (valid.getD r false && (sib.getD r .nan).valid) :=
      fun r => andMask_getD valid sib r (by omega)
    have hml1 : (andMask valid sib).length = X.length := by
      rw [andMask_length valid sib (by omega)]; exact hv
    by_cases hany1 : (andMask valid sib).any id = true
    · rw [if_neg (by rw [hany1]; decide)] at h
      cases hd : degnInvert L op 2 c (if c = 1 then [y, sib] else [sib, y]) y with
      | error e => rw [hd] at h; cases h
      | ok p =>
        obtain ⟨b, y1⟩ := p
        rw [hd] at h
        change (if (!b) = true then pure (y1, List.replicate y.length false)
          else if (!((andMask (andMask valid sib) y1).any id)) = true then
            pure (y1, andMask (andMask valid sib) y1)
          else k y1 (andMask (andMask valid sib) y1)) = Except.ok (vals, mask) at h
        obtain ⟨hlen, htrue, hfalse⟩ := degnInvert_spec L op 2 c _ y y1 b hd
        have hl1 : y1.length = X.length := by omega
        cases b with
        | false =>
          rw [if_pos (by decide : (!false) = true)] at h
          cases h
          have hall := hfalse rfl
          refine ⟨hl1, by simp [hy], fun r hr => ?_⟩
          rw [getD_replicate_false]
          refine finish_false _ (fun _ v hv' => ?_)
          rw [hR] at hv'
          unfold rowBin at hv'
          rw [hsr r hr] at hv'
          simp only [bind, Except.bind, hall] at hv'
          revert hv'
          split <;> intro hv' <;> cases hv'
        | true =>
          rw [if_neg (by decide : ¬ ((!true) = true))] at h
          have hrow : ∀ r, r < X.length → ∀ kk : JF → Jl (Option JF),
              rowBin L ops op c cSib (X.getD r []) (y.getD r .nan) kk =
                (if (!(sib.getD r .nan).valid) = true then pure none
                 else if (y1.getD r .nan).valid = true then kk (y1.getD r .nan)
                 else pure none) := by
            intro r hr kk
            obtain ⟨g, hg, hgv⟩ := htrue rfl r (by omega)
            rw [invArgs_two c hc y sib r] at hg
            unfold rowBin
            rw [hsr r hr]
            show (if (!(sib.getD r .nan).valid) = true then pure none
              else match approxInv L (route op c (if c = 1 then [y.getD r .nan, sib.getD r .nan]
                  else [sib.getD r .nan, y.getD r .nan])) with
                | none => pure none
                | some g => g (y.getD r .nan) >>= fun v => if v.valid then kk v else pure none) = _
            rw [hg]
            dsimp only
            rw [hgv]
            rfl
          have hm2 : ∀ r, (andMask (andMask valid sib) y1).getD r false =
              (valid.getD r false && (sib.getD r .nan).valid && (y1.getD r .nan).valid) := by
            intro r
            rw [andMask_getD _ y1 r (by omega), hm1 r]
          have hml2 : (andMask (andMask valid sib) y1).length = X.length := by
            rw [andMask_length _ y1 (by omega)]; exact hml1
          by_cases hany : (andMask (andMask valid sib) y1).any id = true
          · rw [if_neg (by rw [hany]; decide)] at h
            obtain ⟨h1, h2, h3⟩ := hk y1 _ vals mask hl1 hml2 h
            refine ⟨h1, h2, fun r hr => ?_⟩
            obtain ⟨hiff, himp⟩ := h3 r hr
            rw [hm2 r] at hiff
            rw [hR, hrow r hr]
            exact finish_bin _ _ _ _ _ _ hiff himp
          · have hf : (andMask (andMask valid sib) y1).any id = false := by simpa using hany
            rw [if_pos (by rw [hf]; decide)] at h
            cases h
            refine ⟨hl1, hml2, fun r hr => ?_⟩
            rw [getD_of_any_false _ r hf]
            refine finish_false _ (fun hV v hv' => ?_)
            have hz := getD_of_any_false _ r hf
            rw [hm2 r, hV] at hz
            rw [hR, hrow r hr] at hv'
            revert hv'
            cases hs : (sib.getD r .nan).valid <;> cases hy1 : (vals.getD r .nan).valid <;>
              simp_all [pure, Except.pure]
    · have hf : (andMask valid sib).any id = false := by simpa using hany1
      rw [if_pos (by rw [hf]; decide)] at h
      cases h
      refine ⟨hy, hml1, fun r hr => ?_⟩
      rw [getD_of_any_false _ r hf]
      refine finish_false _ (fun hV v hv' => ?_)
      have hz := getD_of_any_false _ r hf
      rw [hm1 r, hV] at hz
      simp only [Bool.true_and] at hz
      rw [hR] at hv'
      unfold rowBin at hv'
      rw [hsr r hr] at hv'
      change (if (!(sib.getD r .nan).valid) = true then pure none else _) = _ at hv'
      rw [if_pos (by rw [hz]; decide)] at hv'
      cases hv'

theorem invM_found (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (y : List JF)
    (valid : List Bool) (vals : List JF) (mask : List Bool) (hy : y.length = X.length)
    (hv : valid.length = X.length) (h : invM L ops X t (some []) y valid = .ok (vals, mask)) :
    Spec X (rowInv L ops t (some [])) y valid vals mask := by
  rw [invM.eq_def, if_pos rfl] at h
  cases h
  refine ⟨hy, hv, fun r _ => ?_⟩
  have hrow : ∀ row yv, rowInv L ops t (some []) row yv = pure (some yv) := by
    intro row yv; rw [rowInv.eq_def, if_pos rfl]
  rw [hrow]
  exact ⟨by simp [pure, Except.pure], fun _ => rfl⟩

theorem invM_spec (L : Lib) (ops : Ops) (X : List Row) :
    ∀ (t : Tree JF) (loc : Option (List Nat)) (y : List JF) (valid : List Bool)
      (vals : List JF) (mask : List Bool),
      y.length = X.length → valid.length = X.length →
      invM L ops X t loc y valid = .ok (vals, mask) →
      Spec X (rowInv L ops t loc) y valid vals mask := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro loc y valid vals mask hy hv h
    by_cases hloc : loc = some []
    · subst hloc; exact invM_found L ops X _ y valid vals mask hy hv h
    · rw [invM.eq_def, if_neg hloc] at h
      cases h
      refine ⟨hy, by simp [hy], fun r _ => ?_⟩
      rw [getD_replicate_false]
      refine finish_false _ (fun _ w hw => ?_)
      rw [rowInv.eq_def, if_neg hloc] at hw
      cases hw
  | hf i =>
    intro loc y valid vals mask hy hv h
    by_cases hloc : loc = some []
    · subst hloc; exact invM_found L ops X _ y valid vals mask hy hv h
    · rw [invM.eq_def, if_neg hloc] at h
      cases h
      refine ⟨hy, by simp [hy], fun r _ => ?_⟩
      rw [getD_replicate_false]
      refine finish_false _ (fun _ w hw => ?_)
      rw [rowInv.eq_def, if_neg hloc] at hw
      cases hw
  | hb o cs ih =>
    intro loc y valid vals mask hy hv h
    by_cases hloc : loc = some []
    · subst hloc; exact invM_found L ops X _ y valid vals mask hy hv h
    rw [invM.eq_def, if_neg hloc] at h
    match cs, ih, h with
    | [], _, h =>
      cases h
      refine ⟨hy, by simp [hy], fun r _ => ?_⟩
      rw [getD_replicate_false]
      refine finish_false _ (fun _ w hw => ?_)
      rw [rowInv.eq_def, if_neg hloc] at hw
      cases hw
    | [c1], ih, h =>
      dsimp only at h
      cases hop : opDispatch ops 1 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        exact uCase_spec L op X y valid vals mask
          (fun y1 v1 => invM L ops X c1 (subLoc loc 1) y1 v1) (rowInv L ops c1 (subLoc loc 1)) _
          (fun row yv => by rw [rowInv.eq_def, if_neg hloc]; dsimp only; rw [hop]; rfl) hy hv
          (fun y1 v1 vals mask h1 h2 hk => ih c1 (by simp) (subLoc loc 1) y1 v1 vals mask h1 h2 hk) h
    | [c1, c2], ih, h =>
      dsimp only at h
      cases hop : opDispatch ops 2 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        have h' : (if inChild loc 1 = true then
            bCase L ops X op 1 c2 y valid (fun y1 v2 => invM L ops X c1 (subLoc loc 1) y1 v2)
          else bCase L ops X op 2 c1 y valid (fun y1 v2 => invM L ops X c2 (subLoc loc 2) y1 v2)) =
            .ok (vals, mask) := h
        by_cases hin : inChild loc 1 = true
        · rw [if_pos hin] at h'
          exact bCase_spec L ops op 1 (Or.inl rfl) c2 X y valid vals mask
            (fun y1 v2 => invM L ops X c1 (subLoc loc 1) y1 v2) (rowInv L ops c1 (subLoc loc 1)) _
            (fun row yv => by
              rw [rowInv.eq_def, if_neg hloc]; dsimp only; rw [hop]
              show (if inChild loc 1 = true then _ else _) = _
              rw [if_pos hin]) hy hv
            (fun y1 v1 vals mask h1 h2 hk => ih c1 (by simp) (subLoc loc 1) y1 v1 vals mask h1 h2 hk) h'
        · rw [if_neg hin] at h'
          exact bCase_spec L ops op 2 (Or.inr rfl) c1 X y valid vals mask
            (fun y1 v2 => invM L ops X c2 (subLoc loc 2) y1 v2) (rowInv L ops c2 (subLoc loc 2)) _
            (fun row yv => by
              rw [rowInv.eq_def, if_neg hloc]; dsimp only; rw [hop]
              show (if inChild loc 1 = true then _ else _) = _
              rw [if_neg hin]) hy hv
            (fun y1 v1 vals mask h1 h2 hk => ih c2 (by simp) (subLoc loc 2) y1 v1 vals mask h1 h2 hk) h'
    | _ :: _ :: _ :: _, _, h => cases h

/-! ## Properties -/

/-- `eval_inverse_tree_array_masked` agrees with the per-row inversion: row `r` is marked
valid exactly when `y[r]`, every inverse step from the root to the node, and every sibling
value on that path are finite at row `r` (with the path's operators all invertible), and the
returned value at a valid row is the inverted value. `eval_inverse_tree_array` and
`_eval_inverse_tree_array` return the same values with `all(valid)`
(`src/EvaluateInverse.jl:80-183`). -/
def maskedRowSpec : Prop :=
  ∀ (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (loc : Option (List Nat))
    (y vals : List JF) (mask : List Bool),
    y.length = X.length → evalInverseMasked L ops X t loc y = .ok (vals, mask) →
    vals.length = X.length ∧ mask.length = X.length ∧
    (∀ r, r < X.length →
      (mask.getD r false = true ↔
        ∃ v, rowSpec L ops t loc (X.getD r []) (y.getD r .nan) = .ok (some v)) ∧
      (mask.getD r false = true →
        rowSpec L ops t loc (X.getD r []) (y.getD r .nan) = .ok (some (vals.getD r .nan)))) ∧
    evalInverse L ops X t loc y = .ok (vals, mask.all id)

theorem maskedRowSpec_holds : maskedRowSpec := by
  intro L ops X t loc y vals mask hy h
  have hv : (y.map JF.valid).length = X.length := by simp [hy]
  obtain ⟨h1, h2, h3⟩ := invM_spec L ops X t loc y (y.map JF.valid) vals mask hy hv h
  refine ⟨h1, h2, fun r hr => ?_, ?_⟩
  · obtain ⟨hiff, himp⟩ := h3 r hr
    rw [getD_map_valid] at hiff
    by_cases hyv : (y.getD r .nan).valid = true
    · simp only [rowSpec, hyv, ↓reduceIte, true_and] at hiff ⊢
      exact ⟨hiff, himp⟩
    · simp only [rowSpec, hyv, Bool.false_eq_true, ↓reduceIte, false_and] at hiff ⊢
      refine ⟨⟨fun hm => (hiff.mp hm).elim, fun ⟨v, hv⟩ => ?_⟩, fun hm => (hiff.mp hm).elim⟩
      cases hv
  · unfold evalInverse
    rw [h]
    rfl

example : evalInverseMasked nanLib [] [[.fin 1]] (.feature 1) (some []) [.fin 2] =
    .ok ([.fin 2], [true]) := rfl

/-- An operator without an approximate inverse on the path to the node (at the position the
path takes). -/
def NoInvOnPath (L : Lib) (ops : Ops) : Tree JF → List Nat → Prop
  | .branch o [c1], i :: rest =>
    (∃ op, opDispatch ops 1 o = .ok op ∧ ∀ a, approxInv L (route op 1 a) = none) ∨
      (i = 1 ∧ NoInvOnPath L ops c1 rest)
  | .branch o [c1, c2], i :: rest =>
    (i = 1 ∧ ((∃ op, opDispatch ops 2 o = .ok op ∧ ∀ a, approxInv L (route op 1 a) = none) ∨
      NoInvOnPath L ops c1 rest)) ∨
    (i = 2 ∧ ((∃ op, opDispatch ops 2 o = .ok op ∧ ∀ a, approxInv L (route op 2 a) = none) ∨
      NoInvOnPath L ops c2 rest))
  | _, _ => False

theorem rowUn_none (L : Lib) (op : Op) (yv : JF) (k : JF → Jl (Option JF))
    (hk : ∀ v w, k v ≠ .ok (some w)) : ∀ w, rowUn L op yv k ≠ .ok (some w) := by
  intro w h
  unfold rowUn at h
  revert h
  cases ha : approxInv L (route op 1 [yv]) with
  | none => intro h; cases h
  | some g =>
    intro h
    dsimp only at h
    cases hg : g yv with
    | error e => rw [hg] at h; cases h
    | ok v =>
      rw [hg] at h
      change (if v.valid = true then k v else pure none) = _ at h
      by_cases hv : v.valid = true
      · rw [if_pos hv] at h; exact hk v w h
      · rw [if_neg hv] at h; cases h

theorem rowBin_none (L : Lib) (ops : Ops) (op : Op) (c : Nat) (cSib : Tree JF) (row : Row)
    (yv : JF) (k : JF → Jl (Option JF)) (hk : ∀ v w, k v ≠ .ok (some w)) :
    ∀ w, rowBin L ops op c cSib row yv k ≠ .ok (some w) := by
  intro w h
  unfold rowBin at h
  cases hs : evalRow L ops row cSib with
  | error e => rw [hs] at h; cases h
  | ok s =>
    rw [hs] at h
    change (if (!s.valid) = true then pure none
      else match approxInv L (route op c (if c = 1 then [yv, s] else [s, yv])) with
        | none => pure none
        | some g => g yv >>= fun v => if v.valid then k v else pure none) = _ at h
    by_cases hsv : (!s.valid) = true
    · rw [if_pos hsv] at h; cases h
    · rw [if_neg hsv] at h
      revert h
      cases ha : approxInv L (route op c (if c = 1 then [yv, s] else [s, yv])) with
      | none => intro h; cases h
      | some g =>
        intro h
        dsimp only at h
        cases hg : g yv with
        | error e => rw [hg] at h; cases h
        | ok v =>
          rw [hg] at h
          change (if v.valid = true then k v else pure none) = _ at h
          by_cases hv : v.valid = true
          · rw [if_pos hv] at h; exact hk v w h
          · rw [if_neg hv] at h; cases h

theorem rowBin_noinv (L : Lib) (ops : Ops) (op : Op) (c : Nat) (cSib : Tree JF) (row : Row)
    (yv : JF) (k : JF → Jl (Option JF)) (hnone : ∀ a, approxInv L (route op c a) = none) :
    ∀ w, rowBin L ops op c cSib row yv k ≠ .ok (some w) := by
  intro w h
  unfold rowBin at h
  cases hs : evalRow L ops row cSib with
  | error e => rw [hs] at h; cases h
  | ok s =>
    rw [hs] at h
    change (if (!s.valid) = true then pure none
      else match approxInv L (route op c (if c = 1 then [yv, s] else [s, yv])) with
        | none => pure none
        | some g => g yv >>= fun v => if v.valid then k v else pure none) = _ at h
    rw [hnone] at h
    by_cases hsv : (!s.valid) = true
    · rw [if_pos hsv] at h; cases h
    · rw [if_neg hsv] at h; cases h

theorem rowInv_absent (L : Lib) (ops : Ops) (row : Row) :
    ∀ (t : Tree JF) (yv w : JF), rowInv L ops t none row yv ≠ .ok (some w) := by
  intro t
  induction t using Tree.induction with
  | hc v => intro yv w h; rw [rowInv.eq_def, if_neg (by simp)] at h; cases h
  | hf i => intro yv w h; rw [rowInv.eq_def, if_neg (by simp)] at h; cases h
  | hb o cs ih =>
    intro yv w h
    rw [rowInv.eq_def, if_neg (by simp)] at h
    match cs, ih, h with
    | [], _, h => cases h
    | [c1], ih, h =>
      dsimp only at h
      cases hop : opDispatch ops 1 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        exact rowUn_none L op yv _ (fun v w => ih c1 (by simp) v w) w h
    | [c1, c2], ih, h =>
      dsimp only at h
      cases hop : opDispatch ops 2 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        exact rowBin_none L ops op 2 c1 row yv _ (fun v w => ih c2 (by simp) v w) w h
    | _ :: _ :: _ :: _, _, h => cases h

theorem rowInv_noinv (L : Lib) (ops : Ops) (row : Row) :
    ∀ (t : Tree JF) (p : List Nat) (yv w : JF), NoInvOnPath L ops t p →
      rowInv L ops t (some p) row yv ≠ .ok (some w) := by
  intro t
  induction t using Tree.induction with
  | hc v => intro p yv w hn; simp [NoInvOnPath] at hn
  | hf i => intro p yv w hn; simp [NoInvOnPath] at hn
  | hb o cs ih =>
    intro p yv w hn h
    match cs, ih, p, hn, h with
    | [], _, _, hn, _ => simp [NoInvOnPath] at hn
    | [c1], ih, [], hn, _ => simp [NoInvOnPath] at hn
    | [c1, c2], ih, [], hn, _ => simp [NoInvOnPath] at hn
    | _ :: _ :: _ :: _, _, _, hn, _ => simp [NoInvOnPath] at hn
    | [c1], ih, i :: rest, hn, h =>
      rw [rowInv.eq_def, if_neg (by simp)] at h
      dsimp only at h
      cases hop : opDispatch ops 1 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        simp only [NoInvOnPath] at hn
        rcases hn with ⟨op', hop', hnone⟩ | ⟨rfl, hrest⟩
        · rw [hop] at hop'; cases hop'
          change rowUn L op yv _ = _ at h
          unfold rowUn at h
          rw [hnone] at h
          cases h
        · exact rowUn_none L op yv _ (fun v w' => ih c1 (by simp) rest v w' hrest) w h
    | [c1, c2], ih, i :: rest, hn, h =>
      rw [rowInv.eq_def, if_neg (by simp)] at h
      dsimp only at h
      cases hop : opDispatch ops 2 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        simp only [NoInvOnPath] at hn
        rcases hn with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
        · change rowBin L ops op 1 c2 row yv (rowInv L ops c1 (subLoc (some (1 :: rest)) 1) row) = _ at h
          rcases hn with ⟨op', hop', hnone⟩ | hrest
          · rw [hop] at hop'; cases hop'
            exact rowBin_noinv L ops op 1 c2 row yv _ hnone w h
          · exact rowBin_none L ops op 1 c2 row yv _
              (fun v w' => ih c1 (by simp) rest v w' hrest) w h
        · change rowBin L ops op 2 c1 row yv (rowInv L ops c2 (subLoc (some (2 :: rest)) 2) row) = _ at h
          rcases hn with ⟨op', hop', hnone⟩ | hrest
          · rw [hop] at hop'; cases hop'
            exact rowBin_noinv L ops op 2 c1 row yv _ hnone w h
          · exact rowBin_none L ops op 2 c1 row yv _
              (fun v w' => ih c2 (by simp) rest v w' hrest) w h

/-- A structural failure yields an all-false mask: when the node is not in the tree, or an
operator on the path to it has no `approx_inverse` at that position (e.g. `abs`, `relu`,
`mod`, a user operator without an InverseFunctions.jl inverse), every row is invalid
(`src/EvaluateInverse.jl:113-114`). -/
def structuralFailure : Prop :=
  ∀ (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (loc : Option (List Nat))
    (y vals : List JF) (mask : List Bool),
    y.length = X.length → evalInverseMasked L ops X t loc y = .ok (vals, mask) →
    (loc = none ∨ ∃ p, loc = some p ∧ NoInvOnPath L ops t p) →
    ∀ r, mask.getD r false = false

theorem structuralFailure_holds : structuralFailure := by
  intro L ops X t loc y vals mask hy h hs r
  obtain ⟨_, h2, h3, _⟩ := maskedRowSpec_holds L ops X t loc y vals mask hy h
  by_cases hr : r < X.length
  · cases hm : mask.getD r false with
    | false => rfl
    | true =>
      obtain ⟨v, hv⟩ := (h3 r hr).1.mp hm
      unfold rowSpec at hv
      by_cases hyv : (y.getD r .nan).valid = true
      · rw [if_pos hyv] at hv
        rcases hs with rfl | ⟨p, rfl, hn⟩
        · exact absurd hv (rowInv_absent L ops _ t _ v)
        · exact absurd hv (rowInv_noinv L ops _ t p _ v hn)
      · rw [if_neg hyv] at hv; cases hv
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : mask.length ≤ r)]

example : evalInverseMasked nanLib [] [[.fin 1]] (.feature 1) none [.fin 2] =
    .ok ([.fin 2], [false]) := rfl

/-! ## Rewriting the node reproduces the target -/

/-- The tree with the subtree at path `p` replaced by `u` (degree at most 2). -/
def replacePath : Tree JF → List Nat → Tree JF → Tree JF
  | _, [], u => u
  | .branch o [c1], 1 :: rest, u => .branch o [replacePath c1 rest u]
  | .branch o [c1, c2], 1 :: rest, u => .branch o [replacePath c1 rest u, c2]
  | .branch o [c1, c2], 2 :: rest, u => .branch o [c1, replacePath c2 rest u]
  | t, _ :: _, _ => t

/-- Every enum operator, inverted at any position with finite arguments, is a right inverse
wherever it returns a finite value. -/
def RightInvOps (L : Lib) (ops : Ops) : Prop :=
  ∀ (d o : Nat) (op : Op) (I : Nat) (args : List JF) (g : JF → Jl JF) (v : JF),
    opDispatch ops d o = .ok op → args.length = d → 1 ≤ I → I ≤ d →
    (∀ a ∈ args, a.valid = true) → approxInv L (route op I args) = some g →
    g (args.getD (I - 1) .nan) = .ok v → v.valid = true →
    op.eval L (args.set (I - 1) v) = .ok (args.getD (I - 1) .nan)

theorem opDispatch_lookup (ops : Ops) (d o : Nat) (op : Op) (h : opDispatch ops d o = .ok op)
    (h1 : 1 ≤ o) (h2 : o ≤ nopsOf ops d) : (ops[d - 1]?.getD [])[o - 1]? = some op := by
  unfold opDispatch at h
  unfold nopsOf at h2
  have hne : ¬ (ops[d - 1]?.getD []).length = 0 := by omega
  rw [if_neg hne] at h
  have hidx : (if 1 ≤ o ∧ o < (ops[d - 1]?.getD []).length then o
      else (ops[d - 1]?.getD []).length) = o := by
    split <;> omega
  rw [hidx] at h
  revert h
  cases hx : (ops[d - 1]?.getD [])[o - 1]? with
  | none => intro h; cases h
  | some op' => intro h; cases h; rfl

theorem evalRow_branch (L : Lib) (ops : Ops) (row : Row) (o : Nat) (cs : List (Tree JF))
    (vs : List JF) (op : Op) (hvs : evalRows L ops row cs = .ok vs)
    (hlk : (ops[cs.length - 1]?.getD [])[o - 1]? = some op) :
    evalRow L ops row (.branch o cs) = op.eval L vs := by
  simp only [evalRow, hvs, hlk, bind, Except.bind]

theorem rowInv_reproduces (L : Lib) (ops : Ops) (row : Row) (hR : RightInvOps L ops) (nf : Nat) :
    ∀ (t : Tree JF) (p : List Nat) (yv v : JF), t.WF 2 (nopsOf ops) nf → yv.valid = true →
      rowInv L ops t (some p) row yv = .ok (some v) →
      evalRow L ops row (replacePath t p (.const v)) = .ok yv := by
  intro t
  induction t using Tree.induction with
  | hc c =>
    intro p yv v _ _ h
    cases p with
    | nil => rw [rowInv.eq_def, if_pos rfl] at h; cases h; rfl
    | cons i rest => rw [rowInv.eq_def, if_neg (by simp)] at h; cases h
  | hf f =>
    intro p yv v _ _ h
    cases p with
    | nil => rw [rowInv.eq_def, if_pos rfl] at h; cases h; rfl
    | cons i rest => rw [rowInv.eq_def, if_neg (by simp)] at h; cases h
  | hb o cs ih =>
    intro p yv v hwf hyv h
    cases p with
    | nil => rw [rowInv.eq_def, if_pos rfl] at h; cases h; rfl
    | cons i rest =>
    simp only [Tree.WF] at hwf
    obtain ⟨⟨hd1, hd2, _⟩, ⟨ho1, ho2, _⟩, hcs⟩ := hwf
    rw [rowInv.eq_def, if_neg (by simp)] at h
    match cs, ih, hd1, hd2, ho2, hcs, h with
    | [], _, hd1, _, _, _, _ => simp at hd1
    | _ :: _ :: _ :: _, _, _, hd2, _, _, _ => simp at hd2
    | [c1], ih, _, _, ho2, hcs, h =>
      dsimp only at h
      cases hop : opDispatch ops 1 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        rw [hop] at h
        change rowUn L op yv (rowInv L ops c1 (subLoc (some (i :: rest)) 1) row) = _ at h
        unfold rowUn at h
        revert h
        cases hg : approxInv L (route op 1 [yv]) with
        | none => intro h; cases h
        | some g =>
          intro h
          dsimp only at h
          cases hgy : g yv with
          | error e => rw [hgy] at h; cases h
          | ok w =>
            rw [hgy] at h
            change (if w.valid = true then rowInv L ops c1 (subLoc (some (i :: rest)) 1) row w
              else pure none) = _ at h
            by_cases hw : w.valid = true
            · rw [if_pos hw] at h
              by_cases hi : i = 1
              · subst hi
                have hrec := ih c1 (by simp) rest w v (hcs c1 (by simp)) hw h
                have hlk := opDispatch_lookup ops 1 o op hop ho1 (by simpa using ho2)
                have hri := hR 1 o op 1 [yv] g w hop rfl (by decide) (by decide)
                  (by simpa using hyv) hg hgy hw
                have hmap : evalRows L ops row [replacePath c1 rest (.const v)] = .ok [w] := by
                  simp only [evalRows, hrec, bind, Except.bind, pure, Except.pure]
                show evalRow L ops row (.branch o [replacePath c1 rest (.const v)]) = _
                rw [evalRow_branch L ops row o _ [w] op hmap hlk]
                exact hri
              · have hsub : subLoc (some (i :: rest)) 1 = none := by simp [subLoc, hi]
                rw [hsub] at h
                exact absurd h (rowInv_absent L ops row c1 w v)
            · rw [if_neg hw] at h; cases h
    | [c1, c2], ih, _, _, ho2, hcs, h =>
      dsimp only at h
      cases hop : opDispatch ops 2 o with
      | error e => rw [hop] at h; cases h
      | ok op =>
        have hlk := opDispatch_lookup ops 2 o op hop ho1 (by simpa using ho2)
        rw [hop] at h
        by_cases hi1 : i = 1
        · subst hi1
          change rowBin L ops op 1 c2 row yv (rowInv L ops c1 (subLoc (some (1 :: rest)) 1) row) =
            _ at h
          unfold rowBin at h
          cases hs : evalRow L ops row c2 with
          | error e => rw [hs] at h; cases h
          | ok s =>
            rw [hs] at h
            change (if (!s.valid) = true then pure none
              else match approxInv L (route op 1 [yv, s]) with
                | none => pure none
                | some g => g yv >>= fun v => if v.valid then
                    rowInv L ops c1 (subLoc (some (1 :: rest)) 1) row v else pure none) = _ at h
            by_cases hsv : (!s.valid) = true
            · rw [if_pos hsv] at h; cases h
            · rw [if_neg hsv] at h
              have hsv' : s.valid = true := by simpa using hsv
              revert h
              cases hg : approxInv L (route op 1 [yv, s]) with
              | none => intro h; cases h
              | some g =>
                intro h
                dsimp only at h
                cases hgy : g yv with
                | error e => rw [hgy] at h; cases h
                | ok w =>
                  rw [hgy] at h
                  change (if w.valid = true then rowInv L ops c1 (some rest) row w
                    else pure none) = _ at h
                  by_cases hw : w.valid = true
                  · rw [if_pos hw] at h
                    have hrec := ih c1 (by simp) rest w v (hcs c1 (by simp)) hw h
                    have hri := hR 2 o op 1 [yv, s] g w hop rfl (by decide) (by decide)
                      (by simp [hyv, hsv']) hg hgy hw
                    have hmap : evalRows L ops row [replacePath c1 rest (.const v), c2] =
                        .ok [w, s] := by
                      simp only [evalRows, hrec, hs, bind, Except.bind, pure, Except.pure]
                    show evalRow L ops row (.branch o [replacePath c1 rest (.const v), c2]) = _
                    rw [evalRow_branch L ops row o _ [w, s] op hmap hlk]
                    exact hri
                  · rw [if_neg hw] at h; cases h
        · have hne : inChild (some (i :: rest)) 1 = false := by simp [inChild, hi1]
          change (if inChild (some (i :: rest)) 1 = true then _ else
            rowBin L ops op 2 c1 row yv (rowInv L ops c2 (subLoc (some (i :: rest)) 2) row)) = _ at h
          rw [if_neg (by simp [hne])] at h
          unfold rowBin at h
          cases hs : evalRow L ops row c1 with
          | error e => rw [hs] at h; cases h
          | ok s =>
            rw [hs] at h
            change (if (!s.valid) = true then pure none
              else match approxInv L (route op 2 [s, yv]) with
                | none => pure none
                | some g => g yv >>= fun v => if v.valid then
                    rowInv L ops c2 (subLoc (some (i :: rest)) 2) row v else pure none) = _ at h
            by_cases hsv : (!s.valid) = true
            · rw [if_pos hsv] at h; cases h
            · rw [if_neg hsv] at h
              have hsv' : s.valid = true := by simpa using hsv
              revert h
              cases hg : approxInv L (route op 2 [s, yv]) with
              | none => intro h; cases h
              | some g =>
                intro h
                dsimp only at h
                cases hgy : g yv with
                | error e => rw [hgy] at h; cases h
                | ok w =>
                  rw [hgy] at h
                  change (if w.valid = true then rowInv L ops c2 (subLoc (some (i :: rest)) 2) row w
                    else pure none) = _ at h
                  by_cases hw : w.valid = true
                  · rw [if_pos hw] at h
                    by_cases hi2 : i = 2
                    · subst hi2
                      have hrec := ih c2 (by simp) rest w v (hcs c2 (by simp)) hw h
                      have hri := hR 2 o op 2 [s, yv] g w hop rfl (by decide) (by decide)
                        (by simp [hyv, hsv']) hg hgy hw
                      have hmap : evalRows L ops row [c1, replacePath c2 rest (.const v)] =
                          .ok [s, w] := by
                        simp only [evalRows, hrec, hs, bind, Except.bind, pure, Except.pure]
                      show evalRow L ops row (.branch o [c1, replacePath c2 rest (.const v)]) = _
                      rw [evalRow_branch L ops row o _ [s, w] op hmap hlk]
                      exact hri
                    · have hsub : subLoc (some (i :: rest)) 2 = none := by simp [subLoc, hi2]
                      rw [hsub] at h
                      exact absurd h (rowInv_absent L ops row c2 w v)
                  · rw [if_neg hw] at h; cases h

/-- With operators that are right inverses wherever finite, every row the mask marks valid is
reproduced: evaluating the tree with the node replaced by that row's inverted value returns
the target `y[r]` (`src/EvaluateInverse.jl:68-79,102-120`). -/
def rightInverseReproduces : Prop :=
  ∀ (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (p : List Nat) (y vals : List JF)
    (mask : List Bool) (nf r : Nat),
    RightInvOps L ops → t.WF 2 (nopsOf ops) nf → y.length = X.length →
    evalInverseMasked L ops X t (some p) y = .ok (vals, mask) → r < X.length →
    mask.getD r false = true →
    evalRow L ops (X.getD r []) (replacePath t p (.const (vals.getD r .nan))) = .ok (y.getD r .nan)

theorem rightInverseReproduces_holds : rightInverseReproduces := by
  intro L ops X t p y vals mask nf r hR hwf hy h hr hm
  obtain ⟨_, _, h3, _⟩ := maskedRowSpec_holds L ops X t (some p) y vals mask hy h
  have hv := (h3 r hr).2 hm
  unfold rowSpec at hv
  by_cases hyv : (y.getD r .nan).valid = true
  · rw [if_pos hyv] at hv
    exact rowInv_reproduces L ops _ hR nf t p _ _ hwf hyv hv
  · rw [if_neg hyv] at hv; cases hv

theorem rightInvOps_empty (L : Lib) : RightInvOps L [] := by
  intro d o op I args g v h
  unfold opDispatch at h
  rw [if_pos (by simp)] at h
  cases h

example : RightInvOps nanLib [] ∧ (Tree.feature 1 : Tree JF).WF 2 (nopsOf []) 1 ∧
    evalInverseMasked nanLib [] [[.fin 1]] (.feature 1) (some []) [.fin 2] =
      .ok ([.fin 2], [true]) ∧ ([true] : List Bool).getD 0 false = true :=
  ⟨rightInvOps_empty nanLib, by simp [Tree.WF], rfl, rfl⟩

/-- The intended contract with SR's own operator table: every row the mask marks valid is
reproduced by the rewritten tree (`src/EvaluateInverse.jl:102-120`: "Rows outside the
principal branch of a non-injective operator ... are marked invalid"). -/
def maskSound : Prop :=
  ∀ (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (p : List Nat) (y vals : List JF)
    (mask : List Bool) (nf r : Nat),
    t.WF 2 (nopsOf ops) nf → y.length = X.length →
    evalInverseMasked L ops X t (some p) y = .ok (vals, mask) → r < X.length →
    mask.getD r false = true →
    evalRow L ops (X.getD r []) (replacePath t p (.const (vals.getD r .nan))) = .ok (y.getD r .nan)

/-- `x1 / x2` with `x2 = 0` on the row. -/
def divOps : Ops := [[], [.b .div]]
/-- The tree `x1 / x2`. -/
def divTree : Tree JF := .branch 1 [.feature 1, .feature 2]

theorem maskSound_refuted : ¬ maskSound := by
  intro h
  have hrun : evalInverseMasked nanLib divOps [[.fin 1, .fin 0]] divTree (some [1]) [.fin 3] =
      .ok ([.fin 0], [true]) := by with_unfolding_all rfl
  have hwf : divTree.WF 2 (nopsOf divOps) 2 := by
    simp [divTree, Tree.WF, nopsOf, divOps]
  have := h nanLib divOps [[.fin 1, .fin 0]] divTree [1] [.fin 3] [.fin 0] [true] 2 0 hwf rfl
    hrun (by decide) rfl
  have hbad : evalRow nanLib divOps [.fin 1, .fin 0] (replacePath divTree [1] (.const (.fin 0))) =
      .ok .nan := by with_unfolding_all rfl
  have e : evalRow nanLib divOps [.fin 1, .fin 0] (replacePath divTree [1] (.const (.fin 0))) =
      .ok (.fin 3) := this
  rw [hbad] at e
  cases e

/-- The intended contract that masking never throws: rows whose inversion leaves the domain are
marked invalid "instead of failing" (`src/EvaluateInverse.jl:102-120`). Stated for finite
data, a well-formed tree, and a library whose only throwing calls are Base's `sin`, `cos`,
`tan` on an infinity (`DomainError`, confirmed on Julia 1.12). -/
def maskedNoThrow : Prop :=
  ∀ (L : Lib) (ops : Ops) (X : List Row) (t : Tree JF) (p : List Nat) (y : List JF) (nf : Nat),
    (∀ f x, (∃ w, L.base f x = .ok w) ∨
      ((f = .sin ∨ f = .cos ∨ f = .tan) ∧ (x = .posInf ∨ x = .negInf))) →
    (∀ x z, ∃ w, L.pow x z = .ok w) → (∀ x z, ∃ w, L.mod x z = .ok w) →
    t.WF 2 (nopsOf ops) nf → y.length = X.length → (∀ a ∈ y, a.valid = true) →
    (∀ row ∈ X, row.length = nf ∧ ∀ a ∈ row, a.valid = true) →
    ∃ res, evalInverseMasked L ops X t (some p) y = .ok res

/-- A library whose `tan` throws `DomainError` on infinities and is the identity otherwise. -/
def tanLib : Lib :=
  ⟨fun f x => if f = .tan ∧ (x = .posInf ∨ x = .negInf) then
      .error (.domainError "tan(x) is only defined for finite x.") else .ok x,
    fun _ _ => .ok (.fin 1), fun _ _ => .ok (.fin 0), none⟩

/-- Operators `atan` (unary) and `/` (binary). -/
def atanOps : Ops := [[.u .atan], [.b .div]]
/-- The tree `1 / atan(x1)`, inverted at `x1`. -/
def atanTree : Tree JF := .branch 1 [.const (.fin 1), .branch 1 [.feature 1]]

theorem maskedNoThrow_refuted : ¬ maskedNoThrow := by
  intro h
  have hlib : ∀ f x, (∃ w, tanLib.base f x = .ok w) ∨
      ((f = .sin ∨ f = .cos ∨ f = .tan) ∧ (x = .posInf ∨ x = .negInf)) := by
    intro f x
    by_cases hc : f = .tan ∧ (x = .posInf ∨ x = .negInf)
    · exact Or.inr ⟨Or.inr (Or.inr hc.1), hc.2⟩
    · refine Or.inl ⟨x, ?_⟩
      show (if f = .tan ∧ (x = .posInf ∨ x = .negInf) then _ else _) = _
      rw [if_neg hc]
  have hwf : atanTree.WF 2 (nopsOf atanOps) 1 := by
    simp [atanTree, Tree.WF, nopsOf, atanOps]
  obtain ⟨res, hres⟩ := h tanLib atanOps [[.fin 2], [.fin 3]] atanTree [2, 1] [.fin 0, .fin 1] 1
    hlib (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩) hwf rfl (by decide) (by decide)
  have hthrow : evalInverseMasked tanLib atanOps [[.fin 2], [.fin 3]] atanTree (some [2, 1])
      [.fin 0, .fin 1] = .error (.domainError "tan(x) is only defined for finite x.") := by
    with_unfolding_all rfl
  rw [hthrow] at hres
  cases hres

end SymReg.Backsolve
