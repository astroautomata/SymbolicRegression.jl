import SymReg.Units.Core

/-! Algebra of exponent vectors and unfolding lemmas for the dimensional check. -/

namespace SymReg.Units
open DynExpr DynExpr.NodeBase

namespace Dim

theorem div_mul_cancel (a b : Dim) : (a.div b).mul b = a := by
  cases a; cases b; simp only [div, mul, map2, mk.injEq]; grind

theorem mul_div_cancel' (a d : Dim) : a.mul (d.div a) = d := by
  cases a; cases d; simp only [div, mul, map2, mk.injEq]; grind

theorem mul_div_cancel (d b : Dim) : (d.mul b).div b = d := by
  cases d; cases b; simp only [div, mul, map2, mk.injEq]; grind

theorem div_div_cancel (a d : Dim) : a.div (a.div d) = d := by
  cases a; cases d; simp only [div, map2, mk.injEq]; grind

theorem scale_scale_two (d : Dim) : (d.scale 2).scale (1 / 2) = d := by
  cases d; simp only [scale, map, mk.injEq]; grind

theorem scale_scale_three (d : Dim) : (d.scale 3).scale (1 / 3) = d := by
  cases d; simp only [scale, map, mk.injEq]; grind

theorem inv_inv (d : Dim) : d.inv.inv = d := by
  cases d; simp only [inv, map, mk.injEq]; grind

@[simp] theorem one_mul_one : one.mul one = one := by decide +kernel
@[simp] theorem one_div_one : one.div one = one := by decide +kernel
@[simp] theorem one_inv : one.inv = one := by decide +kernel
@[simp] theorem one_scale_two : one.scale (1 / 2) = one := by decide +kernel
@[simp] theorem one_scale_three : one.scale (1 / 3) = one := by decide +kernel

end Dim

/-! ## Pointwise relations on lists -/

/-- Two lists related elementwise. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

theorem All2.length {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, All2 R as bs → bs.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]

theorem All2.imp {α β : Type} {R S : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a ∈ as, ∀ b, R a b → S a b) → All2 R as bs → All2 S as bs
  | _, _, _, .nil => .nil
  | _, _, h, .cons hr t =>
    .cons (h _ List.mem_cons_self _ hr) (t.imp fun a ha b => h a (List.mem_cons_of_mem _ ha) b)

theorem mapM_all2 {α β : Type} (f : α → Jl β) :
    ∀ (cs : List α) (ws : List β), cs.mapM f = .ok ws → All2 (fun c w => f c = .ok w) cs ws
  | [], ws, h => by
    simp only [List.mapM_nil] at h; cases h; exact .nil
  | c :: cs, ws, h => by
    simp only [List.mapM_cons] at h
    cases hc : f c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok w =>
      cases hcs : cs.mapM f with
      | error e => simp [hc, hcs, bind, Except.bind] at h
      | ok ws' =>
        simp [hc, hcs, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact .cons hc (mapM_all2 f cs ws' hcs)

theorem typedL_all2 (table : List (List Builtin)) (xu : List Dim) (allow : Bool) :
    ∀ (cs : List (Tree JF)) (ds : List Dim),
      TypedL table xu allow cs ds ↔ All2 (Typed table xu allow) cs ds
  | [], [] => by simp [TypedL]; exact .nil
  | [], _ :: _ => by simp [TypedL]; intro h; cases h
  | _ :: _, [] => by simp [TypedL]; intro h; cases h
  | c :: cs, d :: ds => by
    simp only [TypedL]
    rw [typedL_all2 table xu allow cs ds]
    constructor
    · rintro ⟨h1, h2⟩; exact .cons h1 h2
    · intro h; cases h with | cons h1 h2 => exact ⟨h1, h2⟩

/-! ## Unfolding the tree reduction -/

theorem tmrF_mapM {B : Type} (D : Nat) (fL : Tree JF → Jl WQ) (fB : Tree JF → Jl B)
    (g : B → List WQ → Jl WQ) :
    ∀ (cs : List (Tree JF)),
      tmrF (m := Jl) D fL fB g cs.length cs = cs.mapM (tmrT (m := Jl) D fL fB g)
  | [] => rfl
  | c :: cs => by
    simp only [List.length_cons, tmrF, List.mapM_cons, tmrF_mapM D fL fB g cs]

theorem dispatch_branch {D : Nat} {ops : List (List Op)} {xu : List Q} {row : List JF}
    {allow : Bool} {o : Nat} {cs : List (Tree JF)} {w : WQ} (hD : cs.length ≤ D)
    (h : dispatch D ops xu row allow (.branch o cs) = .ok w) :
    cs ≠ [] ∧ ∃ op ws, opAt ops (.branch o cs) = .ok op ∧
      All2 (fun c w => dispatch D ops xu row allow c = .ok w) cs ws ∧ degnEval op ws = .ok w := by
  unfold dispatch at h
  simp only [tmrT] at h
  by_cases h0 : cs.length = 0
  · simp [h0, deg0Eval] at h
  · have hnif : nifDeg D cs.length = cs.length := by simp [nifDeg, hD]
    simp only [h0, if_false, hnif, tmrF_mapM] at h
    refine ⟨fun hc => h0 (by simp [hc]), ?_⟩
    simp only [pure, Except.pure, bind, Except.bind] at h
    change (cs.mapM (dispatch D ops xu row allow) >>= fun ws =>
      opAt ops (.branch o cs) >>= fun op => degnEval op ws) = .ok w at h
    cases hws : cs.mapM (dispatch D ops xu row allow) with
    | error e => simp [hws, bind, Except.bind] at h
    | ok ws =>
      simp only [hws, bind, Except.bind] at h
      cases hop : opAt ops (.branch o cs) with
      | error e => simp [hop, bind, Except.bind] at h
      | ok op =>
        simp only [hop, bind, Except.bind] at h
        exact ⟨op, ws, rfl, mapM_all2 _ cs ws hws, h⟩

theorem idx1_ok {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : SymReg.Complexity.idx1 xs i = .ok x) : 1 ≤ i ∧ xs[i - 1]? = some x := by
  unfold SymReg.Complexity.idx1 at h
  by_cases h1 : 1 ≤ i
  · simp only [h1, if_true] at h
    cases hx : xs[i - 1]? with
    | none => simp [hx] at h
    | some y => simp [hx] at h; cases h; exact ⟨h1, rfl⟩
  · simp [h1] at h

theorem opAt_opsOf {sc : Scalars} {table : List (List Builtin)} {o : Nat}
    {cs : List (Tree JF)} {op : Op} (h : opAt (opsOf sc table) (.branch o cs) = .ok op) :
    ∃ b, kindAt table cs.length o = some b ∧ op = b.toOp sc := by
  unfold opAt at h
  cases hl : SymReg.Complexity.idx1 (opsOf sc table) (Tree.branch o cs).degree with
  | error e => simp [hl, bind, Except.bind] at h
  | ok l =>
    simp only [hl, bind, Except.bind] at h
    obtain ⟨h1, hl'⟩ := idx1_ok hl
    obtain ⟨h2, ho⟩ := idx1_ok h
    simp only [Tree.degree, opsOf, List.getElem?_map] at h1 hl'
    simp only [opOf] at h2 ho
    cases ht : table[cs.length - 1]? with
    | none => simp [ht] at hl'
    | some row =>
      simp [ht] at hl'
      subst hl'
      simp only [List.getElem?_map] at ho
      cases hr : row[o - 1]? with
      | none => simp [hr] at ho
      | some b =>
        simp [hr] at ho
        exact ⟨b, by simp [kindAt, h1, h2, ht, hr], ho.symm⟩

/-! ## degn_eval -/

theorem degn_ok {op : Op} {ws : List WQ} {w : WQ} (h : degnEval op ws = .ok w)
    (hv : w.violates = false) :
    (∀ v ∈ ws, v.violates = false) ∧ (∀ v ∈ ws, v.val.valid = true) ∧
      lattice op ws (List.range (2 ^ ws.length)) = .ok w := by
  unfold degnEval at h
  cases hf : ws.find? (·.violates) with
  | some v =>
    simp only [hf] at h; cases h
    have := List.find?_some hf; simp [hv] at this
  | none =>
    simp only [hf] at h
    have hnv : ∀ v ∈ ws, v.violates = false := by
      intro v hv'
      have := List.find?_eq_none.mp hf v hv'
      simpa using this
    by_cases ha : ws.any (fun w => !w.val.valid) = true
    · simp only [ha, if_true] at h; cases h; simp [WQ.bad] at hv
    · simp only [ha, Bool.false_eq_true, if_false] at h
      refine ⟨hnv, ?_, h⟩
      intro v hv'
      simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_exists, not_and]
        at ha
      have := ha v hv'
      cases hval : v.val.valid <;> simp_all

theorem lattice_ok {op : Op} {ws : List WQ} {w : WQ} (hv : w.violates = false) :
    ∀ (is : List Nat), lattice op ws is = .ok w →
      ∃ i ∈ is, op.hasMethod (pattern ws.length i) = true ∧
        allowed (pattern ws.length i) ws = true ∧
        ((i + 1 = 2 ^ ws.length ∧ allScalar op ws = .ok w) ∨
          maybeReturnCall op (argsFor (pattern ws.length i) ws) = .ok (some w))
  | [], h => by simp [lattice] at h; cases h; simp [WQ.bad] at hv
  | i :: is, h => by
    simp only [lattice] at h
    by_cases hm : (op.hasMethod (pattern ws.length i) && allowed (pattern ws.length i) ws) = true
    · simp only [hm, if_true] at h
      simp only [Bool.and_eq_true] at hm
      by_cases hl : i + 1 = 2 ^ ws.length
      · simp only [hl, if_true] at h
        exact ⟨i, List.mem_cons_self, hm.1, hm.2, .inl ⟨hl, h⟩⟩
      · simp only [hl, if_false] at h
        cases hmr : maybeReturnCall op (argsFor (pattern ws.length i) ws) with
        | error e => simp [hmr] at h
        | ok r =>
          cases r with
          | some r =>
            simp [hmr] at h; subst h
            exact ⟨i, List.mem_cons_self, hm.1, hm.2, .inr hmr⟩
          | none =>
            simp [hmr] at h
            obtain ⟨j, hj, h1, h2, h3⟩ := lattice_ok hv is h
            exact ⟨j, List.mem_cons_of_mem _ hj, h1, h2, h3⟩
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, if_false] at h
      obtain ⟨j, hj, h1, h2, h3⟩ := lattice_ok hv is h
      exact ⟨j, List.mem_cons_of_mem _ hj, h1, h2, h3⟩

theorem pattern_length (n i : Nat) : (pattern n i).length = n := by simp [pattern]

theorem pattern_last (n : Nat) : pattern n (2 ^ n - 1) = List.replicate n true := by
  apply List.ext_getElem
  · simp [pattern]
  · intro j h1 h2
    simp only [pattern, List.getElem_map, List.getElem_range, List.getElem_replicate]
    have hj : j < n := by simpa [pattern] using h1
    have hb := Nat.testBit_two_pow_sub_one n (n - 1 - j)
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    have : n - 1 - j < n := by omega
    simp only [this, decide_true, decide_eq_true_eq] at hb
    simp [hb]

theorem pattern_zero (n : Nat) : pattern n 0 = List.replicate n false := by
  apply List.ext_getElem
  · simp [pattern]
  · intro j h1 h2
    simp [pattern]

theorem allowed_replicate_true :
    ∀ (ws : List WQ), allowed (List.replicate ws.length true) ws = true → ∀ v ∈ ws, v.wildcard = true
  | [], _ => by simp
  | w :: ws, h => by
    simp only [List.length_cons, List.replicate_succ, allowed, List.zip_cons_cons, List.all_cons,
      Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    intro v hv
    cases List.mem_cons.mp hv with
    | inl he => subst he; exact h.1
    | inr hm => exact allowed_replicate_true ws h.2 v hm

theorem allowed_replicate_false : ∀ (ws : List WQ), allowed (List.replicate ws.length false) ws = true
  | [] => rfl
  | w :: ws => by
    simp only [List.length_cons, List.replicate_succ, allowed, List.zip_cons_cons, List.all_cons,
      Bool.not_false, Bool.true_or, Bool.true_and]
    exact allowed_replicate_false ws

theorem argsFor_false : ∀ (ws : List WQ), argsFor (List.replicate ws.length false) ws = ws.map .w
  | [] => rfl
  | w :: ws => by
    simp only [List.length_cons, List.replicate_succ, argsFor, List.zip_cons_cons, List.map_cons,
      Bool.false_eq_true, if_false]
    exact congrArg _ (argsFor_false ws)

theorem mapM_toW_argsFor : ∀ (p : List Bool) (ws vs : List WQ), p.length = ws.length →
    (argsFor p ws).mapM Arg.toW = some vs → vs = ws
  | [], [], vs, _, h => by simp [argsFor] at h; subst h; rfl
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | b :: p, w :: ws, vs, hl, h => by
    simp only [argsFor, List.zip_cons_cons, List.map_cons, List.mapM_cons] at h
    cases b with
    | true => simp [Arg.toW, bind, Option.bind] at h
    | false =>
      simp only [Bool.false_eq_true, if_false, Arg.toW] at h
      cases hm : List.mapM Arg.toW (List.map (fun x => if x.1 = true then Arg.t x.2.val else Arg.w x.2) (p.zip ws)) with
      | none => simp [hm, bind, Option.bind] at h
      | some vs' =>
        simp [hm, bind, Option.bind, pure] at h
        subst h
        have := mapM_toW_argsFor p ws vs' (by simpa using hl) (by simpa [argsFor] using hm)
        rw [this]

theorem mapM_toT_map_w : ∀ (ws : List WQ), ws ≠ [] → (ws.map Arg.w).mapM Arg.toT = none
  | [], h => absurd rfl h
  | w :: ws, _ => by simp [List.mapM_cons, Arg.toT, bind, Option.bind]

theorem mapM_toW_map_w : ∀ (ws : List WQ), (ws.map Arg.w).mapM Arg.toW = some ws
  | [] => rfl
  | w :: ws => by simp [List.mapM_cons, Arg.toW, mapM_toW_map_w ws, bind, Option.bind, pure]

theorem mapM_toT_map_t : ∀ (ws : List WQ),
    (ws.map fun w => Arg.t w.val).mapM Arg.toT = some (ws.map WQ.val)
  | [] => rfl
  | w :: ws => by simp [List.mapM_cons, Arg.toT, mapM_toT_map_t ws, bind, Option.bind, pure]

/-- A successful built-in lattice point reaching a `W` method is an all-`W` call of a
`WildcardQuantity` overload. -/
theorem builtin_mrc {sc : Scalars} {b : Builtin} {p : List Bool} {ws : List WQ} {r : WQ}
    (hp : p.length = ws.length)
    (h : maybeReturnCall (b.toOp sc) (argsFor p ws) = .ok (some r)) :
    wop sc b ws = some r ∧ r.violates = false := by
  unfold maybeReturnCall safeCall at h
  simp only [Builtin.toOp] at h
  cases ht : (argsFor p ws).mapM Arg.toT with
  | some vs => simp [ht, typeError, dimensionError] at h
  | none =>
    simp only [ht] at h
    cases hw : (argsFor p ws).mapM Arg.toW with
    | none => simp [hw, Option.bind] at h
    | some vs =>
      have := mapM_toW_argsFor p ws vs hp hw
      subst this
      cases hr : wop sc b vs with
      | none => simp [hw, hr, Option.bind] at h
      | some r' =>
        simp [hw, hr, Option.bind, WQ.valid] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        exact ⟨rfl, by simpa using h1⟩

/-- The last lattice point of a built-in operator computes a dimensionless non-wildcard. -/
theorem builtin_allScalar {sc : Scalars} {b : Builtin} {ws : List WQ} {w : WQ}
    (h : allScalar (b.toOp sc) ws = .ok w) :
    w = ⟨sc b (ws.map WQ.val), Dim.one, false, false⟩ := by
  unfold allScalar at h
  simp only [Builtin.toOp, mapM_toT_map_t] at h
  cases h; rfl

theorem arity_of_hasMethod {sc : Scalars} {b : Builtin} {p : List Bool}
    (h : (b.toOp sc).hasMethod p = true) : p.length = b.arity := by
  simp only [Builtin.toOp, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem specRule_ones (b : Builtin) :
    specRule b (List.replicate b.arity Dim.one) = some Dim.one := by
  cases b <;> simp [specRule, Builtin.arity, List.replicate] <;> decide +kernel

theorem specRule_length {b : Builtin} {ds : List Dim} {d : Dim} (h : specRule b ds = some d) :
    ds.length = b.arity := by
  cases b <;> (match ds with
    | [] => first | (simp [specRule] at h; done) | (simp [specRule] at h; simp [Builtin.arity]; omega)
    | [_] => first | rfl | (simp [specRule] at h; done) | (simp [specRule] at h; simp [Builtin.arity]; omega)
    | [_, _] => first | rfl | (simp [specRule] at h; done) | (simp [specRule] at h; simp [Builtin.arity]; omega)
    | _ :: _ :: _ :: _ => first | (simp [specRule] at h; done) | (simp [specRule] at h; simp [Builtin.arity]; omega))

end SymReg.Units
