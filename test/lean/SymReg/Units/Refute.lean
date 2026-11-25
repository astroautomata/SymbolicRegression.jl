import SymReg.Units.Complete

/-! Per-operator rules that the check violates, exponent truncation, and the generic
behaviour of `degn_eval` and the entry points. -/

namespace SymReg.Units
open DynExpr DynExpr.NodeBase

/-- Metres. -/
def metre : Dim := ⟨1, 0, 0, 0, 0, 0, 0⟩

/-- A finite non-wildcard quantity of the given dimensions, as produced by a feature. -/
def featW (d : Dim) : WQ := ⟨.fin 1, d, false, false⟩

/-- Constant scalar semantics used in the counterexamples. -/
def sc1 : Scalars := fun _ _ => .fin 1

/-! ## Dimensionless functions -/

private theorem eq_two_pow_sub_one_of_bits : ∀ (n i : Nat),
    i < 2 ^ n → (∀ j, j < n → i / 2 ^ j % 2 = 1) → i = 2 ^ n - 1
  | 0, i, hlt, _ => by omega
  | n + 1, i, hlt, hbits => by
    have hmod : i % 2 = 1 := by simpa using hbits 0 (by omega)
    have hdiv_lt : i / 2 < 2 ^ n := by
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
      omega
    have hdiv_bits : ∀ j, j < n → (i / 2) / 2 ^ j % 2 = 1 := by
      intro j hj
      rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ j = 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact hbits (j + 1) (by omega)
    have hih := eq_two_pow_sub_one_of_bits n (i / 2) hdiv_lt hdiv_bits
    have hpow : 1 ≤ 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    omega

private theorem pattern_not_all_true {n i : Nat} (hlt : i < 2 ^ n - 1) :
    (pattern n i).all id = false := by
  by_cases hall : (pattern n i).all id = true
  · exfalso
    have hbits : ∀ j, j < n → i / 2 ^ j % 2 = 1 := by
      intro j hj
      have hmem : (i / 2 ^ (n - 1 - (n - 1 - j)) % 2 == 1) ∈ pattern n i := by
        unfold pattern
        exact List.mem_map.mpr ⟨n - 1 - j, List.mem_range.mpr (by omega), rfl⟩
      have ht := List.all_eq_true.mp hall _ hmem
      simp only [id, beq_iff_eq, show n - 1 - (n - 1 - j) = j by omega] at ht
      exact ht
    have hpow : 1 ≤ 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
    have heq := eq_two_pow_sub_one_of_bits n i (by omega) hbits
    omega
  · cases h : (pattern n i).all id with
    | false => rfl
    | true => exact absurd h hall

private theorem mapM_toT_argsFor_none_of_false :
    ∀ (p : List Bool) (ws : List WQ), p.length = ws.length → false ∈ p →
      (argsFor p ws).mapM Arg.toT = none
  | [], [], _, hf => by simp at hf
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | b :: p, w :: ws, hl, hf => by
    cases b with
    | false => simp [argsFor, List.mapM_cons, Arg.toT, bind, Option.bind]
    | true =>
      have hf' : false ∈ p := by simpa using hf
      simp only [argsFor, List.zip_cons_cons, List.map_cons, ↓reduceIte, List.mapM_cons,
        Arg.toT, bind, Option.bind]
      change (Option.bind ((argsFor p ws).mapM Arg.toT) _) = none
      rw [mapM_toT_argsFor_none_of_false p ws (by simpa using hl) hf']
      rfl

private theorem lattice_fn_prefix {sc : Scalars} {k n : Nat} {ws : List WQ}
    (hlen : ws.length = n) {b : Builtin} (hb : b = .fn k n ∨ b = .safeFn k n) :
    ∀ (is : List Nat) (tail : List Nat),
      (∀ i ∈ is, i < 2 ^ n - 1) →
      lattice (b.toOp sc) ws (is ++ tail) = lattice (b.toOp sc) ws tail
  | [], tail, _ => rfl
  | i :: is, tail, hall => by
    have hi : i < 2 ^ n - 1 := hall i List.mem_cons_self
    have hnotall : (pattern ws.length i).all id = false := by
      rw [hlen]; exact pattern_not_all_true hi
    have hne : i + 1 ≠ 2 ^ ws.length := by rw [hlen]; omega
    simp only [List.cons_append, lattice]
    rcases hb with rfl | rfl
    · have hm : ((Builtin.fn k n).toOp sc).hasMethod (pattern ws.length i) = false := by
        simp [Builtin.toOp, hnotall]
      simp only [hm, Bool.false_and, Bool.false_eq_true, if_false]
      exact lattice_fn_prefix hlen (.inl rfl) is tail (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    · by_cases hcond :
          (((Builtin.safeFn k n).toOp sc).hasMethod (pattern ws.length i) &&
            allowed (pattern ws.length i) ws) = true
      · simp only [hcond, if_true, hne, if_false]
        have hfmem : false ∈ pattern ws.length i := by
          by_cases hm : false ∈ pattern ws.length i
          · exact hm
          · exfalso
            have hallt : (pattern ws.length i).all id = true :=
              List.all_eq_true.mpr fun x hx => by
                cases x with
                | true => rfl
                | false => exact absurd hx hm
            rw [hnotall] at hallt; cases hallt
        have htoT : (argsFor (pattern ws.length i) ws).mapM Arg.toT = none :=
          mapM_toT_argsFor_none_of_false (pattern ws.length i) ws (pattern_length _ _) hfmem
        have hmrc : maybeReturnCall ((Builtin.safeFn k n).toOp sc) (argsFor (pattern ws.length i) ws) =
            .ok none := by
          unfold maybeReturnCall safeCall
          simp only [Builtin.toOp, htoT]
          cases (argsFor (pattern ws.length i) ws).mapM Arg.toW <;> simp [wop]
        rw [hmrc]
        exact lattice_fn_prefix hlen (.inr rfl) is tail (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      · simp only [Bool.not_eq_true] at hcond
        simp only [hcond, Bool.false_eq_true, if_false]
        exact lattice_fn_prefix hlen (.inr rfl) is tail (fun x hx => hall x (List.mem_cons_of_mem _ hx))

/-- `cos`, `exp`, `safe_log`, ... applied to dimensionless, valid, finite arguments are
accepted with a dimensionless result (the physical rule for transcendental functions). -/
def units_dimensionless_fn : Prop :=
  ∀ (sc : Scalars) (k n : Nat) (ws : List WQ), ws.length = n → 0 < n →
    (∀ w ∈ ws, w.violates = false ∧ w.val.valid = true ∧ w.dim = Dim.one) →
    ∀ b ∈ [Builtin.fn k n, Builtin.safeFn k n],
      ∃ r, degnEval (b.toOp sc) ws = .ok r ∧ r.violates = false ∧ r.dim = Dim.one

theorem units_dimensionless_fn_holds : units_dimensionless_fn := by
  intro sc k n ws hlen hpos hok b hb
  have hb' : b = .fn k n ∨ b = .safeFn k n := by simpa using hb
  have hfind : ws.find? (·.violates) = none :=
    List.find?_eq_none.mpr fun w hw => by simp [(hok w hw).1]
  have hany : ws.any (fun w => !w.val.valid) = false := by
    simp only [List.any_eq_false, Bool.not_eq_true']
    intro w hw; simp [(hok w hw).2.1]
  have hpow : 1 ≤ 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
  have hrange : List.range (2 ^ ws.length) = List.range (2 ^ n - 1) ++ [2 ^ n - 1] := by
    conv => lhs; rw [hlen, show 2 ^ n = (2 ^ n - 1) + 1 by omega, List.range_succ]
  have hlat : lattice (b.toOp sc) ws (List.range (2 ^ ws.length)) =
      lattice (b.toOp sc) ws [2 ^ n - 1] := by
    rw [hrange]
    exact lattice_fn_prefix hlen hb' (List.range (2 ^ n - 1)) [2 ^ n - 1]
      (fun i hi => List.mem_range.mp hi)
  have hm : (b.toOp sc).hasMethod (List.replicate ws.length true) = true := by
    rcases hb' with rfl | rfl <;> simp [Builtin.toOp, Builtin.arity, hlen, List.all_replicate]
  have hal : allowed (List.replicate ws.length true) ws = true :=
    allowed_replicate_true_of_dim_one ws (fun w hw => (hok w hw).2.2)
  have hlast_eq : 2 ^ n - 1 + 1 = 2 ^ ws.length := by rw [hlen]; omega
  refine ⟨⟨sc b (ws.map WQ.val), Dim.one, false, false⟩, ?_, rfl, rfl⟩
  unfold degnEval
  simp only [hfind, hany, Bool.false_eq_true, ite_false, hlat]
  unfold lattice
  rw [show pattern ws.length (2 ^ n - 1) = List.replicate ws.length true by
    rw [← hlen]; exact pattern_last ws.length]
  simp only [hm, hal, Bool.and_self, ite_true, hlast_eq]
  simp only [allScalar, Builtin.toOp, mapM_toT_map_t]

/-! ## Dimension-preserving generic operators -/

/-- `neg` and `relu` preserve the dimensions of a non-wildcard argument. -/
def units_neg_preserve : Prop :=
  ∀ (sc : Scalars) (w : WQ), w.violates = false → w.val.valid = true → w.wildcard = false →
    ∃ r, degnEval (Builtin.neg.toOp sc) [w] = .ok r ∧ r.violates = false ∧ r.dim = w.dim

theorem units_neg_preserve_holds : units_neg_preserve := by
  intro sc w hv hf _
  refine ⟨⟨sc .neg [w.val], w.dim, w.wildcard, false⟩, ?_, rfl, rfl⟩
  apply degn_first (by simp)
  · intro x hx; simp at hx; subst hx; exact hv
  · intro x hx; simp at hx; subst hx; exact hf
  · simp [Builtin.toOp, Builtin.arity]
  · simp [Builtin.toOp, wop, wUnary, hv, Arg.toT, Arg.toW, List.mapM_cons, bind, Option.bind, pure]
  · rfl

/-! ## Comparisons -/

/-- `greater`, `less`, `greater_equal`, `less_equal` of two arguments with equal
dimensions are accepted with a dimensionless result. -/
def units_compare : Prop :=
  ∀ (sc : Scalars) (k : Nat) (l r : WQ), l.violates = false → r.violates = false →
    l.val.valid = true → r.val.valid = true → l.dim = r.dim →
    ∃ w, degnEval ((Builtin.cmp k).toOp sc) [l, r] = .ok w ∧ w.violates = false ∧ w.dim = Dim.one

theorem units_compare_holds : units_compare := by
  intro sc k l r hlv hrv hlf hrf hdim
  refine ⟨⟨sc (.cmp k) [l.val, r.val], Dim.one, false, false⟩, ?_, rfl, rfl⟩
  apply degn_first (by simp)
  · intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  · intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  · simp [Builtin.toOp, Builtin.arity]
  · simp [Builtin.toOp, wCmp, hlv, hrv, hdim, Arg.toT, Arg.toW, List.mapM_cons,
      bind, Option.bind, pure, Except.map]
  · rfl

/-! ## Exponent truncation in roots -/

/-- Completeness on the arithmetic fragment for every tree whose subexpressions are finite,
without excluding roots whose exponents are not multiples of 1/25200. -/
def units_root_rounding : Prop :=
  ∀ (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q) (yu : Option Q)
    (row : List JF) (allow : Bool) (t : Tree JF),
    (∀ l ∈ table, ∀ b ∈ l, b.arith = true) → DegLe D t → SubFinite sc table row xu t →
    (∃ d, Typed table (xu.map Q.dim) allow t d ∧ ∀ y, yu = some y → d = y.dim) →
    violatesUnits D (opsOf sc table) xu yu row allow t ≠ .ok true

/-- `sqrt(t)` with `sqrt` the first unary operator. -/
def sq (t : Tree JF) : Tree JF := .branch 1 [t]

/-- `sqrt(sqrt(sqrt(sqrt(x1))))`. -/
def s4 : Tree JF := sq (sq (sq (sq (.feature 1))))

/-- `(s5 * s5) / s4` with `s5 = sqrt(s4)`: dimension m^(1/16) / m^(1/16). -/
def roundTree : Tree JF := .branch 2 [.branch 1 [sq s4, sq s4], s4]

/-- Unary `[sqrt]`, binary `[*, /]`. -/
def roundTable : List (List Builtin) := [[.sqrt], [.mul, .div]]

theorem units_root_rounding_refuted : ¬ units_root_rounding := by
  intro h
  have hsq : ∀ c a, Typed roundTable [metre] true c a →
      Typed roundTable [metre] true (sq c) (a.scale (1 / 2)) := fun c a hc =>
    typed_branch roundTable [metre] true (b := .sqrt) (by simp [kindAt, roundTable]) (.cons hc .nil) rfl
  have h0 : Typed roundTable [metre] true (.feature 1) metre := ⟨by decide, rfl⟩
  have h4 := hsq _ _ (hsq _ _ (hsq _ _ (hsq _ _ h0)))
  have h5 := hsq _ _ h4
  have hm := typed_branch roundTable [metre] true (o := 1) (b := .mul) (by decide)
    (.cons h5 (.cons h5 .nil)) rfl
  have hd := typed_branch roundTable [metre] true (o := 2) (b := .div) (by decide)
    (.cons hm (.cons h4 .nil)) rfl
  apply h 2 sc1 roundTable [⟨.fin 1, metre⟩] (some ⟨.fin 1, Dim.one⟩) [.fin 1] true roundTree
    (by decide) (by simp [roundTree, sq, s4, DegLe])
    (by simp [roundTree, sq, s4, SubFinite, SubFiniteL, sval, svalL, sc1, kindAt, roundTable]
        <;> decide +kernel)
    ⟨_, hd, fun y hy => by cases hy; decide +kernel⟩
  decide +kernel

/-! ## Generic behaviour of degn_eval -/

theorem lattice_none {op : Op} {ws : List WQ} (hm : ∀ p, op.hasMethod p = false) :
    ∀ is, lattice op ws is = .ok WQ.bad
  | [] => rfl
  | i :: is => by simp [lattice, hm, lattice_none hm is]

/-- `degn_eval` returns the first violating argument unchanged; otherwise any nonfinite
argument is a violation, before any operator method is consulted. -/
def units_degn_guard : Prop :=
  ∀ (op : Op) (ws : List WQ),
    (∀ w, ws.find? (·.violates) = some w → degnEval op ws = .ok w) ∧
    ((∀ w ∈ ws, w.violates = false) → (∃ w ∈ ws, w.val.valid = false) →
      degnEval op ws = .ok WQ.bad)

theorem units_degn_guard_holds : units_degn_guard := by
  intro op ws
  refine ⟨fun w hw => by simp [degnEval, hw], fun hnv ⟨w, hw, hf⟩ => ?_⟩
  have hfind : ws.find? (·.violates) = none :=
    List.find?_eq_none.mpr fun v hv => by simp [hnv v hv]
  have hany : ws.any (fun w => !w.val.valid) = true := List.any_eq_true.mpr ⟨w, hw, by simp [hf]⟩
  simp [degnEval, hfind, hany]

/-- The method lattice for any operator: the all-`W` method is tried first and its valid
result returned; its errors other than `MethodError` and `DimensionError` propagate; an
operator with no applicable method is a violation. -/
def units_lattice : Prop :=
  ∀ (op : Op) (ws : List WQ) (r : WQ) (e : JlError), ws ≠ [] →
    (∀ w ∈ ws, w.violates = false ∧ w.val.valid = true) →
    (op.hasMethod (List.replicate ws.length false) = true →
      op.call (ws.map .w) = .ok (.w r) → r.violates = false → degnEval op ws = .ok r) ∧
    (op.hasMethod (List.replicate ws.length false) = true →
      op.call (ws.map .w) = .error e → (∀ m, e ≠ .methodError m) → e ≠ dimensionError →
      degnEval op ws = .error e) ∧
    ((∀ p, op.hasMethod p = false) → degnEval op ws = .ok WQ.bad)

theorem units_lattice_holds : units_lattice := by
  intro op ws r e hne hok
  have hnv : ∀ w ∈ ws, w.violates = false := fun w hw => (hok w hw).1
  have hfin : ∀ w ∈ ws, w.val.valid = true := fun w hw => (hok w hw).2
  have hf : ws.find? (·.violates) = none :=
    List.find?_eq_none.mpr fun w hw => by simp [hnv w hw]
  have ha : ws.any (fun w => !w.val.valid) = false := by
    simp only [List.any_eq_false, Bool.not_eq_true']
    intro w hw; simp [hfin w hw]
  refine ⟨fun hm hc hr => degn_first hne hnv hfin hm hc hr, fun hm hc hme hde => ?_, fun hm => ?_⟩
  · have hlen : ws.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    have h2 : 2 ≤ 2 ^ ws.length := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ ws.length := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ ws.length = k + 1 := ⟨2 ^ ws.length - 1, by omega⟩
    have hne1 : ¬ (0 + 1 = k + 1) := by omega
    have hsc : safeCall op (ws.map .w) = .error e := by
      unfold safeCall; rw [hc]
      cases e <;> simp_all
    unfold degnEval
    simp only [hf, ha, Bool.false_eq_true, if_false, hk, List.range_succ_eq_map, lattice,
      pattern_zero, hm, allowed_replicate_false, Bool.and_self, if_true, hne1,
      argsFor_false, maybeReturnCall, hsc, hde]
  · simp only [degnEval, hf, ha, Bool.false_eq_true, if_false]
    exact lattice_none hm _

example : ∃ (op : Op) (ws : List WQ) (r : WQ), ws ≠ [] ∧
    (∀ w ∈ ws, w.violates = false ∧ w.val.valid = true) ∧
    op.hasMethod (List.replicate ws.length false) = true ∧ op.call (ws.map .w) = .ok (.w r) ∧
    r.violates = false :=
  ⟨Builtin.abs.toOp sc1, [featW metre], ⟨.fin 1, metre, false, false⟩, by simp,
    by intro w hw; simp at hw; subst hw; exact ⟨rfl, rfl⟩, by decide, by decide +kernel, rfl⟩

/-! ## Entry points -/

/-- The node methods (`src/DimensionalAnalysis.jl:223-275`): the first column is read
first (BoundsError on an empty dataset); without units the result is `false`; target units
without input units throw; with input units the check of `violatesUnits` runs on the first
column, and without target units it reports exactly the evaluation's violation flag.
Expression wrappers check `get_tree(tree)`. -/
def units_entry : Prop :=
  ∀ (D : Nat) (ops : List (List Op)) (columns : List (List JF)) (xu : Option (List Q))
    (yu : Option Q) (allow : Bool) (t : Tree JF) (E : Type) (getTree : E → Tree JF) (e : E),
    (columns = [] → violatesDataset D ops columns xu yu allow t = .error .boundsError) ∧
    (∀ col rest, columns = col :: rest →
      (xu = none → yu = none → violatesDataset D ops columns xu yu allow t = .ok false) ∧
      (xu = none → yu ≠ none → violatesDataset D ops columns xu yu allow t =
        .error (.errorException "This should never happen. Please submit a bug report.")) ∧
      (∀ xs, xu = some xs →
        violatesDataset D ops columns xu yu allow t = violatesUnits D ops xs yu col allow t)) ∧
    (∀ xs row, violatesUnits D ops xs none row allow t =
      (dispatch D ops xs row allow t).map (·.violates)) ∧
    violatesExpr getTree D ops columns xu yu allow e =
      violatesDataset D ops columns xu yu allow (getTree e)

theorem units_entry_holds : units_entry := by
  intro D ops columns xu yu allow t E getTree e
  refine ⟨fun h => by subst h; rfl, fun col rest h => ?_, fun xs row => ?_, rfl⟩
  · subst h
    refine ⟨fun h1 h2 => by subst h1; subst h2; rfl, fun h1 h2 => ?_, fun xs h1 => by subst h1; rfl⟩
    subst h1
    cases yu with
    | none => exact absurd rfl h2
    | some y => rfl
  · unfold violatesUnits
    cases dispatch D ops xs row allow t <;> rfl

example : ∃ (col : List JF) (rest : List (List JF)), [[JF.fin 1]] = col :: rest :=
  ⟨[.fin 1], [], rfl⟩

/-- The hypotheses of `units_degn_guard` are satisfiable. -/
example : (∀ w ∈ [(⟨.nan, metre, false, false⟩ : WQ)], w.violates = false) ∧
    ∃ w ∈ [(⟨.nan, metre, false, false⟩ : WQ)], w.val.valid = false :=
  ⟨by simp, ⟨⟨.nan, metre, false, false⟩, by simp, rfl⟩⟩

end SymReg.Units
