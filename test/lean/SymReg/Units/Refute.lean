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

/-- `cos`, `exp`, `safe_log`, ... applied to dimensionless, valid, finite arguments are
accepted with a dimensionless result (the physical rule for transcendental functions). -/
def units_dimensionless_fn : Prop :=
  ∀ (sc : Scalars) (k n : Nat) (ws : List WQ), ws.length = n → 0 < n →
    (∀ w ∈ ws, w.violates = false ∧ w.val.valid = true ∧ w.dim = Dim.one) →
    ∀ b ∈ [Builtin.fn k n, Builtin.safeFn k n],
      ∃ r, degnEval (b.toOp sc) ws = .ok r ∧ r.violates = false ∧ r.dim = Dim.one

theorem units_dimensionless_fn_refuted : ¬ units_dimensionless_fn := by
  intro h
  obtain ⟨r, hr, hv, _⟩ := h sc1 0 1 [featW Dim.one] rfl (by decide)
    (by intro w hw; simp at hw; subst hw; exact ⟨rfl, rfl, rfl⟩) (.fn 0 1) (by simp)
  have : degnEval ((Builtin.fn 0 1).toOp sc1) [featW Dim.one] = .ok WQ.bad := by decide +kernel
  rw [this] at hr; cases hr; simp [WQ.bad] at hv

/-! ## Dimension-preserving generic operators -/

/-- `neg` and `relu` preserve the dimensions of a non-wildcard argument. -/
def units_neg_preserve : Prop :=
  ∀ (sc : Scalars) (w : WQ), w.violates = false → w.val.valid = true → w.wildcard = false →
    ∃ r, degnEval (Builtin.neg.toOp sc) [w] = .ok r ∧ r.violates = false ∧ r.dim = w.dim

theorem units_neg_preserve_refuted : ¬ units_neg_preserve := by
  intro h
  obtain ⟨r, hr, hv, _⟩ := h sc1 (featW metre) rfl rfl rfl
  have : degnEval (Builtin.neg.toOp sc1) [featW metre] = .ok WQ.bad := by decide +kernel
  rw [this] at hr; cases hr; simp [WQ.bad] at hv

/-! ## Comparisons -/

/-- `greater`, `less`, `greater_equal`, `less_equal` of two arguments with equal
dimensions are accepted with a dimensionless result. -/
def units_compare : Prop :=
  ∀ (sc : Scalars) (k : Nat) (l r : WQ), l.violates = false → r.violates = false →
    l.val.valid = true → r.val.valid = true → l.dim = r.dim →
    ∃ w, degnEval ((Builtin.cmp k).toOp sc) [l, r] = .ok w ∧ w.violates = false ∧ w.dim = Dim.one

theorem units_compare_refuted : ¬ units_compare := by
  intro h
  obtain ⟨w, hw, hv, _⟩ := h sc1 0 (featW metre) (featW metre) rfl rfl rfl rfl rfl
  have : degnEval ((Builtin.cmp 0).toOp sc1) [featW metre, featW metre] = .ok WQ.bad := by
    decide +kernel
  rw [this] at hw; cases hw; simp [WQ.bad] at hv

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
