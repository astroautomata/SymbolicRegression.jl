import SymReg.Units.Sound

/-! Completeness of the dimensional check on the arithmetic operators, and the generic
first lattice point of `degn_eval`. -/

namespace SymReg.Units
open DynExpr DynExpr.NodeBase

/-- The first lattice point: when no argument violates or is nonfinite, an operator whose
all-`W` method returns a valid quantity yields exactly that quantity. -/
theorem degn_first {op : Op} {ws : List WQ} {r : WQ} (hne : ws ≠ [])
    (hnv : ∀ w ∈ ws, w.violates = false) (hfin : ∀ w ∈ ws, w.val.valid = true)
    (hm : op.hasMethod (List.replicate ws.length false) = true)
    (hc : op.call (ws.map .w) = .ok (.w r)) (hr : r.violates = false) :
    degnEval op ws = .ok r := by
  unfold degnEval
  have hf : ws.find? (·.violates) = none :=
    List.find?_eq_none.mpr fun w hw => by simp [hnv w hw]
  have ha : ws.any (fun w => !w.val.valid) = false := by
    simp only [List.any_eq_false, Bool.not_eq_true']
    intro w hw; simp [hfin w hw]
  have hlen : ws.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
  have h2 : 2 ≤ 2 ^ ws.length := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ ws.length := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ ws.length = k + 1 := ⟨2 ^ ws.length - 1, by omega⟩
  simp only [hf, ha, Bool.false_eq_true, if_false, hk, List.range_succ_eq_map, lattice,
    pattern_zero, hm, allowed_replicate_false, Bool.and_self, if_true]
  have hne1 : ¬ (0 + 1 = k + 1) := by omega
  simp only [hne1, if_false, argsFor_false, maybeReturnCall, safeCall, hc, WQ.valid, hr,
    Bool.not_false, Bool.and_self, if_true]

/-- Child facts used by the completeness induction. -/
def CP (sc : Scalars) (table : List (List Builtin)) (row : List JF) (xu : List Q)
    (P : Dim → Prop) (c : Tree JF) (w : WQ) : Prop :=
  w.violates = false ∧ w.val = sval sc table row xu c ∧ (w.wildcard = false → ∀ a, P a → a = w.dim)

theorem svalL_eq {sc : Scalars} {table : List (List Builtin)} {row : List JF} {xu : List Q} :
    ∀ {cs : List (Tree JF)} {ws : List WQ},
      All2 (fun c w => w.val = sval sc table row xu c) cs ws → svalL sc table row xu cs = ws.map WQ.val
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp [svalL, svalL_eq t, h]

theorem subFiniteL_mem {sc : Scalars} {table : List (List Builtin)} {row : List JF} {xu : List Q} :
    ∀ {cs : List (Tree JF)}, SubFiniteL sc table row xu cs → ∀ c ∈ cs,
      (sval sc table row xu c).valid = true ∧ SubFinite sc table row xu c
  | [], _, c, hc => by simp at hc
  | _ :: _, ⟨h1, h2, h3⟩, c, hc => by
    cases List.mem_cons.mp hc with
    | inl he => subst he; exact ⟨h1, h2⟩
    | inr hm => exact subFiniteL_mem h3 c hm

section
variable (sc : Scalars)

theorem addSub_complete {bb : Builtin} (hb : bb = .add ∨ bb = .sub) {l rr : WQ}
    {Pl Pr : Dim → Prop} (hlv : l.violates = false) (hrv : rr.violates = false)
    (Ul : l.wildcard = false → ∀ a, Pl a → a = l.dim)
    (Ur : rr.wildcard = false → ∀ a, Pr a → a = rr.dim)
    (hex : ∃ a c, Pl a ∧ Pr c ∧ specRule bb [a, c] = some d0) :
    (wAddSub sc bb l rr).violates = false ∧
      (wAddSub sc bb l rr).val = sc bb [l.val, rr.val] ∧
      ((wAddSub sc bb l rr).wildcard = false → ∀ d, (∃ a c, Pl a ∧ Pr c ∧ specRule bb [a, c] = some d) →
        d = (wAddSub sc bb l rr).dim) := by
  have hs : ∀ a c d, specRule bb [a, c] = some d ↔ a = c ∧ a = d := by
    intro a c d
    rcases hb with rfl | rfl <;> by_cases h : a = c <;> simp [specRule, h]
  unfold wAddSub
  rw [if_neg (by simp [hlv]), if_neg (by simp [hrv])]
  obtain ⟨a0, c0, ha0, hc0, hs0⟩ := hex
  rw [hs] at hs0
  by_cases hd : l.dim = rr.dim
  · rw [if_pos hd]
    refine ⟨rfl, rfl, fun hw d ⟨a, c, ha, hc, hsd⟩ => ?_⟩
    rw [hs] at hsd
    simp only [Bool.and_eq_false_iff] at hw
    rcases hw with hw | hw
    · rw [← hsd.2]; exact Ul hw a ha
    · rw [← hsd.2, hsd.1, hd]; exact Ur hw c hc
  · rw [if_neg hd]
    by_cases hlw : l.wildcard = true <;> by_cases hrw : rr.wildcard = true
    · rw [if_pos (by simp [hlw, hrw])]
      exact ⟨rfl, rfl, fun h => by simp at h⟩
    · rw [if_neg (by simp [hlw, hrw]), if_pos hlw]
      refine ⟨rfl, rfl, fun _ d ⟨a, c, _, hc, hsd⟩ => ?_⟩
      rw [hs] at hsd
      rw [← hsd.2, hsd.1]; exact Ur (by simpa using hrw) c hc
    · rw [if_neg (by simp [hlw, hrw]), if_neg hlw, if_pos hrw]
      refine ⟨rfl, rfl, fun _ d ⟨a, c, ha, _, hsd⟩ => ?_⟩
      rw [hs] at hsd
      rw [← hsd.2]; exact Ul (by simpa using hlw) a ha
    · exfalso
      have e1 := Ul (by simpa using hlw) a0 ha0
      have e2 := Ur (by simpa using hrw) c0 hc0
      exact hd (e1 ▸ e2 ▸ hs0.1)

theorem mulDiv_complete {bb : Builtin} {dop : Dim → Dim → Dim}
    (hspec : ∀ a c d, specRule bb [a, c] = some d ↔ d = dop a c) {l rr : WQ}
    {Pl Pr : Dim → Prop} (hlv : l.violates = false) (hrv : rr.violates = false)
    (Ul : l.wildcard = false → ∀ a, Pl a → a = l.dim)
    (Ur : rr.wildcard = false → ∀ a, Pr a → a = rr.dim) :
    (wMulDiv sc bb dop l rr).violates = false ∧
      (wMulDiv sc bb dop l rr).val = sc bb [l.val, rr.val] ∧
      ((wMulDiv sc bb dop l rr).wildcard = false → ∀ d,
        (∃ a c, Pl a ∧ Pr c ∧ specRule bb [a, c] = some d) → d = (wMulDiv sc bb dop l rr).dim) := by
  unfold wMulDiv
  rw [if_neg (by simp [hlv]), if_neg (by simp [hrv])]
  refine ⟨rfl, rfl, fun hw d ⟨a, c, ha, hc, hsd⟩ => ?_⟩
  simp only [Bool.or_eq_false_iff] at hw
  rw [(hspec a c d).mp hsd, Ul hw.1 a ha, Ur hw.2 c hc]

theorem pow_complete {l rr : WQ} {Pl Pr : Dim → Prop} (hlv : l.violates = false)
    (hrv : rr.violates = false)
    (Ul : l.wildcard = false → ∀ a, Pl a → a = l.dim)
    (Ur : rr.wildcard = false → ∀ a, Pr a → a = rr.dim)
    (hex : ∃ a c, Pl a ∧ Pr c ∧ specRule .pow [a, c] = some d0) :
    (wPow sc l rr).violates = false ∧ (wPow sc l rr).val = sc .pow [l.val, rr.val] ∧
      ((wPow sc l rr).wildcard = false → ∀ d,
        (∃ a c, Pl a ∧ Pr c ∧ specRule .pow [a, c] = some d) → d = (wPow sc l rr).dim) := by
  obtain ⟨a0, c0, ha0, hc0, hs0⟩ := hex
  have hab : a0 = Dim.one ∧ c0 = Dim.one := by
    by_cases h : a0 = Dim.one ∧ c0 = Dim.one
    · exact h
    · simp [specRule, h] at hs0
  have h1 : (decide (l.dim = Dim.one) || l.wildcard) = true := by
    cases hw : l.wildcard
    · have := Ul hw a0 ha0; simp [← this, hab.1]
    · simp
  have h2 : (decide (rr.dim = Dim.one) || rr.wildcard) = true := by
    cases hw : rr.wildcard
    · have := Ur hw c0 hc0; simp [← this, hab.2]
    · simp
  unfold wPow
  rw [if_neg (by simp [hlv]), if_neg (by simp [hrv]), if_pos (by simp [h1, h2])]
  refine ⟨rfl, rfl, fun _ d ⟨a, c, _, _, hsd⟩ => ?_⟩
  by_cases h : a = Dim.one ∧ c = Dim.one
  · simp [specRule, h] at hsd; exact hsd.symm
  · simp [specRule, h] at hsd

theorem unary_complete {bb : Builtin} {dop sdop : Dim → Dim}
    (hspec : ∀ a d, specRule bb [a] = some d ↔ d = sdop a) {l : WQ} {P : Dim → Prop}
    (hlv : l.violates = false) (U : l.wildcard = false → ∀ a, P a → a = l.dim)
    (hexact : l.wildcard = false → dop l.dim = sdop l.dim) :
    (wUnary sc bb dop l).violates = false ∧ (wUnary sc bb dop l).val = sc bb [l.val] ∧
      ((wUnary sc bb dop l).wildcard = false → ∀ d,
        (∃ a, P a ∧ specRule bb [a] = some d) → d = (wUnary sc bb dop l).dim) := by
  unfold wUnary
  rw [if_neg (by simp [hlv])]
  refine ⟨rfl, rfl, fun hw d ⟨a, ha, hsd⟩ => ?_⟩
  rw [(hspec a d).mp hsd, U hw a ha, hexact hw]

variable (table : List (List Builtin)) (row : List JF) (xu : List Q) (allow : Bool)

/-- Completeness of every arithmetic `WildcardQuantity` overload against `specRule`. -/
theorem wop_complete {b : Builtin} (harith : b.arith = true) {ws : List WQ}
    {cs : List (Tree JF)} {d0 : Dim}
    (hc : All2 (fun c w => CP sc table row xu (Typed table (xu.map Q.dim) allow c) c w) cs ws)
    (hex : ∃ ds, All2 (Typed table (xu.map Q.dim) allow) cs ds ∧ specRule b ds = some d0)
    (hroot : ∀ w, ws = [w] → w.wildcard = false →
      (b = .sqrt → w.dim.RootExact 2) ∧ (b = .cbrt → w.dim.RootExact 3)) :
    ∃ r, wop sc b ws = some r ∧ r.violates = false ∧ r.val = sc b (ws.map WQ.val) ∧
      (r.wildcard = false → ∀ d,
        (∃ ds, All2 (Typed table (xu.map Q.dim) allow) cs ds ∧ specRule b ds = some d) →
          d = r.dim) := by
  obtain ⟨ds0, hds0, hs0⟩ := hex
  have hl0 := specRule_length hs0
  have hl1 := hds0.length
  have hl2 := hc.length
  rcases ws with _ | ⟨l, _ | ⟨rr, _ | ⟨x, ws⟩⟩⟩
  · cases b <;> simp [Builtin.arith, Builtin.arity] at harith hl0 hl1 hl2 <;> omega
  · rcases cs with _ | ⟨c1, _ | ⟨c2, cs⟩⟩ <;> simp at hl2
    cases hc with | cons hlc hc' => cases hc' with | nil =>
    obtain ⟨hlv, hlval, Ul⟩ := hlc
    rcases ds0 with _ | ⟨a0, _ | _⟩ <;> simp at hl1
    have hx := hroot l rfl
    have one : ∀ {sdop : Dim → Dim}, (∀ a d, specRule b [a] = some d ↔ d = sdop a) →
        ∀ {r : WQ}, (r.wildcard = false → ∀ d, (∃ a, Typed table (xu.map Q.dim) allow c1 a ∧
          specRule b [a] = some d) → d = r.dim) →
        (r.wildcard = false → ∀ d, (∃ ds, All2 (Typed table (xu.map Q.dim) allow) [c1] ds ∧
          specRule b ds = some d) → d = r.dim) := by
      intro sdop _ r hu hw d ⟨ds, hds, hsd⟩
      cases hds with | cons ha hn => cases hn with | nil => exact hu hw d ⟨_, ha, hsd⟩
    cases b <;> simp [Builtin.arith] at harith
    case sqrt =>
      have hsp : ∀ a d, specRule .sqrt [a] = some d ↔ d = a.scale (1 / 2) := by
        intro a d; simp [specRule, eq_comm]
      obtain ⟨h1, h2, h3⟩ := unary_complete sc hsp (dop := Dim.root 2) hlv Ul
        (fun hw => (hx hw).1 rfl)
      exact ⟨_, rfl, h1, h2, one hsp h3⟩
    case cbrt =>
      have hsp : ∀ a d, specRule .cbrt [a] = some d ↔ d = a.scale (1 / 3) := by
        intro a d; simp [specRule, eq_comm]
      obtain ⟨h1, h2, h3⟩ := unary_complete sc hsp (dop := Dim.root 3) hlv Ul
        (fun hw => (hx hw).2 rfl)
      exact ⟨_, rfl, h1, h2, one hsp h3⟩
    case abs =>
      have hsp : ∀ a d, specRule .abs [a] = some d ↔ d = id a := by
        intro a d; simp [specRule, eq_comm]
      obtain ⟨h1, h2, h3⟩ := unary_complete sc hsp (dop := id) hlv Ul (fun _ => rfl)
      exact ⟨_, rfl, h1, h2, one hsp h3⟩
    case inv =>
      have hsp : ∀ a d, specRule .inv [a] = some d ↔ d = Dim.inv a := by
        intro a d; simp [specRule, eq_comm]
      obtain ⟨h1, h2, h3⟩ := unary_complete sc hsp (dop := Dim.inv) hlv Ul (fun _ => rfl)
      exact ⟨_, rfl, h1, h2, one hsp h3⟩
    all_goals simp [Builtin.arity] at hl0
  · rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, cs⟩⟩⟩ <;> simp at hl2
    cases hc with | cons hlc hc' => cases hc' with | cons hrc hc'' => cases hc'' with | nil =>
    obtain ⟨hlv, hlval, Ul⟩ := hlc
    obtain ⟨hrv, hrval, Ur⟩ := hrc
    rcases ds0 with _ | ⟨a0, _ | ⟨c0, _ | _⟩⟩ <;> simp at hl1
    cases hds0 with | cons ha0 hn => cases hn with | cons hc0 hn' => cases hn' with | nil =>
    have two : ∀ {r : WQ}, (r.wildcard = false → ∀ d, (∃ a c, Typed table (xu.map Q.dim) allow c1 a ∧
          Typed table (xu.map Q.dim) allow c2 c ∧ specRule b [a, c] = some d) → d = r.dim) →
        (r.wildcard = false → ∀ d, (∃ ds, All2 (Typed table (xu.map Q.dim) allow) [c1, c2] ds ∧
          specRule b ds = some d) → d = r.dim) := by
      intro r hu hw d ⟨ds, hds, hsd⟩
      cases hds with | cons ha hn => cases hn with | cons hc hn' => cases hn' with | nil =>
        exact hu hw d ⟨_, _, ha, hc, hsd⟩
    cases b <;> simp [Builtin.arith] at harith
    case add =>
      obtain ⟨h1, h2, h3⟩ := addSub_complete sc (bb := .add) (by simp) hlv hrv Ul Ur
        ⟨a0, c0, ha0, hc0, hs0⟩
      exact ⟨_, rfl, h1, h2, two h3⟩
    case sub =>
      obtain ⟨h1, h2, h3⟩ := addSub_complete sc (bb := .sub) (by simp) hlv hrv Ul Ur
        ⟨a0, c0, ha0, hc0, hs0⟩
      exact ⟨_, rfl, h1, h2, two h3⟩
    case mul =>
      obtain ⟨h1, h2, h3⟩ := mulDiv_complete sc (bb := .mul) (dop := Dim.mul)
        (fun a c d => by simp [specRule, eq_comm]) hlv hrv Ul Ur
      exact ⟨_, rfl, h1, h2, two h3⟩
    case div =>
      obtain ⟨h1, h2, h3⟩ := mulDiv_complete sc (bb := .div) (dop := Dim.div)
        (fun a c d => by simp [specRule, eq_comm]) hlv hrv Ul Ur
      exact ⟨_, rfl, h1, h2, two h3⟩
    case pow =>
      obtain ⟨h1, h2, h3⟩ := pow_complete sc hlv hrv Ul Ur ⟨a0, c0, ha0, hc0, hs0⟩
      exact ⟨_, rfl, h1, h2, two h3⟩
    all_goals simp [Builtin.arity] at hl0
  · cases b <;> simp [Builtin.arith, Builtin.arity] at harith hl0 hl1 hl2 <;> omega

end

mutual
/-- Only operator entries traversed by the tree must be arithmetic; feature
indices must be readable in the supplied first sample. -/
def ArithInput (table : List (List Builtin)) (row : List JF) : Tree JF → Prop
  | .const _ => True
  | .feature i => i ≤ row.length
  | .branch o cs => (∀ b, kindAt table cs.length o = some b → b.arith = true) ∧
      ArithInputL table row cs
def ArithInputL (table : List (List Builtin)) (row : List JF) : List (Tree JF) → Prop
  | [] => True
  | c :: cs => ArithInput table row c ∧ ArithInputL table row cs
end

private theorem arithInput_mem {table : List (List Builtin)} {row : List JF} :
    ∀ {cs : List (Tree JF)}, ArithInputL table row cs →
      ∀ c ∈ cs, ArithInput table row c
  | [], _, _, hc => by simp at hc
  | _ :: _, h, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact arithInput_mem h.2 c hc

private theorem all2_mapM {α β : Type} {f : α → Jl β} :
    ∀ {cs : List α} {ws : List β}, All2 (fun c w => f c = .ok w) cs ws → cs.mapM f = .ok ws
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp [List.mapM_cons, h, all2_mapM hs, bind, Except.bind, pure, Except.pure]

private theorem exists_columns {α β : Type} (R : α → β → Prop) :
    ∀ cs : List α, (∀ c ∈ cs, ∃ w, R c w) → ∃ ws, All2 R cs ws
  | [], _ => ⟨[], .nil⟩
  | c :: cs, h => by
    obtain ⟨w, hw⟩ := h c (by simp)
    obtain ⟨ws, hws⟩ := exists_columns R cs (fun a ha => h a (by simp [ha]))
    exact ⟨w :: ws, .cons hw hws⟩

private theorem opAt_of_kindAt {sc : Scalars} {table : List (List Builtin)}
    {o : Nat} {cs : List (Tree JF)} {b : Builtin} (h : kindAt table cs.length o = some b) :
    opAt (opsOf sc table) (.branch o cs) = .ok (b.toOp sc) := by
  unfold kindAt at h
  split at h
  next h₀ =>
    cases ht : table[cs.length - 1]? with
    | none => simp [ht] at h
    | some os =>
      have ho : os[o - 1]? = some b := by simpa [ht] using h
      simp [opAt, Tree.degree, opOf, SymReg.Complexity.idx1, opsOf, ht, ho,
        h₀.1, h₀.2, bind, Except.bind, pure, Except.pure]
  next _ => cases h

/-- Core induction constructs the successful check result for arithmetic trees. -/
theorem complete_core (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q)
    (row : List JF) (allow : Bool) :
    ∀ t : Tree JF, ArithInput table row t → DegLe D t → SubFinite sc table row xu t →
      RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
      (∃ d, Typed table (xu.map Q.dim) allow t d) →
      ∃ w, dispatch D (opsOf sc table) xu row allow t = .ok w ∧
        CP sc table row xu (Typed table (xu.map Q.dim) allow t) t w := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro _ _ _ _ _
    refine ⟨_, rfl, rfl, rfl, fun hw a ha => ?_⟩
    simp only [Typed] at ha
    simp only at hw; subst hw
    simpa using ha
  | hf i =>
    rintro hi _ _ _ ⟨d, hd⟩
    have hpos : 1 ≤ i := hd.1
    simp only [Typed, List.getElem?_map] at hd
    cases hu : xu[i - 1]? with
    | none => simp [hu] at hd
    | some u =>
      have hidx : i - 1 < row.length := by
        change i ≤ row.length at hi
        omega
      have hx : row[i - 1]? = some (row[i - 1]'hidx) := List.getElem?_eq_getElem hidx
      refine ⟨⟨(row[i - 1]'hidx) * u.val, u.dim, false, false⟩, ?_, rfl, ?_, fun _ a ha => ?_⟩
      · simp [dispatch, tmrT, deg0Eval, SymReg.Complexity.idx1, hpos, hx, hu, bind, Except.bind,
          pure, Except.pure]
      · simp [sval, hx, hu]
      · simpa [Typed, hu] using ha.2.symm
  | hb o cs ih =>
    intro harith hdeg hfin hroots ⟨d0, hty⟩
    simp only [DegLe] at hdeg
    simp only [Typed] at hty
    obtain ⟨b, ds, hk, htl, hsr⟩ := hty
    have hop := opAt_of_kindAt (sc := sc) hk
    have hds := (typedL_all2 table (xu.map Q.dim) allow cs ds).mp htl
    have hab : b.arith = true := harith.1 _ hk
    have hne : cs ≠ [] := by intro hc; simp [hc, kindAt] at hk
    simp only [SubFinite] at hfin
    simp only [RootsExact] at hroots
    obtain ⟨ws, hcols⟩ := exists_columns
      (fun c w => dispatch D (opsOf sc table) xu row allow c = .ok w ∧
        CP sc table row xu (Typed table (xu.map Q.dim) allow c) c w) cs fun c hc => by
      obtain ⟨dc, _, hdc⟩ := hds.mem_left c hc
      exact ih c hc (arithInput_mem harith.2 c hc) (hdeg.2 c hc) (subFiniteL_mem hfin c hc).2
        (rootsExactL_mem hroots.2 c hc) ⟨dc, hdc⟩
    have hall := hcols.imp (fun _ _ _ h => h.1)
    have hchild := hcols.imp (fun _ _ _ h => h.2)
    have hroot : ∀ w', ws = [w'] → w'.wildcard = false →
        (b = .sqrt → w'.dim.RootExact 2) ∧ (b = .cbrt → w'.dim.RootExact 3) := by
      intro w' hws hww
      subst hws
      cases hall with
      | cons hc1 hrest =>
        cases hrest
        have hk1 : kindAt table 1 o = some b := by simpa using hk
        have hv1 : w'.violates = false := by
          cases hchild with | cons h1 _ => exact h1.1
        have := hroots.1 _ w' rfl hc1 hv1 hww
        exact ⟨fun hb => this.1 (hb ▸ hk1), fun hb => this.2 (hb ▸ hk1)⟩
    obtain ⟨r, hwop, hrv, hrval, hru⟩ :=
      wop_complete sc table row xu allow hab hchild ⟨ds, hds, hsr⟩ hroot
    have hnv : ∀ v ∈ ws, v.violates = false := fun v hv => by
      obtain ⟨c, _, hcv⟩ := hchild.mem_right v hv; exact hcv.1
    have hfv : ∀ v ∈ ws, v.val.valid = true := fun v hv => by
      obtain ⟨c, hc, hcv⟩ := hchild.mem_right v hv
      rw [hcv.2.1]; exact (subFiniteL_mem hfin c hc).1
    have hwsne : ws ≠ [] := by
      intro he; subst he; cases hall; exact hne rfl
    have hlen := specRule_length hsr
    have hm : (b.toOp sc).hasMethod (List.replicate ws.length false) = true := by
      have : ws.length = b.arity := by rw [hall.length, ← hds.length, hlen]
      cases b <;> simp [Builtin.arith] at hab <;> simp [Builtin.toOp, this, List.all_replicate]
    have hcall : (b.toOp sc).call (ws.map .w) = .ok (.w r) := by
      cases b <;> simp [Builtin.arith] at hab <;>
        simp only [Builtin.toOp, mapM_toT_map_w ws hwsne, mapM_toW_map_w, hwop]
    have hdg := degn_first hwsne hnv hfv hm hcall hrv
    have hmap := all2_mapM hall
    have hnif : nifDeg D cs.length = cs.length := by simp [nifDeg, hdeg.1]
    refine ⟨r, ?_, ?_⟩
    · unfold dispatch
      simp only [tmrT, List.length_eq_zero_iff, hne, if_false, hnif, tmrF_mapM,
        pure, Except.pure, bind, Except.bind]
      change (cs.mapM (dispatch D (opsOf sc table) xu row allow) >>= fun ws =>
        opAt (opsOf sc table) (.branch o cs) >>= fun op => degnEval op ws) = .ok r
      simp [hmap, hop, hdg, bind, Except.bind]
    · refine ⟨hrv, ?_, fun hw a ha => hru hw a ?_⟩
      · have hvals : All2 (fun c w => w.val = sval sc table row xu c) cs ws :=
          hchild.imp fun _ _ _ h => h.2.1
        simp only [sval, hk, svalL_eq hvals, hrval]
      · simp only [Typed] at ha
        obtain ⟨b'', ds', hk'', htl', hsr'⟩ := ha
        rw [hk] at hk''; cases hk''
        exact ⟨ds', (typedL_all2 table (xu.map Q.dim) allow cs ds').mp htl', hsr'⟩

/-- Completeness on `+ - * / ^ sqrt cbrt abs inv`: a dimensionally consistent tree (some
choice of constant dimensions types it, with the target's dimensions if present) is never
reported as violating, provided every subexpression is finite on the first row and no
root truncates exponents. -/
def units_complete_arith : Prop :=
  ∀ (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q) (yu : Option Q)
    (row : List JF) (allow : Bool) (t : Tree JF),
    ArithInput table row t → DegLe D t → SubFinite sc table row xu t →
    RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
    (∃ d, Typed table (xu.map Q.dim) allow t d ∧ ∀ y, yu = some y → d = y.dim) →
    violatesUnits D (opsOf sc table) xu yu row allow t = .ok false

theorem units_complete_arith_holds : units_complete_arith := by
  intro D sc table xu yu row allow t harith hdeg hfin hroots ⟨d, hd, hy⟩
  obtain ⟨w, hw, hv, _, hu⟩ := complete_core D sc table xu row allow t harith hdeg hfin hroots ⟨d, hd⟩
  cases yu with
  | none => simp [violatesUnits, hw, hv, bind, Except.bind, pure, Except.pure]
  | some y =>
    cases hwa : w.wildcard
    · have hd' : w.dim = y.dim := (hu hwa d hd).symm.trans (hy y rfl)
      simp [violatesUnits, hw, hv, hwa, hd', bind, Except.bind, pure, Except.pure]
    · simp [violatesUnits, hw, hv, hwa, bind, Except.bind, pure, Except.pure]

/-- The preconditions are satisfiable: `x1 * x1` with metre units and target m^2. -/
example : let m : Dim := ⟨1, 0, 0, 0, 0, 0, 0⟩
    let t : Tree JF := .branch 1 [.feature 1, .feature 1]
    (∀ l ∈ [[], [Builtin.mul]], ∀ b ∈ l, b.arith = true) ∧ DegLe 2 t ∧
    SubFinite (fun _ _ => .fin 1) [[], [.mul]] [.fin 2] [⟨.fin 1, m⟩] t ∧
    RootsExact (dispatch 2 (opsOf (fun _ _ => .fin 1) [[], [.mul]]) [⟨.fin 1, m⟩] [.fin 2] true)
      [[], [.mul]] t ∧
    (∃ d, Typed [[], [.mul]] (([⟨.fin 1, m⟩] : List Q).map Q.dim) true t d ∧
      ∀ y, (some ⟨.fin 1, m.mul m⟩ : Option Q) = some y → d = y.dim) := by
  intro m t
  refine ⟨by decide, by simp [t, DegLe], ?_, by simp [t, RootsExact, RootsExactL], m.mul m, ?_,
    fun y hy => by cases hy; rfl⟩
  · simp only [t, SubFinite, SubFiniteL, sval]
    exact ⟨by decide +kernel, trivial, by decide +kernel, trivial, trivial⟩
  · simp only [t, Typed, TypedL]
    exact ⟨.mul, [m, m], by decide, ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, trivial⟩, rfl⟩

end SymReg.Units
