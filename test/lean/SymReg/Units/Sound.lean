import SymReg.Units.Lemmas

/-! Soundness of the dimensional check: an accepted tree has a consistent assignment of
dimensions to its constants, and a wildcard result can take every dimension. -/

namespace SymReg.Units
open DynExpr DynExpr.NodeBase

/-- The dimensions `P` describes are reachable by `w`: its own, and every dimension when
it is a wildcard. -/
def Sat (P : Dim → Prop) (w : WQ) : Prop := P w.dim ∧ (w.wildcard = true → ∀ d, P d)

theorem Sat.mono {P P' : Dim → Prop} {w : WQ} (h : ∀ d, P d → P' d) (hs : Sat P w) :
    Sat P' w := ⟨h _ hs.1, fun hw d => h d (hs.2 hw d)⟩

theorem All2.imp2 {α β : Type} {R S : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a ∈ as, ∀ b ∈ bs, R a b → S a b) → All2 R as bs →
      All2 S as bs
  | _, _, _, .nil => .nil
  | _, _, h, .cons hr t =>
    .cons (h _ List.mem_cons_self _ List.mem_cons_self hr)
      (t.imp2 fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem All2.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, All2 R as bs → ∀ b ∈ bs, ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hr t, b, hb => by
    cases List.mem_cons.mp hb with
    | inl he => subst he; exact ⟨_, List.mem_cons_self, hr⟩
    | inr hm =>
      obtain ⟨a, ha, h⟩ := t.mem_right b hm
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem All2.mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, All2 R as bs → ∀ a ∈ as, ∃ b ∈ bs, R a b
  | _, _, .nil, _, ha => by simp at ha
  | _, _, .cons hr t, a, ha => by
    cases List.mem_cons.mp ha with
    | inl he => subst he; exact ⟨_, List.mem_cons_self, hr⟩
    | inr hm =>
      obtain ⟨b, hb, h⟩ := t.mem_left a hm
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem All2.const {α β : Type} {R : α → β → Prop} (y : β) :
    ∀ (as : List α), (∀ a ∈ as, R a y) → All2 R as (List.replicate as.length y)
  | [], _ => .nil
  | a :: as, h => .cons (h a List.mem_cons_self)
      (All2.const y as fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem rootsExactL_mem {ev : Tree JF → Jl WQ} {table : List (List Builtin)} :
    ∀ {cs : List (Tree JF)}, RootsExactL ev table cs → ∀ c ∈ cs, RootsExact ev table c
  | [], _, c, hc => by simp at hc
  | _ :: _, ⟨h1, h2⟩, c, hc => by
    cases List.mem_cons.mp hc with
    | inl he => subst he; exact h1
    | inr hm => exact rootsExactL_mem h2 c hm

section
variable (sc : Scalars)

theorem addSub_sound {bb : Builtin} (hb : bb = .add ∨ bb = .sub) {l rr r : WQ}
    {Pl Pr : Dim → Prop} (hl : Sat Pl l) (hr : Sat Pr rr) (hlv : l.violates = false)
    (hrv : rr.violates = false) (h : wAddSub sc bb l rr = r) (hv : r.violates = false) :
    Sat (fun d => ∃ a c, Pl a ∧ Pr c ∧ specRule bb [a, c] = some d) r := by
  have hs : ∀ a, specRule bb [a, a] = some a := by
    intro a; rcases hb with rfl | rfl <;> simp [specRule]
  unfold wAddSub at h
  simp only [hlv, hrv, Bool.false_eq_true, if_false] at h
  by_cases hd : l.dim = rr.dim
  · simp only [hd, if_true] at h; subst h
    refine ⟨⟨l.dim, rr.dim, hl.1, hr.1, by rw [hd]; exact hs _⟩, ?_⟩
    intro hw d
    simp only [Bool.and_eq_true] at hw
    exact ⟨d, d, hl.2 hw.1 d, hr.2 hw.2 d, hs d⟩
  · simp only [hd, if_false] at h
    by_cases hlw : l.wildcard = true <;> by_cases hrw : rr.wildcard = true
    · simp only [hlw, hrw, Bool.and_self, if_true] at h; subst h
      exact ⟨⟨_, _, hl.2 hlw _, hr.2 hrw _, hs _⟩, fun _ d => ⟨d, d, hl.2 hlw d, hr.2 hrw d, hs d⟩⟩
    · simp only [hlw, hrw, Bool.and_false, Bool.false_eq_true, if_false, if_true] at h; subst h
      exact ⟨⟨_, _, hl.2 hlw _, hr.1, hs _⟩, fun hw => by simp at hw⟩
    · simp only [hlw, hrw, Bool.false_and, Bool.false_eq_true, if_false, if_true] at h; subst h
      exact ⟨⟨_, _, hl.1, hr.2 hrw _, hs _⟩, fun hw => by simp at hw⟩
    · simp only [hlw, hrw, Bool.false_and, Bool.false_eq_true, if_false] at h; subst h
      simp [WQ.bad] at hv

theorem mulDiv_sound {bb : Builtin} {dop : Dim → Dim → Dim}
    (hspec : ∀ a c, specRule bb [a, c] = some (dop a c))
    (hl1 : ∀ c d, ∃ a, dop a c = d) (hr1 : ∀ a d, ∃ c, dop a c = d) {l rr r : WQ}
    {Pl Pr : Dim → Prop} (hl : Sat Pl l) (hr : Sat Pr rr) (hlv : l.violates = false)
    (hrv : rr.violates = false) (h : wMulDiv sc bb dop l rr = r) :
    Sat (fun d => ∃ a c, Pl a ∧ Pr c ∧ specRule bb [a, c] = some d) r := by
  unfold wMulDiv at h
  simp only [hlv, hrv, Bool.false_eq_true, if_false] at h; subst h
  refine ⟨⟨l.dim, rr.dim, hl.1, hr.1, hspec _ _⟩, ?_⟩
  intro hw d
  simp only [Bool.or_eq_true] at hw
  rcases hw with hw | hw
  · obtain ⟨a, ha⟩ := hl1 rr.dim d
    exact ⟨a, rr.dim, hl.2 hw a, hr.1, by rw [hspec, ha]⟩
  · obtain ⟨c, hc⟩ := hr1 l.dim d
    exact ⟨l.dim, c, hl.1, hr.2 hw c, by rw [hspec, hc]⟩

theorem pow_sound {l rr r : WQ} {Pl Pr : Dim → Prop} (hl : Sat Pl l) (hr : Sat Pr rr)
    (hlv : l.violates = false) (hrv : rr.violates = false) (h : wPow sc l rr = r)
    (hv : r.violates = false) :
    Sat (fun d => ∃ a c, Pl a ∧ Pr c ∧ specRule .pow [a, c] = some d) r := by
  unfold wPow at h
  simp only [hlv, hrv, Bool.false_eq_true, if_false] at h
  by_cases hc : ((decide (l.dim = Dim.one) || l.wildcard) &&
      (decide (rr.dim = Dim.one) || rr.wildcard)) = true
  · simp only [hc, if_true] at h; subst h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    have ha : Pl Dim.one := by
      rcases hc.1 with h1 | h1
      · exact h1 ▸ hl.1
      · exact hl.2 h1 _
    have hb : Pr Dim.one := by
      rcases hc.2 with h1 | h1
      · exact h1 ▸ hr.1
      · exact hr.2 h1 _
    exact ⟨⟨_, _, ha, hb, by simp [specRule]⟩, fun hw => by simp at hw⟩
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, if_false] at h; subst h
    simp [WQ.bad] at hv

theorem unary_sound {bb : Builtin} {dop : Dim → Dim} {l r : WQ} {P : Dim → Prop}
    (hspec : ∀ a, ∃ e, specRule bb [a] = some e ∧ (l.wildcard = false → a = l.dim → e = dop a))
    (hsurj : ∀ d, ∃ a, specRule bb [a] = some d)
    (hl : Sat P l) (hlv : l.violates = false) (h : wUnary sc bb dop l = r) :
    Sat (fun d => ∃ a, P a ∧ specRule bb [a] = some d) r := by
  unfold wUnary at h
  simp only [hlv, Bool.false_eq_true, if_false] at h; subst h
  cases hw : l.wildcard
  · obtain ⟨e, he, hed⟩ := hspec l.dim
    exact ⟨⟨l.dim, hl.1, by rw [he, hed hw rfl]⟩, fun h => by simp [hw] at h⟩
  · have hall : ∀ d, ∃ a, P a ∧ specRule bb [a] = some d := fun d => by
      obtain ⟨a, ha⟩ := hsurj d; exact ⟨a, hl.2 hw a, ha⟩
    exact ⟨hall _, fun _ => hall⟩

theorem cmp_sound {k : Nat} {l rr r : WQ} {Pl Pr : Dim → Prop}
    (hl : Sat Pl l) (hr : Sat Pr rr) (hlv : l.violates = false) (hrv : rr.violates = false)
    (h : wCmp sc k l rr = .ok r) :
    Sat (fun d => ∃ a c, Pl a ∧ Pr c ∧ specRule (.cmp k) [a, c] = some d) r := by
  unfold wCmp at h
  simp only [hlv, hrv, Bool.or_self, Bool.false_eq_true, if_false] at h
  by_cases hc : (decide (l.dim = rr.dim) || l.wildcard || rr.wildcard) = true
  · simp only [hc, if_true, Except.ok.injEq] at h; subst h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    refine ⟨?_, fun hw => by simp at hw⟩
    rcases hc with (hd | hlw) | hrw
    · exact ⟨l.dim, rr.dim, hl.1, hr.1, by simp [specRule, hd]⟩
    · exact ⟨rr.dim, rr.dim, hl.2 hlw rr.dim, hr.1, by simp [specRule]⟩
    · exact ⟨l.dim, l.dim, hl.1, hr.2 hrw l.dim, by simp [specRule]⟩
  · simp only [Bool.not_eq_true] at hc
    simp [hc] at h

variable (table : List (List Builtin)) (xu : List Dim) (allow : Bool)

/-- Soundness of every `WildcardQuantity` overload against `specRule`. -/
theorem wop_sound {b : Builtin} {ws : List WQ} {r : WQ} {cs : List (Tree JF)}
    (hw : wop sc b ws = some r) (hv : r.violates = false)
    (hc : All2 (fun c w => Sat (Typed table xu allow c) w ∧ w.violates = false) cs ws)
    (hroot : ∀ w, ws = [w] → w.wildcard = false →
      (b = .sqrt → w.dim.RootExact 2) ∧ (b = .cbrt → w.dim.RootExact 3)) :
    Sat (fun d => ∃ ds, All2 (Typed table xu allow) cs ds ∧ specRule b ds = some d) r := by
  have two : ∀ {cl cr : Tree JF},
      Sat (fun d => ∃ a c, Typed table xu allow cl a ∧ Typed table xu allow cr c ∧
        specRule b [a, c] = some d) r →
      Sat (fun d => ∃ ds, All2 (Typed table xu allow) [cl, cr] ds ∧ specRule b ds = some d) r :=
    fun h => h.mono fun d ⟨a, c, ha, hc, hs⟩ => ⟨[a, c], .cons ha (.cons hc .nil), hs⟩
  have one : ∀ {cl : Tree JF},
      Sat (fun d => ∃ a, Typed table xu allow cl a ∧ specRule b [a] = some d) r →
      Sat (fun d => ∃ ds, All2 (Typed table xu allow) [cl] ds ∧ specRule b ds = some d) r :=
    fun h => h.mono fun d ⟨a, ha, hs⟩ => ⟨[a], .cons ha .nil, hs⟩
  rcases ws with _ | ⟨l, _ | ⟨rr, _ | ⟨x, ws⟩⟩⟩
  · cases b <;> simp [wop] at hw
  · cases hc with | cons hlc hc' => cases hc' with | nil =>
    obtain ⟨hl, hlv⟩ := hlc
    have hx := hroot l rfl
    cases b
    all_goals first | (simp [wop] at hw; done) | skip
    case sqrt =>
      simp only [wop, Option.some.injEq] at hw
      exact one (unary_sound sc (fun a => ⟨_, rfl, fun hw' ha => by
          subst ha; exact ((hx hw').1 rfl).symm⟩)
        (fun d => ⟨d.scale 2, by simp [specRule, Dim.scale_scale_two]⟩) hl hlv hw)
    case cbrt =>
      simp only [wop, Option.some.injEq] at hw
      exact one (unary_sound sc (fun a => ⟨_, rfl, fun hw' ha => by
          subst ha; exact ((hx hw').2 rfl).symm⟩)
        (fun d => ⟨d.scale 3, by simp [specRule, Dim.scale_scale_three]⟩) hl hlv hw)
    case abs =>
      simp only [wop, Option.some.injEq] at hw
      exact one (unary_sound sc (fun a => ⟨_, rfl, fun _ _ => rfl⟩)
        (fun d => ⟨d, by simp [specRule]⟩) hl hlv hw)
    case inv =>
      simp only [wop, Option.some.injEq] at hw
      exact one (unary_sound sc (fun a => ⟨_, rfl, fun _ _ => rfl⟩)
        (fun d => ⟨d.inv, by simp [specRule, Dim.inv_inv]⟩) hl hlv hw)
    case neg =>
      simp only [wop, Option.some.injEq] at hw
      exact one (unary_sound sc (fun a => ⟨_, rfl, fun _ _ => rfl⟩)
        (fun d => ⟨d, by simp [specRule]⟩) hl hlv hw)
  · cases hc with | cons hlc hc' => cases hc' with | cons hrc hc'' => cases hc'' with | nil =>
    obtain ⟨hl, hlv⟩ := hlc
    obtain ⟨hr, hrv⟩ := hrc
    cases b
    all_goals first | (simp [wop] at hw; done) | skip
    case add =>
      simp only [wop, Option.some.injEq] at hw
      exact two (addSub_sound sc (by simp) hl hr hlv hrv hw hv)
    case sub =>
      simp only [wop, Option.some.injEq] at hw
      exact two (addSub_sound sc (by simp) hl hr hlv hrv hw hv)
    case mul =>
      simp only [wop, Option.some.injEq] at hw
      exact two (mulDiv_sound sc (fun a c => by simp [specRule])
        (fun c d => ⟨d.div c, Dim.div_mul_cancel d c⟩)
        (fun a d => ⟨d.div a, Dim.mul_div_cancel' a d⟩) hl hr hlv hrv hw)
    case div =>
      simp only [wop, Option.some.injEq] at hw
      exact two (mulDiv_sound sc (fun a c => by simp [specRule])
        (fun c d => ⟨d.mul c, Dim.mul_div_cancel d c⟩)
        (fun a d => ⟨a.div d, Dim.div_div_cancel a d⟩) hl hr hlv hrv hw)
    case pow =>
      simp only [wop, Option.some.injEq] at hw
      exact two (pow_sound sc hl hr hlv hrv hw hv)
  · cases b <;> simp [wop] at hw

theorem typed_branch {o : Nat} {cs : List (Tree JF)} {b : Builtin}
    (hk : kindAt table cs.length o = some b) {ds : List Dim} {d : Dim}
    (hds : All2 (Typed table xu allow) cs ds) (hr : specRule b ds = some d) :
    Typed table xu allow (.branch o cs) d := by
  simp only [Typed]
  exact ⟨b, ds, hk, (typedL_all2 table xu allow cs ds).mpr hds, hr⟩

end

/-- Core induction: every non-violating result of the check reaches its dimension, and
every dimension when it is a wildcard. -/
theorem sound_core (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q)
    (row : List JF) (allow : Bool) :
    ∀ t : Tree JF, DegLe D t →
      RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
      ∀ w, dispatch D (opsOf sc table) xu row allow t = .ok w → w.violates = false →
        Sat (Typed table (xu.map Q.dim) allow t) w := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro _ _ w h _
    simp only [dispatch, tmrT, deg0Eval] at h; cases h
    exact ⟨by simp [Typed], fun hw d => by simp [Typed] at hw ⊢; exact Or.inl hw⟩
  | hf i =>
    intro _ _ w h _
    simp only [dispatch, tmrT, deg0Eval, bind, Except.bind] at h
    cases hx : SymReg.Complexity.idx1 row i with
    | error e => simp [hx] at h
    | ok x =>
      cases hu : SymReg.Complexity.idx1 xu i with
      | error e => simp [hx, hu] at h
      | ok u =>
        simp [hx, hu] at h; subst h
        obtain ⟨h1, hu'⟩ := idx1_ok hu
        exact ⟨by simp [Typed, h1, hu'], fun hw => by simp at hw⟩
  | hb o cs ih =>
    intro hdeg hroots w h hv
    simp only [DegLe] at hdeg
    obtain ⟨_, op, ws, hop, hall, hdeg'⟩ := dispatch_branch hdeg.1 h
    obtain ⟨b, hk, rfl⟩ := opAt_opsOf hop
    obtain ⟨hnv, _, hlat⟩ := degn_ok hdeg' hv
    simp only [RootsExact] at hroots
    have hlen : ws.length = cs.length := hall.length
    have hchild : All2 (fun c w => Sat (Typed table (xu.map Q.dim) allow c) w ∧
        w.violates = false) cs ws :=
      hall.imp2 fun c hc w hw hcw =>
        ⟨ih c hc (hdeg.2 c hc) (rootsExactL_mem hroots.2 c hc) w hcw (hnv w hw), hnv w hw⟩
    obtain ⟨i, hi, hm, hal, hcase⟩ := lattice_ok hv _ hlat
    have hpl : (pattern ws.length i).length = b.arity := arity_of_hasMethod hm
    rw [pattern_length] at hpl
    rcases hcase with ⟨hlast, hs⟩ | hmrc
    · rw [builtin_allScalar hs]
      have hi' : i = 2 ^ ws.length - 1 := by omega
      rw [hi', pattern_last] at hal
      have hwild := allowed_replicate_true ws hal
      refine ⟨?_, fun h => by simp at h⟩
      have hds : All2 (Typed table (xu.map Q.dim) allow) cs (List.replicate cs.length Dim.one) :=
        All2.const _ cs fun c hc => by
          obtain ⟨w', hw', hcw⟩ := hchild.mem_left c hc
          rcases hwild w' hw' with hw | hd
          · exact hcw.1.2 hw _
          · exact hd ▸ hcw.1.1
      refine typed_branch table (xu.map Q.dim) allow hk hds ?_
      rw [← hlen, hpl]; exact specRule_ones b
    · obtain ⟨hwop, _⟩ := builtin_mrc (pattern_length _ _) hmrc
      rcases hwop with hwop | ⟨k, l, rr, rfl, hws, hcmp⟩
      · have hroot : ∀ w', ws = [w'] → w'.wildcard = false →
            (b = .sqrt → w'.dim.RootExact 2) ∧ (b = .cbrt → w'.dim.RootExact 3) := by
          intro w' hws hww
          subst hws
          cases hall with
          | cons hc1 hrest =>
            cases hrest
            have hk1 : kindAt table 1 o = some b := by simpa using hk
            have := hroots.1 _ w' rfl hc1 (hnv w' (by simp)) hww
            exact ⟨fun hb => this.1 (hb ▸ hk1), fun hb => this.2 (hb ▸ hk1)⟩
        exact (wop_sound sc table (xu.map Q.dim) allow hwop hv hchild hroot).mono
          fun d ⟨ds, hds, hs⟩ => typed_branch table (xu.map Q.dim) allow hk hds hs
      · subst hws
        cases hchild with | cons hlc hc' => cases hc' with | cons hrc hc'' => cases hc'' with | nil =>
        exact (cmp_sound sc hlc.1 hrc.1 hlc.2 hrc.2 hcmp).mono
          fun d ⟨a, c, ha, hc, hs⟩ =>
            typed_branch table (xu.map Q.dim) allow hk (.cons ha (.cons hc .nil)) hs

/-- Soundness: a tree the check accepts is dimensionally consistent: some choice of
dimensions for its constants (dimensionless ones when `dimensionless_constants_only`)
types it, with the target's dimensions when `y_units` is present. -/
def units_sound : Prop :=
  ∀ (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q) (yu : Option Q)
    (row : List JF) (allow : Bool) (t : Tree JF),
    DegLe D t → RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
    violatesUnits D (opsOf sc table) xu yu row allow t = .ok false →
    ∃ d, Typed table (xu.map Q.dim) allow t d ∧ ∀ y, yu = some y → d = y.dim

theorem units_sound_holds : units_sound := by
  intro D sc table xu yu row allow t hdeg hroots h
  unfold violatesUnits at h
  cases hd : dispatch D (opsOf sc table) xu row allow t with
  | error e => simp [hd, bind, Except.bind] at h
  | ok w =>
    simp only [hd, bind, Except.bind] at h
    cases yu with
    | none =>
      simp [pure, Except.pure] at h
      exact ⟨w.dim, (sound_core D sc table xu row allow t hdeg hroots w hd h).1,
        fun y hy => by cases hy⟩
    | some y =>
      simp [pure, Except.pure] at h
      obtain ⟨hv, hy⟩ := h
      have hs := sound_core D sc table xu row allow t hdeg hroots w hd hv
      cases hw : w.wildcard
      · have : w.dim = y.dim := by simpa [hw] using hy
        exact ⟨w.dim, hs.1, fun y' hy' => by cases hy'; exact this⟩
      · exact ⟨y.dim, hs.2 hw _, fun y' hy' => by cases hy'; rfl⟩

/-- Wildcard propagation: a non-violating wildcard result can be given every dimension by
choosing its constants' dimensions. -/
def units_wildcard_any : Prop :=
  ∀ (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q) (row : List JF)
    (allow : Bool) (t : Tree JF) (w : WQ),
    DegLe D t → RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
    dispatch D (opsOf sc table) xu row allow t = .ok w → w.violates = false →
    w.wildcard = true → ∀ d, Typed table (xu.map Q.dim) allow t d

theorem units_wildcard_any_holds : units_wildcard_any := by
  intro D sc table xu row allow t w hdeg hroots h hv hw
  exact (sound_core D sc table xu row allow t hdeg hroots w h hv).2 hw

/-- Dimensions under a single assignment to constant addresses in a GraphNode heap. -/
def graphDim (table : List (List Builtin)) (xu : List Dim) (allow : Bool)
    (g : Graph JF) (assign : Addr → Dim) : Nat → Addr → Option Dim
  | 0, _ => none
  | n + 1, a => do
    let c ← g.cells a
    if c.degree = 0 then
      if c.constant then some (if allow then assign a else Dim.one)
      else if c.feature = 0 then none else xu[c.feature - 1]?
    else
      let b ← kindAt table c.degree c.op
      let ds ← c.children.mapM (graphDim table xu allow g assign n)
      specRule b ds

-- Source: src/DimensionalAnalysis.jl:200–215 (break_sharing=Val(true)).
def graphDispatch (D : Nat) (sc : Scalars) (table : List (List Builtin))
    (xu : List Q) (row : List JF) (allow : Bool) (g : Graph JF) (n : Nat) (a : Addr) :
    Option (Jl WQ) :=
  (g.unfold n a).map (dispatch D (opsOf sc table) xu row allow)

def graphUnitsSound : Prop :=
  ∀ (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q) (yu : Option Q)
    (row : List JF) (allow : Bool) (g : Graph JF) (n : Nat) (a : Addr) (t : Tree JF),
    g.unfold n a = some t → DegLe D t →
    RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
    violatesUnits D (opsOf sc table) xu yu row allow t = .ok false →
    ∃ assign d, graphDim table (xu.map Q.dim) allow g assign n a = some d ∧
      ∀ y, yu = some y → d = y.dim

def graphWildcardAny : Prop :=
  ∀ (D : Nat) (sc : Scalars) (table : List (List Builtin)) (xu : List Q)
    (row : List JF) (allow : Bool) (g : Graph JF) (n : Nat) (a : Addr) (t : Tree JF) (w : WQ),
    g.unfold n a = some t → DegLe D t →
    RootsExact (dispatch D (opsOf sc table) xu row allow) table t →
    graphDispatch D sc table xu row allow g n a = some (.ok w) →
    w.violates = false → w.wildcard = true →
    ∀ d, ∃ assign, graphDim table (xu.map Q.dim) allow g assign n a = some d

private def ratioHeap : Addr × Graph JF :=
  let (c, g) := Graph.ofTree (Heap.empty : Graph JF) (.const (.fin 2))
  g.alloc ⟨2, false, none, 0, 1, [c, c]⟩

private def ratioTree : Tree JF := .branch 1 [.const (.fin 2), .const (.fin 2)]
private def ratioTable : List (List Builtin) := [[], [.div]]
private def ratioSc : Scalars := fun _ _ => .fin 1
private def metre : Dim := { Dim.one with length := 1 }

private theorem ratioDims (assign : Addr → Dim) :
    graphDim ratioTable [] true ratioHeap.2 assign 2 ratioHeap.1 = some Dim.one := by
  change some ((assign 0).div (assign 0)) = some Dim.one
  congr 1
  cases assign 0
  simp [Dim.div, Dim.map2, Dim.one]
  all_goals grind

private theorem ratioRoots :
    RootsExact (dispatch 2 (opsOf ratioSc ratioTable) [] [] true) ratioTable ratioTree := by
  simp [ratioTree, RootsExact, RootsExactL, ratioTable, kindAt]

theorem graphUnitsSound_refuted : ¬ graphUnitsSound := by
  intro h
  obtain ⟨assign, d, hd, hy⟩ :=
    h 2 ratioSc ratioTable [] (some ⟨.fin 1, metre⟩) [] true ratioHeap.2 2 ratioHeap.1
      ratioTree rfl (by simp [ratioTree, DegLe]) ratioRoots (by decide +kernel)
  change graphDim ratioTable [] true ratioHeap.2 assign 2 ratioHeap.1 = some d at hd
  rw [ratioDims] at hd
  cases hd
  exact (by decide : Dim.one ≠ metre) (hy _ rfl)

theorem graphWildcardAny_refuted : ¬ graphWildcardAny := by
  intro h
  obtain ⟨assign, hd⟩ :=
    h 2 ratioSc ratioTable [] [] true ratioHeap.2 2 ratioHeap.1 ratioTree
      ⟨.fin 1, Dim.one, true, false⟩ rfl (by simp [ratioTree, DegLe]) ratioRoots
      (by decide +kernel) rfl rfl metre
  change graphDim ratioTable [] true ratioHeap.2 assign 2 ratioHeap.1 = some metre at hd
  rw [ratioDims] at hd
  exact (by decide : Dim.one ≠ metre) (Option.some.inj hd)

/-- The preconditions are satisfiable: a single feature with metre units. -/
example : DegLe 2 (.feature 1 : Tree JF) ∧
    RootsExact (dispatch 2 (opsOf (fun _ _ => .fin 1) []) [⟨.fin 1, Dim.one⟩] [.fin 2] true)
      [] (.feature 1) ∧
    violatesUnits 2 (opsOf (fun _ _ => .fin 1) []) [⟨.fin 1, Dim.one⟩] none [.fin 2] true
      (.feature 1) = .ok false := by
  refine ⟨by simp [DegLe], by simp [RootsExact], ?_⟩
  decide +kernel

/-- The hypotheses of `units_wildcard_any` are satisfiable: a constant with wildcards on. -/
example : DegLe 2 (.const (.fin 3) : Tree JF) ∧
    RootsExact (dispatch 2 (opsOf (fun _ _ => .fin 1) []) [] [] true) [] (.const (.fin 3)) ∧
    dispatch 2 (opsOf (fun _ _ => .fin 1) []) [] [] true (.const (.fin 3)) =
      .ok ⟨.fin 3, Dim.one, true, false⟩ :=
  ⟨by simp [DegLe], by simp [RootsExact], by decide +kernel⟩

end SymReg.Units
