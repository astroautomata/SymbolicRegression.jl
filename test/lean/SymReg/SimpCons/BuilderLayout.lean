import SymReg.Options.Constructor
import DynExpr.Simplify.EnumConstruction

namespace SymReg.SimpCons
open DynExpr
open SymReg.Options (Args Services construct opmap mapOperators)

private def documentedPairs (ops : List (List Nat)) (pairs : List (Nat × ConstraintValue)) : Prop :=
  ∀ p ∈ pairs, ∃ (d : Nat) (ds : List Nat), ops[d]? = some ds ∧ opmap p.1 ∈ ds ∧
    match p.2 with
    | .scalar _ => d = 0
    | .tuple ns => 0 < d ∧ ns.length = d + 1

private def aliasesCollide (pairs : List (Nat × ConstraintValue)) : Prop :=
  ∃ p ∈ pairs, ∃ q ∈ pairs, p.1 ≠ q.1 ∧ opmap p.1 = opmap q.1

private def slotMatches (dict : List (Nat × ConstraintValue)) (d op : Nat)
    (v : ConstraintValue) : Prop :=
  (∀ p ∈ dict, opmap p.1 = op → v = p.2) ∧
  ((∀ p ∈ dict, opmap p.1 ≠ op) →
    if d = 0 then v = .scalar (-1) else
      ∃ ns, v = .tuple ns ∧ ns.length = d + 1 ∧ ∀ n ∈ ns, n = -1)

private def hasPairLayout (ops : List (List Nat)) (pairs : List (Nat × ConstraintValue))
    (table : List (List ConstraintValue)) : Prop :=
  table.length = ops.length ∧
    ∀ (d : Nat) ds, ops[d]? = some ds →
      ∃ row, table[d]? = some row ∧ row.length = ds.length ∧
        ∀ (i : Nat) op v, ds[i]? = some op → row[i]? = some v →
          slotMatches (toDict pairs) d op v

private def builderOptions (ops : List (List Nat)) (useEnum : Bool)
    (pairs : List (Nat × ConstraintValue)) : Args :=
  { operators := if useEnum then some { ops := ops, standard := true } else none
    unary := if useEnum then none else some (ops[0]?.getD [])
    binary := if useEnum then none else some (ops[1]?.getD [])
    constraints := some (.operatorPairs pairs) }

/-- The documented keyed limits should retain their values and the enum's slot order
through either public operator-selection route. -/
def builderPairLayout : Prop :=
  ∀ (ops : List (List Nat)) useEnum (pairs : List (Nat × ConstraintValue)),
    (useEnum = false → ops.length = 2) →
    (mapOperators ops).flatten.Nodup → documentedPairs (mapOperators ops) pairs →
    let result := construct ({} : Services) (builderOptions ops useEnum pairs)
    (aliasesCollide pairs → result = .error
      (.errorException "Operator keys refer to the same operator more than once.")) ∧
    (¬ aliasesCollide pairs → ∃ o, result = .ok o ∧
      hasPairLayout (mapOperators ops) pairs o.constraints)

theorem builderPairLayout_refuted : ¬ builderPairLayout := by
  intro h
  have hn : ¬ aliasesCollide [(101, .tuple [-1, 3])] := by simp [aliasesCollide]
  obtain ⟨result, he, _⟩ := (h [[], [101]] true [(101, .tuple [-1, 3])]
    (by simp) (by decide) (by simp [documentedPairs, mapOperators, opmap] <;> exact
      ⟨1, [101], rfl, by simp, by decide, rfl⟩)).2 hn
  have hw : construct ({} : Services) (builderOptions [[], [101]] true [(101, .tuple [-1, 3])]) =
      .error (.errorException "KeyError: degree is not an operator key") := rfl
  rw [hw] at he
  cases he

private def legacyLayoutAfterHelpers : Prop :=
  ∀ (unary binary : List Nat) (pairs : List (Nat × ConstraintValue))
    (helpers : List (List Nat) → Jl Unit)
    (operatorConstructor : Option Nat → List (List Nat) → Jl SymReg.Options.Operators),
    let ops := mapOperators [unary, binary]
    helpers [unary, binary] = .ok () →
    ops.flatten.Nodup → documentedPairs ops pairs →
    let result := construct { helpers, operatorConstructor } (builderOptions [unary, binary] false pairs)
    (aliasesCollide pairs → result = .error
      (.errorException "Operator keys refer to the same operator more than once.")) ∧
    (¬ aliasesCollide pairs →
      match operatorConstructor none ops with
      | .error e => result = .error e
      | .ok enum => enum.ops = ops → ∃ o, result = .ok o ∧ hasPairLayout o.operators.ops pairs o.constraints)

private theorem legacyDisjoint (u b : List Nat) (h : (u ++ b).Nodup) :
    (b.any (fun op => u.contains op)) = false := by
  apply List.any_eq_false.mpr
  intro op hb
  have hd := List.nodup_append.mp h
  simpa using fun hu => hd.2.2 op hu op hb rfl

private theorem layoutRow (u b : List Nat) (pairs : List (Nat × ConstraintValue))
    (hn : (u ++ b).Nodup) (hl : documentedPairs [u, b] pairs)
    (hi : ¬ aliasesCollide pairs) (d : Nat) (ops : List Nat)
    (hd : [u, b][d]? = some ops) :
    let dict := ((toDict pairs).map (fun (op, v) => (opmap op, v))).reverse
    ∃ row, buildDegree (d + 1) ops (.pairs dict) = .ok row ∧
      row.length = ops.length ∧
      ∀ (i : Nat) op v, ops[i]? = some op → row[i]? = some v → slotMatches (toDict pairs) d op v := by
  let dict := ((toDict pairs).map (fun (op, v) => (opmap op, v))).reverse
  let default : ConstraintValue :=
    if d = 0 then .scalar (-1) else .tuple (List.replicate (d + 1) (-1))
  let get : Nat → ConstraintValue := fun op =>
    ((dict.find? (fun p => p.1 == op)).map Prod.snd).getD default
  have findLaw (op : Nat) :
      slotMatches (toDict pairs) d op (get op) ∧
        (∀ v, dict.find? (fun p => p.1 == op) = some (op, v) →
          ∃ p ∈ toDict pairs, opmap p.1 = op ∧ p.2 = v) := by
    cases he : dict.find? (fun p => p.1 == op) with
    | none =>
      have hnone : ∀ p ∈ toDict pairs, opmap p.1 ≠ op := by
        intro p hp hkey
        have hm : (opmap p.1, p.2) ∈ dict := by
          simpa [dict, List.mem_map] using
            (List.mem_map.mpr ⟨p, hp, rfl⟩ :
              (opmap p.1, p.2) ∈ (toDict pairs).map (fun (op, v) => (opmap op, v)))
        have hc := List.find?_eq_none.mp he _ hm
        simp [hkey] at hc
      refine ⟨⟨fun p hp hk => False.elim (hnone p hp hk), ?_⟩, by simp⟩
      intro _
      by_cases dz : d = 0
      · simp [get, he, default, dz]
      · refine (ite_eq_right dz ▸ ?_)
        exact ⟨List.replicate (d + 1) (-1), by simp [get, he, default, dz], by simp,
          fun _ hm => List.eq_of_mem_replicate hm⟩
    | some kv =>
      have hmem := List.mem_of_find?_eq_some he
      have hkey : kv.1 = op := by simpa using List.find?_some he
      obtain ⟨p, hp, hpv⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
      change (opmap p.1, p.2) = kv at hpv
      have hk : opmap p.1 = op := (congrArg Prod.fst hpv).trans hkey
      have hv' := congrArg Prod.snd hpv
      have hv : p.2 = kv.2 := hv'
      refine ⟨⟨?_, fun ha => False.elim (ha p hp hk)⟩, ?_⟩
      · intro q hq hqk
        have heq : p.1 = q.1 := by
          apply Classical.byContradiction
          exact fun hne => hi ⟨p, toDict_subset pairs hp, q, toDict_subset pairs hq,
            hne, hk.trans hqk.symm⟩
        have hpq : p = q := by
          obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
          obtain ⟨j, hqj⟩ := List.mem_iff_getElem?.mp hq
          have hx : ((toDict pairs).map Prod.fst)[i]? = some p.1 := by simp [hpi]
          have hy : ((toDict pairs).map Prod.fst)[j]? = some q.1 := by simp [hqj]
          have hij := (toDict_nodup pairs).eq_of_getElem?_eq
            (List.getElem?_eq_some_iff.mp hx).choose (hx.trans (by rw [hy, heq]))
          subst j
          exact Option.some.inj (hpi.symm.trans hqj)
        simp [get, he, ← hv, hpq]
      · intro v hok
        have heq := Option.some.inj hok
        exact ⟨p, hp, hk, hv.trans (congrArg Prod.snd heq)⟩
  have converts (op : Nat) (hm : op ∈ ops) :
      match get op with
      | .scalar _ => d = 0
      | .tuple ns => d ≠ 0 ∧ ns.length = d + 1 := by
    cases he : dict.find? (fun p => p.1 == op) with
    | none => by_cases dz : d = 0 <;> simp [get, default, he, dz]
    | some kv =>
      have hkey : kv.1 = op := by simpa using List.find?_some he
      obtain ⟨p, hp, hk, hv⟩ := (findLaw op).2 kv.2 (by simpa [← hkey] using he)
      obtain ⟨e, ds, he', hop, ht⟩ := hl p (toDict_subset pairs hp)
      have hde : d = e := by
        have h1 : d < 2 := by simpa using (List.getElem?_eq_some_iff.mp hd).choose
        have h2 : e < 2 := by simpa using (List.getElem?_eq_some_iff.mp he').choose
        have hh := (List.nodup_append.mp hn).2.2
        have hx : op ∈ ds := hk ▸ hop
        have hd' : d = 0 ∨ d = 1 := by omega
        have he'' : e = 0 ∨ e = 1 := by omega
        rcases hd' with rfl | rfl <;> rcases he'' with rfl | rfl
        · rfl
        · simp at hd he'
          subst ops
          subst ds
          exact False.elim (hh op hm op hx rfl)
        · simp at hd he'
          subst ops
          subst ds
          exact False.elim (hh op hx op hm rfl)
        · rfl
      subst e
      simpa [get, he, ← hv, Nat.pos_iff_ne_zero] using ht
  refine ⟨ops.map get, ?_, by simp, ?_⟩
  · have hd0 : (d + 1 = 1) ↔ d = 0 := by omega
    unfold buildDegree
    simp only [hd0]
    apply mapM_ok_on
    intro op hm
    have hc := converts op hm
    have heq : ((dict.find? (fun q => q.1 == op)).map Prod.snd).getD default = get op := rfl
    rw [heq]
    cases hg : get op <;> simp_all [pure, Except.pure]
  · intro i op v hop hv
    have he : get op = v := by simpa [hop] using hv
    exact he ▸ (findLaw op).1

private theorem legacyLayoutAfterHelpers_holds : legacyLayoutAfterHelpers := by
  intro unary binary pairs helpers operatorConstructor
  dsimp only
  intro hhelper hn hl
  let u := unary.map opmap
  let b := binary.map opmap
  have hnd : (u ++ b).Nodup := by simpa [u, b, mapOperators] using hn
  have hroute : SymReg.Options.routeConstraints (builderOptions [unary, binary] false pairs)
      (mapOperators [unary, binary]) (mapOperators [unary, binary]) =
        .ok (none, some (.pairs pairs), some (.pairs pairs)) := by
    have hd := legacyDisjoint u b hnd
    change ((do
      if b.any (fun op => u.contains op) then
        throw (JlError.assertionError "Operator appears in unary and binary operators")
      pure (none, some (.pairs pairs), some (.pairs pairs))) :
        Jl (Option ConstraintInput × Option DegreeInput × Option DegreeInput)) = _
    rw [hd]
    rfl
  let a : Args := {
    unary := some unary
    binary := some binary
    constraints := some (.operatorPairs pairs) }
  have hroute' : SymReg.Options.routeConstraints a [u, b] [u, b] =
      .ok (none, some (.pairs pairs), some (.pairs pairs)) := hroute
  have hv : SymReg.Options.validateScalars (SymReg.Options.supplyDefaults a) a.lossScale =
      .ok () := rfl
  have hresult (table : List (List ConstraintValue))
      (h : buildConstraints opmap [u, b] none (some (.pairs pairs)) (some (.pairs pairs)) =
        .ok table) :
      match operatorConstructor none [u, b] with
      | .error e => construct { helpers, operatorConstructor } a = .error e
      | .ok enum => ∃ o, construct { helpers, operatorConstructor } a = .ok o ∧
          o.constraints = table ∧ o.operators = enum := by
    cases hc : operatorConstructor none [u, b] <;>
      unfold construct SymReg.Options.constructParts <;>
      simp [show SymReg.Options.validateInitial a = .ok () from rfl, hv, hhelper,
        SymReg.Options.resolveExpression, buildNested, hroute', bind, Except.bind, pure,
        Except.pure, Except.map, h, mapOperators, u, b, a, SymReg.Options.resolveComplexity,
        SymReg.Options.complexityMapping, SymReg.Options.resolveOperators, hc] <;>
      first | exact ⟨_, rfl, rfl, rfl⟩ | rfl
  constructor
  · rintro ⟨p, hp, q, hq, hne, he⟩
    obtain ⟨i, vi⟩ := p
    obtain ⟨j, vj⟩ := q
    have hm := mapKeys_fails_on_alias opmap pairs i j vi vj hp hq hne he
    have hw : buildConstraints opmap [u, b] none (some (.pairs pairs)) (some (.pairs pairs)) =
        .error (.errorException "Operator keys refer to the same operator more than once.") := by
      simp [buildConstraints, buildAll, SymReg.Constraints.enum1, degreeInputAt,
        normalizeDegree, hm, bind, Except.bind, pure, Except.pure, Except.map,
        List.range'_succ, List.mapM_cons, List.mapM_nil]
    change construct { helpers, operatorConstructor } a =
      .error (.errorException "Operator keys refer to the same operator more than once.")
    unfold construct SymReg.Options.constructParts
    simp [show SymReg.Options.validateInitial a = .ok () from rfl, hv, hhelper,
      SymReg.Options.resolveExpression, buildNested, hroute', bind, Except.bind, pure,
      Except.pure, Except.map, hw, mapOperators, u, b, a]
    rfl
  · intro hi
    have hi' : ∀ p ∈ toDict pairs, ∀ q ∈ toDict pairs, opmap p.1 = opmap q.1 → p.1 = q.1 := by
      intro p hp q hq he
      apply Classical.byContradiction
      exact fun hne => hi ⟨p, toDict_subset pairs hp, q, toDict_subset pairs hq, hne, he⟩
    have hm := mapKeys_of_injective opmap pairs hi'
    have hl' : documentedPairs [u, b] pairs := hl
    obtain ⟨ur, hu, hun, hul⟩ := layoutRow u b pairs hnd hl' hi 0 u rfl
    obtain ⟨br, hb, hbn, hbl⟩ := layoutRow u b pairs hnd hl' hi 1 b rfl
    have ht : buildConstraints opmap [u, b] none (some (.pairs pairs)) (some (.pairs pairs)) =
        .ok [ur, br] := by
      simp [buildConstraints, buildAll, SymReg.Constraints.enum1, degreeInputAt,
        normalizeDegree, hm, bind, Except.bind, pure, Except.pure, Except.map,
        List.range'_succ, List.mapM_cons, List.mapM_nil, hu, hb]
    have hh := hresult [ur, br] ht
    change (match operatorConstructor none [u, b] with
      | .error e => construct { helpers, operatorConstructor } a = .error e
      | .ok enum => enum.ops = [u, b] →
          ∃ o, construct { helpers, operatorConstructor } a = .ok o ∧
            hasPairLayout o.operators.ops pairs o.constraints)
    cases he : operatorConstructor none [u, b] with
    | error e => simpa only [he] using hh
    | ok enum =>
      intro heq
      rw [he] at hh
      obtain ⟨o, ho, hc, henum⟩ := hh
      refine ⟨o, ho, ?_⟩
      rw [hc, henum, heq]
      change hasPairLayout [u, b] pairs [ur, br]
      refine ⟨rfl, ?_⟩
      intro d ds hd
      cases d with
      | zero =>
        simp at hd
        subst ds
        exact ⟨ur, rfl, hun, hul⟩
      | succ d =>
        cases d with
        | zero =>
          simp at hd
          subst ds
          exact ⟨br, rfl, hbn, hbl⟩
        | succ _ => simp at hd

open DynExpr.Simplify (Fn Globals makeEnumKw)

-- Source: src/Options.jl:894-904; DynamicExpressions 2.13 src/OperatorEnumConstruction.jl:122-134,322.
private def legacyEnum (decode : Nat → Fn) (inBase : Fn → Bool) (state : Globals)
    (emptyOld : Bool) (ops : List (List Nat)) : Jl (List (List Fn) × Globals) :=
  makeEnumKw inBase .operatorEnum (ops[1]?.map (List.map decode))
    (ops[0]?.map (List.map decode)) true emptyOld state

-- Source: src/Options.jl:1017-1032. The second call extends the first call's state.
private def legacyCanonical (decode : Nat → Fn) (inBase : Fn → Bool) (state : Globals)
    (raw : List (List Nat)) (_ : Option Nat) (ops : List (List Nat)) :
    Jl SymReg.Options.Operators := do
  let (_, next) ← legacyEnum decode inBase state true raw
  let _ ← legacyEnum decode inBase next false ops
  pure ⟨ops, true, 0⟩


-- Source: src/Options.jl:181-201; the fixed function IDs are in `opmap`.
-- Codes through 118 are reserved for plain identities, including every OP_MAP
-- key and value. Above that range, plain and broadcast IDs occupy separate slots.
def operatorCode : Fn → Nat
  | .plain id => if id < 119 then id else 119 + 2 * (id - 119)
  | .bcast id => 120 + 2 * id

def operatorDecode (code : Nat) : Fn :=
  if code < 119 then .plain code
  else if (code - 119) % 2 = 0 then .plain (119 + (code - 119) / 2)
  else .bcast ((code - 119) / 2)

theorem operatorCode_decode (code : Nat) : operatorCode (operatorDecode code) = code := by
  unfold operatorDecode
  by_cases h : code < 119
  · simp [h, operatorCode]
  · have hl : ¬119 + (code - 119) / 2 < 119 := by omega
    by_cases parity : (code - 119) % 2 = 0 <;>
      simp [h, parity, operatorCode, hl] <;> omega

theorem operatorDecode_code (op : Fn) : operatorDecode (operatorCode op) = op := by
  cases op with
  | plain id =>
    by_cases h : id < 119
    · simp [operatorCode, operatorDecode, h]
    · have hc : ¬119 + 2 * (id - 119) < 119 := by omega
      simp [operatorCode, operatorDecode, h, hc] <;> omega
  | bcast id =>
    have hc : ¬120 + 2 * id < 119 := by omega
    have hm : ¬(120 + 2 * id - 119) % 2 = 0 := by omega
    have hd : (120 + 2 * id - 119) / 2 = id := by omega
    simp [operatorCode, operatorDecode, hc, hm, hd]

private theorem opmap_large (id : Nat) (h : 119 ≤ id) : opmap id = id := by
  unfold opmap
  split <;> try omega
  split <;> try omega
  split <;> omega

private theorem opmap_small (id : Nat) (h : id < 119) : opmap id < 119 := by
  unfold opmap
  split <;> try omega
  split <;> try omega
  split <;> omega

-- OP_MAP has plain function keys. A BroadcastFunction is a distinct key.
private def canonicalFn : Fn → Fn
  | .plain op => .plain (opmap op)
  | .bcast op => .bcast op

theorem operatorDecode_opmap (code : Nat) :
    operatorDecode (opmap code) = canonicalFn (operatorDecode code) := by
  by_cases h : code < 119
  · simp [operatorDecode, h, opmap_small code h, canonicalFn]
  · rw [opmap_large code (by omega)]
    unfold operatorDecode
    rw [ite_eq_right h]
    split
    · simp only [canonicalFn]
      rw [opmap_large (119 + (code - 119) / 2) (by omega)]
    · rfl

private def builderLegacyPairLayoutAbstract : Prop :=
  ∀ (unary binary : List Nat) (pairs : List (Nat × ConstraintValue)) (decode : Nat → Fn)
    (inBase : Fn → Bool) (state : Globals),
    (∀ i j, decode i = decode j → i = j) →
    (∀ i, decode (opmap i) = canonicalFn (decode i)) →
    let raw := [unary, binary]
    let helpers := fun ops => (legacyEnum decode inBase state true ops).map (fun _ => ())
    let operatorConstructor := legacyCanonical decode inBase state raw
    let ops := mapOperators raw
    let result := construct { helpers, operatorConstructor } (builderOptions raw false pairs)
    (∀ err, helpers [unary, binary] = .error err → result = .error err) ∧
    (helpers [unary, binary] = .ok () → ops.flatten.Nodup → documentedPairs ops pairs →
      (aliasesCollide pairs → result = .error
        (.errorException "Operator keys refer to the same operator more than once.")) ∧
      (¬ aliasesCollide pairs →
        match operatorConstructor none ops with
        | .error e => result = .error e
        | .ok _ => ∃ o, result = .ok o ∧ hasPairLayout o.operators.ops pairs o.constraints))

private theorem builderLegacyPairLayoutAbstract_holds : builderLegacyPairLayoutAbstract := by
  intro unary binary pairs decode inBase state _ _
  dsimp only
  let raw := [unary, binary]
  let helpers := fun ops => (legacyEnum decode inBase state true ops).map (fun _ => ())
  let operatorConstructor := legacyCanonical decode inBase state raw
  constructor
  · intro err he
    let a := builderOptions raw false pairs
    have hv : SymReg.Options.validateScalars (SymReg.Options.supplyDefaults a) a.lossScale =
        .ok () := rfl
    change construct { helpers, operatorConstructor } a = .error err
    have he' : helpers raw = .error err := he
    unfold construct SymReg.Options.constructParts
    simp only [show SymReg.Options.validateInitial a = .ok () from rfl, hv,
      bind, Except.bind, pure, Except.pure, Option.getD_some]
    change (Except.map (SymReg.Options.assemble a) (do helpers raw; _)) = _
    rw [he']
    rfl
  · intro hh hn hl
    have h := legacyLayoutAfterHelpers_holds unary binary pairs helpers operatorConstructor hh hn hl
    refine ⟨h.1, ?_⟩
    intro ha
    have hr := h.2 ha
    change (match operatorConstructor none (mapOperators raw) with
      | .error e => construct { helpers, operatorConstructor } (builderOptions raw false pairs) = .error e
      | .ok _ => ∃ o, construct { helpers, operatorConstructor } (builderOptions raw false pairs) =
          .ok o ∧ hasPairLayout o.operators.ops pairs o.constraints)
    change (match operatorConstructor none (mapOperators raw) with
      | .error e => construct { helpers, operatorConstructor } (builderOptions raw false pairs) = .error e
      | .ok enum => enum.ops = mapOperators raw →
        ∃ o, construct { helpers, operatorConstructor } (builderOptions raw false pairs) =
          .ok o ∧ hasPairLayout o.operators.ops pairs o.constraints) at hr
    cases he : operatorConstructor none (mapOperators raw) with
    | error e => simpa only [he] using hr
    | ok enum =>
      rw [he] at hr
      apply hr
      unfold operatorConstructor legacyCanonical at he
      cases h₁ : legacyEnum decode inBase state true raw with
      | error e => simp [h₁, bind, Except.bind] at he
      | ok previous =>
        cases h₂ : legacyEnum decode inBase previous.2 false (mapOperators raw) with
        | error e => simp [h₁, h₂, bind, Except.bind] at he
        | ok next =>
          have he' : (⟨mapOperators raw, true, 0⟩ : SymReg.Options.Operators) = enum := by
            simpa [h₁, h₂, bind, Except.bind, pure, Except.pure] using he
          exact congrArg SymReg.Options.Operators.ops he'.symm

def builderLegacyPairLayout : Prop :=
  ∀ (unary binary : List Nat) (pairs : List (Nat × ConstraintValue))
    (inBase : Fn → Bool) (state : Globals),
    let raw := [unary, binary]
    let helpers := fun ops => (legacyEnum operatorDecode inBase state true ops).map (fun _ => ())
    let operatorConstructor := legacyCanonical operatorDecode inBase state raw
    let ops := mapOperators raw
    let result := construct { helpers, operatorConstructor } (builderOptions raw false pairs)
    (∀ err, helpers raw = .error err → result = .error err) ∧
    (helpers raw = .ok () → ops.flatten.Nodup → documentedPairs ops pairs →
      (aliasesCollide pairs → result = .error
        (.errorException "Operator keys refer to the same operator more than once.")) ∧
      (¬ aliasesCollide pairs →
        match operatorConstructor none ops with
        | .error e => result = .error e
        | .ok _ => ∃ o, result = .ok o ∧ hasPairLayout o.operators.ops pairs o.constraints))

theorem builderLegacyPairLayout_holds : builderLegacyPairLayout := by
  intro unary binary pairs inBase state
  exact builderLegacyPairLayoutAbstract_holds unary binary pairs operatorDecode inBase state
    (fun i j h => (operatorCode_decode i).symm.trans
      ((congrArg operatorCode h).trans (operatorCode_decode j))) operatorDecode_opmap

example : opmap (operatorCode (.plain 5)) = operatorCode (.plain 105) ∧
    opmap (operatorCode (.plain 6)) = operatorCode (.plain 105) ∧
    opmap (operatorCode (.bcast 5)) = operatorCode (.bcast 5) := by decide

end SymReg.SimpCons
