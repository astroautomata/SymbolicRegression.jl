import SymReg.MLJ.Core

namespace SymReg.MLJ
open DynExpr

variable {D : Type} [Dims D]

def units_clean : Prop := ∀ (D : Type) [Dims D] (us : List D) (u : D),
  (cleanUnitsVec us = none ↔ ∀ v ∈ us, v = Dims.none) ∧
    (cleanUnitsVec us = none ∨ cleanUnitsVec us = some us) ∧
    (cleanUnits u = none ↔ u = Dims.none) ∧ (u ≠ Dims.none → cleanUnits u = some u)

theorem units_clean_holds : units_clean := by
  intro D _ us u
  refine ⟨?_, ?_, ?_, fun h => by simp [cleanUnits, h]⟩
  · unfold cleanUnitsVec
    split
    · rename_i h
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rename_i h
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact ⟨(fun hc => nomatch hc), fun h' => absurd h' h⟩
  · unfold cleanUnitsVec; split <;> simp
  · unfold cleanUnits; split <;> simp_all

omit [Dims D] in
theorem firstDims_ok : ∀ (rows : List (List (Cell D))) (dims : List D), firstDims rows = .ok dims →
    dims.length = rows.length ∧ ∀ (t : Nat) row d, rows[t]? = some row → dims[t]? = some d →
      ∃ c rest, row = c :: rest ∧ d = c.2
  | [], dims, h => by simp [firstDims] at h; subst h; simp
  | [] :: _, _, h => by simp [firstDims] at h
  | (c :: rest) :: rs, dims, h => by
    cases hr : firstDims rs with
    | error e => simp [firstDims, hr, bind, Except.bind] at h
    | ok ds =>
      simp [firstDims, hr, bind, Except.bind, pure, Except.pure] at h
      subst h
      obtain ⟨hl, hg⟩ := firstDims_ok rs ds hr
      refine ⟨by simp [hl], ?_⟩
      intro t row d h1 h2
      cases t with
      | zero => simp at h1 h2; exact ⟨c, rest, h1.symm, h2.symm⟩
      | succ t => exact hg t row d (by simpa using h1) (by simpa using h2)

theorem checkRows_ok : ∀ (i : Nat) (rows : List (List (Cell D))) (dims : List D),
    checkRows i rows dims = .ok () → ∀ (t : Nat) row d, rows[t]? = some row → dims[t]? = some d →
      ∀ c ∈ row, c.2 = d
  | _, [], _, _, _, _, _, h1, _ => by simp at h1
  | _, _ :: _, [], _, _, _, _, _, h2 => by simp at h2
  | i, r :: rs, d :: ds, h, t, row, d', h1, h2 => by
    simp only [checkRows] at h
    split at h
    · rename_i hall
      cases t with
      | zero =>
        simp at h1 h2; subst h1; subst h2
        intro c hc; simpa using List.all_eq_true.mp hall c hc
      | succ t => exact checkRows_ok (i + 1) rs ds h t row d' (by simpa using h1) (by simpa using h2)
    · cases h

def units_unwrap : Prop := ∀ (D : Type) [Dims D] (rows : List (List (Cell D))) (vals : List (List JF))
    (dims : List D),
  unwrapMatrix rows = .ok (vals, dims) →
  vals = rows.map (·.map Prod.fst) ∧ dims.length = rows.length ∧
    ∀ (t : Nat) row d, rows[t]? = some row → dims[t]? = some d → ∀ c ∈ row, c.2 = d

theorem units_unwrap_holds : units_unwrap := by
  intro D _ rows vals dims h
  simp only [unwrapMatrix] at h
  cases h1 : firstDims rows with
  | error e => simp [h1, bind, Except.bind] at h
  | ok ds =>
    cases h2 : checkRows 1 rows ds with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok u =>
      simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, (firstDims_ok rows ds h1).1, checkRows_ok 1 rows ds h2⟩

omit [Dims D] in
theorem firstDims_pre (pre : List (Cell D × List (Cell D))) (rows : List (List (Cell D))) :
    firstDims (pre.map (fun p => p.1 :: p.2) ++ rows) =
      (firstDims rows).map (pre.map (fun p => p.1.2) ++ ·) := by
  induction pre with
  | nil => simp only [List.map_nil, List.nil_append]; cases firstDims rows <;> rfl
  | cons p pre ih =>
    simp only [List.map_cons, List.cons_append, firstDims, ih]
    cases firstDims rows <;> rfl

theorem checkRows_pre (pre : List (Cell D × List (Cell D))) (hpre : ∀ p ∈ pre, ∀ x ∈ p.2, x.2 = p.1.2) :
    ∀ (i : Nat) (rows : List (List (Cell D))) (ds : List D),
      checkRows i (pre.map (fun p => p.1 :: p.2) ++ rows) (pre.map (fun p => p.1.2) ++ ds) =
        checkRows (i + pre.length) rows ds := by
  induction pre with
  | nil => intro i rows ds; rfl
  | cons p pre ih =>
    intro i rows ds
    have hall : (p.1 :: p.2).all (fun c => decide (c.2 = p.1.2)) = true := by
      simp only [List.all_cons, decide_true, Bool.true_and]
      exact List.all_eq_true.mpr fun x hx => by simpa using hpre p (by simp) x hx
    simp only [List.map_cons, List.cons_append, checkRows, hall, if_true]
    rw [ih (fun q hq => hpre q (by simp [hq]))]
    simp only [List.length_cons]
    congr 1; omega

def units_unwrap_error : Prop := ∀ (D : Type) [Dims D] (pre : List (Cell D × List (Cell D)))
    (c : Cell D) (rest : List (Cell D)) (post : List (List (Cell D))),
  (∀ p ∈ pre, ∀ x ∈ p.2, x.2 = p.1.2) → (∃ x ∈ rest, x.2 ≠ c.2) → (∀ r ∈ post, r ≠ []) →
  unwrapMatrix (pre.map (fun p => p.1 :: p.2) ++ (c :: rest) :: post) =
    .error (.errorException s!"Inconsistent units in feature {pre.length + 1} of matrix.")

omit [Dims D] in
theorem firstDims_nonempty : ∀ (rows : List (List (Cell D))), (∀ r ∈ rows, r ≠ []) →
    ∃ ds, firstDims rows = .ok ds
  | [], _ => ⟨[], rfl⟩
  | [] :: _, h => absurd rfl (h [] (by simp))
  | (c :: _) :: rs, h => by
    obtain ⟨ds, hds⟩ := firstDims_nonempty rs (fun r hr => h r (by simp [hr]))
    exact ⟨c.2 :: ds, by simp [firstDims, hds, bind, Except.bind, pure, Except.pure]⟩

theorem units_unwrap_error_holds : units_unwrap_error := by
  intro D _ pre c rest post hpre hbad hpost
  obtain ⟨ds, hds⟩ := firstDims_nonempty post hpost
  have hfd : firstDims (pre.map (fun p => p.1 :: p.2) ++ (c :: rest) :: post) =
      .ok (pre.map (fun p => p.1.2) ++ c.2 :: ds) := by
    rw [firstDims_pre]; simp [firstDims, hds, bind, Except.bind, pure, Except.pure, Except.map]
  have hnot : ((c :: rest).all fun x => decide (x.2 = c.2)) = false := by
    obtain ⟨x, hx, hne⟩ := hbad
    cases ha : (c :: rest).all fun x => decide (x.2 = c.2)
    · rfl
    · have := List.all_eq_true.mp ha x (by simp [hx]); simp at this; exact absurd this hne
  have hcr : checkRows 1 (pre.map (fun p => p.1 :: p.2) ++ (c :: rest) :: post)
      (pre.map (fun p => p.1.2) ++ c.2 :: ds) =
      .error (.errorException s!"Inconsistent units in feature {pre.length + 1} of matrix.") := by
    rw [checkRows_pre pre hpre]
    simp only [checkRows, hnot, Bool.false_eq_true, if_false]
    rw [Nat.add_comm]
  simp [unwrapMatrix, hfd, hcr, bind, Except.bind]

def units_vector : Prop := ∀ (D : Type) [Dims D] (c : Cell D) (rest : List (Cell D)),
  ((∀ x ∈ rest, x.2 = c.2) → unwrapVector (c :: rest) = .ok ((c :: rest).map Prod.fst, c.2)) ∧
  ((∃ x ∈ rest, x.2 ≠ c.2) → unwrapVector (c :: rest) =
    .error (.errorException "Inconsistent units in vector.")) ∧
  unwrapVector ([] : List (Cell D)) = .error .boundsError

theorem units_vector_holds : units_vector := by
  intro D _ c rest
  refine ⟨fun h => ?_, fun ⟨x, hx, hne⟩ => ?_, rfl⟩
  · have : ((c :: rest).all fun x => decide (x.2 = c.2)) = true := by
      simp only [List.all_cons, decide_true, Bool.true_and]
      exact List.all_eq_true.mpr fun x hx => by simpa using h x hx
    simp [unwrapVector, this]
  · have : ((c :: rest).all fun x => decide (x.2 = c.2)) = false := by
      cases ha : (c :: rest).all fun x => decide (x.2 = c.2)
      · rfl
      · have := List.all_eq_true.mp ha x (by simp [hx]); simp at this; exact absurd this hne
    simp [unwrapVector, this]

def units_match : Prop := ∀ (D : Type) [Dims D] (a b : List D),
  (a.length = b.length → (unitsMatch (some a) (some b) = .ok true ↔ a = b)) ∧
    (b ≠ [] → unitsMatch none (some b) = .ok false ∧ unitsMatch (some b) none = .ok false) ∧
    unitsMatch (none : Option (List D)) none = .ok true

theorem zip_all_eq : ∀ (a b : List D), a.length = b.length →
    (((a.zip b).all fun p => decide (p.1 = p.2)) = true ↔ a = b)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq,
      List.cons.injEq]
    rw [zip_all_eq a b (by simpa using h)]

theorem units_match_holds : units_match := by
  intro D _ a b
  refine ⟨fun hl => ?_, fun hb => ?_, rfl⟩
  · simp only [unitsMatch, if_pos hl]
    constructor
    · intro h; exact (zip_all_eq a b hl).mp (Except.ok.inj h)
    · intro h; rw [(zip_all_eq a b hl).mpr h]
  · cases b with
    | nil => exact absurd rfl hb
    | cons _ _ => exact ⟨rfl, rfl⟩

def matrix_names : Prop := ∀ (D : Type) [Dims D] (sub : Nat → String) (x : Data D) (xt : Mat)
    (names disp : List String) (units : List D),
  getMatrixAndInfo sub x = .ok (xt, names, disp, units) →
  names.length = xt.rows.length ∧ units.length = xt.rows.length ∧
    (x.isTable = true → names = disp) ∧
    (x.isTable = false → names = (List.range xt.rows.length).map (fun i => s!"x{i + 1}") ∧
      disp = (List.range xt.rows.length).map (fun i => "x" ++ sub (i + 1)))

theorem matrix_names_holds : matrix_names := by
  intro D _ sub x xt names disp units h
  simp only [getMatrixAndInfo] at h
  cases ht : transposed x with
  | error e => simp [ht, bind, Except.bind] at h
  | ok p =>
    obtain ⟨n, rows⟩ := p
    cases hu : unwrapMatrix rows with
    | error e =>
      rw [ht] at h
      cases x <;> simp [hu, bind, Except.bind] at h
    | ok q =>
      obtain ⟨vals, dims⟩ := q
      obtain ⟨hv, hdl, _⟩ := units_unwrap_holds D rows vals dims hu
      have hrows : xt.rows = vals ∧ units = dims ∧
          (names, disp) = (match x with
            | .table cols => (cols.map Prod.fst, cols.map Prod.fst)
            | _ => ((List.range rows.length).map (fun i => s!"x{i + 1}"),
                (List.range rows.length).map (fun i => "x" ++ sub (i + 1)))) := by
        rw [ht] at h
        cases x <;> simp [hu, bind, Except.bind, pure, Except.pure] at h <;>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> simp
      obtain ⟨hxr, hud, hnd⟩ := hrows
      have hlen : xt.rows.length = rows.length := by rw [hxr, hv]; simp
      rw [hlen, hud, hdl]
      cases x with
      | table cols =>
        simp at hnd
        obtain ⟨rfl, rfl⟩ := hnd
        cases cols with
        | nil => simp [transposed] at ht
        | cons c cs =>
          simp only [transposed] at ht
          split at ht
          · cases ht; simp [Data.isTable]
          · cases ht
      | vector v => simp at hnd; obtain ⟨rfl, rfl⟩ := hnd; simp [Data.isTable]
      | matrix n' cols => simp at hnd; obtain ⟨rfl, rfl⟩ := hnd; simp [Data.isTable]

end SymReg.MLJ
