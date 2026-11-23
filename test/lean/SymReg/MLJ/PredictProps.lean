import SymReg.MLJ.ReportProps
import SymReg.MLJ.UnitsProps

namespace SymReg.MLJ
open DynExpr SymReg.HofMig

/-- Data that `_predict` does not mistake for a `(data=..., idx=...)` selector. -/
def NotSelector {D : Type} : Data D → Prop
  | .table cols => selectorKeys (cols.map Prod.fst) = false
  | _ => True

theorem predict1_plain [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D) (x : Data D)
    (hx : NotSelector x) (idx : Idx) (fresh : Nat) :
    predict1 sv m fr (.data x) idx fresh = predictCore1 sv m fr x idx fresh := by
  cases x with
  | table cols => simp only [NotSelector] at hx; simp [predict1, hx]
  | _ => rfl

theorem predictK_plain [Dims D] (sv : PredictServices D) (m : Regressor) (fr : FitK D) (x : Data D)
    (hx : NotSelector x) (idx : Idx) (fresh : Nat) :
    predictK sv m fr (.data x) idx fresh = predictCoreK sv m fr x idx fresh := by
  cases x with
  | table cols => simp only [NotSelector] at hx; simp [predictK, hx]
  | _ => rfl

/-- Follow nested data/index pairs up to the final data payload. -/
def resolvePrediction : PInput D → Idx → Data D × Idx
  | .data x, idx => (x, idx)
  | .select x idx, _ => resolvePrediction x idx

theorem resolvePrediction_predict1 [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D)
    (input : PInput D) (idx : Idx) (fresh : Nat) :
    predict1 sv m fr input idx fresh =
      predict1 sv m fr (.data (resolvePrediction input idx).1)
        (resolvePrediction input idx).2 fresh := by
  induction input generalizing idx with
  | data _ => rfl
  | select _ j ih => exact ih j

/-- The core of `_predict` after the report, on validated data. -/
theorem prepare_ok [Dims D] {sv : PredictServices D} {fr : FitResult S U D} {x : Data D} {xt : Mat}
    {names disp : List String} {units : List D}
    (hg : getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units)) (hn : names = fr.variableNames)
    (hu : unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true) :
    prepare sv fr x false = .ok (xt, false) := by
  simp [prepare, hg, validateNames, hn, validateUnits, hu, bind, Except.bind, pure, Except.pure]

/-! ## Overriding the equation -/

def pred_select : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (fr1 : Fit1 D) (frK : FitK D) (x : PInput D) (i idx : Idx) (fresh : Nat),
  predict1 sv m fr1 (.select x i) idx fresh = predict1 sv m fr1 x i fresh ∧
    predictK sv m frK (.select x i) idx fresh = predictK sv m frK x i fresh

theorem pred_select_holds : pred_select := by
  intro D _ sv m fr1 frK x i idx fresh; exact ⟨rfl, rfl⟩

def pred_default : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (fr : Fit1 D) (x : Data D) (fresh f : Nat) (r : Report1),
  fullReport1 m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  ∀ xt tree, prepare sv fr x false = .ok (xt, false) →
    index r.equations r.bestIdx = .ok tree →
    predictCore1 sv m fr x .none fresh = .ok (evalMlj1 fr tree xt)

theorem pred_default_holds : pred_default := by
  intro D _ sv m fr x fresh f r hr he xt tree hp hi
  have hn : r.equations.isEmpty = false := by cases h : r.equations <;> simp_all
  simp [predictCore1, hr, hn, hp, hi, bind, Except.bind, pure, Except.pure]

def pred_defaultK : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (fr : FitK D) (x : Data D) (fresh f : Nat) (r : ReportK),
  fullReportK m fr false fresh = .ok (r, f) →
  (r.equations.isEmpty || r.equations.any List.isEmpty) = false →
  ∀ xt, prepare sv fr x false = .ok (xt, false) →
  r.bestIdx.length = r.equations.length →
    predictCoreK sv m fr x .none fresh = (do
      let pieces ← ((r.equations.zip r.bestIdx).zipIdx).mapM (targetPiece fr xt)
      return (hcatPieces pieces).map fun cols =>
        if fr.yIsTable then .table (fr.yVariableNames.getD []) cols else .matrix cols)

theorem pred_defaultK_holds : pred_defaultK := by
  intro D _ sv m fr x fresh f r hr hn xt hp hi
  simp [predictCoreK, hr, hn, hp, perTarget, hi, bind, Except.bind, pure, Except.pure]

/-! ## Single-target predictions -/

def pred_idx : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D)
    (x : Data D) (fresh f : Nat) (r : Report1) (xt : Mat) (names disp : List String) (units : List D)
    (i : Int) (tree : Nat),
  NotSelector x → fullReport1 m fr false fresh = .ok (r, f) →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true →
  1 ≤ i → r.equations[(i - 1).toNat]? = some tree →
  predict1 sv m fr (.data x) (.int i) fresh =
    .ok (if (fr.options.eval tree xt.rows).2 then ⟨(fr.options.eval tree xt.rows).1, fr.yUnits⟩
      else ⟨List.replicate xt.nobs (.fin 0), fr.yUnits⟩)

theorem pred_idx_holds : pred_idx := by
  intro D _ sv m fr x fresh f r xt names disp units i tree hx hr hg hn hu hi ht
  rw [predict1_plain sv m fr x hx]
  have hne : r.equations.isEmpty = false := by
    cases he : r.equations with
    | nil => rw [he] at ht; simp at ht
    | cons _ _ => rfl
  have hidx : index r.equations i = .ok tree := by
    unfold index; rw [if_neg (by omega), ht]
  simp only [predictCore1, hr, hne, prepare_ok hg hn hu, hidx, bind, Except.bind, pure, Except.pure]
  rcases hev : fr.options.eval tree xt.rows with ⟨out, c⟩
  simp only [evalMlj1, fallback1, wrap1, hev]
  cases c <;> rfl

example : (1 : Int) ≤ 1 ∧ ([7] : List Nat)[((1 : Int) - 1).toNat]? = some 7 := by decide

def pred_bounds : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D)
    (x : Data D) (fresh f : Nat) (r : Report1) (xt : Mat) (names disp : List String) (units : List D)
    (i : Int),
  fullReport1 m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true →
  (i < 1 ∨ (r.equations.length : Int) < i) →
  predictCore1 sv m fr x (.int i) fresh = .error .boundsError ∧
    ∀ input idx, resolvePrediction input idx = (x, .int i) →
      NotSelector x → predict1 sv m fr input idx fresh = .error .boundsError

theorem pred_bounds_holds : pred_bounds := by
  intro D _ sv m fr x fresh f r xt names disp units i hr hne hg hn hu hi
  have hne' : r.equations.isEmpty = false := by
    cases he : r.equations with
    | nil => exact absurd he hne
    | cons _ _ => rfl
  have hidx : index r.equations i = .error .boundsError := by
    unfold index
    split
    · rfl
    · have : r.equations[(i - 1).toNat]? = none := List.getElem?_eq_none (by omega)
      rw [this]
  have hcore : predictCore1 sv m fr x (.int i) fresh = .error .boundsError := by
    simp [predictCore1, hr, hne', prepare_ok hg hn hu, hidx, bind, Except.bind]
  refine ⟨hcore, ?_⟩
  intro input idx hresolved hx
  rw [resolvePrediction_predict1, hresolved]
  exact (predict1_plain sv m fr x hx (.int i) fresh).trans hcore

def pred_empty : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D)
    (x : Data D) (idx : Idx) (fresh f : Nat) (r : Report1) (xt : Mat) (names disp : List String)
    (units : List D),
  NotSelector x → fullReport1 m fr false fresh = .ok (r, f) → r.equations = [] →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) →
  predict1 sv m fr (.data x) idx fresh = .ok ⟨List.replicate xt.nobs (.fin 0), fr.yUnits⟩

theorem pred_empty_holds : pred_empty := by
  intro D _ sv m fr x idx fresh f r xt names disp units hx hr he hg
  rw [predict1_plain sv m fr x hx]
  simp [predictCore1, hr, he, prepare, hg, fallback1, wrap1, bind, Except.bind, pure, Except.pure]

def pred_names : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (fr : Fit1 D) (frK : FitK D) (x : Data D) (idx : Idx) (fresh f : Nat)
    (r : Report1) (rK : ReportK) (xt : Mat) (names disp : List String) (units : List D),
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) →
  (fullReport1 m fr false fresh = .ok (r, f) → r.equations ≠ [] → names ≠ fr.variableNames →
    predictCore1 sv m fr x idx fresh =
      .error (.assertionError "Variable names do not match fitted regressor.")) ∧
  (fullReportK m frK false fresh = .ok (rK, f) →
    (rK.equations.isEmpty || rK.equations.any List.isEmpty) = false →
    names ≠ frK.variableNames →
    predictCoreK sv m frK x idx fresh =
      .error (.assertionError "Variable names do not match fitted regressor."))

theorem pred_names_holds : pred_names := by
  intro D _ sv m fr frK x idx fresh f r rK xt names disp units hg
  constructor
  · intro hr hne hn
    have hne' : r.equations.isEmpty = false := by cases he : r.equations <;> simp_all
    simp [predictCore1, hr, hne', prepare, hg, validateNames, hn, bind, Except.bind]
  · intro hr hne hn
    simp [predictCoreK, hr, hne, prepare, hg, validateNames, hn, bind, Except.bind]

def pred_units : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D)
    (x : Data D) (idx : Idx) (fresh f : Nat) (r : Report1) (xt : Mat) (names disp : List String)
    (units a b : List D),
  fullReport1 m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  cleanUnitsVec units = some a → fr.xUnits = some b →
  (a.length = b.length → a ≠ b → predictCore1 sv m fr x idx fresh =
    .error (.assertionError "Units of new data do not match units of fitted regressor.")) ∧
  (a.length ≠ b.length → a.length ≠ 1 → b.length ≠ 1 →
    predictCore1 sv m fr x idx fresh = .error (.dimensionMismatch "arrays could not be broadcast"))

theorem pred_units_holds : pred_units := by
  intro D _ sv m fr x idx fresh f r xt names disp units a b hr hne hg hn ha hb
  have hne' : r.equations.isEmpty = false := by cases he : r.equations <;> simp_all
  constructor
  · intro hlen hne
    have hd : ((a.zip b).all fun p => decide (p.1 = p.2)) = false := by
      cases he : ((a.zip b).all fun p => decide (p.1 = p.2))
      · rfl
      · exact (hne ((zip_all_eq a b hlen).mp he)).elim
    simp [predictCore1, hr, hne', prepare, hg, validateNames, hn, validateUnits, ha, hb,
      unitsMatch, hlen, hd, bind, Except.bind, pure, Except.pure]
    rfl
  · intro hlen hna hnb
    have hu : unitsMatch (some a) (some b) =
        .error (.dimensionMismatch "arrays could not be broadcast") := by
      cases a with
      | nil =>
        cases b with
        | nil => exact False.elim (hlen rfl)
        | cons x xs => cases xs <;> simp_all [unitsMatch]
      | cons x xs =>
        cases xs with
        | nil => simp at hna
        | cons y ys =>
          cases b with
          | nil => rfl
          | cons z zs => cases zs <;> simp_all [unitsMatch]
    simp [predictCore1, hr, hne', prepare, hg, validateNames, hn, validateUnits, ha, hb, hu,
      bind, Except.bind, pure, Except.pure]

def pred_vec : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : Fit1 D)
    (x : Data D) (fresh f : Nat) (r : Report1) (xt : Mat) (names disp : List String) (units : List D)
    (is : List Int),
  NotSelector x → fullReport1 m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true →
  predict1 sv m fr (.data x) (.vec is) fresh =
    if ∃ i ∈ is, i < 1 ∨ (r.equations.length : Int) < i then .error .boundsError
    else .error (.methodError "no method matching eval_tree_mlj(::Vector, ...)")

theorem pred_vec_holds : pred_vec := by
  intro D _ sv m fr x fresh f r xt names disp units is hx hr hne hg hn hu
  rw [predict1_plain sv m fr x hx]
  have hne' : r.equations.isEmpty = false := by
    cases he : r.equations with
    | nil => exact absurd he hne
    | cons _ _ => rfl
  simp only [predictCore1, hr, hne', prepare_ok hg hn hu, bind, Except.bind, pure, Except.pure]
  suffices h :
      (do let _ ← is.mapM (index r.equations)
          throw (.methodError "no method matching eval_tree_mlj(::Vector, ...)") : Jl (Col D)) =
        if ∃ i ∈ is, i < 1 ∨ (r.equations.length : Int) < i then .error .boundsError
        else .error (.methodError "no method matching eval_tree_mlj(::Vector, ...)") from h
  induction is with
  | nil => simp [bind, Except.bind, pure, Except.pure]; rfl
  | cons i is ih =>
    have hibad : (i < 1 ∨ (r.equations.length : Int) < i) →
        index r.equations i = .error .boundsError := by
      intro h
      unfold index
      split
      · rfl
      · rw [List.getElem?_eq_none (by omega)]
    by_cases hi : i < 1 ∨ (r.equations.length : Int) < i
    · simp [List.mapM_cons, hibad hi, hi, bind, Except.bind]
    · have hsize : (i - 1).toNat < r.equations.length := by omega
      have hiok : index r.equations i = .ok r.equations[(i - 1).toNat] := by
        unfold index
        rw [if_neg (by omega), List.getElem?_eq_getElem hsize]
      simp only [List.mapM_cons, hiok, bind, Except.bind, List.mem_cons,
        exists_eq_or_imp, hi, false_or]
      cases hrest : is.mapM (index r.equations) <;>
        simpa [hrest, bind, Except.bind, pure, Except.pure] using ih

/-- A feature table is treated as data unless its keys are exactly `data` and `idx`. -/
def pred_feature_table : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (fr : Fit1 D) (cols : List (String × List (Cell D))) (idx : Idx) (fresh : Nat),
  selectorOk (cols.map Prod.fst) = false →
  predict1 sv m fr (.data (.table cols)) idx fresh = predictCore1 sv m fr (.table cols) idx fresh

def unitServices : PredictServices Unit := ⟨fun _ => "", fun _ _ => .error .boundsError,
  fun _ _ => .error .boundsError⟩

/-- One equation (tree 0, loss 1) trained on the features `data` and `x2`. -/
def tableFit : Fit1 Unit :=
  ⟨defaultModel, ⟨0, ⟨[slotOf (.fin 1) 1 0]⟩⟩, 100, 1,
    ⟨signRt, .log, fun _ => 1, fun _ _ => "", fun _ _ => ([.fin 3], true), 0⟩,
    ["data", "x2"], none, false, none, none⟩

def dataTable : List (String × List (Cell Unit)) := [("data", [(.fin 1, ())]), ("x2", [(.fin 2, ())])]

theorem pred_feature_table_refuted : ¬ pred_feature_table := by
  intro h
  have := congrArg Except.toOption
    (h Unit unitServices defaultModel tableFit dataTable .none 0 (by decide))
  have h1 : (predict1 unitServices defaultModel tableFit (.data (.table dataTable)) .none 0).toOption =
      none := by decide +kernel
  have h2 : (predictCore1 unitServices defaultModel tableFit (.table dataTable) .none 0).toOption =
      some ⟨[.fin 3], none⟩ := by decide +kernel
  rw [h1, h2] at this; cases this

/-! ## Multitarget predictions -/

def predK_int : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : FitK D)
    (x : Data D) (fresh f : Nat) (r : ReportK) (xt : Mat) (names disp : List String) (units : List D)
    (i : Int),
  NotSelector x → fullReportK m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  (∀ eqs ∈ r.equations, eqs ≠ []) →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true →
  predictK sv m fr (.data x) (.int i) fresh =
    .error (.methodError "no method matching keys(::Int64, ::Vector)")

theorem nonempty_flag {r : ReportK} (hne : r.equations ≠ []) (hall : ∀ eqs ∈ r.equations, eqs ≠ []) :
    (r.equations.isEmpty || r.equations.any List.isEmpty) = false := by
  cases he : r.equations with
  | nil => exact absurd he hne
  | cons e es =>
    rw [he] at hall
    simp only [List.isEmpty_cons, Bool.false_or]
    cases ha : (e :: es).any List.isEmpty
    · rfl
    · obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp ha
      exact absurd (List.isEmpty_iff.mp hqe) (hall q hq)

theorem predK_int_holds : predK_int := by
  intro D _ sv m fr x fresh f r xt names disp units i hx hr hne hall hg hn hu
  rw [predictK_plain sv m fr x hx]
  simp only [predictCoreK, hr, nonempty_flag hne hall, prepare_ok hg hn hu, perTarget, bind,
    Except.bind, pure, Except.pure]
  rfl

def predK_length : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : FitK D)
    (x : Data D) (fresh f : Nat) (r : ReportK) (xt : Mat) (names disp : List String) (units : List D)
    (is : List Int),
  NotSelector x → fullReportK m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  (∀ eqs ∈ r.equations, eqs ≠ []) →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true → is.length ≠ r.equations.length →
  predictK sv m fr (.data x) (.vec is) fresh =
    .error (.dimensionMismatch
      s!"all inputs to eachindex must have the same indices, got Base.OneTo({is.length}) and Base.OneTo({r.equations.length})")

theorem predK_length_holds : predK_length := by
  intro D _ sv m fr x fresh f r xt names disp units is hx hr hne hall hg hn hu hl
  rw [predictK_plain sv m fr x hx]
  simp only [predictCoreK, hr, nonempty_flag hne hall, prepare_ok hg hn hu, perTarget, bind,
    Except.bind, pure, Except.pure, if_neg hl]
  rfl

def predK_empty : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : FitK D)
    (x : Data D) (idx : Idx) (fresh f : Nat) (r : ReportK) (xt : Mat) (names disp : List String)
    (units : List D) (out : OutK D),
  NotSelector x → fullReportK m fr false fresh = .ok (r, f) → (∃ eqs ∈ r.equations, eqs = []) →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → fallbackK fr xt = .ok out →
  predictK sv m fr (.data x) idx fresh = .ok (some out)

theorem predK_empty_holds : predK_empty := by
  intro D _ sv m fr x idx fresh f r xt names disp units out hx hr he hg hf
  rw [predictK_plain sv m fr x hx]
  have hflag : (r.equations.isEmpty || r.equations.any List.isEmpty) = true := by
    obtain ⟨q, hq, rfl⟩ := he
    simp only [Bool.or_eq_true]
    exact .inr (List.any_eq_true.mpr ⟨[], hq, rfl⟩)
  simp [predictCoreK, hr, hflag, prepare, hg, hf, bind, Except.bind, pure, Except.pure]

/-- Whenever a multitarget prediction is a matrix, it has one column per target. -/
def predK_width : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (fr : FitK D) (x : Data D) (idx : Idx) (fresh : Nat) (cols : List (Col D)),
  predictK sv m fr (.data x) idx fresh = .ok (some (.matrix cols)) → cols.length = fr.numTargets

/-- Two targets with one equation each; tree 0 fails to evaluate (NaN), tree 1 gives 2. -/
def twoTargetFit : FitK Unit :=
  ⟨defaultModel, ⟨0, [⟨[slotOf (.fin 1) 1 0]⟩, ⟨[slotOf (.fin 1) 1 1]⟩]⟩, 100, 2,
    ⟨signRt, .log, fun _ => 1, fun _ _ => "",
      fun t _ => if t = 0 then ([.nan], false) else ([.fin 2], true), 0⟩,
    ["x1"], some ["y1", "y2"], false, none, none⟩

def oneCell : Data Unit := .matrix 1 [[(.fin 0, ())]]

theorem twoTarget_output :
    (predictK unitServices defaultModel twoTargetFit (.data oneCell) .none 0).toOption =
      some (some (.matrix [⟨[.fin 0], none⟩, ⟨[.fin 0], none⟩, ⟨[.fin 2], none⟩])) := by
  decide +kernel

def pred_selector_payload : Prop := pred_select ∧
  (∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
      (fr1 : Fit1 D) (frK : FitK D) (x : Data D) (inner outer : Idx) (fresh : Nat),
    NotSelector x →
    predict1 sv m fr1 (.select (.data x) inner) outer fresh = predictCore1 sv m fr1 x inner fresh ∧
    predictK sv m frK (.select (.data x) inner) outer fresh = predictCoreK sv m frK x inner fresh) ∧
  let hall : Hof := ⟨[slotOf (.fin 2) 1 1, slotOf (.fin 1) 2 2]⟩
  let opts := { plainOpts .linear with
    eval := fun tree rows =>
      (if rows = [[.fin 7]] then [.fin (if tree = 1 then 10 else 20)] else [.fin 0], true) }
  let x : PInput Unit := .data (.matrix 1 [[(.fin 7, ())]])
  let fit1 := { fit1Of hall .linear with options := opts }
  let fitK : FitK Unit :=
    ⟨defaultModel, ⟨0, [hall, hall]⟩, 100, 2, opts, ["x1"], some ["y1", "y2"], false, none, none⟩
  (predict1 unitServices defaultModel fit1 (.select x (.int 1)) (.int 2) 0).toOption =
      some ⟨[.fin 10], none⟩ ∧
  (predict1 unitServices defaultModel fit1 (.select x (.int 2)) (.int 1) 0).toOption =
      some ⟨[.fin 20], none⟩ ∧
  (predictK unitServices defaultModel fitK (.select x (.vec [1, 2])) (.vec [2, 1]) 0).toOption =
      some (some (.matrix [⟨[.fin 10], none⟩, ⟨[.fin 20], none⟩])) ∧
  (predictK unitServices defaultModel fitK (.select x (.vec [2, 1])) (.vec [1, 2]) 0).toOption =
      some (some (.matrix [⟨[.fin 20], none⟩, ⟨[.fin 10], none⟩]))

theorem pred_selector_payload_holds : pred_selector_payload := by
  refine ⟨pred_select_holds, ?_⟩
  constructor
  · intro D _ sv m fr1 frK x inner outer fresh hx
    exact ⟨predict1_plain sv m fr1 x hx inner fresh, predictK_plain sv m frK x hx inner fresh⟩
  · decide +kernel

theorem predK_width_refuted : ¬ predK_width := by
  intro h
  have := h Unit unitServices defaultModel twoTargetFit oneCell .none 0 _
    (ok_of_toOption twoTarget_output)
  revert this; decide

theorem zipIdx_get : ∀ (l : List α) (n t : Nat) (e : α × Nat), (l.zipIdx n)[t]? = some e →
    l[t]? = some e.1 ∧ e.2 = n + t
  | [], _, _, _, h => by simp at h
  | a :: l, n, 0, e, h => by simp [List.zipIdx_cons] at h; subst h; simp
  | a :: l, n, t + 1, e, h => by
    simp only [List.zipIdx_cons, List.getElem?_cons_succ] at h
    have := zipIdx_get l (n + 1) t e h
    exact ⟨by simpa using this.1, by omega⟩

theorem zip_get : ∀ (a : List α) (b : List β) (t : Nat) (p : α × β), (a.zip b)[t]? = some p →
    a[t]? = some p.1 ∧ b[t]? = some p.2
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: a, y :: b, 0, p, h => by simp at h; subst h; simp
  | x :: a, y :: b, t + 1, p, h => by
    simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
    simpa using zip_get a b t p h

theorem hcat_columns : ∀ (ps : List (Piece D)), (∀ p ∈ ps, ∃ c, p = .column c) →
    ∃ cols, hcatPieces ps = some cols ∧ cols.length = ps.length ∧
      ∀ (t : Nat) c, cols[t]? = some c → ps[t]? = some (.column c)
  | [], _ => ⟨[], rfl, rfl, fun _ _ h => by simp at h⟩
  | p :: ps, h => by
    obtain ⟨c, rfl⟩ := h p (by simp)
    obtain ⟨cols, hc, hl, hg⟩ := hcat_columns ps (fun q hq => h q (by simp [hq]))
    refine ⟨c :: cols, by simp [hcatPieces, hc], by simp [hl], ?_⟩
    intro t d hd
    cases t with
    | zero => simp at hd; subst hd; rfl
    | succ t => simpa using hg t d (by simpa using hd)

theorem wrapK_ok {v : List JF} {us : Option (List D)} {k t : Nat}
    (hyu : us = none ∨ ∃ u, us = some u ∧ u.length = k) (ht : t < k) :
    wrapK v us (t + 1) = .ok ⟨v, us.bind (·[t]?)⟩ := by
  rcases hyu with rfl | ⟨u, rfl, hu⟩
  · rfl
  · have hget : u[t]? = some u[t] := List.getElem?_eq_getElem (by omega)
    have hidx : index u ((t + 1 : Nat) : Int) = .ok u[t] := by
      unfold index
      rw [if_neg (by omega), show (((t + 1 : Nat) : Int) - 1).toNat = t by omega, hget]
    simp only [wrapK]; rw [hidx]; simp [hget, bind, Except.bind, pure, Except.pure]

theorem targetPiece_ok [Dims D] {fr : FitK D} {xt : Mat} {eqs : List Nat} {i : Int} {t : Nat}
    {tree : Nat} {col : Col D} (htree : index eqs i = .ok tree)
    (hc : (fr.options.eval tree xt.rows).2 = true)
    (hw : wrapK (fr.options.eval tree xt.rows).1 fr.yUnits (t + 1) = .ok col) :
    targetPiece fr xt ((eqs, i), t) = .ok (.column col) := by
  rcases hev : fr.options.eval tree xt.rows with ⟨out, c⟩
  rw [hev] at hc hw
  simp only at hc hw
  subst hc
  simp [targetPiece, htree, evalMljK, hev, hw, bind, Except.bind, pure, Except.pure]

/-- An index vector selects, per output, that output's equation (src/MLJInterface.jl:599-603). -/
def predK_vec : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor) (fr : FitK D)
    (x : Data D) (fresh f : Nat) (r : ReportK) (xt : Mat) (names disp : List String) (units : List D)
    (is : List Int),
  NotSelector x → fullReportK m fr false fresh = .ok (r, f) → r.equations ≠ [] →
  (∀ eqs ∈ r.equations, eqs ≠ []) →
  getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, units) → names = fr.variableNames →
  unitsMatch (cleanUnitsVec units) fr.xUnits = .ok true → fr.yIsTable = false →
  (fr.yUnits = none ∨ ∃ us, fr.yUnits = some us ∧ us.length = r.equations.length) →
  is.length = r.equations.length →
  (∀ (t : Nat) eqs (i : Int), r.equations[t]? = some eqs → is[t]? = some i →
    ∃ tree, index eqs i = .ok tree ∧ (fr.options.eval tree xt.rows).2 = true) →
  ∃ cols, predictK sv m fr (.data x) (.vec is) fresh = .ok (some (.matrix cols)) ∧
    cols.length = r.equations.length ∧
    ∀ (t : Nat) eqs (i : Int) tree c, r.equations[t]? = some eqs → is[t]? = some i →
      index eqs i = .ok tree → cols[t]? = some c →
      c.values = (fr.options.eval tree xt.rows).1 ∧ c.unit = fr.yUnits.bind (·[t]?)

theorem predK_vec_holds : predK_vec := by
  intro D _ sv m fr x fresh f r xt names disp units is hx hr hne hall hg hn hu htab hyu hlen hev
  rw [predictK_plain sv m fr x hx]
  have hpiece : ∀ e ∈ (r.equations.zip is).zipIdx, ∃ tree,
      index e.1.1 e.1.2 = .ok tree ∧ targetPiece fr xt e =
        .ok (.column ⟨(fr.options.eval tree xt.rows).1, fr.yUnits.bind (·[e.2]?)⟩) := by
    intro e he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    obtain ⟨hz, he2⟩ := zipIdx_get _ 0 j e hj
    obtain ⟨h1, h2⟩ := zip_get _ _ j e.1 hz
    obtain ⟨tree, htree, hc⟩ := hev j e.1.1 e.1.2 h1 h2
    have hjt : j < r.equations.length := lt_of_get h1
    refine ⟨tree, htree, ?_⟩
    obtain ⟨⟨eqs, i⟩, t⟩ := e
    simp only at he2 htree hc ⊢
    subst he2
    exact targetPiece_ok htree hc (wrapK_ok (by simpa using hyu) (by omega))
  obtain ⟨pieces, hp⟩ := mapM_of _ (fun e he => by
    obtain ⟨tree, _, h⟩ := hpiece e he; exact ⟨_, h⟩)
  obtain ⟨hplen, hpget⟩ := mapM_ok _ _ hp
  have hcols : ∀ p ∈ pieces, ∃ c, p = .column c := by
    intro p hp'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp'
    have : j < ((r.equations.zip is).zipIdx).length := hplen ▸ lt_of_get hj
    obtain ⟨e, he⟩ : ∃ e, ((r.equations.zip is).zipIdx)[j]? = some e :=
      ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨tree, _, ht⟩ := hpiece e (List.mem_of_getElem? he)
    have := hpget j e p he hj
    rw [ht] at this; cases this; exact ⟨_, rfl⟩
  obtain ⟨cols, hc, hcl, hcg⟩ := hcat_columns pieces hcols
  have hLlen : ((r.equations.zip is).zipIdx).length = r.equations.length := by
    simp [List.length_zipIdx, List.length_zip, hlen]
  refine ⟨cols, ?_, by omega, ?_⟩
  · simp only [predictCoreK, hr, nonempty_flag hne hall, prepare_ok hg hn hu, perTarget, if_pos hlen,
      bind, Except.bind, pure, Except.pure, hp, hc, htab]
    rfl
  · intro t eqs i tree c h1 h2 htree hct
    have hpt := hcg t c hct
    have : t < ((r.equations.zip is).zipIdx).length := hplen ▸ lt_of_get hpt
    obtain ⟨e, he⟩ : ∃ e, ((r.equations.zip is).zipIdx)[t]? = some e :=
      ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨hz, he2⟩ := zipIdx_get _ 0 t e he
    obtain ⟨h1', h2'⟩ := zip_get _ _ t e.1 hz
    obtain ⟨tree', htree', ht⟩ := hpiece e (List.mem_of_getElem? he)
    have := hpget t e _ he hpt
    rw [ht] at this
    have heq := get_unique h1 h1'
    have hiq := get_unique h2 h2'
    rw [← heq, ← hiq, htree] at htree'
    cases htree'
    cases this
    simp [he2]

end SymReg.MLJ
