import SymReg.MLJ.PredictProps

namespace SymReg.MLJ
open DynExpr SymReg.HofMig

variable {D : Type} [Dims D]

theorem update1_ok {sv : FitServices D} {m : Regressor} {old : Option (Fit1 D)} {x y : Data D}
    {w : Option (List JF)} {fresh f : Nat} {fr : Fit1 D} {r : Report1}
    (h : update1 sv m old x y w fresh = .ok (fr, r, f)) :
    ∃ o xt names disp xu yt yn yu n st, warmOptions sv m old = .ok o ∧
      getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, xu) ∧ formatY1 y = .ok (yt, yn, yu) ∧
      remaining m old = .ok n ∧
      sv.search1 ⟨n, xt, yt, w, names, disp, o, old.map FitResult.state, cleanUnitsVec xu,
        cleanUnits yu⟩ = .ok st ∧
      fr = ⟨m, st, m.niterations, 1, o, names, yn, y.isTable,
        cleanUnitsVec xu, cleanUnits yu⟩ ∧
      fullReport1 m fr true fresh = .ok (r, f) := by
  simp only [update1] at h
  cases h1 : warmOptions sv m old with
  | error e => simp [h1, bind, Except.bind] at h
  | ok o =>
  cases h2 : getMatrixAndInfo sv.subscript x with
  | error e => simp [h1, h2, bind, Except.bind] at h
  | ok p2 =>
  obtain ⟨xt, names, disp, xu⟩ := p2
  cases h3 : formatY1 y with
  | error e => simp [h1, h2, h3, bind, Except.bind] at h
  | ok p3 =>
  obtain ⟨yt, yn, yu⟩ := p3
  cases h4 : remaining m old with
  | error e => simp [h1, h2, h3, h4, bind, Except.bind] at h
  | ok n =>
  cases h5 : sv.search1 ⟨n, xt, yt, w, names, disp, o, old.map FitResult.state, cleanUnitsVec xu,
      cleanUnits yu⟩ with
  | error e => simp [h1, h2, h3, h4, h5, bind, Except.bind] at h
  | ok st =>
  cases h6 : fullReport1 m (⟨m, st, m.niterations, 1, o, names, yn,
      y.isTable, cleanUnitsVec xu, cleanUnits yu⟩ : Fit1 D) true fresh with
  | error e => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at h
  | ok p6 =>
  obtain ⟨r', f'⟩ := p6
  simp [h1, h2, h3, h4, h5, h6, bind, Except.bind, pure, Except.pure] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨o, xt, names, disp, xu, yt, yn, yu, n, st, rfl, rfl, rfl, rfl, h5, rfl, h6⟩

theorem updateK_ok {sv : FitServices D} {m : Regressor} {old : Option (FitK D)} {x y : Data D}
    {w : Option (List JF)} {fresh f : Nat} {fr : FitK D} {r : ReportK}
    (h : updateK sv m old x y w fresh = .ok (fr, r, f)) :
    ∃ o xt names disp xu yt yn yu n st, warmOptions sv m old = .ok o ∧
      getMatrixAndInfo sv.subscript x = .ok (xt, names, disp, xu) ∧
      formatYK sv.subscript y = .ok (yt, yn, yu) ∧ remaining m old = .ok n ∧
      sv.searchK ⟨n, xt, yt, w.map fun w => List.replicate yt.rows.length w, names, disp, o,
        old.map FitResult.state, cleanUnitsVec xu, cleanUnitsVec yu⟩ = .ok st ∧
      fr = ⟨m, st, m.niterations, yt.rows.length, o, names, some yn,
        y.isTable, cleanUnitsVec xu, cleanUnitsVec yu⟩ ∧
      fullReportK m fr true fresh = .ok (r, f) := by
  simp only [updateK] at h
  cases h1 : warmOptions sv m old with
  | error e => simp [h1, bind, Except.bind] at h
  | ok o =>
  cases h2 : getMatrixAndInfo sv.subscript x with
  | error e => simp [h1, h2, bind, Except.bind] at h
  | ok p2 =>
  obtain ⟨xt, names, disp, xu⟩ := p2
  cases h3 : formatYK sv.subscript y with
  | error e => simp [h1, h2, h3, bind, Except.bind] at h
  | ok p3 =>
  obtain ⟨yt, yn, yu⟩ := p3
  cases h4 : remaining m old with
  | error e => simp [h1, h2, h3, h4, bind, Except.bind] at h
  | ok n =>
  cases h5 : sv.searchK ⟨n, xt, yt, w.map fun w => List.replicate yt.rows.length w, names, disp, o,
      old.map FitResult.state, cleanUnitsVec xu, cleanUnitsVec yu⟩ with
  | error e => simp [h1, h2, h3, h4, h5, bind, Except.bind] at h
  | ok st =>
  cases h6 : fullReportK m (⟨m, st, m.niterations, yt.rows.length, o,
      names, some yn, y.isTable, cleanUnitsVec xu, cleanUnitsVec yu⟩ : FitK D) true fresh with
  | error e => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at h
  | ok p6 =>
  obtain ⟨r', f'⟩ := p6
  simp [h1, h2, h3, h4, h5, h6, bind, Except.bind, pure, Except.pure] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨o, xt, names, disp, xu, yt, yn, yu, n, st, rfl, rfl, rfl, rfl, h5, rfl, h6⟩

omit [Dims D] in
theorem warm_some {sv : FitServices D} {m : Regressor} {old : FitResult S U D} {o : Opts}
    (h : warmOptions sv m (some old) = .ok o) :
    sv.getOptions m = .ok o ∧ sv.checkWarm old.options o = .ok () := by
  simp only [warmOptions] at h
  cases h1 : sv.getOptions m with
  | error e => simp [h1, bind, Except.bind] at h
  | ok o' =>
    cases h2 : sv.checkWarm old.options o' with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok u =>
      simp [h1, h2, bind, Except.bind, pure, Except.pure] at h; subst h; exact ⟨rfl, h2⟩

omit [Dims D] in
theorem remaining_ok {m : Regressor} {old : Option (FitResult S U D)} {n : Int}
    (h : remaining m old = .ok n) :
    n = (match old with
      | none => m.niterations
      | some old => iterationDifference m.niterations old.niterations) ∧ 0 ≤ n := by
  cases old <;> simp only [remaining] at h ⊢ <;> split at h
  all_goals first | exact ⟨(Except.ok.inj h).symm, by rw [← Except.ok.inj h]; assumption⟩ | cases h

/-! ## Fitting and warm starts -/

def fit_fresh : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (m : Regressor) (x y : Data D)
    (w : Option (List JF)) (fresh f : Nat) (fr : Fit1 D) (r : Report1),
  fit1 sv m x y w fresh = .ok (fr, r, f) →
  ∃ call : Call1 D, sv.search1 call = .ok fr.state ∧ call.saved = none ∧
    call.niterations = m.niterations ∧ call.weights = w ∧ call.options = fr.options ∧
    call.variableNames = fr.variableNames ∧ fr.niterations = m.niterations ∧ fr.model = m ∧
    fr.numTargets = 1 ∧ fr.yIsTable = y.isTable ∧ fullReport1 m fr true fresh = .ok (r, f)

theorem fit_fresh_holds : fit_fresh := by
  intro D _ sv m x y w fresh f fr r h
  obtain ⟨o, xt, names, disp, xu, yt, yn, yu, n, st, _, _, _, h4, h5, rfl, h6⟩ := update1_ok h
  obtain ⟨hn, _⟩ := remaining_ok h4
  simp at hn
  subst hn
  exact ⟨_, h5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h6⟩

def update_warm : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (m : Regressor)
    (old fr : Fit1 D) (oldK frK : FitK D) (x y : Data D) (w : Option (List JF))
    (fresh f : Nat) (r : Report1) (rK : ReportK),
  (update1 sv m (some old) x y w fresh = .ok (fr, r, f) →
    sv.getOptions m = .ok fr.options ∧ sv.checkWarm old.options fr.options = .ok () ∧
    ∃ call : Call1 D, sv.search1 call = .ok fr.state ∧ call.saved = some old.state ∧
      call.niterations = iterationDifference m.niterations old.niterations ∧
      0 ≤ call.niterations ∧ fr.niterations = m.niterations) ∧
  (updateK sv m (some oldK) x y w fresh = .ok (frK, rK, f) →
    sv.getOptions m = .ok frK.options ∧ sv.checkWarm oldK.options frK.options = .ok () ∧
    ∃ call : CallK D, sv.searchK call = .ok frK.state ∧ call.saved = some oldK.state ∧
      call.niterations = iterationDifference m.niterations oldK.niterations ∧
      0 ≤ call.niterations ∧ frK.niterations = m.niterations)

theorem update_warm_holds : update_warm := by
  intro D _ sv m old fr oldK frK x y w fresh f r rK
  constructor
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h1, _, _, h4, h5, rfl, _⟩ := update1_ok h
    obtain ⟨hg, hc⟩ := warm_some h1
    obtain ⟨hn, hpos⟩ := remaining_ok h4
    exact ⟨hg, hc, _, h5, rfl, hn, hpos, rfl⟩
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h1, _, _, h4, h5, rfl, _⟩ := updateK_ok h
    obtain ⟨hg, hc⟩ := warm_some h1
    obtain ⟨hn, hpos⟩ := remaining_ok h4
    exact ⟨hg, hc, _, h5, rfl, hn, hpos, rfl⟩

def update_incompatible : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (m : Regressor)
    (old : Fit1 D) (oldK : FitK D) (x y : Data D) (w : Option (List JF)) (fresh : Nat) (o : Opts)
    (e : JlError),
  sv.getOptions m = .ok o →
  (sv.checkWarm old.options o = .error e → update1 sv m (some old) x y w fresh = .error e) ∧
  (sv.checkWarm oldK.options o = .error e → updateK sv m (some oldK) x y w fresh = .error e)

theorem update_incompatible_holds : update_incompatible := by
  intro D _ sv m old oldK x y w fresh o e hg
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simp [update1, warmOptions, hg, hc, bind, Except.bind]
  · simp [updateK, warmOptions, hg, hc, bind, Except.bind]

def update_decrease : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (m : Regressor)
    (old : Fit1 D) (oldK : FitK D) (x y : Data D) (w : Option (List JF))
    (fresh : Nat) (o : Opts) (xi : Mat × List String × List String × List D)
    (yi : List JF × Option (List String) × D) (yk : Mat × List String × List D),
  sv.getOptions m = .ok o → getMatrixAndInfo sv.subscript x = .ok xi →
  (sv.checkWarm old.options o = .ok () → formatY1 y = .ok yi →
    iterationDifference m.niterations old.niterations < 0 →
    update1 sv m (some old) x y w fresh = .error (.assertionError "niterations >= 0")) ∧
  (sv.checkWarm oldK.options o = .ok () → formatYK sv.subscript y = .ok yk →
    iterationDifference m.niterations oldK.niterations < 0 →
    updateK sv m (some oldK) x y w fresh = .error (.assertionError "niterations >= 0"))

theorem update_decrease_holds : update_decrease := by
  intro D _ sv m old oldK x y w fresh o xi yi yk hg hx
  obtain ⟨a, b, c, d⟩ := xi
  constructor
  · intro hc hy hlt
    have hr : remaining m (some old) = .error (.assertionError "niterations >= 0") := by
      simp [remaining]; omega
    obtain ⟨p, q, s⟩ := yi
    simp [update1, warmOptions, hg, hc, hx, hy, hr, bind, Except.bind, pure, Except.pure]
  · intro hc hy hlt
    have hr : remaining m (some oldK) = .error (.assertionError "niterations >= 0") := by
      simp [remaining]; omega
    obtain ⟨p, q, s⟩ := yk
    simp [updateK, warmOptions, hg, hc, hx, hy, hr, bind, Except.bind, pure, Except.pure]

example : iterationDifference (-9223372036854775808) 1 = 9223372036854775807 := by decide

/-- `clean!` reports nothing and changes nothing; a negative `niterations` is
rejected only later, by the assertion in `_update`. -/
def clean_negative : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (m : Regressor)
    (x y : Data D) (w : Option (List JF)) (fresh : Nat) (o : Opts)
    (xi : Mat × List String × List String × List D) (yi : List JF × Option (List String) × D)
    (yk : Mat × List String × List D),
  clean m = ("", m) ∧
  (sv.getOptions m = .ok o → getMatrixAndInfo sv.subscript x = .ok xi → formatY1 y = .ok yi →
    m.niterations < 0 → fit1 sv m x y w fresh = .error (.assertionError "niterations >= 0")) ∧
  (sv.getOptions m = .ok o → getMatrixAndInfo sv.subscript x = .ok xi →
    formatYK sv.subscript y = .ok yk →
    m.niterations < 0 → fitK sv m x y w fresh = .error (.assertionError "niterations >= 0"))

theorem clean_negative_holds : clean_negative := by
  intro D _ sv m x y w fresh o xi yi yk
  obtain ⟨a, b, c, d⟩ := xi
  refine ⟨rfl, ?_, ?_⟩
  · intro hg hx hy hlt
    have hr : remaining m (none : Option (Fit1 D)) =
        .error (.assertionError "niterations >= 0") := by simp [remaining]; omega
    obtain ⟨p, q, s⟩ := yi
    simp [fit1, update1, warmOptions, hg, hx, hy, hr, bind, Except.bind, pure, Except.pure]
  · intro hg hx hy hlt
    have hr : remaining m (none : Option (FitK D)) =
        .error (.assertionError "niterations >= 0") := by simp [remaining]; omega
    obtain ⟨p, q, s⟩ := yk
    simp [fitK, updateK, warmOptions, hg, hx, hy, hr, bind, Except.bind, pure, Except.pure]

def fitK_targets : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (m : Regressor)
    (old : Option (FitK D)) (x y : Data D) (w : Option (List JF)) (fresh f : Nat) (fr : FitK D)
    (r : ReportK),
  updateK sv m old x y w fresh = .ok (fr, r, f) →
  ∃ (call : CallK D) (names : List String) (units : List D), sv.searchK call = .ok fr.state ∧
    formatYK sv.subscript y = .ok (call.y, names, units) ∧
    fr.numTargets = call.y.rows.length ∧ call.weights = w.map (List.replicate fr.numTargets) ∧
    call.saved = old.map FitResult.state ∧ fr.yVariableNames = some names ∧
    fr.niterations = m.niterations

theorem fitK_targets_holds : fitK_targets := by
  intro D _ sv m old x y w fresh f fr r h
  obtain ⟨o, xt, names, disp, xu, yt, yn, yu, n, st, _, _, hy, h4, h5, rfl, _⟩ := updateK_ok h
  exact ⟨_, yn, yu, h5, hy, rfl, rfl, rfl, rfl, rfl⟩

def msgMulti : String := "For multi-output regression, please use `MultitargetSRRegressor`."
def msgSingle : String := "For single-output regression, please use `SRRegressor`."

def format_y1 : Prop := ∀ (D : Type) [Dims D] (cols : List (String × List (Cell D))) (n : Nat)
    (mcols : List (List (Cell D))) (c : List (Cell D)),
  formatY1 (.table cols) = .error (.assertionError msgMulti) ∧
  (mcols.length > 1 → formatY1 (.matrix n mcols) = .error (.assertionError msgMulti)) ∧
  formatY1 (.matrix n [c]) = formatY1 (.vector c)

theorem format_y1_holds : format_y1 := by
  intro D _ cols n mcols c
  refine ⟨rfl, fun h => by simp [formatY1, h, msgMulti], by simp [formatY1]⟩

def format_yK : Prop := ∀ (D : Type) [Dims D] (sub : Nat → String) (v : List (Cell D)) (n : Nat)
    (mcols : List (List (Cell D))),
  formatYK sub (.vector v) = .error (.assertionError msgSingle) ∧
  (mcols.length ≤ 1 → formatYK sub (.matrix n mcols) = .error (.assertionError msgSingle))

theorem format_yK_holds : format_yK := by
  intro D _ sub v n mcols
  refine ⟨rfl, fun h => ?_⟩
  simp [formatYK, msgSingle, show ¬ mcols.length > 1 by omega]

def machine_fit : Prop := ∀ (D : Type) [Dims D] (sv : FitServices D) (mach : Machine1 D)
    (fresh : Nat),
  machineFit1 sv mach true fresh = (fit1 sv mach.model mach.x mach.y mach.w fresh).map
      (fun p => ({ mach with fitresult := some p.1, report := some p.2.1 }, p.2.2)) ∧
  ∀ old, mach.fitresult = some old → machineFit1 sv mach false fresh =
    (update1 sv mach.model (some old) mach.x mach.y mach.w fresh).map
      (fun p => ({ mach with fitresult := some p.1, report := some p.2.1 }, p.2.2))

theorem machine_fit_holds : machine_fit := by
  intro D _ sv mach fresh
  refine ⟨?_, fun old hold => ?_⟩
  · simp only [machineFit1, Bool.true_or, if_true]
    cases fit1 sv mach.model mach.x mach.y mach.w fresh <;> rfl
  · simp only [machineFit1, hold, Option.isNone_some, Bool.false_or, Bool.false_eq_true, if_false]
    cases update1 sv mach.model (some old) mach.x mach.y mach.w fresh <;> rfl

def machine_unfitted : Prop := ∀ (D : Type) [Dims D] (sv : PredictServices D) (m : Regressor)
    (x y : Data D) (w : Option (List JF)) (xnew : Option (PInput D)) (fresh : Nat) (mach : Machine1 D)
    (fr : Fit1 D),
  machinePredict1 sv (machine1 m x y w) xnew fresh = .error (.argumentError
    "This machine has not been fitted. Call `fit!(mach)` before `predict`.") ∧
  machineReport1 (machine1 m x y w) = .error (.argumentError
    "This machine has not been fitted. Call `fit!(mach)` before `report`.") ∧
  (mach.fitresult = some fr →
    machinePredict1 sv mach none fresh = predict1 sv mach.model fr (.data mach.x) .none fresh)

theorem machine_unfitted_holds : machine_unfitted := by
  intro D _ sv m x y w xnew fresh mach fr
  refine ⟨rfl, rfl, fun h => ?_⟩
  simp [machinePredict1, checkFitted, h, bind, Except.bind]

def fitted_after_fit : Prop := ∀ (D : Type) (m : Regressor) (fr1 : Fit1 D) (frK : FitK D)
    (fresh f : Nat) (r1 : Report1) (rK : ReportK),
  (fullReport1 m fr1 true fresh = .ok (r1, f) →
    fittedParams1 m fr1 fresh = .ok (r1.bestIdx, r1.equations, r1.equationStrings)) ∧
  (fullReportK m frK true fresh = .ok (rK, f) →
    fittedParamsK m frK fresh = .ok (rK.bestIdx, rK.equations, rK.equationStrings))

theorem fitted_after_fit_holds : fitted_after_fit := by
  intro D m fr1 frK fresh f r1 rK
  constructor
  · intro h; simp [fittedParams1, h, bind, Except.bind, pure, Except.pure]
  · intro h; simp [fittedParamsK, h, bind, Except.bind, pure, Except.pure]

/-! ## Struct defaults and keywords -/

def defaults : Prop := ∀ (k : ModelName) (s : String),
  ∃ m, construct k (.symbol s) = .ok m ∧ m.name = k ∧
    m.niterations = (if k.isTest then 1 else 100) ∧ m.selection = chooseBestMethod ∧ m.parallelism = s

theorem defaults_holds : defaults := fun _ _ => ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- The default `niterations` of the non-test models is the documented `10`. -/
def defaults_doc : Prop := ∀ k : ModelName, k.isTest = false → defaultNiterations k = documentedNiterations

theorem defaults_doc_refuted : ¬ defaults_doc := fun h => by
  have := h .srRegressor rfl; simp [defaultNiterations, documentedNiterations, ModelName.isTest] at this

/-- Every documented spelling of `parallelism`, including a string, constructs a model. -/
def parallelism_string : Prop := ∀ (k : ModelName) (s : String),
  s ∈ ["serial", "multithreading", "multiprocessing"] → ∃ m, construct k (.string s) = .ok m

theorem parallelism_string_refuted : ¬ parallelism_string := fun h => by
  obtain ⟨m, hm⟩ := h .srRegressor "serial" (by simp)
  simp [construct, storeParallelism, bind, Except.bind] at hm

end SymReg.MLJ
