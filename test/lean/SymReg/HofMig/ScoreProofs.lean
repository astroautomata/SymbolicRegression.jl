import SymReg.HofMig.Scores

namespace SymReg.HofMig
open DynExpr
open SymReg.Loss (LossPrecision)
open DynExpr.Expressions.Sampling (greater)

attribute [local semireducible] Rat.add Rat.mul Rat.inv Rat.sub

private theorem relu_zero_of_nan (x : ScoreFloat) (h : x.value = .nan) :
    (relu x).value = .fin 0 := by simp [relu, h, greater]

private theorem div_nan_left (x y : ScoreFloat) (h : x.value = .nan) :
    (x.div y).value = .nan := by
  unfold ScoreFloat.div
  cases hy : y.value <;> split <;> simp_all [ScoreFloat.round, JF.neg, JF.div, LossPrecision.round]

private theorem div_nan_right (x y : ScoreFloat) (h : y.value = .nan) :
    (x.div y).value = .nan := by
  cases hx : x.value <;>
    simp [ScoreFloat.div, ScoreFloat.round, h, hx, JF.div, LossPrecision.round]

private theorem add_nan_left (x y : ScoreFloat) (h : x.value = .nan) :
    (x.add y).value = .nan := by
  cases hy : y.value <;> simp [ScoreFloat.add, ScoreFloat.round, h, hy, JF.add, LossPrecision.round]

private theorem add_nan_right (x y : ScoreFloat) (h : y.value = .nan) :
    (x.add y).value = .nan := by
  cases hx : x.value <;> simp [ScoreFloat.add, ScoreFloat.round, h, hx, JF.add, LossPrecision.round]

private theorem neg_nan (x : ScoreFloat) (h : x.value = .nan) : x.neg.value = .nan := by
  simp [ScoreFloat.neg, h, JF.neg]

def direct_nan : Prop := ∀ (cur last : ScoreFloat) (delta : ScoreDelta),
  cur.value = .nan ∨ last.value = .nan → (directScore cur last delta).value = .fin 0

theorem direct_nan_holds : direct_nan := by
  intro cur last delta h
  have hd : (cur.add last.neg).value = .nan := h.elim
    (add_nan_left cur last.neg) (fun hl => add_nan_right cur last.neg (neg_nan last hl))
  exact relu_zero_of_nan _ (div_nan_left _ _ (neg_nan _ hd))

private theorem score_nan_input (rt : ScalarRuntime) (cur last : ScoreFloat) (delta : ScoreDelta)
    (h : (epsilon cur).value = .nan) :
    (zeroCenteredScore rt cur last delta).map ScoreFloat.value = .ok (.fin 0) := by
  have hlog : (scoreLogInput cur last).value = .nan := add_nan_right _ _ h
  let x : ScoreFloat := ⟨(scoreLogInput cur last).precision, .nan, false⟩
  have hn := relu_zero_of_nan _ (div_nan_left x.neg (delta.asFloat x.precision) rfl)
  simp [zeroCenteredScore, scalarLog, hlog, x, bind, Except.bind, pure, Except.pure, Except.map,
    show (relu (x.neg.div (delta.asFloat x.precision))).value = .fin 0 from hn]

def zero_score_nan : Prop := ∀ (rt : ScalarRuntime) (cur last : ScoreFloat) (delta : ScoreDelta),
  cur.value = .nan → (zeroCenteredScore rt cur last delta).map ScoreFloat.value = .ok (.fin 0)

theorem zero_score_nan_holds : zero_score_nan := by
  intro rt cur last delta h
  exact score_nan_input rt cur last delta (by simp [epsilon, h])

def zero_score_nonfinite : Prop := ∀ (rt : ScalarRuntime) (cur last : ScoreFloat) (delta : ScoreDelta),
  cur.value = .posInf ∨ cur.value = .negInf →
    (zeroCenteredScore rt cur last delta).map ScoreFloat.value = .ok (.fin 0)

theorem zero_score_nonfinite_holds : zero_score_nonfinite := by
  intro rt cur last delta h
  exact score_nan_input rt cur last delta (by rcases h with h | h <;> simp [epsilon, h])

private def zeroUlp : LossPrecision → Rat
  | .float16 => 1 / (2 : Rat)^24
  | .float32 => 1 / (2 : Rat)^149
  | .float64 => 1 / (2 : Rat)^1074

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 2048 in
private theorem zero_log_input (p : LossPrecision) (a b : Bool) :
    scoreLogInput ⟨p, .fin 0, a⟩ ⟨p, .fin 0, b⟩ = ⟨p, .fin (zeroUlp p), false⟩ := by
  cases p <;> cases a <;> cases b <;> decide +kernel

/-- Equal zeros leave only the current IEEE type's smallest subnormal at the log input. -/
def zero_ratio : Prop := ∀ (rt : ScalarRuntime) (p : LossPrecision) (a b : Bool) (delta : ScoreDelta),
  scoreLogInput ⟨p, .fin 0, a⟩ ⟨p, .fin 0, b⟩ = ⟨p, .fin (zeroUlp p), false⟩ ∧
  zeroCenteredScore rt ⟨p, .fin 0, a⟩ ⟨p, .fin 0, b⟩ delta =
    (scalarLog rt ⟨p, .fin (zeroUlp p), false⟩).map (fun logValue =>
      relu (logValue.neg.div (delta.asFloat p)))

theorem zero_ratio_holds : zero_ratio := by
  intro rt p a b delta
  refine ⟨zero_log_input p a b, ?_⟩
  unfold zeroCenteredScore
  rw [zero_log_input]
  let input : ScoreFloat := ⟨p, .fin (zeroUlp p), false⟩
  have hc : ∀ v, scalarLog rt input = .ok v → v.precision = p := by
    intro v hv
    simp only [scalarLog, input] at hv
    split at hv
    · cases hv
    · split at hv
      · cases hv; rfl
      · split at hv <;> cases hv <;> rfl
  change (do let v ← scalarLog rt input; pure (relu (v.neg.div (delta.asFloat v.precision)))) = _
  cases hs : scalarLog rt input with
  | error e => rfl
  | ok v => simp [hc v hs, bind, Except.bind, pure, Except.pure, Except.map]

def zero_ratio_no_improvement : Prop := ∀ (rt : ScalarRuntime) (delta : Int64),
  0 < delta →
    (zeroCenteredScore rt ⟨rt.precision, .fin 0, false⟩ ⟨rt.precision, .fin 0, false⟩ (.integer delta)).map
      ScoreFloat.value = .ok (.fin 0)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 2048 in
theorem zero_ratio_no_improvement_refuted : ¬ zero_ratio_no_improvement := by
  intro hp
  let rt : ScalarRuntime := ⟨fun _ _ => (-6548164122079683 : Rat) / 8796093022208, .float64⟩
  have hn : (zeroCenteredScore rt ⟨.float64, .fin 0, false⟩ ⟨.float64, .fin 0, false⟩ (.integer 1)).map
      ScoreFloat.value ≠ .ok (.fin 0) := by decide +kernel
  exact hn (hp rt 1 (by decide))

def direct_formula : Prop := ∀ (cur last : ScoreFloat) (delta : ScoreDelta),
  directScore cur last delta =
    let diff := cur.add last.neg
    relu (diff.neg.div (delta.asFloat diff.precision))

private def half (p : LossPrecision) : ScoreFloat := ⟨p, .fin (1 / 2), false⟩

private def halfUlp : LossPrecision → Rat
  | .float16 => 1 / (2 : Rat)^11
  | .float32 => 1 / (2 : Rat)^24
  | .float64 => 1 / (2 : Rat)^53

/-- The first mask must precede epsilon, and the second must keep the sign of zero. -/
def logarithmic_formula : Prop := ∀ (rt : ScalarRuntime) (p : LossPrecision),
  scoreLogInput (half p) ⟨p, .fin 0, true⟩ = ⟨p, .fin (halfUlp p), false⟩ ∧
  scoreLogInput (half p) ⟨p, .fin 0, false⟩ = ⟨p, .posInf, false⟩ ∧
  zeroCenteredScore rt (half p) ⟨p, .fin 0, false⟩ (.integer 1) = .ok ⟨p, .fin 0, true⟩ ∧
  zeroCenteredScore rt ⟨.float16, .fin (2047 / 2048), false⟩ ⟨.float16, .fin 1, false⟩
      (.float ⟨p, .fin 1, false⟩) = .ok ⟨p, .fin 0, true⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 2048 in
theorem logarithmic_formula_holds : logarithmic_formula := by
  intro rt p
  have hn : scoreLogInput (half p) ⟨p, .fin 0, true⟩ = ⟨p, .fin (halfUlp p), false⟩ := by
    cases p <;> decide +kernel
  have hp : scoreLogInput (half p) ⟨p, .fin 0, false⟩ = ⟨p, .posInf, false⟩ := by
    cases p <;> decide +kernel
  have he : scoreLogInput ⟨.float16, .fin (2047 / 2048), false⟩ ⟨.float16, .fin 1, false⟩ =
      ⟨.float16, .fin 1, false⟩ := by decide +kernel
  refine ⟨hn, hp, ?_, ?_⟩
  · unfold zeroCenteredScore
    rw [hp, show scalarLog rt ⟨p, .posInf, false⟩ = .ok ⟨p, .posInf, false⟩ from rfl]
    cases p <;> decide +kernel
  · unfold zeroCenteredScore
    rw [he, show scalarLog rt ⟨.float16, .fin 1, false⟩ = .ok ⟨.float16, .fin 0, false⟩ from rfl]
    cases p <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
example (rt : ScalarRuntime) :
    zeroCenteredScore rt ⟨.float16, .fin 1, false⟩ ⟨.float16, .fin (-1), false⟩
      (.float ⟨.float32, .fin 0, true⟩) =
    (scalarLog rt ⟨.float16, .fin (1 / 1024), false⟩).map (fun x =>
      relu (x.neg.div ⟨.float32, .fin 0, true⟩)) := by
  have h : scoreLogInput ⟨.float16, .fin 1, false⟩ ⟨.float16, .fin (-1), false⟩ =
      ⟨.float16, .fin (1 / 1024), false⟩ := by decide +kernel
  unfold zeroCenteredScore
  rw [h]
  cases scalarLog rt ⟨.float16, .fin (1 / 1024), false⟩ <;> rfl

private theorem round_good (x : ScoreFloat) (p : LossPrecision)
    (h : x.value = .posInf ∨ ∃ q : Rat, x.value = .fin q ∧ 0 ≤ q) :
    (x.round p).value ≠ .nan ∧ (x.round p).value ≠ .negInf := by
  rcases h with hp | ⟨q, hq, hle⟩
  · simp [ScoreFloat.round, hp, LossPrecision.round]
  · have hn : ¬ q < 0 := Rat.not_lt.mpr hle
    by_cases hz : q = 0
    · simp [ScoreFloat.round, hq, LossPrecision.round, hz]
    · simp only [ScoreFloat.round, hq, LossPrecision.round, if_neg hz, if_neg hn]
      split <;> simp

private theorem relu_nonnegative (x : ScoreFloat) :
    (relu x).value = .posInf ∨ ∃ q : Rat, (relu x).value = .fin q ∧ 0 ≤ q := by
  unfold relu
  split
  · rename_i h
    cases hx : x.value with
    | fin q =>
      right
      refine ⟨q, rfl, Rat.le_of_lt ?_⟩
      simpa [greater, hx] using h
    | nan | negInf => simp_all [greater]
    | posInf => exact Or.inl rfl
  · exact Or.inr ⟨0, rfl, Rat.le_refl⟩

private theorem rowScore_good (rt : ScalarRuntime) (scale : LossScale) (pair : ScoreFloat × Int)
    (prev : Option (ScoreFloat × Int)) (out : ScoreFloat)
    (h : rowScore rt scale pair.1 pair.2 prev = .ok out) :
    out.value ≠ .nan ∧ out.value ≠ .negInf := by
  cases prev with
  | none => cases h; simp
  | some p =>
    obtain ⟨last, lastC⟩ := p
    simp only [rowScore] at h
    split at h
    · cases h; exact round_good _ _ (relu_nonnegative _)
    · unfold zeroCenteredScore at h
      cases hl : scalarLog rt (scoreLogInput pair.1 last) with
      | error e => simp [hl, bind, Except.bind] at h
      | ok v =>
        simp [hl, bind, Except.bind, pure, Except.pure] at h
        subst out
        exact round_good _ _ (relu_nonnegative _)

theorem typedScoreRows_good (rt : ScalarRuntime) (scale : LossScale) (xs : List (ScoreFloat × Int))
    (prev : Option (ScoreFloat × Int)) (out : List ScoreFloat)
    (h : typedScoreRows rt scale xs prev = .ok out) :
    ∀ s ∈ out, s.value ≠ .nan ∧ s.value ≠ .negInf := by
  induction xs generalizing prev out with
  | nil => cases h; simp
  | cons x xs ih =>
    simp only [typedScoreRows] at h
    cases hx : rowScore rt scale x.1 x.2 prev with
    | error e => simp [hx, bind, Except.bind] at h
    | ok value =>
      cases ht : typedScoreRows rt scale xs (some x) with
      | error e => simp [hx, ht, bind, Except.bind] at h
      | ok tail =>
        simp [hx, ht, bind, Except.bind, pure, Except.pure] at h
        subst out
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact rowScore_good rt scale x prev _ hx
        · exact ih _ _ ht _ hs

def first_score_zero : Prop := ∀ (rt : ScalarRuntime) (scale : LossScale)
    (pair : ScoreFloat × Int) (tail : List (ScoreFloat × Int)) (out : List ScoreFloat),
  typedScoreRows rt scale (pair :: tail) none = .ok out → out.head? = some ⟨rt.precision, .fin 0, false⟩

theorem first_score_zero_holds : first_score_zero := by
  intro rt scale pair tail out h
  cases ht : typedScoreRows rt scale tail (some pair) <;>
    simp [typedScoreRows, rowScore, ht, bind, Except.bind, pure, Except.pure] at h
  subst out
  rfl

private theorem find_negative (before : List Member) (m : Member) (after : List Member)
    (hbefore : ∀ x ∈ before, less x.loss (.fin 0) = false) (hm : less m.loss (.fin 0) = true) :
    firstNegative .log (before ++ m :: after) = some m := by
  exact List.find?_eq_some_iff_append.mpr ⟨hm, before, after, rfl,
    fun x hx => by simp [hbefore x hx]⟩

def log_negative_rejected : Prop := ∀ (W : Type) (rt : ScalarRuntime) (s : FormatServices W)
    (h : Hof) (fresh next : Nat) (world copiedWorld : W) (visits : List FrontierEvent)
    (before after : List Member) (bad : Member),
  runFrontier s.copy h fresh world = (.ok (before ++ bad :: after), next, copiedWorld, visits) →
  (∀ e stopped, s.scaleAt .log copiedWorld = (.error e, stopped) →
    runFormatHof rt .log s h fresh world =
      (.error (.failure e), next, stopped, .hall :: visits.map FormatEvent.frontier)) ∧
  (∀ live, s.scaleAt .log copiedWorld = (.ok .log, live) →
    (∀ m ∈ before, less m.loss (.fin 0) = false) → less bad.loss (.fin 0) = true →
    runFormatHof rt .log s h fresh world =
      (.error (.negativeLoss (bad.scoreLoss rt.precision) negativeLossMessage), next, live,
        .hall :: visits.map FormatEvent.frontier))

theorem log_negative_rejected_holds : log_negative_rejected := by
  intro W rt s h fresh next world copiedWorld visits before after bad hf
  exact ⟨fun e stopped hr => by simp [runFormatHof, hf, hr],
    fun live hr hb hn => by simp [runFormatHof, hf, hr, find_negative before bad after hb hn]⟩

example (rt : ScalarRuntime) :
    let m := specimen (.fin 0) (.fin (-1)) (-1)
    let s : FormatServices Nat := { copy := stockFrontierCopy, compute := fun _ n => (.ok 1, n + 1) }
    runFormatHof rt .log s ⟨[⟨m, true⟩]⟩ 2 0 =
      (.error (.negativeLoss ⟨rt.precision, .fin (-1), false⟩ negativeLossMessage), 4, 0,
        [.hall, .frontier (.visit 0), .frontier (.copy 0)]) := rfl

private def singletonResolution {W : Type} (s : FormatServices W) (m : Member) (world : W) :
    Jl Int × W × List FormatEvent :=
  if m.complexity = -1 then ((s.compute m world).1, (s.compute m world).2,
    [FormatEvent.compute m.treeId]) else (.ok m.complexity, world, [])

def linear_singleton : Prop := ∀ (W : Type) (rt : ScalarRuntime) (s : FormatServices W)
    (m : Member) (fresh : Nat) (world : W),
  s.readScale = none →
  let result := runFormatHof rt .linear s ⟨[⟨m, true⟩]⟩ fresh world
  (m.loss = .nan → result =
    (.ok ⟨[], [], [], [], []⟩, fresh, world, [.hall, .frontier (.visit 0), .scores])) ∧
  (m.loss ≠ .nan →
    let visits := [FormatEvent.hall, .frontier (.visit 0), .frontier (.copy m.objectId)]
    (∀ e next live, s.copy m fresh world = (.error e, next, live) →
      result = (.error (.failure e), next, live, visits)) ∧
    (∀ copied next live, s.copy m fresh world = (.ok copied, next, live) →
      let (resolved, world', calls) := singletonResolution s copied live
      let events := visits ++ (.resolve copied.objectId :: calls)
      match resolved with
      | .error e => result = (.error (.failure e), next, world', events)
      | .ok c => result =
          (.ok ⟨[copied.tree], [⟨rt.precision, .fin 0, false⟩], [copied.scoreLoss rt.precision], [c],
            [copied.treeId]⟩,
            next, world', events ++ [.scores])))

theorem linear_singleton_holds : linear_singleton := by
  intro W rt s m fresh world hr
  refine ⟨?_, ?_⟩
  · intro hn
    simp [runFormatHof, runFrontier, scanFrontier, hn, FormatServices.scaleAt, hr,
      firstNegative, resolveRows, typedScoreRows]
  intro hn
  constructor
  · intro e next live he
    simp [runFormatHof, runFrontier, scanFrontier, dominatesEarlier, hn, he]
  · intro copied next live hc
    by_cases hm : copied.complexity = -1
    · cases hs : s.compute copied live with
      | mk answer world' =>
        cases answer <;>
          simp [singletonResolution, hm, runFormatHof, runFrontier, scanFrontier,
            dominatesEarlier, hn, hc, FormatServices.scaleAt, hr, firstNegative, resolveRows, hs, typedScoreRows,
            rowScore, Except.map, pure, Except.pure, bind, Except.bind]
    · simp [singletonResolution, hm, runFormatHof, runFrontier, scanFrontier,
        dominatesEarlier, hn, hc, FormatServices.scaleAt, hr, firstNegative, resolveRows, typedScoreRows,
        rowScore, Except.map, pure, Except.pure, bind, Except.bind]

example : (specimen (.fin 0) (.fin (-1))).loss ≠ .nan := by decide

private theorem resolveRows_length {W : Type} (compute : Member → W → Jl Int × W)
    (ms : List Member) (world : W) (sizes : List Int)
    (h : (resolveRows compute ms world).1 = .ok sizes) : sizes.length = ms.length := by
  induction ms generalizing world sizes with
  | nil => cases h; rfl
  | cons m ms ih =>
    by_cases hm : m.complexity = -1
    · cases hc : compute m world with
      | mk ans world' =>
        cases ans with
        | error e => simp [resolveRows, hm, hc] at h
        | ok c =>
          cases ht : (resolveRows compute ms world').1 with
          | error e => simp [resolveRows, hm, hc, ht, Except.map] at h
          | ok tail =>
            have hlen := ih _ _ ht
            simp [resolveRows, hm, hc, ht, Except.map] at h
            subst sizes
            simp [hlen]
    · cases ht : (resolveRows compute ms world).1 with
      | error e => simp [resolveRows, hm, ht, Except.map] at h
      | ok tail =>
        have hlen := ih _ _ ht
        simp [resolveRows, hm, ht, Except.map] at h
        subst sizes
        simp [hlen]

/-- Indexed description, with the predecessor at index `i` used for row `i+1`. -/
private def ScoresAligned (rt : ScalarRuntime) (scale : LossScale) (xs : List (ScoreFloat × Int))
    (previous : Option (ScoreFloat × Int)) (out : List ScoreFloat) : Prop :=
  out.length = xs.length ∧ ∀ (i : Nat) (pair : ScoreFloat × Int),
    xs[i]? = some pair →
    (rowScore rt scale pair.1 pair.2 (match i with | 0 => previous | j + 1 => xs[j]?)).map
      some = .ok out[i]?

private theorem typedScoreRows_aligned (rt : ScalarRuntime) (scale : LossScale)
    (xs : List (ScoreFloat × Int)) (previous : Option (ScoreFloat × Int)) (out : List ScoreFloat)
    (h : typedScoreRows rt scale xs previous = .ok out) : ScoresAligned rt scale xs previous out := by
  induction xs generalizing previous out with
  | nil => cases h; simp [ScoresAligned]
  | cons pair xs ih =>
    simp only [typedScoreRows] at h
    cases hs : rowScore rt scale pair.1 pair.2 previous with
    | error e => simp [hs, bind, Except.bind] at h
    | ok score =>
      cases ht : typedScoreRows rt scale xs (some pair) with
      | error e => simp [hs, ht, bind, Except.bind] at h
      | ok tail =>
        simp [hs, ht, bind, Except.bind, pure, Except.pure] at h
        subst out
        obtain ⟨hlen, halign⟩ := ih _ _ ht
        refine ⟨by simp [hlen], ?_⟩
        intro i x hi
        cases i with
        | zero =>
          have he : pair = x := by simpa using hi
          subst x
          simp [hs, Except.map]
        | succ j =>
          have hj : xs[j]? = some x := by simpa using hi
          cases j <;> simpa using halign _ x hj

def format_lengths : Prop := ∀ (W : Type) (rt : ScalarRuntime) (scale : LossScale)
    (s : FormatServices W) (h : Hof) (fresh : Nat) (world : W) (out : TypedFormatted),
  s.readScale = none →
  (runFormatHof rt scale s h fresh world).1 = .ok out →
  ∃ front next copiedWorld visits,
    runFrontier s.copy h fresh world = (.ok front, next, copiedWorld, visits) ∧
    out.trees = front.map Member.tree ∧ out.losses = front.map (fun m => m.scoreLoss rt.precision) ∧
    out.treeIds = front.map Member.treeId ∧
    out.complexities.length = front.length ∧
    (resolveRows s.compute front copiedWorld).1 = .ok out.complexities ∧
    ScoresAligned rt scale (out.losses.zip out.complexities) none out.scores

theorem format_lengths_holds : format_lengths := by
  intro W rt scale s h fresh world out hr hh
  simp only [runFormatHof, FormatServices.scaleAt, hr] at hh
  cases hf : runFrontier s.copy h fresh world with
  | mk front state =>
    obtain ⟨next, copiedWorld, visits⟩ := state
    cases front with
    | error e => simp [hf] at hh
    | ok ms =>
      cases hn : firstNegative scale ms with
      | some bad => simp [hf, hn] at hh
      | none =>
        cases hc : resolveRows s.compute ms copiedWorld with
        | mk result state' =>
          obtain ⟨world', events⟩ := state'
          cases result with
          | error e => simp [hf, hn, hc] at hh
          | ok sizes =>
            cases hs : typedScoreRows rt scale ((ms.map fun m => m.scoreLoss rt.precision).zip sizes) none with
            | error e => simp [hf, hn, hc, hs] at hh
            | ok values =>
              simp [hf, hn, hc, hs] at hh
              subst out
              have hc' : (resolveRows s.compute ms copiedWorld).1 = .ok sizes := by simp [hc]
              exact ⟨ms, next, copiedWorld, visits, rfl, rfl, rfl, rfl, resolveRows_length _ _ _ _ hc', hc',
                typedScoreRows_aligned _ _ _ _ _ hs⟩

example (rt : ScalarRuntime) (s : FormatServices Unit) :
    s.readScale = none → (runFormatHof rt .linear s ⟨[]⟩ 0 ()).1 = .ok ⟨[], [], [], [], []⟩ := by
  intro hr
  simp [runFormatHof, runFrontier, scanFrontier, FormatServices.scaleAt, hr,
    firstNegative, resolveRows, typedScoreRows]

private theorem collectFormats_stop {E S A : Type} (format : Hof → S → Except E A × S)
    (before : List Hof) (st st' : S) (done : List A)
    (h : collectFormats format before st = (.ok done, st'))
    (failed : Hof) (after : List Hof) (e : E) (st'' : S)
    (he : format failed st' = (.error e, st'')) :
    collectFormats format (before ++ failed :: after) st = (.error e, st'') := by
  induction before generalizing st done with
  | nil =>
    simp [collectFormats] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [collectFormats, he]
  | cons lead rest ih =>
    cases hl : format lead st with
    | mk outcome state =>
      cases outcome with
      | error err => simp [collectFormats, hl] at h
      | ok x =>
        cases hr : collectFormats format rest state with
        | mk outputs state' =>
          cases outputs with
          | error err => simp [collectFormats, hl, hr, Except.map] at h
          | ok ys =>
            simp [collectFormats, hl, hr, Except.map] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [collectFormats, hl, ih _ _ hr, Except.map]

def format_many_error : Prop := ∀ (W : Type) (rt : ScalarRuntime) (scale : LossScale)
    (s : FormatServices W) (before after : List Hof) (bad : Hof) (fresh next final : Nat)
    (world world' world'' : W) (done : List TypedFormatted) (earlier events : List FormatEvent)
    (e : FormatError),
  runFormatMany rt scale s before fresh world = (.ok done, next, world', earlier) →
  runFormatHof rt scale s bad next world' = (.error e, final, world'', events) →
  runFormatMany rt scale s (before ++ bad :: after) fresh world =
    (.error e, final, world'', earlier ++ events)

theorem format_many_error_holds : format_many_error := by
  intro W rt scale s before after bad fresh next final world world' world'' done earlier events e hp he
  exact collectFormats_stop (formatStep rt scale s) before (fresh, world, [])
    (next, world', earlier) done hp bad after e (final, world'', earlier ++ events)
    (by simp [formatStep, he])

example (rt : ScalarRuntime) (tail : List Hof) :
    let m := specimen (.fin 0) (.fin (-1)) (-1)
    let h : Hof := ⟨[⟨m, true⟩]⟩
    let e := JlError.userError "custom complexity failed"
    let s : FormatServices Nat := {
      copy := stockFrontierCopy
      compute := fun _ n => if n = 0 then (.ok 7, 1) else (.error e, n + 1) }
    (runFormatMany rt .linear s ([h, h] ++ tail) 2 0).2 =
      (6, 2, [.hall, .frontier (.visit 0), .frontier (.copy 0), .resolve 2, .compute 3, .scores,
        .hall, .frontier (.visit 0), .frontier (.copy 0), .resolve 4, .compute 5]) := rfl

end SymReg.HofMig
