import SymReg.Plugins.Frequencies
import SymReg.Population.Tournament
import SymReg.Loss.RoundOrder

/-!
`src/plugins/AdaptiveParsimony.jl:129-132,166-202,223-233`.
Native Float32 and Float64 loss types use their own conversion and multiplication.
The installed exponential's boundary branches are modeled separately from its finite kernel.
-/
namespace SymReg.Plugins
open DynExpr

attribute [local semireducible] Rat.add Rat.mul Rat.inv

@[simp] theorem jfFiniteAdd (a b : Rat) : JF.fin a + JF.fin b = .fin (a + b) := rfl
@[simp] theorem jfFiniteSub (a b : Rat) : JF.fin a - JF.fin b = .fin (a - b) := by
  change JF.fin (a + -b) = .fin (a - b)
  rw [Rat.sub_eq_add_neg]
@[simp] theorem jfFiniteMul (a b : Rat) : JF.fin a * JF.fin b = .fin (a * b) := rfl
@[simp] theorem jfFiniteNeg (a : Rat) : -(JF.fin a) = .fin (-a) := rfl
@[simp] theorem jfFiniteDiv (a b : Rat) (hb : b ≠ 0) :
    JF.fin a / JF.fin b = .fin (a / b) := by
  change (if b = 0 then _ else _) = _
  simp [hb]

/-- Finite `exp` and the conversion/multiplication in the member's loss type L,
`src/plugins/AdaptiveParsimony.jl:175,179`. Services include IEEE rounding/overflow. -/
structure FloatServices where
  cast : JF → JF := id
  mul : JF → JF → JF := JF.mul
  expFinite : Rat → JF

/-- Julia exp's exact zero and nonfinite cases. -/
def exponential (rt : FloatServices) : JF → JF
  | .nan => .nan
  | .posInf => .posInf
  | .negInf => .fin 0
  | .fin x => if x = 0 then .fin 1 else rt.expFinite x

/-- `src/plugins/AdaptiveParsimony.jl:129-132`. -/
structure ParsimonyConfig where
  tournament : Bool := true
  mutationAcceptance : Bool := true
  deriving DecidableEq, Repr

/-- Legacy factory `src/plugins/AdaptiveParsimony.jl:225-232`. -/
def defaultParsimony (frequency tournament : Bool) : Option ParsimonyConfig :=
  if frequency || tournament then some ⟨tournament, frequency⟩ else none

inductive ParsimonyCall where
  | complexity | parentComplexity | treeComplexity
  | readBin (size : Int)
  | frequencyCast | scalingCast | multiply | exp | divide | one | zero
  deriving DecidableEq

def inParsimonyRange (maxsize size : Int) : Prop := 0 < size ∧ size ≤ maxsize

instance (maxsize size : Int) : Decidable (inParsimonyRange maxsize size) :=
  inferInstanceAs (Decidable (_ ∧ _))

def frequencyAt (h : FrequencyHeap) (s : Statistics) (size : Int) : Jl JF := do
  let xs ← h.read s.normalized
  Loss.at1 xs size.toNat

structure TournamentScalars (L : Type) where
  one : L
  zero : L
  cast : JF → Jl L
  mul : L → L → Jl L
  exp : L → Jl L

-- Source: src/plugins/AdaptiveParsimony.jl:166-180
-- function tournament_cost_multiplier(
--     s::AdaptiveParsimonyState,
--     p::AdaptiveParsimonyPlugin,
--     member::AbstractPopMember{T,L,N},
--     options::AbstractOptions,
-- ) where {T,L,N}
--     p.tournament || return one(L)
--     sz = compute_complexity(member, options)
--     frequency = if (0 < sz <= options.maxsize)
--         L(s.rss.normalized_frequencies[sz])
--     else
--         zero(L)
--     end
--     return exp(L(options.adaptive_parsimony_scaling) * frequency)
-- end
def tournamentMultiplier {L : Type} (rt : TournamentScalars L) (h : FrequencyHeap)
    (s : Statistics) (p : ParsimonyConfig) (scaling : JF) (maxsize : Int)
    (complexity : Jl Int) : Jl L × List ParsimonyCall :=
  if !p.tournament then (.ok rt.one, [.one]) else
  match complexity with
  | .error e => (.error e, [.complexity])
  | .ok sz =>
    let (f, calls) :=
      if inParsimonyRange maxsize sz then
        match frequencyAt h s sz with
        | .error e => (.error e, [.complexity, .readBin sz])
        | .ok x => (rt.cast x, [.complexity, .readBin sz, .frequencyCast])
      else (.ok rt.zero, [.complexity, .zero])
    match f with
    | .error e => (.error e, calls)
    | .ok v =>
      match rt.cast scaling with
      | .error e => (.error e, calls ++ [.scalingCast])
      | .ok a =>
        match rt.mul a v with
        | .error e => (.error e, calls ++ [.scalingCast, .multiply])
        | .ok e => (rt.exp e, calls ++ [.scalingCast, .multiply, .exp])

def acceptanceFallback : JF := round64 (.fin (1 / 1000000))

private def acceptanceBin (h : FrequencyHeap) (s : Statistics) (maxsize size : Int) :
    Jl JF × List ParsimonyCall :=
  if inParsimonyRange maxsize size then (frequencyAt h s size, [.readBin size])
  else (.ok acceptanceFallback, [])

-- Source: src/plugins/AdaptiveParsimony.jl:182-202
-- function mutation_acceptance_multiplier(
--     s::AdaptiveParsimonyState,
--     p::AdaptiveParsimonyPlugin,
--     ctx::MutationAcceptanceContext,
--     options::AbstractOptions,
-- )
--     p.mutation_acceptance || return 1.0
--     old_size = compute_complexity(ctx.parent_member, options)
--     new_size = compute_complexity(ctx.new_tree, options)
--     old_frequency = if (0 < old_size <= options.maxsize)
--         Float64(s.rss.normalized_frequencies[old_size])
--     else
--         1e-6
--     end
--     new_frequency = if (0 < new_size <= options.maxsize)
--         Float64(s.rss.normalized_frequencies[new_size])
--     else
--         1e-6
--     end
--     return old_frequency / new_frequency
-- end
def parsimonyAcceptance (h : FrequencyHeap) (s : Statistics) (p : ParsimonyConfig)
    (maxsize : Int) (oldSize newSize : Jl Int) : Jl JF × List ParsimonyCall :=
  if !p.mutationAcceptance then (.ok (.fin 1), []) else
  match oldSize with
  | .error e => (.error e, [.parentComplexity])
  | .ok old =>
    match newSize with
    | .error e => (.error e, [.parentComplexity, .treeComplexity])
    | .ok new =>
      let (a, callsA) := acceptanceBin h s maxsize old
      let calls := [.parentComplexity, .treeComplexity] ++ callsA
      match a with
      | .error e => (.error e, calls)
      | .ok x =>
        let (b, callsB) := acceptanceBin h s maxsize new
        match b with
        | .error e => (.error e, calls ++ callsB)
        | .ok y => (.ok (fdiv64 x y), calls ++ callsB ++ [.divide])

def parsimony_disabled : Prop := ∀ (L : Type) (rt : TournamentScalars L) h s scaling maxsize
    other oldSize newSize,
  tournamentMultiplier rt h s ⟨false, other⟩ scaling maxsize oldSize = (.ok rt.one, [.one]) ∧
  parsimonyAcceptance h s ⟨other, false⟩ maxsize oldSize newSize = (.ok (.fin 1), [])

theorem parsimony_disabled_holds : parsimony_disabled := by
  intro L rt h s scaling maxsize other oldSize newSize
  exact ⟨rfl, rfl⟩
def parsimony_factory : Prop := ∀ frequency tournament,
  (defaultParsimony frequency tournament = none ↔ frequency = false ∧ tournament = false) ∧
  (frequency = true ∨ tournament = true →
    defaultParsimony frequency tournament = some ⟨tournament, frequency⟩)

theorem parsimony_factory_holds : parsimony_factory := by
  intro frequency tournament
  cases frequency <;> cases tournament <;> decide

def out_of_range_multiplier : Prop := ∀ (L : Type) (rt : TournamentScalars L)
    h s scaling maxsize size other, size ≤ 0 ∨ maxsize < size →
  let (r, calls) := tournamentMultiplier rt h s ⟨true, other⟩ scaling maxsize (.ok size)
  ((.readBin size : ParsimonyCall) ∉ calls) ∧ .zero ∈ calls ∧
  r = ((rt.cast scaling).bind fun a => (rt.mul a rt.zero).bind rt.exp)

theorem out_of_range_multiplier_holds : out_of_range_multiplier := by
  intro L rt h s scaling maxsize size other hs
  have hRange : ¬ inParsimonyRange maxsize size := by
    unfold inParsimonyRange
    omega
  cases hc : rt.cast scaling with
  | error e => simp [tournamentMultiplier, hRange, hc, Except.bind]
  | ok a =>
    cases hm : rt.mul a rt.zero <;> simp [tournamentMultiplier, hRange, hc, hm, Except.bind]

def acceptance_same_size : Prop := ∀ h s maxsize size other,
  let r := (parsimonyAcceptance h s ⟨other, true⟩ maxsize (.ok size) (.ok size)).1
  if inParsimonyRange maxsize size then
    match frequencyAt h s size with
    | .error e => r = .error e
    | .ok (.fin q) => r = .ok (if q = 0 then .nan else .fin 1)
    | .ok _ => r = .ok .nan
  else r = .ok (.fin 1)

theorem acceptance_same_size_holds : acceptance_same_size := by
  intro h s maxsize size other
  by_cases hs : inParsimonyRange maxsize size
  · simp only [parsimonyAcceptance, acceptanceBin, hs, if_true, Bool.not_true,
      Bool.false_eq_true, if_false]
    cases frequencyAt h s size with
    | error e => rfl
    | ok x =>
      cases x with
      | fin q =>
        by_cases hz : q = 0
        · simp [hz, fdiv64, JF.div, HDiv.hDiv, Div.div, round64, Loss.LossPrecision.round]
        · change Except.ok (fdiv64 (.fin q) (.fin q)) =
            Except.ok (if q = 0 then JF.nan else .fin 1)
          rw [if_neg hz]
          unfold fdiv64
          rw [jfFiniteDiv _ _ hz, ratDivSelf _ hz]
          decide +kernel
      | nan | posInf | negInf => rfl
  · simp only [parsimonyAcceptance, acceptanceBin, hs, if_false, Bool.not_true,
      Bool.false_eq_true]
    decide +kernel

def acceptance_rarer_size : Prop := ∀ h s maxsize oldSize newSize other x y,
  (acceptanceBin h s maxsize oldSize).1 = .ok (.fin x) →
  (acceptanceBin h s maxsize newSize).1 = .ok (.fin y) →
  0 < y → y ≤ x →
  let r := (parsimonyAcceptance h s ⟨other, true⟩ maxsize (.ok oldSize) (.ok newSize)).1
  r = .ok (round64 (.fin (x / y))) ∧
  (r = .ok .posInf ∨ ∃ q : Rat, r = .ok (.fin q) ∧ 1 ≤ q)

theorem acceptance_rarer_size_holds : acceptance_rarer_size := by
  intro h s maxsize oldSize newSize other x y hx hy hp hle
  cases ha : acceptanceBin h s maxsize oldSize with
  | mk av callsA =>
    cases hb : acceptanceBin h s maxsize newSize with
    | mk bv callsB =>
      rw [ha] at hx
      rw [hb] at hy
      cases hx
      cases hy
      simp only [parsimonyAcceptance, ha, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        fdiv64, jfFiniteDiv _ _ (Rat.ne_of_gt hp)]
      refine ⟨trivial, ?_⟩
      have hdiv := ratDivMono hp hle
      rw [ratDivSelf _ (Rat.ne_of_gt hp)] at hdiv
      rcases Loss.LossPrecision.float64.round_ge_nonneg (by decide : (0 : Rat) ≤ 1)
          hdiv (by decide +kernel : round64 (.fin 1) = .fin 1) with hr | ⟨q, hq, hle⟩
      · exact Or.inl (congrArg Except.ok hr)
      · exact Or.inr ⟨q, congrArg Except.ok hq, hle⟩

example : (0 : Rat) < 1 ∧ (1 : Rat) ≤ 2 := by decide

inductive TournamentPrecision where
  | float32 | float64
  deriving DecidableEq

def TournamentPrecision.precision : TournamentPrecision → Loss.LossPrecision
  | .float32 => .float32
  | .float64 => .float64

-- Source: Julia base/special/exp.jl, MAX_EXP and exp_impl for Float32 and Float64.
def TournamentPrecision.overflows (p : TournamentPrecision) (x : Rat) : Bool :=
  match p with
  | .float32 => decide (11629080 / 131072 < x)
  | .float64 => decide (6243314768165360 / 8796093022208 ≤ x)

def tournamentExp (p : TournamentPrecision) (kernel : TournamentPrecision → Rat → JF) : JF → JF
  | .nan => .nan
  | .negInf => .fin 0
  | .posInf => .posInf
  | .fin x =>
    if p.overflows x then .posInf
    else if x = 0 then .fin 1
    else kernel p x

def ieeeTournament (p : TournamentPrecision) (kernel : TournamentPrecision → Rat → JF) :
    TournamentScalars JF where
  one := .fin 1
  zero := .fin 0
  cast x := .ok (p.precision.round x)
  mul a b := .ok (p.precision.round (a * b))
  exp x := .ok (tournamentExp p kernel x)

-- Source: src/Options.jl:856,1334
def parsimonyScaling (modern : Bool) (given : Option JF) : JF :=
  given.getD (if modern then .fin 1040 else .fin 20)

def scaling_thresholds : Prop := ∀ p kernel h s maxsize size other x,
  inParsimonyRange maxsize size → frequencyAt h s size = .ok x →
  let round := p.precision.round
  let exponent := round (JF.fin 1040 * round x)
  let r := (tournamentMultiplier (ieeeTournament p kernel) h s ⟨true, other⟩
    (parsimonyScaling true none) maxsize (.ok size)).1
  (exponent = .posInf → r = .ok .posInf) ∧
  (∀ q, exponent = .fin q →
    (match p with
     | .float32 => (11629080 / 131072 : Rat) < q
     | .float64 => (6243314768165360 / 8796093022208 : Rat) ≤ q) →
    r = .ok .posInf)

theorem scaling_thresholds_holds : scaling_thresholds := by
  intro p kernel h s maxsize size other x hs hx
  have hc : p.precision.round (.fin 1040) = .fin 1040 := by cases p <;> decide +kernel
  simp only [tournamentMultiplier, Bool.not_true, Bool.false_eq_true, if_false, hs, if_true,
    hx, ieeeTournament, parsimonyScaling, Option.getD, hc, Prod.fst]
  constructor
  · intro he
    rw [he]
    rfl
  · intro q he ho
    rw [he]
    cases p <;> simp [tournamentExp, TournamentPrecision.overflows, ho]

def tournament_finite : Prop := ∀ p kernel n h s window size,
  0 < n → inParsimonyRange n size →
  initStatistics Heap.empty n window = .ok (s, h) →
  ∃ value, (tournamentMultiplier (ieeeTournament p kernel) h s ⟨true, true⟩
    (parsimonyScaling true none) n (.ok size)).1 = .ok value ∧ value.valid = true

set_option maxRecDepth 4096 in
theorem tournament_finite_refuted : ¬ tournament_finite := by
  intro claim
  let h₁ := (Heap.empty.alloc (List.replicate 10 (JF.fin 1))).2
  let f := fdiv64 (.fin 1) (fsum64 (List.replicate 10 (.fin 1)))
  let h := (h₁.alloc (List.replicate 10 f)).2
  let s : Statistics := ⟨100000, 0, 1⟩
  let kernel : TournamentPrecision → Rat → JF := fun _ _ => .fin 1
  have hi : initStatistics Heap.empty 10 100000 = .ok (s, h) := rfl
  have ht : (tournamentMultiplier (ieeeTournament .float32 kernel) h s ⟨true, true⟩
      (parsimonyScaling true none) 10 (.ok 1)).1 = .ok .posInf := by decide +kernel
  obtain ⟨value, hv, hf⟩ := claim .float32 kernel 10 h s 100000 1 (by decide) (by decide) hi
  rw [ht] at hv
  cases hv
  contradiction

def overflow_costs : Prop := ∀ p kernel h s scaling maxsize size other before after cost converted,
  (tournamentMultiplier (ieeeTournament p kernel) h s ⟨true, other⟩
    scaling maxsize (.ok size)).1 = .ok .posInf →
  p.precision.round cost = .fin converted → 0 < converted →
  let neutral := fun (_ : Unit) (w : Unit) => (.ok (JF.fin 1), w)
  let parsimony := fun (_ : Unit) (w : Unit) =>
    ((tournamentMultiplier (ieeeTournament p kernel) h s ⟨true, other⟩
      scaling maxsize (.ok size)).1, w)
  let hooks := List.replicate before neutral ++ parsimony :: List.replicate after neutral
  (Population.adjusted p.precision (fun _ _ => cost) hooks () ()).1 = .ok .posInf ∧
  (Population.adjusted p.precision (fun _ _ => .fin 0) hooks () ()).1 = .ok .nan

theorem overflow_costs_holds : overflow_costs := by
  intro p kernel h s scaling maxsize size other before after cost converted hm hc hp
  dsimp only
  simp only [hm]
  rw [Population.adjusted_one_infinite, Population.adjusted_one_infinite, hc]
  have hn : ¬ converted.num < 0 := by
    have := Rat.num_nonneg.mpr (Rat.le_of_lt hp)
    omega
  have hz : converted ≠ 0 := Rat.ne_of_gt hp
  have hm : JF.fin converted * .posInf = .posInf := by
    change (if converted = 0 then JF.nan else if (decide (converted.num < 0) != false) then
      .negInf else .posInf) = _
    simp [hn, hz]
  rw [hm]
  exact ⟨rfl, rfl⟩

example : (0 : Rat) < 1 := by decide

example : ¬ inParsimonyRange 3 0 := by decide

end SymReg.Plugins
