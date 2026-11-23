import SymReg.HofMig.Core
import SymReg.Loss.Core

namespace SymReg.HofMig
open DynExpr
open DynExpr.Expressions.Sampling (greater)

open SymReg.Loss (LossPrecision)

/-- IEEE floating values for the score helpers. The extra bit is needed when
JF's finite value is zero. NaN payloads and NaN signs are not modeled. -/
structure ScoreFloat where
  precision : LossPrecision
  value : JF
  negativeZero : Bool := false
  deriving DecidableEq

def ScoreFloat.signbit (x : ScoreFloat) : Bool :=
  match x.value with
  | .fin q => if q = 0 then x.negativeZero else decide (q < 0)
  | .negInf => true
  | _ => false

def ScoreFloat.round (x : ScoreFloat) (p : LossPrecision) : ScoreFloat :=
  let value := p.round x.value
  ⟨p, value, if value = .fin 0 then x.signbit else false⟩

private def promotePrecision : LossPrecision → LossPrecision → LossPrecision
  | .float64, _ | _, .float64 => .float64
  | .float32, _ | _, .float32 => .float32
  | _, _ => .float16

def ScoreFloat.neg (x : ScoreFloat) : ScoreFloat :=
  ⟨x.precision, JF.neg x.value, if x.value = .fin 0 then !x.negativeZero else false⟩

def ScoreFloat.add (x y : ScoreFloat) : ScoreFloat :=
  let p := promotePrecision x.precision y.precision
  let negativeZero := x.value == .fin 0 && y.value == .fin 0 &&
    x.negativeZero && y.negativeZero
  (ScoreFloat.mk p (JF.add x.value y.value) negativeZero).round p

def ScoreFloat.div (x y : ScoreFloat) : ScoreFloat :=
  let p := promotePrecision x.precision y.precision
  let numerator := if y.value = .fin 0 ∧ y.negativeZero then JF.neg x.value else x.value
  (ScoreFloat.mk p (JF.div numerator y.value) (x.signbit != y.signbit)).round p

inductive ScoreDelta where
  | integer (value : Int64)
  | float (value : ScoreFloat)

def ScoreDelta.asFloat (p : LossPrecision) : ScoreDelta → ScoreFloat
  | .integer n => ⟨p, p.round (.fin (n.toInt : Rat)), false⟩
  | .float x => x

/-- The positive finite Float32/Float64 libm log values in Julia Base.
Float16 dispatches through Float32 (`base/math.jl:1306-1312`). -/
structure ScalarRuntime where
  ieeeLog : LossPrecision → Rat → Rat
  precision : LossPrecision

def ScalarRuntime.logPositive (rt : ScalarRuntime) (q : Rat) : JF :=
  let p := if rt.precision = .float16 then .float32 else rt.precision
  rt.precision.round (p.round (.fin (rt.ieeeLog p q)))

-- Source: Julia v1.12.0 base/float.jl:985-993
/-- Toggling the significand's low bit leaves a gap of one ULP for finite
values, including subnormals and both zeros. For infinities and NaNs the
subtraction produces NaN. -/
def epsilon (x : ScoreFloat) : ScoreFloat :=
  ⟨x.precision, (match x.value with
   | .fin q => .fin (x.precision.ulp (if q = 0 then x.precision.minNormal else q))
   | _ => .nan), false⟩

-- Source: Julia v1.12.0 base/special/log.jl:287-331
private def logDomainMessage : String :=
  "log was called with a negative real argument but will only return a complex result if called with a complex argument. Try log(Complex(x))."

def scalarLog (rt : ScalarRuntime) (x : ScoreFloat) : Jl ScoreFloat :=
  let p := x.precision
  match x.value with
  | .nan => .ok ⟨p, .nan, false⟩
  | .posInf => .ok ⟨p, .posInf, false⟩
  | .negInf => .error (.domainError logDomainMessage)
  | .fin q =>
    if q < 0 then .error (.domainError logDomainMessage)
    else if q = 0 then .ok ⟨p, .negInf, false⟩
    else if q = 1 then .ok ⟨p, .fin 0, false⟩
    else .ok ⟨p, { rt with precision := p }.logPositive q, false⟩

-- Source: src/Operators.jl:116-118; Julia v1.12.0 base/bool.jl:180-184
/-
function relu(x)
    return (x > zero(x)) * x
end
-/
def relu (x : ScoreFloat) : ScoreFloat :=
  if greater x.value (.fin 0) then x else ⟨x.precision, .fin 0, x.signbit⟩

-- Source: src/HallOfFame.jl:326-329
/-
function compute_direct_score(cur_loss, last_loss, delta_c)
    delta = cur_loss - last_loss
    return relu(-delta / delta_c)
end
-/
def directScore (cur last : ScoreFloat) (delta : ScoreDelta) : ScoreFloat :=
  let difference := cur.add last.neg
  relu (difference.neg.div (delta.asFloat difference.precision))

-- Source: src/HallOfFame.jl:330-333
/-
function compute_zero_centered_score(cur_loss, last_loss, delta_c)
    log_ratio = log(relu(cur_loss / last_loss) + eps(cur_loss))
    return relu(-log_ratio / delta_c)
end
-/
def scoreLogInput (cur last : ScoreFloat) : ScoreFloat :=
  (relu (cur.div last)).add (epsilon cur)

def zeroCenteredScore (rt : ScalarRuntime) (cur last : ScoreFloat)
    (delta : ScoreDelta) : Jl ScoreFloat := do
  let logRatio ← scalarLog rt (scoreLogInput cur last)
  return relu (logRatio.neg.div (delta.asFloat logRatio.precision))

inductive LossScale where
  | log | linear | other
  deriving DecidableEq, Repr

/-- `show_score_column`, src/HallOfFame.jl:203. -/
def showScoreColumn (scale : LossScale) : Bool := scale == .log

/-- The named tuple returned by src/HallOfFame.jl:324. -/
structure Formatted where
  trees : List Nat
  scores : List JF
  losses : List JF
  complexities : List Int
  deriving DecidableEq, Repr

def Member.scoreLoss (m : Member) (p : LossPrecision) : ScoreFloat :=
  ⟨p, m.loss, m.lossNegativeZero⟩

/-- The scored arrays keep IEEE type and zero sign until projected to JF. -/
structure TypedFormatted where
  trees : List Nat
  scores : List ScoreFloat
  losses : List ScoreFloat
  complexities : List Int
  treeIds : List Nat

def rowScore (rt : ScalarRuntime) (scale : LossScale) (cur : ScoreFloat) (c : Int)
    (previous : Option (ScoreFloat × Int)) : Jl ScoreFloat :=
  match previous with
  | none => .ok ⟨rt.precision, .fin 0, false⟩
  | some (last, lastC) => do
    let delta := ScoreDelta.integer (Int64.ofInt c - Int64.ofInt lastC)
    let score ← if scale = .linear then pure (directScore cur last delta)
      else zeroCenteredScore rt cur last delta
    return score.round rt.precision

/-- Score loop at src/HallOfFame.jl:302-323. Complexity is already resolved. -/
def typedScoreRows (rt : ScalarRuntime) (scale : LossScale) :
    List (ScoreFloat × Int) → Option (ScoreFloat × Int) → Jl (List ScoreFloat)
  | [], _ => .ok []
  | pair :: rest, previous => do
    let score ← rowScore rt scale pair.1 pair.2 previous
    let scores ← typedScoreRows rt scale rest (some pair)
    return score :: scores

def scoreRows (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int)
    (ms : List Member) (previous : Option (JF × Int)) : Jl (List JF) :=
  (typedScoreRows rt scale (ms.map fun m => (m.scoreLoss rt.precision, (resolveComplexity compute m).2))
    (previous.map fun (loss, c) => (⟨rt.precision, loss, false⟩, c))).map (List.map ScoreFloat.value)

def negativeLossMessage : String :=
  "Your loss function must be non-negative. To allow negative losses, set the `loss_scale` to linear, or consider wrapping your loss inside an exponential."

inductive FormatError where
  | failure (error : JlError)
  | negativeLoss (loss : ScoreFloat) (message : String)
  deriving DecidableEq

def firstNegative (scale : LossScale) (ms : List Member) : Option Member :=
  if scale = .log then ms.find? (fun m => less m.loss (.fin 0)) else none

inductive FormatEvent where
  | hall
  | frontier (event : FrontierEvent)
  | resolve (member : Nat)
  | compute (tree : Nat)
  | scores
  deriving DecidableEq

structure FormatServices (W : Type) where
  copy : FrontierCopy W
  compute : Member → W → Jl Int × W
  readScale : Option (W → Jl LossScale × W) := none

def FormatServices.scaleAt (s : FormatServices W) (stock : LossScale) (world : W) :
    Jl LossScale × W :=
  match s.readScale with
  | none => (.ok stock, world)
  | some read => read world

-- Source: src/HallOfFame.jl:308-323
def scoreRowsWithScale (rt : ScalarRuntime) (read : W → Jl LossScale × W) :
    List (ScoreFloat × Int) → Option (ScoreFloat × Int) → W → Jl (List ScoreFloat) × W
  | [], _, world => (.ok [], world)
  | pair :: rest, previous, world =>
    let (score, live) := match previous with
      | none => (rowScore rt .linear pair.1 pair.2 none, world)
      | some _ =>
        let (scale, live) := read world
        (scale.bind fun scale => rowScore rt scale pair.1 pair.2 previous, live)
    match score with
    | .error e => (.error e, live)
    | .ok value =>
      let (tail, final) := scoreRowsWithScale rt read rest (some pair) live
      (tail.map (value :: ·), final)

/-- The successful prefix of custom computations stays visible even on error. -/
def resolveRows {W : Type} (compute : Member → W → Jl Int × W) :
    List Member → W → Jl (List Int) × W × List FormatEvent
  | [], world => (.ok [], world, [])
  | m :: ms, world =>
    let (result, world', invocation) :=
      if m.complexity = -1 then
        let (result, w) := compute m world
        (result, w, [FormatEvent.compute m.treeId])
      else (.ok m.complexity, world, [])
    match result with
    | .error e => (.error e, world', .resolve m.objectId :: invocation)
    | .ok c =>
      let (tail, world'', events) := resolveRows compute ms world'
      (tail.map (c :: ·), world'', .resolve m.objectId :: (invocation ++ events))

-- Source: src/HallOfFame.jl:284-325
/-
function format_hall_of_fame(hof::HallOfFame{T,L}, options) where {T,L}
    dominating = calculate_pareto_frontier(hof)

    # Only check for negative losses if using logarithmic scaling
    options.loss_scale == :log && for member in dominating
        if member.loss < 0.0
            throw(
                DomainError(
                    member.loss,
                    "Your loss function must be non-negative. To allow negative losses, set the `loss_scale` to linear, or consider wrapping your loss inside an exponential.",
                ),
            )
        end
    end

    trees = [member.tree for member in dominating]
    losses = [member.loss for member in dominating]
    complexities = [compute_complexity(member, options) for member in dominating]
    scores = Array{L}(undef, length(dominating))

    cur_loss = typemax(L)
    last_loss = cur_loss
    last_complexity = zero(eltype(complexities))

    for i in 1:length(dominating)
        complexity = complexities[i]
        cur_loss = losses[i]
        delta_c = complexity - last_complexity
        scores[i] = if i == 1
            zero(L)
        else
            if options.loss_scale == :linear
                compute_direct_score(cur_loss, last_loss, delta_c)
            else
                compute_zero_centered_score(cur_loss, last_loss, delta_c)
            end
        end
        last_loss = cur_loss
        last_complexity = complexity
    end
    return (; trees, scores, losses, complexities)
end
-/
def runFormatHof {W : Type} (rt : ScalarRuntime) (scale : LossScale) (s : FormatServices W)
    (h : Hof) (fresh : Nat) (world : W) :
    Except FormatError TypedFormatted × Nat × W × List FormatEvent :=
  let (front, next, world, visits) := runFrontier s.copy h fresh world
  let frontierCalls := FormatEvent.hall :: visits.map FormatEvent.frontier
  match front with
  | .error e => (.error (.failure e), next, world, frontierCalls)
  | .ok ms =>
    let (read, world) := s.scaleAt scale world
    match read with
    | .error e => (.error (.failure e), next, world, frontierCalls)
    | .ok selected =>
      match firstNegative selected ms with
      | some m =>
        (.error (.negativeLoss (m.scoreLoss rt.precision) negativeLossMessage), next, world, frontierCalls)
      | none =>
        let trees := ms.map Member.tree
        let losses := ms.map (fun m => m.scoreLoss rt.precision)
        let (complexities, world', events) := resolveRows s.compute ms world
        match complexities with
        | .error e => (.error (.failure e), next, world', frontierCalls ++ events)
        | .ok sizes =>
          let (scores, world'') := match s.readScale with
            | none => (typedScoreRows rt scale (losses.zip sizes) none, world')
            | some read => scoreRowsWithScale rt read (losses.zip sizes) none world'
          let result := match scores with
            | .error e => .error (FormatError.failure e)
            | .ok values => .ok (⟨trees, values, losses, sizes, ms.map Member.treeId⟩ : TypedFormatted)
          (result, next, world'', frontierCalls ++ events ++ [.scores])

/-- Stock copy and pure complexity projection used by the report model. -/
def formatHof (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int)
    (h : Hof) (fresh : Nat) : Jl (Formatted × Nat) := do
  let (front, f) := calculatePareto h fresh
  match firstNegative scale front with
  | some _ => throw (.domainError negativeLossMessage)
  | none =>
    let scores ← scoreRows rt scale compute front none
    return (⟨front.map Member.tree, scores, front.map Member.loss,
      front.map (fun m => (resolveComplexity compute m).2)⟩, f)

-- Source: src/HallOfFame.jl:335-342
/-
function format_hall_of_fame(hof::AbstractVector{<:HallOfFame}, options)
    outs = [format_hall_of_fame(h, options) for h in hof]
    return (;
        trees=[out.trees for out in outs],
        scores=[out.scores for out in outs],
        losses=[out.losses for out in outs],
        complexities=[out.complexities for out in outs],
    )
end
-/
def collectFormats {E S A : Type} (format : Hof → S → Except E A × S) :
    List Hof → S → Except E (List A) × S
  | [], st => (.ok [], st)
  | h :: hs, st =>
    let (out, st') := format h st
    match out with
    | .error e => (.error e, st')
    | .ok value =>
      let (outs, st'') := collectFormats format hs st'
      (outs.map (value :: ·), st'')

def formatStep {W : Type} (rt : ScalarRuntime) (scale : LossScale) (s : FormatServices W)
    (h : Hof) (st : Nat × W × List FormatEvent) :
    Except FormatError TypedFormatted × (Nat × W × List FormatEvent) :=
  let (out, next, world, events) := runFormatHof rt scale s h st.1 st.2.1
  (out, next, world, st.2.2 ++ events)

def runFormatMany {W : Type} (rt : ScalarRuntime) (scale : LossScale) (s : FormatServices W)
    (hs : List Hof) (fresh : Nat) (world : W) :
    Except FormatError (List TypedFormatted) × (Nat × W × List FormatEvent) :=
  collectFormats (formatStep rt scale s) hs (fresh, world, [])

private def stockFormatServices (compute : Nat → Int) : FormatServices Unit :=
  { copy := stockFrontierCopy, compute := fun m _ => (.ok (compute m.tree), ()) }

private def FormatError.asJl (e : FormatError) : JlError :=
  match e with
  | .failure cause => cause
  | .negativeLoss _ message => .domainError message

def formatHofTyped (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int)
    (h : Hof) (fresh : Nat) : Jl (TypedFormatted × Nat) :=
  let (result, next, _, _) := runFormatHof rt scale (stockFormatServices compute) h fresh ()
  match result with
  | .error e => .error e.asJl
  | .ok out => .ok (out, next)

def formatManyTyped (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int)
    (hs : List Hof) (fresh : Nat) : Jl (List TypedFormatted × Nat) :=
  let (result, next, _, _) := runFormatMany rt scale (stockFormatServices compute) hs fresh ()
  match result with
  | .error e => .error e.asJl
  | .ok out => .ok (out, next)

def formatMany (rt : ScalarRuntime) (scale : LossScale) (compute : Nat → Int) :
    List Hof → Nat → Jl (List Formatted × Nat)
  | [], fresh => pure ([], fresh)
  | h :: hs, fresh => do
    let (out, f) ← formatHof rt scale compute h fresh
    let (outs, f') ← formatMany rt scale compute hs f
    return (out :: outs, f')

end SymReg.HofMig
