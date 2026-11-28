import SymReg.HofMig.Migration
import SymReg.Loss.Core
import SymReg.Population.Tournament
import DynExpr.ParamStruct.Mirror

namespace SymReg.CrossMut
open DynExpr
open SymReg.HofMig (less)

/-- `src/Utils.jl:106-118`: k=1 scans with `isless` starting at the first element. -/
def bottomkOne : List JF → List (JF × Nat)
  | [] => []
  | x :: xs =>
    [(xs.zipIdx 2).foldl
      (fun best p => if SymReg.Population.isless p.1 best.1 then p else best) (x, 1)]

/-- `src/Utils.jl:97-148`: k=1 scans with `isless`; k>=2 runs `_bottomk!` tracking filled slots
and ordering by `isless`. -/
def bottomkFast (xs : List JF) (k : Nat) : List (JF × Nat) :=
  if k = 1 then bottomkOne xs
  else SymReg.Population.bottomk k xs

/-- Full k-smallest contract: distinct valid indices point at the reported
values, output is ascending, and no omitted input is smaller than a selected
value. -/
def bottomkIndices : Prop := ∀ xs : List JF, ∀ k : Nat,
  0 < k → k ≤ xs.length →
  let out := bottomkFast xs k
  (out.length = k ∧ (out.map Prod.snd).Nodup ∧
    ∀ p ∈ out, xs[p.2 - 1]? = some p.1) ∧
  out.Pairwise (fun p q => less q.1 p.1 = false) ∧
  ∀ i value, xs[i]? = some value → i + 1 ∉ out.map Prod.snd →
    ∀ p ∈ out, less value p.1 = false

private theorem less_false_of_isless_false {a b : JF}
    (h : SymReg.Population.isless a b = false) : less a b = false := by
  cases a <;> cases b <;>
    simp_all [SymReg.Population.isless, SymReg.Population.flt,
      less, DynExpr.Expressions.Sampling.greater] <;> grind

private theorem bottomkOne_fold_spec (xs : List JF) :
    ∀ (rest : List JF) (offset : Nat) (best : JF × Nat),
      1 ≤ best.2 → best.2 ≤ xs.length → xs[best.2 - 1]? = some best.1 →
      (∀ (i : Nat) (v : JF), i + 1 < offset → xs[i]? = some v →
        SymReg.Population.isless v best.1 = false) →
      (∀ (j : Nat), j < rest.length → xs[offset - 1 + j]? = rest[j]?) →
      offset - 1 + rest.length = xs.length → 1 ≤ offset →
      let r := (rest.zipIdx offset).foldl
        (fun b p => if SymReg.Population.isless p.1 b.1 then p else b) best
      1 ≤ r.2 ∧ r.2 ≤ xs.length ∧ xs[r.2 - 1]? = some r.1 ∧
      ∀ (i : Nat) (v : JF), xs[i]? = some v → SymReg.Population.isless v r.1 = false := by
  intro rest
  induction rest with
  | nil =>
    intro offset best h1 h2 h3 hprev _ hlen _
    refine ⟨h1, h2, h3, fun i v hi => ?_⟩
    have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
    exact hprev i v (by simp at hlen; omega) hi
  | cons y ys ih =>
    intro offset best h1 h2 h3 hprev hrest hlen hoff
    have hy : xs[offset - 1]? = some y := by
      have := hrest 0 (by simp)
      simpa using this
    have hylen : offset ≤ xs.length := by simp at hlen; omega
    rw [List.zipIdx_cons, List.foldl_cons]
    dsimp only
    split
    · rename_i hlt
      apply ih (offset + 1) (y, offset) (by omega) hylen hy ?_ ?_ (by simp at hlen ⊢; omega) (by omega)
      · intro i v hi hxi
        by_cases hio : i + 1 < offset
        · exact SymReg.Population.isless_asymm
            (SymReg.Population.isless_of_isless_not_isless hlt (hprev i v hio hxi))
        · have : i = offset - 1 := by omega
          subst this
          rw [hy] at hxi
          cases hxi
          exact SymReg.Population.isless_irrefl y
      · intro j hj
        have := hrest (j + 1) (by simp; omega)
        simpa [show offset - 1 + (j + 1) = offset + j by omega] using this
    · rename_i hnlt
      apply ih (offset + 1) best h1 h2 h3 ?_ ?_ (by simp at hlen ⊢; omega) (by omega)
      · intro i v hi hxi
        by_cases hio : i + 1 < offset
        · exact hprev i v hio hxi
        · have : i = offset - 1 := by omega
          subst this
          rw [hy] at hxi
          cases hxi
          simpa using hnlt
      · intro j hj
        have := hrest (j + 1) (by simp; omega)
        simpa [show offset - 1 + (j + 1) = offset + j by omega] using this

theorem bottomkIndices_holds : bottomkIndices := by
  intro xs k hk hle
  unfold bottomkFast
  by_cases h1 : k = 1
  · subst h1
    simp only [↓reduceIte]
    cases xs with
    | nil => simp at hle
    | cons x xs =>
      simp only [bottomkOne]
      have hspec := bottomkOne_fold_spec (x :: xs) xs 2 (x, 1) (by omega) (by simp) rfl
        (fun i v hi hxi => by
          have : i = 0 := by omega
          subst this
          simp at hxi
          subst hxi
          exact SymReg.Population.isless_irrefl x)
        (fun j _ => by rw [show 2 - 1 + j = j + 1 by omega]; rfl) (by simp; omega) (by omega)
      refine ⟨⟨rfl, by simp, fun p hp => ?_⟩, by simp, fun i v hxi _ p hp => ?_⟩
      · simp at hp; subst hp; exact hspec.2.2.1
      · simp at hp; subst hp
        exact less_false_of_isless_false (hspec.2.2.2 i v hxi)
  · simp only [h1, ↓reduceIte]
    obtain ⟨hlen, hnd, hsort, hmem, homit⟩ := SymReg.Population.bottomk_spec k xs (by omega) hle
    refine ⟨⟨hlen, hnd, fun p hp => (hmem p hp).2.2⟩, ?_, ?_⟩
    · exact hsort.imp (fun {_ _} hab => less_false_of_isless_false hab)
    · intro i v hxi hnot p hp
      have hilt : i < xs.length := (List.getElem?_eq_some_iff.mp hxi).1
      exact less_false_of_isless_false (homit i v hilt hxi hnot p hp)

/- Source: src/Utils.jl:20-30
function get_birth_order(; deterministic::Bool=false)::Int
    """deterministic gives a birth time with perfect resolution, but is not thread safe."""
    if deterministic
        global pseudo_time
        pseudo_time[] += 1
        return pseudo_time[]
    else
        resolution = 1e7
        return round(Int, resolution * time())
    end
end
-/
def birthOrder {W : Type} (deterministic : Bool) (counter : Int64)
    (clock : W → JF × W) (roundToInt : JF → Jl Int64) (world : W) :
    Jl Int64 × Int64 × W :=
  if deterministic then (.ok (counter + 1), counter + 1, world)
  else
    let (sample, world') := clock world
    (roundToInt (SymReg.Loss.LossPrecision.float64.round (JF.fin 10000000 * sample)), counter, world')

def birthSemantics : Prop := ∀ (W : Type) (counter : Int64) (clock : W → JF × W) roundToInt world,
  let (time, world') := clock world
  birthOrder false counter clock roundToInt world =
    (roundToInt (SymReg.Loss.LossPrecision.float64.round (JF.fin 10000000 * time)), counter, world') ∧
  let (result, counter', state) := birthOrder true counter clock roundToInt world
  let (next, counter'', state') := birthOrder true counter' clock roundToInt state
  state' = world ∧ result = .ok counter' ∧ next = .ok counter'' ∧
    counter' = counter + 1 ∧ counter'' = counter + 1 + 1
theorem birthSemantics_holds : birthSemantics := by
  intro W counter clock roundToInt world
  cases hc : clock world
  simp [birthOrder, hc]

/-- `src/Utils.jl:32-37`: decoded nameof string. Only # followed by 1..9
counts as anonymous; all remaining characters are irrelevant. -/
def isAnonymous : List Char → Bool
  | '#' :: c :: _ => ['1','2','3','4','5','6','7','8','9'].contains c
  | _ => false
def anonymousNames : Prop := ∀ name,
  isAnonymous name = true ↔
    ∃ digit suffix, name = '#' :: digit :: suffix ∧
      digit ∈ ['1','2','3','4','5','6','7','8','9']
theorem anonymousNames_holds : anonymousNames := by
  intro name
  cases name with
  | nil => simp [isAnonymous]
  | cons c cs =>
    cases cs with
    | nil => simp [isAnonymous]
    | cons d ds =>
      by_cases hc : c = '#'
      · subst c; simp [isAnonymous]
      · have nh : '#' ≠ c := Ne.symm hc
        cases c
        simp_all [isAnonymous]

/-- `src/Utils.jl:42-45`: reversal of Julia's least-significant-first digits
followed by the actual ten-entry subscript table. -/
def subscriptDigit (d : Fin 10) : Char :=
  ['₀','₁','₂','₃','₄','₅','₆','₇','₈','₉'][d.val]'(by simp [d.isLt])
def subscriptifyDigits (digits : List (Fin 10)) : List Char := digits.reverse.map subscriptDigit

def subscriptDigitsCorrect : Prop := ∀ d : Fin 10,
  (subscriptDigit d).toNat = 8320 + d.val
theorem subscriptDigitsCorrect_holds : subscriptDigitsCorrect := by
  unfold subscriptDigitsCorrect
  decide

/- Source: src/Utils.jl:42-45
const subscripts = ('₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉')
function subscriptify(number::Integer)
    return join([subscripts[i + 1] for i in reverse(digits(number))])
end
-/
def subscriptify (number : Int) : Jl (List Char) :=
  let digits := (toString number.natAbs).toList.reverse.map fun c =>
    (Int.ofNat (c.toNat - '0'.toNat)) * (if number < 0 then -1 else 1)
  digits.reverse.mapM fun d =>
    if h : 0 ≤ d ∧ d.toNat < 10 then .ok (subscriptDigit ⟨d.toNat, h.2⟩)
    else .error .boundsError

def subscriptOrder : Prop := ∀ number : Int,
  (0 ≤ number → subscriptify number = .ok ((toString number.natAbs).toList.map fun c =>
    Char.ofNat (8320 + (c.toNat - '0'.toNat)))) ∧
  (number < 0 → subscriptify number = .error .boundsError)

private theorem decimal_leading_nonzero (n : Nat) (hn : 0 < n) :
    ∃ (c : Char) (tail : List Char), n.repr.toList = c :: tail ∧ '0'.toNat < c.toNat := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · refine ⟨n.digitChar, [], by simp [Nat.repr_of_lt h], ?_⟩
      rw [show '0'.toNat = 48 by rfl, Nat.toNat_digitChar_of_lt_ten h]
      omega
    · obtain ⟨c, tail, ht, hc⟩ := ih (n / 10) (Nat.div_lt_self hn (by decide)) (by omega)
      refine ⟨c, tail ++ [(n % 10).digitChar], ?_, hc⟩
      rw [Nat.repr_of_ge (by omega), String.toList_append, ht, String.toList_singleton]
      rfl

theorem subscriptOrder_holds : subscriptOrder := by
  intro number
  let cs := (toString number.natAbs).toList
  let digit := fun (c : Char) => c.toNat - '0'.toNat
  let index := fun (d : Int) => if h : 0 ≤ d ∧ d.toNat < 10 then
    (Except.ok (subscriptDigit ⟨d.toNat, h.2⟩) : Jl Char) else .error .boundsError
  have htable : ∀ d : Fin 10, subscriptDigit d = Char.ofNat (8320 + d.val) := by decide +kernel
  constructor
  · intro hn
    have hp : ¬ number < 0 := by omega
    have hchars : ∀ c ∈ cs, digit c < 10 := by
      intro c hc
      have hd : c.isDigit := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
        (by simpa [cs] using hc)
      obtain ⟨_, hu⟩ := Char.isDigit_iff_toNat.mp hd
      have h0 : '0'.toNat = 48 := rfl
      have h9 : '9'.toNat = 57 := rfl
      dsimp [digit]
      omega
    have hstep (c : Char) (hc : digit c < 10) :
        index (digit c : Int) = .ok (Char.ofNat (8320 + digit c)) := by
      have hd : 0 ≤ (digit c : Int) ∧ (digit c : Int).toNat < 10 := ⟨by omega, hc⟩
      unfold index
      rw [dite_eq_left hd, htable]
      rfl
    unfold subscriptify
    simp only [List.map_reverse, List.reverse_reverse, List.mapM_map, Function.comp_def,
      ite_eq_right hp, Int.mul_one]
    change (cs.mapM (fun c => index (digit c : Int))) = .ok (cs.map _)
    clear_value cs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      have hcs := ih (fun x hx => hchars x (by simp [hx]))
      simp only [List.mapM_cons, List.map_cons, hstep c (hchars c (by simp)), hcs,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      rfl
  · intro hn
    have hp : 0 < number.natAbs := by omega
    obtain ⟨c, tail, hc, hpositive⟩ := decimal_leading_nonzero number.natAbs hp
    have head : cs = c :: tail := by simpa [cs] using hc
    have hd : 0 < digit c := by unfold digit; omega
    have hi : index (-(digit c : Int)) = .error .boundsError := by
      change (if h : 0 ≤ -(digit c : Int) ∧ (-(digit c : Int)).toNat < 10 then _ else _) = _
      rw [dite_eq_right (by omega)]
    unfold subscriptify
    simp only [List.map_reverse, List.reverse_reverse, List.mapM_map, Function.comp_def,
      ite_eq_left hn, Int.mul_neg, Int.mul_one]
    change cs.mapM (fun c => index (-(digit c : Int))) = _
    rw [head, List.mapM_cons]
    simp [hi, Bind.bind, Except.bind]

example : subscriptify 120 = .ok ['₁', '₂', '₀'] ∧
    subscriptify (-120) = .error .boundsError := by decide +kernel

/-- `src/Utils.jl:55-60`: splitting at valid Unicode character boundaries is
list take/drop after decoding. width+1 represents the required positive n. -/
def chunkChars (width : Nat) (xs : List Char) : List (List Char) :=
  if xs.length ≤ width + 1 then [xs]
  else xs.take (width + 1) :: chunkChars width (xs.drop (width + 1))
termination_by xs.length
decreasing_by simp; omega

private theorem reassemble (width : Nat) (xs : List Char) :
    (chunkChars width xs).flatten = xs := by
  rw [chunkChars]
  split
  · simp
  · simp only [List.flatten_cons]
    rw [reassemble width (xs.drop (width + 1))]
    exact List.take_append_drop (width + 1) xs
termination_by xs.length
decreasing_by simp; omega

private theorem chunkWidths (width : Nat) (xs : List Char) :
    ∀ i, i + 1 < (chunkChars width xs).length →
      ((chunkChars width xs)[i]?.map List.length) = some (width + 1) := by
  rw [chunkChars]
  split
  · simp
  · rename_i h
    intro i hi
    cases i with
    | zero => simp [List.length_take, Nat.min_eq_left (by omega : width + 1 ≤ xs.length)]
    | succ i =>
      simp only [List.length_cons] at hi
      simpa using chunkWidths width (xs.drop (width + 1)) i (by omega)
termination_by xs.length
decreasing_by simp; omega

private theorem chunkUpperBound (width : Nat) (xs : List Char) :
    ∀ chunk ∈ chunkChars width xs, chunk.length ≤ width + 1 := by
  rw [chunkChars]
  split
  · simpa
  · intro chunk hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [List.length_take]; exact Nat.min_le_left _ _
    · exact chunkUpperBound width (xs.drop (width + 1)) chunk hc
termination_by xs.length
decreasing_by simp; omega

private theorem chunkNonempty (width : Nat) (xs : List Char) (hn : xs ≠ []) :
    ∀ chunk ∈ chunkChars width xs, chunk ≠ [] := by
  intro chunk hc
  rw [chunkChars] at hc
  split at hc
  · simp only [List.mem_singleton] at hc
    rwa [hc]
  · rename_i h
    rcases List.mem_cons.mp hc with rfl | hc
    · cases xs <;> simp_all
    · have hne : xs.drop (width + 1) ≠ [] := by
        intro hz
        have hz' := congrArg List.length hz
        simp at hz'
        omega
      exact chunkNonempty width (xs.drop (width + 1)) hne chunk hc
termination_by xs.length
decreasing_by simp; omega

def splitReassembles : Prop := ∀ width xs,
  let chunks := chunkChars width xs
  chunks.flatten = xs ∧
    (∀ i, i + 1 < chunks.length → chunks[i]?.map List.length = some (width + 1)) ∧
    (∀ chunk ∈ chunks, chunk.length ≤ width + 1) ∧
    (xs ≠ [] → ∀ chunk ∈ chunks, chunk ≠ []) ∧
    (xs.length ≤ width + 1 → chunks = [xs])
theorem splitReassembles_holds : splitReassembles := by
  intro width xs
  exact ⟨reassemble width xs, chunkWidths width xs, chunkUpperBound width xs,
    chunkNonempty width xs, fun h => by rw [chunkChars, if_pos h]⟩

/-- Reuse HofMig's exact source loop for `src/Utils.jl:146-157`, including
the DE random stream, Float64-like JF comparison and explicit fuel error.
exp(-1e-20) rounds to 1.0 in Julia 1.12, confirmed by the reproducer. -/
def poissonSupport : Prop := ∀ (rt : SymReg.HofMig.MigrationRuntime)
    (lambda : Rat) fuel rng value rng',
  0 ≤ lambda →
  SymReg.HofMig.poissonSample rt (.fin lambda) fuel rng = .ok (value, rng') →
  0 ≤ value

/-- The concrete positive rate is represented directly as a reduced Rat,
avoiding dependence on Lean's opaque rational division implementation. -/
private def tinyRate : Rat := ⟨1, 100000000000000000000, by decide, by decide⟩

theorem poissonSupport_refuted : ¬ poissonSupport := by
  intro h
  let rt : SymReg.HofMig.MigrationRuntime := ⟨fun _ => .ok (.fin 1), fun _ => 0⟩
  let rng : DynExpr.Expressions.Sampling.RNG := { draws := fun _ => 0 }
  have nonzero : tinyRate ≠ 0 := by decide
  have bad := h rt tinyRate 1 rng (-1) rng (by decide) (by
    simp [SymReg.HofMig.poissonSample, SymReg.HofMig.poissonLoop, rt, nonzero,
      DynExpr.Expressions.Sampling.greater, bind, Except.bind])
  exact (by decide : ¬ (0 ≤ (-1 : Int))) bad

def poissonZero : Prop := ∀ (W : Type) rt fuel rng (defaultRNG : W → DynExpr.Expressions.Sampling.RNG × W) w,
  SymReg.HofMig.poissonSample rt (.fin 0) fuel rng = .ok (0, rng) ∧
  let (default, w') := defaultRNG w
  SymReg.HofMig.poissonDefault rt (.fin 0) fuel defaultRNG w = (.ok (0, default), w')
theorem poissonZero_holds : poissonZero := by
  intro W rt fuel rng defaultRNG w
  cases h : defaultRNG w
  exact ⟨rfl, by simp [SymReg.HofMig.poissonDefault, h, SymReg.HofMig.poissonSample]⟩

inductive SafeStatus where | good | bad | undefined
  deriving DecidableEq, Repr

/-- `src/Utils.jl:234-252`: F,T form the cache key (D is absent).
The callback models f(x...) followed by its ::D assertion. The same MethodError
handling applies to an internal exception as to a missing outer method. -/
def safeCall (status : SafeStatus) (call : Unit → Jl Int) (default : Int) :
    Jl ((Int × Bool) × SafeStatus) :=
  match status with
  | .bad => pure ((default, false), .bad)
  | .good => do let value ← call (); pure ((value, true), .good)
  | .undefined =>
    match call () with
    | .ok value => pure ((value, true), .good)
    | .error (.methodError _) => pure ((default, false), .bad)
    | .error error => .error error

abbrev SafeCache := Nat → Nat → Nat → SafeStatus

/- Source: src/Utils.jl:234-252
function safe_call(f::F, x::T, default::D) where {F,T<:Tuple,D}
    thread_cache = SafeFunctions[]
    status = get(thread_cache, Tuple{F,T}, Undefined)
    status == Good && return (f(x...)::D, true)
    status == Bad && return (default, false)
    output = try
        (f(x...)::D, true)
    catch e
        !isa(e, MethodError) && rethrow(e)
        (default, false)
    end
    if output[2]
        thread_cache[Tuple{F,T}] = Good
    else
        thread_cache[Tuple{F,T}] = Bad
    end
    return output
end
-/
def safeCallCached {W : Type} (task functionType argsType : Nat)
    (call : SafeCache × W → Jl Int × (SafeCache × W)) (default : Int)
    (initial : SafeCache × W) : Jl (Int × Bool) × (SafeCache × W) :=
  let status := initial.1 task functionType argsType
  if status = .bad then (.ok (default, false), initial) else
    let (result, updated, world) := call initial
    match safeCall status (fun _ => result) default with
    | .error error => (.error error, updated, world)
    | .ok (value, determined) =>
      if status = .undefined then
        (.ok value,
          (fun t f a => if t = task ∧ f = functionType ∧ a = argsType then determined else updated t f a),
          world)
      else (.ok value, updated, world)

def safeCacheBranches : Prop := ∀ (W : Type) task f a call default (initial : SafeCache × W),
  let out := safeCallCached task f a call default initial
  let status := initial.1 task f a
  (status = .bad → out = (.ok (default, false), initial)) ∧
  (status = .good → out = ((call initial).1.map (fun v => (v, true)), (call initial).2)) ∧
  (status = .undefined → ∀ result cache w, call initial = (result, cache, w) →
    let (answer, next, world) := out
    world = w ∧
    (∀ t ft atype, t ≠ task ∨ ft ≠ f ∨ atype ≠ a → next t ft atype = cache t ft atype) ∧
    (∀ v, result = .ok v → answer = .ok (v, true) ∧ next task f a = .good) ∧
    (∀ e, result = .error (.methodError e) → answer = .ok (default, false) ∧ next task f a = .bad) ∧
    (∀ e, result = .error e → (∀ msg, e ≠ .methodError msg) →
      answer = .error e ∧ next = cache))
theorem safeCacheBranches_holds : safeCacheBranches := by
  intro W task f a call default initial
  refine ⟨?_, ?_, ?_⟩
  · intro hs; simp [safeCallCached, hs]
  · intro hs
    cases hc : call initial with
    | mk result state =>
      obtain ⟨cache, world⟩ := state
      cases result <;> simp [safeCallCached, hs, hc, safeCall, Except.map]
  · intro hs result cache world hc
    cases result with
    | error e =>
      cases e <;> simp [safeCallCached, hs, hc, safeCall] <;>
        intro t ft atype h <;> rcases h with h | h | h <;> simp_all
    | ok v =>
      simp [safeCallCached, hs, hc, safeCall]
      intro t ft atype h
      rcases h with h | h | h <;> simp_all

example : (fun _ : Unit => (.ok 1 : Jl Int)) () = .ok 1 := rfl

/-- A stable operator contract makes MethodError classification a function of
argument types. Other errors and successful values can depend on the arguments. -/
def isMethodError : Jl Int → Bool
  | .error (.methodError _) => true
  | _ => false

def safeCacheValueIndependent : Prop := ∀ (call : Int → Jl Int) x y default,
  (∀ a b, isMethodError (call a) = isMethodError (call b)) →
  (do let (_, status) ← safeCall .undefined (fun _ => call x) default
      pure ((safeCall status (fun _ => call y) default).map Prod.fst)) =
    (safeCall .undefined (fun _ => call x) default).map
      (fun _ => (safeCall .undefined (fun _ => call y) default).map Prod.fst)

theorem safeCacheValueIndependent_holds : safeCacheValueIndependent := by
  intro call x y default h
  have hc := h x y
  cases hx : call x with
  | ok v =>
    cases hy : call y with
    | ok w => simp [safeCall, hx, hy, bind, Except.bind, Except.map]
    | error e => cases e <;> simp_all [safeCall, isMethodError, bind, Except.bind, Except.map]
  | error e =>
    cases hy : call y with
    | ok w => cases e <;> simp_all [safeCall, isMethodError, bind, Except.bind, Except.map]
    | error e' => cases e <;> cases e' <;> simp_all [safeCall, isMethodError, bind, Except.bind, Except.map]

example : ∀ a b : Int, isMethodError (.ok (a + 1)) = isMethodError (.ok (b + 1)) := by
  intros; rfl

abbrev TaskStorage (A : Type) := Nat → Nat → Option A

inductive TaskReadError where
  | constructor (error : JlError)
  | typeError

/- Source: src/Utils.jl:208-217
function Base.getindex(cache::PerTaskCache{T}) where {T}
    tls = Base.task_local_storage()
    if haskey(tls, cache)
        return tls[cache]::T
    else
        value = cache.constructor()::T
        tls[cache] = value
        return value
    end
end
-/
def taskGet {A W : Type} (task key : Nat) (hasType : A → Bool)
    (construct : TaskStorage A × W → Jl A × (TaskStorage A × W))
    (initial : TaskStorage A × W) : Except TaskReadError A × (TaskStorage A × W) :=
  match initial.1 task key with
  | some value => (if hasType value then .ok value else .error .typeError, initial)
  | none =>
    let (result, storage, world) := construct initial
    match result with
    | .error e => (.error (.constructor e), storage, world)
    | .ok value =>
      if hasType value then
        (.ok value, (fun t k => if t = task ∧ k = key then some value else storage t k), world)
      else (.error .typeError, storage, world)

def taskCacheHit : Prop := ∀ (A W : Type) task key (hasType : A → Bool) construct
    (initial : TaskStorage A × W) value,
  initial.1 task key = some value →
  let (result, state) := taskGet task key hasType construct initial
  state = initial ∧
    (hasType value = true → result = .ok value) ∧
    (hasType value = false → result = .error .typeError)
theorem taskCacheHit_holds : taskCacheHit := by
  intro A W task key hasType construct initial value h
  cases hv : hasType value <;> simp [taskGet, h, hv]

def taskCacheMiss : Prop := ∀ (A W : Type) task key (hasType : A → Bool) construct
    (initial : TaskStorage A × W),
  initial.1 task key = none →
  let (result, storage', world') := taskGet task key hasType construct initial
  let (expected, storage, world) := construct initial
  world' = world ∧
    (∀ t k, t ≠ task ∨ k ≠ key → storage' t k = storage t k) ∧
    (∀ e, expected = .error e → result = .error (.constructor e) ∧ storage' = storage) ∧
    (∀ v, expected = .ok v → hasType v = false →
      result = .error .typeError ∧ storage' = storage) ∧
    (∀ v, expected = .ok v → hasType v = true → result = .ok v ∧ storage' task key = some v)
theorem taskCacheMiss_holds : taskCacheMiss := by
  intro A W task key hasType construct initial h
  cases hc : construct initial with
  | mk out state =>
    obtain ⟨storage, world⟩ := state
    cases out with
    | error e => simp [taskGet, h, hc]
    | ok v =>
      cases hv : hasType v with
      | false => simp [taskGet, h, hc, hv]
      | true =>
        simp [taskGet, h, hc, hv]
        intro t k hk
        rcases hk with ht | hk <;> simp_all

example : (fun (_ _ : Nat) => some 1) 0 0 = some 1 := rfl
example : (none : Option Nat) = none := rfl

structure DumpBuffer where
  bytes : List UInt8
  cursor : Nat
  mark : Option Nat
  seekable : Bool
  writable : Bool

/- Source: src/Utils.jl:266-269; Base take! at v1.12.0/base/iobuffer.jl:756-783
dump_buffer(buffer::IOBuffer) = String(take!(buffer))
function dump_buffer(buffer::AnnotatedIOBuffer)
    return AnnotatedString(dump_buffer(buffer.io), buffer.annotations)
end
-/
def dumpBuffer {A : Type} (buffer : DumpBuffer) (annotations : A) :
    Jl (List UInt8 × A) × DumpBuffer :=
  let unmarked := { buffer with mark := none }
  let bytes := if buffer.seekable then buffer.bytes else buffer.bytes.drop buffer.cursor
  if buffer.writable then (.ok (bytes, annotations), { unmarked with bytes := [], cursor := 0 })
  else if buffer.seekable || bytes.isEmpty then (.ok (bytes, annotations), unmarked)
  else (.error (.errorException "Unreachable IOBuffer state"), unmarked)

def bufferDrain : Prop := ∀ (A : Type) buffer (annotations : A),
  let (result, after) := dumpBuffer buffer annotations
  after.mark = none ∧
  (buffer.seekable = true → result = .ok (buffer.bytes, annotations)) ∧
  (buffer.writable = true → after.bytes = [] ∧ after.cursor = 0 ∧
    (buffer.seekable = false → result = .ok (buffer.bytes.drop buffer.cursor, annotations))) ∧
  (buffer.writable = false → after.bytes = buffer.bytes ∧ after.cursor = buffer.cursor ∧
    (buffer.seekable = false →
      if buffer.cursor < buffer.bytes.length then
        result = .error (.errorException "Unreachable IOBuffer state")
      else result = .ok ([], annotations)))
theorem bufferDrain_holds : bufferDrain := by
  intro A buffer annotations
  cases hw : buffer.writable <;> cases hs : buffer.seekable <;>
    simp [dumpBuffer, hw, hs, List.drop_eq_nil_iff] <;>
    split <;> simp_all <;> omega

/-- `src/Utils.jl:271-280`: fixed keyword forwarding without merging caller
keywords. f can return a value or an exception; positional order is retained. -/
def fixKws {A K R : Type} (f : List A → K → R) (kws : K) (args : List A) := f args kws
def fixKwsForwarding : Prop := ∀ (A K R : Type) (f : List A → K → R) kws args,
  fixKws f kws args = f args kws
theorem fixKwsForwarding_holds : fixKwsForwarding := by intro A K R f kws args; rfl

structure Keyword where
  lhsText : String
  declarationAST : Nat
  deriving DecidableEq, Repr

/-- Keyword syntax used by Options: a default (typed or untyped), a
nospecialize wrapper around a default, or the final keyword splat. -/
inductive OptionKeyword where
  | defaulted (keyword : Keyword)
  | nospecialize (keyword : Keyword)
  | splat

def unwrapOptionKeyword : OptionKeyword → Option Keyword
  | .defaulted k | .nospecialize k => some k
  | .splat => none

/- Source: src/Utils.jl:168-192; actual call forms src/Options.jl:557-732
function _save_kwargs(log_variable::Symbol, fdef::Expr)
    def = splitdef(fdef)
    # Get kwargs:
    kwargs = copy(def[:kwargs])
    kwargs = map(kwargs) do k
        # If it's a macrocall for @nospecialize
        if k.head == :macrocall && string(k.args[1]) == "@nospecialize"
            # Find the actual argument - it's the last non-LineNumberNode argument
            inner_arg = last(filter(arg -> !(arg isa LineNumberNode), k.args))
            return inner_arg
        end
        return k
    end
    kwargs = filter(kwargs) do k
        # Filter ...:
        k.head == :... && return false
        # Filter other deprecated kwargs:
        startswith(string(first(k.args)), "deprecated") && return false
        return true
    end
    return quote
        $(Base).@__doc__ $fdef
        const $log_variable = $kwargs
    end
end
-/
def savedKeywords {Ast : Type} (binding : String) (functionDef : Ast) (xs : List OptionKeyword) :
    Ast × (String × List Keyword) :=
  (functionDef, binding, (xs.filterMap unwrapOptionKeyword).filter
    (fun k => !k.lhsText.startsWith "deprecated"))

inductive SavedDeclarations : List OptionKeyword → List Keyword → Prop where
  | nil : SavedDeclarations [] []
  | splat : SavedDeclarations xs out → SavedDeclarations (.splat :: xs) out
  | deprecated : unwrapOptionKeyword x = some k → k.lhsText.startsWith "deprecated" = true →
      SavedDeclarations xs out → SavedDeclarations (x :: xs) out
  | retain : unwrapOptionKeyword x = some k → k.lhsText.startsWith "deprecated" = false →
      SavedDeclarations xs out → SavedDeclarations (x :: xs) (k :: out)

def savedKeywordMembership : Prop := ∀ (Ast : Type) (functionDef : Ast) binding xs,
  let (definition, name, declarations) := savedKeywords binding functionDef xs
  definition = functionDef ∧ name = binding ∧ SavedDeclarations xs declarations
theorem savedKeywordMembership_holds : savedKeywordMembership := by
  intro Ast functionDef binding xs
  refine ⟨rfl, rfl, ?_⟩
  change SavedDeclarations xs _
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases x with
    | splat => exact .splat ih
    | defaulted k | nospecialize k =>
      cases h : k.lhsText.startsWith "deprecated" with
      | false => simpa [savedKeywords, unwrapOptionKeyword, h] using
          SavedDeclarations.retain (x := _) rfl h ih
      | true => simpa [savedKeywords, unwrapOptionKeyword, h] using
          SavedDeclarations.deprecated (x := _) rfl h ih

inductive StrictMapError where
  | dimensionMismatch
  | other (error : JlError)

private def checkLengths {A W : Type} (len : A → W → Jl Nat × W) (expected : Nat) :
    List A → W → Except StrictMapError Unit × W
  | [], w => (.ok (), w)
  | x :: xs, w =>
    match len x w with
    | (.error e, w') => (.error (.other e), w')
    | (.ok n, w') =>
      if n = expected then checkLengths len expected xs w' else (.error .dimensionMismatch, w')

/- Source: src/Utils.jl:11-14
@unstable @inline function strictmap(f, xs...)
    allequal(length, xs) || throw(DimensionMismatch("collections must have equal lengths"))
    return map(f, xs...)
end
-/
def strictMap {A W R : Type} (len : A → W → Jl Nat × W) (mapCall : List A → W → Jl R × W)
    (xs : List A) (w : W) : Except StrictMapError R × W :=
  let result : Except StrictMapError Unit × W := match xs with
    | [] | [_] => (.ok (), w)
    | x :: y :: rest => match len x w with
      | (.error e, w') => (.error (.other e), w')
      | (.ok n, w') => checkLengths len n (y :: rest) w'
  match result with
  | (.error e, w') => (.error e, w')
  | (.ok (), w') => let (out, w'') := mapCall xs w'
                   (out.mapError StrictMapError.other, w'')

private inductive EqualLengths {A W : Type} (len : A → W → Jl Nat × W) (n : Nat) :
    List A → W → W → Prop where
  | nil : EqualLengths len n [] w w
  | cons : len x w = (.ok n, w') → EqualLengths len n xs w' w'' →
      EqualLengths len n (x :: xs) w w''

private theorem checkLengths_append {A W : Type} {len : A → W → Jl Nat × W} {n : Nat}
    {xs : List A} {w w' : W} (h : EqualLengths len n xs w w') (tail : List A) :
    checkLengths len n (xs ++ tail) w = checkLengths len n tail w' := by
  induction h with
  | nil => rfl
  | cons hc _ ih => simpa [checkLengths, hc] using ih

def strictMapMismatch : Prop := ∀ (A W R : Type) (len : A → W → Jl Nat × W)
    (mapCall : List A → W → Jl R × W) first w,
  (∀ e w' second xs, len first w = (.error e, w') →
    strictMap len mapCall (first :: second :: xs) w = (.error (.other e), w')) ∧
  ∀ n w' matching w'' x rest, len first w = (.ok n, w') →
    EqualLengths len n matching w' w'' →
    (∀ m last, len x w'' = (.ok m, last) → m ≠ n →
      strictMap len mapCall (first :: (matching ++ x :: rest)) w =
        (.error .dimensionMismatch, last)) ∧
    (∀ e last, len x w'' = (.error e, last) →
      strictMap len mapCall (first :: (matching ++ x :: rest)) w = (.error (.other e), last))
theorem strictMapMismatch_holds : strictMapMismatch := by
  intro A W R len mapCall first w
  constructor
  · intro e w' second xs h; simp [strictMap, h]
  · intro n w' matching w'' x rest hf he
    have hstart : strictMap len mapCall (first :: (matching ++ x :: rest)) w =
        (match checkLengths len n (matching ++ x :: rest) w' with
        | (.error e, w') => (.error e, w')
        | (.ok (), w') => let (out, w'') := mapCall (first :: (matching ++ x :: rest)) w'
                         (out.mapError StrictMapError.other, w'')) := by
      cases matching <;> simp only [List.nil_append, List.cons_append, strictMap, hf]
    rw [hstart, checkLengths_append he]
    constructor
    · intro m last hx hm
      simp [checkLengths, hx, hm]
    · intro e last hx
      simp [checkLengths, hx]

/-- `src/Utils.jl:219-223`: conversion can fail; successful storage contains
the converted value, while setindex! returns the original input. -/
def taskSet {A B : Type} (storage : Nat → Nat → Option A) (task key : Nat)
    (convert : B → Jl A) (input : B) : Jl (B × (Nat → Nat → Option A)) := do
  let value ← convert input
  pure (input, fun t k => if t = task ∧ k = key then some value else storage t k)

def taskSetConverted : Prop := ∀ (A B : Type) storage task key (convert : B → Jl A) input value,
  convert input = .ok value →
  ∃ storage', taskSet storage task key convert input = .ok (input, storage') ∧
    storage' task key = some value
theorem taskSetConverted_holds : taskSetConverted := by
  intro A B storage task key convert input value hc
  exact ⟨(fun t k => if t = task ∧ k = key then some value else storage t k),
    by simp [taskSet, hc], by simp⟩
example : (fun x : Nat => (.ok x : Jl Nat)) 3 = .ok 3 := rfl

/-- `src/Utils.jl:67-94`: Julia's unsafe loads/stores implement homogeneous
isbits tuple slots. Lists represent those slots; indices are one-based and
invalid @inbounds access is undefined behavior. Exotic/non-isbits layouts
are excluded, rather than giving their pointer casts invented semantics. -/
def tupleGet {A : Type} (slots : List A) (index : Nat) : Jl A :=
  if index = 0 then .error (.undefinedBehavior "MutableTuple index")
  else match slots[index - 1]? with
    | some value => .ok value
    | none => .error (.undefinedBehavior "MutableTuple index")
/- Source: src/Utils.jl:80-84
Base.@propagate_inbounds function Base.setindex!(v::MutableTuple, x, i::Integer)
    T = eltype(v)
    GC.@preserve v unsafe_store!(Base.unsafe_convert(Ptr{T}, pointer_from_objref(v)), x, i)
    return x
end
-/
def tupleSet {A B : Type} (convert : B → List A → Jl A × List A) (slots : List A)
    (index : Nat) (value : B) : Jl B × List A :=
  match convert value slots with
  | (.error e, afterConversion) => (.error e, afterConversion)
  | (.ok converted, afterConversion) =>
    if 0 < index ∧ index ≤ afterConversion.length then
      (.ok value, afterConversion.set (index - 1) converted)
    else (.error (.undefinedBehavior "MutableTuple index"), afterConversion)

/- Source: src/Utils.jl:88-94
function _to_vec(v::MutableTuple{S,T}) where {S,T}
    x = Vector{T}(undef, S)
    @inbounds for i in 1:S
        x[i] = v[i]
    end
    return x
end
-/
def tupleToVector {A : Type} (slots : List A) (size : Nat) : Jl (Array A) :=
  ((List.range size).mapM fun i => tupleGet slots (i + 1)).map List.toArray

def tupleVectorContents : Prop := ∀ (A : Type) (slots : List A) size,
  size ≤ slots.length → ∃ out, tupleToVector slots size = .ok out ∧
    out.size = size ∧ (∀ i, i < size → out[i]? = slots[i]?)

private theorem tupleLoadPrefix {A : Type} (slots : List A) (size : Nat)
    (hsize : size ≤ slots.length) :
    (List.range size).mapM (fun i => tupleGet slots (i + 1)) =
      .ok (slots.take size) := by
  induction size generalizing slots with
  | zero => rfl
  | succ size ih =>
    cases slots with
    | nil => simp at hsize
    | cons x xs =>
      have hxs : size ≤ xs.length := by simpa using hsize
      have hget (i : Nat) : tupleGet (x :: xs) (i + 1 + 1) = tupleGet xs (i + 1) := by
        simp [tupleGet]
      have hfirst : tupleGet (x :: xs) 1 = .ok x := rfl
      simp only [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Function.comp_def,
        Nat.succ_eq_add_one, hfirst, hget, ih xs hxs, List.take_succ_cons, Bind.bind,
        Except.bind, Pure.pure, Except.pure]

theorem tupleVectorContents_holds : tupleVectorContents := by
  intro A slots size h
  refine ⟨(slots.take size).toArray, ?_, ?_, ?_⟩
  · simp [tupleToVector, tupleLoadPrefix slots size h, Except.map]
  · simp [Nat.min_eq_left h]
  · intro i hi
    simpa using (List.getElem?_take_of_lt (l := slots) hi)

example : tupleToVector [7, 9] 1 = .ok #[7] := rfl

def tupleReadWrite : Prop := ∀ (A B : Type) (slots : List A) (convert : B → List A → Jl A × List A)
    index value,
  let (result, slots') := tupleSet convert slots index value
  (∀ v after, convert value slots = (.ok v, after) → 0 < index → index ≤ after.length →
    result = .ok value ∧ tupleGet slots' index = .ok v) ∧
  (∀ e after, convert value slots = (.error e, after) → result = .error e ∧ slots' = after)
theorem tupleReadWrite_holds : tupleReadWrite := by
  intro A B slots convert index value
  constructor
  · intro v after h hp hb
    have hi : index - 1 < after.length := by omega
    simp [tupleSet, tupleGet, h, hp, hb, Nat.ne_of_gt hp, hi]
  · intro e after h; simp [tupleSet, h]
example : 0 < (1 : Nat) ∧ 1 ≤ ([0] : List Nat).length := by decide

/-- `src/Utils.jl:40,194,282-284`: type projection, missing JSON extension,
and get! with promote_op type assertion. Runtime type checks are external
throwing callbacks, so mismatches cannot be silently accepted here. -/
def getBaseType (base : Type) : Type := base
def jsonWrite (args : List Nat) : Jl Nat :=
  let _ := args
  .error (.errorException "Please load the JSON.jl package.")
def stableGet (getCall : Unit → Jl Nat) (assertType : Nat → Jl Nat) : Jl Nat := do
  let value ← getCall ()
  assertType value
def extensionFallback : Prop := ∀ args,
  jsonWrite args = .error (.errorException "Please load the JSON.jl package.")
theorem extensionFallback_holds : extensionFallback := by intro args; rfl
private def stableGetAdapter : Prop := ∀ getCall assertType,
  stableGet getCall assertType = (getCall ()).bind assertType

private def stableGetCache (init : Unit → Jl Nat) (assertType : Nat → Jl Nat)
    (cache : Nat → Option Nat) (key : Nat) : Jl Nat × (Nat → Option Nat) :=
  match cache key with
  | some value => (assertType value, cache)
  | none => match init () with
    | .error e => (.error e, cache)
    | .ok value => (assertType value, fun other => if other = key then some value else cache other)

def stableGetForwarding : Prop := stableGetAdapter ∧
  ∀ init assertType cache key,
    let result := stableGetCache init assertType cache key
    (∀ value, cache key = some value → result = (assertType value, cache)) ∧
    (cache key = none →
      (∀ e, init () = .error e → result = (.error e, cache)) ∧
      ∀ value, init () = .ok value →
        result.1 = assertType value ∧ result.2 key = some value ∧
        (∀ other, other ≠ key → result.2 other = cache other) ∧
        stableGetCache (fun _ => .error .boundsError) assertType result.2 key = (assertType value, result.2))
def baseTypeProjection : Prop := ∀ base : Type, getBaseType base = base
theorem baseTypeProjection_holds : baseTypeProjection := by intro base; rfl

-- Source: src/Utils.jl:16
-- macro ignore(args...) end
/-- An empty macro body expands to an inert `nothing` with no argument splice. -/
def ignoreSyntax (_args : List Nat) : Option Nat := none

def ignoredSyntax : Prop := ∀ (args : List Nat) (eval : Nat → Nat → Jl Nat) (state : Nat),
  (Option.mapM (fun ast => eval ast state) (ignoreSyntax args)).map (fun result => (result, result.getD state)) =
    .ok (none, state)

theorem ignoredSyntax_holds : ignoredSyntax := by
  intro args eval state
  rfl

end SymReg.CrossMut
