import DynExpr.Expressions.Sampling
import SymReg.Constraints
import Init.Data.Rat.Lemmas

namespace SymReg.HofMig
open DynExpr
open DynExpr.Expressions.Sampling (RNG greater)

@[simp] theorem jf_finite_mul (a b : Rat) : JF.fin a * JF.fin b = .fin (a * b) := rfl
@[simp] theorem jf_finite_add (a b : Rat) : JF.fin a + JF.fin b = .fin (a + b) := rfl

/-- IEEE `<`, used by src/HallOfFame.jl:289, via the DE comparison model. -/
def less (a b : JF) : Bool := greater b a

/-- IEEE `isless` on `Float64`, used by src/HallOfFame.jl:131: `<` with `NaN` ordered last. -/
def isless : JF → JF → Bool
  | .nan, _ => false
  | _, .nan => true
  | a, b => less a b

/-- IEEE `>=` in src/HallOfFame.jl:181; equality with NaN is false. -/
def greaterEqual (a b : JF) : Bool :=
  match a, b with
  | .nan, _ | _, .nan => false
  | _, _ => greater a b || decide (a = b)

/-- The default member fields read by src/HallOfFame.jl:120-131,180-181,299-322
and src/Migration.jl:42-43; src/PopMember.jl:30-40. `tree` is uninterpreted
expression content; `objectId` and `treeId` are distinct allocation identities. -/
structure Member where
  cost : JF
  loss : JF
  complexity : Int
  tree : Nat
  objectId : Nat
  treeId : Nat
  birth : Int := 0
  reference : Int := 0
  parent : Int := -1
  lossNegativeZero : Bool := false
  deriving DecidableEq, Repr

/-- Observable content of a member, excluding the identities of its two allocations. -/
def payload (m : Member) : JF × JF × Int × Nat × Int × Int × Int :=
  (m.cost, m.loss, m.complexity, m.tree, m.birth, m.reference, m.parent)

/-- `copy(::PopMember)`, src/PopMember.jl:170-178. Expression-copy internals are
already modelled in DE; here the member and copied expression get fresh identities.
The supply is shared across hall updates, hall copies, frontier copies and migration. -/
def copyMember (m : Member) (fresh : Nat) : Member × Nat :=
  ({ m with objectId := fresh, treeId := fresh + 1 }, fresh + 2)

/-- The member-wise copying comprehensions in src/HallOfFame.jl:113,187. -/
def copyMembers : List Member → Nat → List Member × Nat
  | [], fresh => ([], fresh)
  | m :: ms, fresh =>
      let (m', f') := copyMember m fresh
      let (ms', f'') := copyMembers ms f'
      (m' :: ms', f'')

-- Source: src/PopMember.jl:195-201
/-
function recompute_complexity!(
    member::AbstractPopMember, options::AbstractOptions; break_sharing=Val(false)
)::Int
    complexity = compute_complexity(member.tree, options; break_sharing)
    setfield!(member, :complexity, complexity)
    return complexity
end
-/
@[simp] def recomputeComplexity (compute : Nat → Int) (m : Member) : Member × Int :=
  let c := compute m.tree
  ({ m with complexity := c }, c)

-- Source: src/PopMember.jl:187-194
/-
function compute_complexity(
    member::AbstractPopMember, options::AbstractOptions; break_sharing=Val(false)
)::Int
    complexity = getfield(member, :complexity)
    complexity == -1 && return recompute_complexity!(member, options; break_sharing)
    # TODO: Turn this into a warning, and then return normal compute_complexity instead.
    return complexity
end
-/
def resolveComplexity (compute : Nat → Int) (m : Member) : Member × Int :=
  if m.complexity = -1 then recomputeComplexity compute m else (m, m.complexity)

/-- The paired `.members[c]` and `.exists[c]` fields, src/HallOfFame.jl:27-32. -/
structure Slot where
  member : Member
  «exists» : Bool
  deriving DecidableEq, Repr

/-- A per-complexity array. Lean list index `i` represents Julia complexity `i+1`,
src/HallOfFame.jl:17-25. Equal lengths of the two Julia arrays are structural here. -/
structure Hof where
  slots : List Slot
  deriving DecidableEq, Repr

/-- Prototype creation and slot comprehension, src/HallOfFame.jl:72-108.
`signals i` supplies the independently generated birth and reference values;
the first prototype is allocated even when maxsize is zero. -/
def initHof (maxsize : Int) (tree fresh : Nat) (signals : Nat → Int × Int) : Hof × Nat :=
  let make := fun i =>
    let sig := signals i
    ({ cost := .fin 0, loss := .posInf, complexity := 1, tree := tree,
       objectId := fresh + 2 * i, treeId := fresh + 2 * i + 1,
       birth := sig.1, reference := sig.2, parent := -1 } : Member)
  ({ slots := (List.range maxsize.toNat).map (fun i => ⟨make i, false⟩) },
    fresh + 2 * max 1 maxsize.toNat)

/-- `eltype(hof)` and `eltype(typeof(hof))`, src/HallOfFame.jl:55-57. The
concrete default-member representation is the same for both dispatch paths. -/
def memberEltype (_ : Hof) (_onType : Bool) : Type := Member

/-- `copy(hof)`, src/HallOfFame.jl:111-115. Absent placeholder members are copied too. -/
def copyHof (h : Hof) (fresh : Nat) : Hof × Nat :=
  let (ms, f) := copyMembers (h.slots.map Slot.member) fresh
  (⟨(ms.zip (h.slots.map Slot.exists)).map (fun (m, e) => ⟨m, e⟩)⟩, f)

/-- Scalar `_update_hall_of_fame_unchecked!`, src/HallOfFame.jl:126-135.
NaN challengers are rejected; ties keep the incumbent; non-NaN challengers replace
absent slots or NaN incumbents via `isless`. -/
def updateUnchecked (h : Hof) (m : Member) (size : Int) (fresh : Nat) : Hof × Nat :=
  if 0 < size ∧ size ≤ (h.slots.length : Int) then
    if m.cost = .nan then (h, fresh)
    else match h.slots[size.toNat - 1]? with
      | none => (h, fresh)
      | some s =>
        if !s.exists || isless m.cost s.member.cost then
          let (m', f) := copyMember m fresh
          (⟨h.slots.set (size.toNat - 1) ⟨m', true⟩⟩, f)
        else (h, fresh)
  else (h, fresh)

/-- Scalar `update_hall_of_fame!`, src/HallOfFame.jl:117-123. The callback is
`check_constraints(tree, options, maxsize, size)`; it can return a Julia exception.
The computed cache is returned explicitly, reflecting mutation of the input member. -/
def updateChecked (h : Hof) (m : Member) (maxsize : Int) (fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool) :
    Jl (Hof × Member × Nat) := do
  let (m', size) := resolveComplexity compute m
  if ¬ (0 < size ∧ size ≤ maxsize) then return (h, m', fresh)
  if !(← check m' maxsize size) then return (h, m', fresh)
  let (h', f') := updateUnchecked h m' size fresh
  return (h', m', f')

/-- Vector `_update_hall_of_fame_unchecked!`, src/HallOfFame.jl:137-146. -/
def updateManyUnchecked (h : Hof) (ms : List Member) (fresh : Nat)
    (compute : Nat → Int) : Hof × List Member × Nat :=
  match ms with
  | [] => (h, [], fresh)
  | m :: rest =>
    let (m', size) := resolveComplexity compute m
    let (h', f') := updateUnchecked h m' size fresh
    let (h'', rest', f'') := updateManyUnchecked h' rest f' compute
    (h'', m' :: rest', f'')

/-- Vector `update_hall_of_fame!`, src/HallOfFame.jl:149-157; a throwing
constraint check stops the loop, as in Julia. -/
def updateManyChecked (h : Hof) (ms : List Member) (maxsize : Int) (fresh : Nat)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool) :
    Jl (Hof × List Member × Nat) := do
  match ms with
  | [] => return (h, [], fresh)
  | m :: rest =>
    let (h', m', f') ← updateChecked h m maxsize fresh compute check
    let (h'', rest', f'') ← updateManyChecked h' rest maxsize f' compute check
    return (h'', m' :: rest', f'')

inductive UpdateEvent where
  | visit (member : Nat)
  | compute (tree options : Nat) (breakSharing : Bool)
  | cache (member : Nat) (size : Int)
  | check (tree options : Nat) (maxsize size : Int)
  | compare (size : Int)
  | copy (member : Nat)
  | store (size : Int)
  | mark (size : Int)
  deriving DecidableEq, Repr

structure UpdateState where
  hall : Hof
  fresh : Nat
  caches : List (Nat × Int) := []
  members : List Member := []
  input : List Member := []
  events : List UpdateEvent := []
  deriving DecidableEq, Repr

structure UpdateServices where
  options : Nat
  maxsize : UpdateState → Jl Int × UpdateState
  compute : Nat → Nat → Bool → UpdateState → Jl Int × UpdateState
  check : Nat → Nat → Int → Int → UpdateState → Jl Bool × UpdateState
  tree : Member → UpdateState → Jl Nat × UpdateState := fun m st => (.ok m.treeId, st)
  copy : Member → UpdateState → Jl Member × UpdateState :=
    fun m st =>
      let (copied, fresh) := copyMember m st.fresh
      (.ok copied, { st with fresh })
  store : Int → Member → UpdateState → Jl Member × UpdateState := fun _ m st => (.ok m, st)
  cost : Member → UpdateState → Jl JF × UpdateState := fun m st => (.ok m.cost, st)
  isNaN : JF → UpdateState → Jl Bool × UpdateState := fun a st => (.ok (a == .nan), st)
  compare : JF → JF → UpdateState → Jl Bool × UpdateState :=
    fun a b st => (.ok (isless a b), st)

def UpdateState.record (st : UpdateState) (event : UpdateEvent) : UpdateState :=
  { st with events := st.events ++ [event] }

/-- Latest fields of the same mutable member, with its separately resolved cache. -/
def UpdateState.readMember (st : UpdateState) (m : Member) : Member :=
  let live := (st.members.find? (fun p => p.objectId == m.objectId)).getD m
  let complexity := ((st.caches.find? (fun p => p.1 == m.objectId)).map Prod.snd).getD
    live.complexity
  { live with complexity }

/-- Replacing a live member's fields also replaces any previously cached size. -/
def UpdateState.writeMember (st : UpdateState) (m : Member) : UpdateState :=
  { st with members := m :: st.members, caches := (m.objectId, m.complexity) :: st.caches }

def compareCosts (s : UpdateServices) (m : Member) (size : Int) (st : UpdateState) :
    Jl Bool × UpdateState :=
  match s.cost (st.readMember m) st with
  | (.error e, st) => (.error e, st)
  | (.ok a, st) =>
    match st.hall.slots[size.toNat - 1]? with
    | none => (.error .boundsError, st)
    | some slot =>
      match s.cost (st.readMember slot.member) st with
      | (.error e, st) => (.error e, st)
      | (.ok b, st) => s.compare a b (st.record (.compare size))

-- Source: src/HallOfFame.jl:126-135
/-
function _update_hall_of_fame_unchecked!(
    hall_of_fame::HallOfFame, member::AbstractPopMember, size::Int
)
    0 < size <= lastindex(hall_of_fame.exists) || return nothing
    isnan(member.cost) && return nothing
    if !hall_of_fame.exists[size] || isless(member.cost, hall_of_fame.members[size].cost)
        hall_of_fame.members[size] = copy(member)
        hall_of_fame.exists[size] = true
    end
    return nothing
end
-/
def runUnchecked (s : UpdateServices) (m : Member) (size : Int) (st : UpdateState) :
    Jl Unit × UpdateState :=
  if 0 < size ∧ size ≤ (st.hall.slots.length : Int) then
    match s.cost (st.readMember m) st with
    | (.error e, st) => (.error e, st)
    | (.ok c, st) =>
      match s.isNaN c st with
      | (.error e, st) => (.error e, st)
      | (.ok true, st) => (.ok (), st)
      | (.ok false, st) =>
        match st.hall.slots[size.toNat - 1]? with
        | none => (.error .boundsError, st)
        | some slot =>
          let (accept, st) := if slot.exists then compareCosts s m size st else (.ok true, st)
          match accept with
          | .error e => (.error e, st)
          | .ok false => (.ok (), st)
          | .ok true =>
            let st := st.record (.copy m.objectId)
            match s.copy (st.readMember m) st with
            | (.error e, st) => (.error e, st)
            | (.ok copied, st) =>
              match s.store size copied (st.record (.store size)) with
              | (.error e, st) => (.error e, st)
              | (.ok stored, st) =>
                (.ok (), { (st.record (.mark size)) with
                  hall := ⟨st.hall.slots.set (size.toNat - 1) ⟨stored, true⟩⟩ })
  else (.ok (), st)

-- Source: src/PopMember.jl:187-201
def runComplexity (s : UpdateServices) (m : Member) (st : UpdateState)
    (breakSharing : Bool := false) (force : Bool := false) : Jl Int × UpdateState :=
  let m := st.readMember m
  let cached := m.complexity
  if force || cached == -1 then
    match s.tree m st with
    | (.error e, st) => (.error e, st)
    | (.ok tree, st) =>
      match s.compute tree s.options breakSharing (st.record (.compute tree s.options breakSharing)) with
      | (.error e, st) => (.error e, st)
      | (.ok size, st) => (.ok size, { (st.record (.cache m.objectId size)) with
          caches := (m.objectId, size) :: st.caches })
  else (.ok cached, st)

-- Source: src/HallOfFame.jl:117-123
/-
function update_hall_of_fame!(
    hall_of_fame::HallOfFame, member::AbstractPopMember, options::AbstractOptions
)
    size = compute_complexity(member, options)
    0 < size <= options.maxsize || return nothing
    check_constraints(member.tree, options, options.maxsize, size) || return nothing
    return _update_hall_of_fame_unchecked!(hall_of_fame, member, size)
end
-/
def runChecked (s : UpdateServices) (m : Member) (st : UpdateState) : Jl Unit × UpdateState :=
  match runComplexity s m st with
  | (.error e, st) => (.error e, st)
  | (.ok size, st) =>
    if size ≤ 0 then (.ok (), st) else
      match s.maxsize st with
      | (.error e, st) => (.error e, st)
      | (.ok limit, st) =>
        if size > limit then (.ok (), st) else
          match s.tree (st.readMember m) st with
          | (.error e, st) => (.error e, st)
          | (.ok tree, st) =>
            match s.maxsize st with
            | (.error e, st) => (.error e, st)
            | (.ok limit, st) =>
              match s.check tree s.options limit size (st.record (.check tree s.options limit size)) with
              | (.error e, st) => (.error e, st)
              | (.ok false, st) => (.ok (), st)
              | (.ok true, st) => runUnchecked s m size st

-- Source: src/HallOfFame.jl:149-157
/-
function update_hall_of_fame!(
    hall_of_fame::HallOfFame,
    members::AbstractVector{<:AbstractPopMember},
    options::AbstractOptions,
)
    for member in members
        update_hall_of_fame!(hall_of_fame, member, options)
    end
    return nothing
end
-/
inductive UpdateSource where
  | member (value : Member)
  | hallSlot (index : Nat)
  | inputSlot (index : Nat)

def runCheckedSources (s : UpdateServices) : List UpdateSource → UpdateState → Jl Unit × UpdateState
  | [], st => (.ok (), st)
  | source :: rest, st =>
    let member := match source with
      | .member value => some value
      | .hallSlot i => st.hall.slots[i]?.map Slot.member
      | .inputSlot i => st.input[i]?
    match member with
    | none => (.error .boundsError, st)
    | some m =>
      match runChecked s m (st.record (.visit m.objectId)) with
      | (.error e, st) => (.error e, st)
      | (.ok (), st) => runCheckedSources s rest st

def runManyChecked (s : UpdateServices) (members : List Member) (st : UpdateState) :
    Jl Unit × UpdateState :=
  runCheckedSources s ((List.range members.length).map .inputSlot) { st with input := members }

def runCheckedAliased (s : UpdateServices) (st : UpdateState) : Jl Unit × UpdateState :=
  runCheckedSources s ((List.range st.hall.slots.length).map .hallSlot) st

/-- One inner comparison loop in `calculate_pareto_frontier`,
src/HallOfFame.jl:175-185. Only existing lower-complexity slots are inspected. -/
def dominatesEarlier (m : Member) (earlier : List Slot) : Bool :=
  !(earlier.any (fun s => s.exists && greaterEqual m.loss s.member.loss))

/-- Outer scan of `calculate_pareto_frontier`, src/HallOfFame.jl:167-189. A NaN loss is
skipped (line 172). All lower slots enter the comparison prefix, including previously
rejected and skipped members. -/
def frontRaw (earlier : List Slot) : List Slot → List Member
  | [] => []
  | s :: ss =>
    let rest := frontRaw (earlier ++ [s]) ss
    if s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier then s.member :: rest
    else rest

/-- `calculate_pareto_frontier`, src/HallOfFame.jl:163-190. Copying selected
members in order has the same allocation order as copying at each `push!`. -/
def calculatePareto (h : Hof) (fresh : Nat) : List Member × Nat :=
  copyMembers (frontRaw [] h.slots) fresh

inductive FrontierEvent where
  | visit (slot : Nat)
  | copy (member : Nat)
  deriving DecidableEq, Repr

abbrev FrontierCopy (W : Type) := Member → Nat → W → Jl Member × Nat × W

def stockFrontierCopy (m : Member) (fresh : Nat) (world : W) : Jl Member × Nat × W :=
  let (copied, next) := copyMember m fresh
  (.ok copied, next, world)

-- Source: src/HallOfFame.jl:163-190
def scanFrontier (copy : FrontierCopy W) (earlier : List Slot) :
    List Slot → Nat → W → Jl (List Member) × Nat × W × List FrontierEvent
  | [], fresh, world => (.ok [], fresh, world, [])
  | s :: ss, fresh, world =>
    let visit := FrontierEvent.visit earlier.length
    if s.exists && s.member.loss != .nan && dominatesEarlier s.member earlier then
      let call := FrontierEvent.copy s.member.objectId
      match copy s.member fresh world with
      | (.error e, final, stopped) => (.error e, final, stopped, [visit, call])
      | (.ok m, next, live) =>
        let (result, final, world', events) := scanFrontier copy (earlier ++ [s]) ss next live
        (result.map (m :: ·), final, world', visit :: call :: events)
    else
      let (result, final, world', events) := scanFrontier copy (earlier ++ [s]) ss fresh world
      (result, final, world', visit :: events)

def runFrontier (copy : FrontierCopy W) (h : Hof) (fresh : Nat) (world : W) :
    Jl (List Member) × Nat × W × List FrontierEvent :=
  scanFrontier copy [] h.slots fresh world

/-- No population or hall owns any identities at or beyond the fresh supply. -/
def Below (fresh : Nat) (m : Member) : Prop := m.objectId < fresh ∧ m.treeId < fresh

/-- A small member used only to exhibit satisfiable hypotheses and counterexamples. -/
def specimen (cost loss : JF) (complexity : Int := 1) : Member :=
  { cost, loss, complexity, tree := 0, objectId := 0, treeId := 1 }

end SymReg.HofMig
