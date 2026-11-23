import SymReg.Registry

/-!
Review aid: list proven registry entries whose `prop` holds by definitional
unfolding alone. Run with `lake env lean Restating.lean`. The results are
advisory: a documented contract stated independently of the model may
legitimately be definitionally equal to it.

For each proven entry, the `prop` is reduced to weak head normal form and its
`∀`/`→` binders are opened; the conclusion is split into its `∧` conjuncts
(recursively, also under further binders). A conjunct `a = b`, `HEq a b` or
`a ↔ b` is *defeq* when `isDefEq a b` succeeds at default transparency within
`checkHeartbeats` thousand heartbeats (a timeout counts as not defeq); `True`
is always defeq, and `∃ x, P x` is defeq when every conjunct of `P ?x` is,
with `?x` solved by unification (this catches `∃ r, f x = r`). Output:
* `DEFEQ <id>` when every conjunct is defeq;
* `PARTIAL <id> k/n` when `k` of the `n` conjuncts are;
* either line ends with `SAME-AREA-DEFEQ` when some defeq conjunct equates two
  terms whose head constants come from the same area module (`SymReg.<Area>`)
  with at least one a definition, or one side is the other's head definition
  unfolded once: a model equal to another model or to its own body.
The run ends with `DEFEQ-WARNINGS total=N defeq=R partial=P same-area=S` and one
`AREA <area> proven=N defeq=R partial=P same-area=S` line per id prefix.
-/

open Lean Meta

namespace Restating

/-- Id prefixes (before the first `-`) to check; empty checks every area. -/
def onlyAreas : List String := []

/-- Heartbeat budget, in thousands, for each `whnf` or `isDefEq` call. -/
def checkHeartbeats : Nat := 20000

def areaOf (id : String) : String := (id.splitOn "-").headD id

/-- Run `x` with a fresh budget of `checkHeartbeats`; a timeout or error gives `none`. -/
def bounded (x : MetaM α) : MetaM (Option α) :=
  withCurrHeartbeats <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := checkHeartbeats * 1000 }) <|
      tryCatchRuntimeEx (some <$> x) fun _ => pure none

/-- Second component of the module defining `c`, when that module is under `SymReg`. -/
def areaModule (env : Environment) (c : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? c
  let m ← env.header.moduleNames[idx.toNat]?
  match m.components with
  | root :: area :: _ => if root == `SymReg then some area else none
  | _ => none

def headConst (e : Expr) : Option Name := e.consumeMData.getAppFn.constName?

def isDefn (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) => true
  | _ => false

/-- `b` is `a` with its head area definition unfolded once, up to reducible unfolding. -/
def unfoldsTo (a b : Expr) : MetaM Bool := do
  let env ← getEnv
  let some c := headConst a | return false
  unless isDefn env c && (areaModule env c).isSome do return false
  let some a' ← unfoldDefinition? a | return false
  return (← bounded (withReducible (isDefEq a'.headBeta b))).getD false

def sameArea (a b : Expr) : MetaM Bool := do
  let env ← getEnv
  if let (some ca, some cb) := (headConst a, headConst b) then
    if let (some ma, some mb) := (areaModule env ca, areaModule env cb) then
      if ma == mb && (isDefn env ca || isDefn env cb) then return true
  return (← unfoldsTo a b) || (← unfoldsTo b a)

structure Conjunct where
  defeq : Bool
  sameArea : Bool

def compareSides (a b : Expr) : MetaM Conjunct := do
  unless (← bounded (isDefEq a b)).getD false do return ⟨false, false⟩
  return ⟨true, ← sameArea a b⟩

partial def conjuncts (e : Expr) : MetaM (Array Conjunct) := do
  let some e ← bounded (whnf e) | return #[⟨false, false⟩]
  if e.isForall then
    return ← forallTelescope e fun _ body => conjuncts body
  match e.getAppFnArgs with
  | (``And, #[p, q]) => return (← conjuncts p) ++ (← conjuncts q)
  | (``True, #[]) => return #[⟨true, false⟩]
  | (``Eq, #[_, a, b]) => return #[← compareSides a b]
  | (``HEq, #[_, a, _, b]) => return #[← compareSides a b]
  | (``Iff, #[a, b]) => return #[← compareSides a b]
  | (``Exists, #[ty, p]) =>
    let witness ← mkFreshExprMVar ty
    let inner ← conjuncts (p.beta #[witness])
    return #[⟨inner.all (·.defeq) && (← witness.mvarId!.isAssigned), false⟩]
  | _ => return #[⟨false, false⟩]

structure Counts where
  proven : Nat := 0
  defeq : Nat := 0
  partly : Nat := 0
  sameArea : Nat := 0

def Counts.add (c : Counts) (n k : Nat) (same : Bool) : Counts :=
  { proven := c.proven + 1
    defeq := c.defeq + (if k == n then 1 else 0)
    partly := c.partly + (if 0 < k && k < n then 1 else 0)
    sameArea := c.sameArea + (if same then 1 else 0) }

def Counts.fields (c : Counts) : String :=
  s!"defeq={c.defeq} partial={c.partly} same-area={c.sameArea}"

set_option maxHeartbeats 0 in
#eval show MetaM Unit from do
  let mut total : Counts := {}
  let mut areas : Std.HashMap String Counts := {}
  for e in SymReg.Registry.all do
    unless e.status == .proven do continue
    let area := areaOf e.id
    unless onlyAreas.isEmpty || onlyAreas.contains area do continue
    let cs ← withoutModifyingState (conjuncts (mkConst e.prop))
    let n := cs.size
    let k := cs.foldl (fun count c => if c.defeq then count + 1 else count) (0 : Nat)
    let same := cs.any (·.sameArea)
    let hint := if same then " SAME-AREA-DEFEQ" else ""
    if k == n then
      IO.println s!"DEFEQ {e.id}{hint}"
    else if 0 < k then
      IO.println s!"PARTIAL {e.id} {k}/{n}{hint}"
    total := total.add n k same
    areas := areas.insert area ((areas.getD area {}).add n k same)
  for (area, c) in areas.toArray.qsort (·.1 < ·.1) do
    IO.println s!"AREA {area} proven={c.proven} {c.fields}"
  IO.println s!"DEFEQ-WARNINGS total={total.proven} {total.fields}"

end Restating
