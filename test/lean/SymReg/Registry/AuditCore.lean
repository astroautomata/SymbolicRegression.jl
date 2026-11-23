import Lean
import DynExpr.Registry.Types
import SymReg.Registry.Generality

/-!
Registry audit, used by `Audit.lean`. The checks are those of the DynamicExpressions
formalization's `Audit.lean`:

* ids are unique;
* status is `proven`, `refuted` or `todo` (an open property, printed as `TODO <id>` and
  counted without failing); `stuck` fails;
* `prop` is a closed, universe-monomorphic `Prop` constant;
* `thm` is a theorem whose type is `prop` (proven) or `¬ prop` (refuted);
* `thm` depends only on `propext`, `Classical.choice`, `Quot.sound`, and
  axioms declared in `DynExpr.Runtime.Axioms`;
* every property quantifies over at least one data variable (no single worked
  examples), except ids in `staticFacts`, which are printed as `STATIC` lines for review.

It prints `COVER-FILE`, `COVER-FN`, and `REFUTED` lines consumed by `scripts/run-repros.sh`.
-/

namespace SymReg.Registry
open Lean Meta DynExpr.Registry

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def runtimeAxiomModule : Name := `DynExpr.Runtime.Axioms

def axiomAllowed (env : Environment) (ax : Name) : Bool :=
  standardAxioms.contains ax ||
    match env.getModuleIdxFor? ax with
    | some idx => env.header.moduleNames[idx.toNat]? == some runtimeAxiomModule
    | none => false

/-- Audit `entries`; throws if any check fails. -/
def audit (entries : List Entry) (staticFacts : List String) : MetaM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  let mut seen : Std.HashSet String := {}
  let mut counts : Std.HashMap String Nat := {}
  for e in entries do
    let statusName := toString (repr e.status)
    counts := counts.insert statusName (counts.getD statusName 0 + 1)
    if seen.contains e.id then
      failures := failures.push s!"{e.id}: duplicate id"
    seen := seen.insert e.id
    IO.println s!"COVER-FILE {e.juliaFile}"
    for fn in e.juliaFns do
      IO.println s!"COVER-FN {fn}"
    match e.status with
    | .stuck =>
      failures := failures.push s!"{e.id}: status {statusName}"
      continue
    | .todo | .proven | .refuted => pure ()
    let some propInfo := env.find? e.prop
      | failures := failures.push s!"{e.id}: prop {e.prop} not found"; continue
    unless propInfo.levelParams.isEmpty do
      failures := failures.push s!"{e.id}: prop {e.prop} has universe parameters"
      continue
    let propExpr := mkConst e.prop
    unless ← isProp propExpr do
      failures := failures.push s!"{e.id}: {e.prop} is not a Prop"
      continue
    if staticFacts.contains e.id then
      IO.println s!"STATIC {e.id}: {e.statement}"
    else if (← countForallData 6 propExpr) == 0 then
      failures := failures.push s!"{e.id}: property quantifies over no input"
    if e.status == .todo then
      IO.println s!"TODO {e.id}"
      continue
    let some thm := e.thm
      | failures := failures.push s!"{e.id}: settled entry has no theorem"; continue
    let some (.thmInfo thmInfo) := env.find? thm
      | failures := failures.push s!"{e.id}: theorem {thm} not found"; continue
    unless thmInfo.levelParams.isEmpty do
      failures := failures.push s!"{e.id}: theorem {thm} has universe parameters"
      continue
    let expected := if e.status == .proven then propExpr else mkNot propExpr
    unless ← isDefEq thmInfo.type expected do
      failures := failures.push s!"{e.id}: type of {thm} is not {expected}"
      continue
    let axioms ← collectAxioms thm
    for ax in axioms do
      unless axiomAllowed env ax do
        failures := failures.push s!"{e.id}: {thm} uses disallowed axiom {ax}"
    if e.status == .refuted then
      IO.println s!"REFUTED {e.id}"
  for (k, v) in counts.toList do
    IO.println s!"STATUS {k} {v}"
  IO.println s!"ENTRIES {entries.length}"
  unless failures.isEmpty do
    for f in failures do
      IO.println s!"FAIL {f}"
    throwError m!"audit failed with {failures.size} problem(s)"
  IO.println "AUDIT OK"

end SymReg.Registry
