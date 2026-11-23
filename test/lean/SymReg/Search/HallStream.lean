import SymReg.Search.StateProofs
import SymReg.HofMig.Frontier
import DynExpr.Registry.Types

namespace SymReg.Search
open DynExpr
open SymReg.HofMig

-- Source: src/SymbolicRegression.jl:913-921,1156-1165
-- if !isnothing(guesses)
--     parsed_seed_members = parse_guesses(
--         eltype(state.halls_of_fame[1]), guesses, datasets, options
--     )
--     for j in 1:nout
--         state.seed_members[j] = copy(parsed_seed_members[j])
--         update_hall_of_fame!(state.halls_of_fame[j], parsed_seed_members[j], options)
--     end
-- end
-- update_hall_of_fame!(state.halls_of_fame[j], cur_pop.members, options)
-- update_hall_of_fame!(state.halls_of_fame[j], best_seen.members[best_seen.exists], options)
-- dominating = calculate_pareto_frontier(state.halls_of_fame[j])

/-- Projection onto one output and onto successfully collected worker replies, in
head order. The initial hall has already been created or restored and rescored. -/
def accumulateHall (maxsize : Nat) (compute : Nat → Int) (check : Member → Int → Int → Jl Bool)
    (initial : Hof) (fresh : Nat) (guesses : List Member) (replies : List Reply) : Jl (Hof × Nat) := do
  let (initial, _, fresh) ← updateManyChecked initial guesses maxsize fresh compute check
  replies.foldlM (fun (h, f) reply => (mergeResult h reply maxsize f compute check).map
    (fun r => (r.1, r.2.2))) (initial, fresh)

private def collectedMembers (r : Reply) : List Member :=
  r.population ++ (r.bestSeen.slots.filter Slot.exists).map Slot.member

private theorem fold_reduces (maxsize : Nat) (compute : Nat → Int)
    (check : Member → Int → Int → Jl Bool) (replies : List Reply) (h : Hof) (f : Nat) :
    replies.foldlM (fun (hall, supply) reply => (mergeResult hall reply maxsize supply compute check).map
      (fun r => (r.1, r.2.2))) (h, f) =
    (updateManyChecked h (replies.flatMap collectedMembers) maxsize f compute check).map
      (fun r => (r.1, r.2.2)) := by
  induction replies generalizing h f with
  | nil => rfl
  | cons reply rest ih =>
    simp only [List.foldlM_cons, List.flatMap_cons]
    rw [checked_many_append_holds, merge_stream_holds]
    cases hm : updateManyChecked h (collectedMembers reply) maxsize f compute check with
    | error e =>
      have hm' : updateManyChecked h
          (reply.population ++ (reply.bestSeen.slots.filter Slot.exists).map Slot.member)
          maxsize f compute check = .error e := hm
      simp [hm', bind, Except.bind, Except.map]
    | ok p =>
      rcases p with ⟨h', left, f'⟩
      have hm' : updateManyChecked h
          (reply.population ++ (reply.bestSeen.slots.filter Slot.exists).map Slot.member)
          maxsize f compute check = .ok (h', left, f') := hm
      simp only [hm', bind, Except.bind, Except.map]
      have hi := ih h' f'
      cases hr : updateManyChecked h' (List.flatMap collectedMembers rest) maxsize f' compute check <;>
        simpa only [hr, bind, Except.bind, pure, Except.pure, Except.map] using hi

/-- Every in-range slot chooses the lowest checked cost in the stream for that
output, including guesses and the restored incumbent. Ties retain the incumbent;
an incumbent NaN is not ordered below or above another cost. -/
def hall_stream_best : Prop :=
  ∀ (maxsize k fresh : Nat) (initial : Hof) (guesses : List Member) (replies : List Reply)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
    k < initial.slots.length →
    (accumulateHall maxsize compute check initial fresh guesses replies).map (fun out => slotPayload out.1 k) =
    bestChecked k maxsize compute check (slotPayload initial k)
      (guesses ++ replies.flatMap collectedMembers)

theorem hall_stream_best_holds : hall_stream_best := by
  intro maxsize k fresh initial guesses replies compute check hk
  have h := checked_all_slots_best_seen_holds initial (guesses ++ replies.flatMap collectedMembers)
    maxsize fresh k compute check hk
  rw [checked_many_append_holds] at h
  unfold accumulateHall
  cases hs : updateManyChecked initial guesses maxsize fresh compute check with
  | error e => simpa [hs, bind, Except.bind, Except.map] using h
  | ok a =>
    rcases a with ⟨hall, seeds, supply⟩
    simp only [hs, bind, Except.bind] at h ⊢
    rw [fold_reduces]
    cases hr : updateManyChecked hall (List.flatMap collectedMembers replies) maxsize supply compute check <;>
      simpa [hr, pure, Except.pure, Except.map] using h

example : 0 < (⟨[⟨specimen (.fin 0) (.fin 1), false⟩]⟩ : Hof).slots.length := by decide

/-- The frontier omits a winning slot if an earlier occupied slot has an equal or
smaller loss. It retains the loss, cost and tree payloads of the remaining winners. -/
def hall_stream_frontier : Prop :=
  ∀ (maxsize fresh : Nat) (initial : Hof) (guesses : List Member) (replies : List Reply)
    (compute : Nat → Int) (check : Member → Int → Int → Jl Bool),
    (accumulateHall maxsize compute check initial fresh guesses replies).map
      (fun (h, f) => (calculatePareto h f).1.map payload) =
    (accumulateHall maxsize compute check initial fresh guesses replies).map
      (fun (h, _) => (frontSpec [] h.slots).map payload)

theorem hall_stream_frontier_holds : hall_stream_frontier := by
  intro maxsize fresh initial guesses replies compute check
  cases hr : accumulateHall maxsize compute check initial fresh guesses replies with
  | error e => rfl
  | ok p =>
    obtain ⟨h, f⟩ := p
    simp only [Except.map, Except.ok.injEq]
    exact (frontier_exact_holds h f).1

open DynExpr.Registry in
def hallStreamEntries : List Entry := [
  { id := "search-hall-best-collected", juliaFile := "src/SymbolicRegression.jl",
    juliaFns := ["_initialize_search!", "_main_search_loop!"],
    statement := "At each complexity slot in one output's hall, the saved incumbent, guesses, collected populations, and collected cycle winners compete in arrival order using the checked cost comparison.",
    preconditions := "Existing slot; guesses are parsed and the initial hall has been restored and rescored or newly created.",
    status := .todo, prop := ``hall_stream_best
    notes := "Needs actual per-output receipts, initial guesses, prior hall state and intervening hook writes." },
  { id := "search-collected-pareto-frontier", juliaFile := "src/SymbolicRegression.jl",
    juliaFns := ["_main_search_loop!"],
    statement := "The frontier of the accumulated output hall contains its occupied non-NaN winners whose losses are not greater than or equal to any earlier occupied slot's loss.",
    preconditions := "Parsed guesses and already restored/rescored or newly created starting hall.",
    status := .proven, prop := ``hall_stream_frontier, thm := some ``hall_stream_frontier_holds }
]

end SymReg.Search
