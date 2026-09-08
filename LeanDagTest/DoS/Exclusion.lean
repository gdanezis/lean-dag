import LeanDagTest.Mysticeti.Growth
import LeanDag.DoS.Exclusion
import LeanDag.DoS.Counting
import Mathlib.Tactic.IntervalCases
/-!
# Liveness survives exclusion, end to end

`dos-equivocation-and-growth.md` §8 and §7 S8. The witness that makes the
chain true of something rather than merely stated:

> exclusion bites → the correct set still meets `2f+1` → blocks keep being
> produced → a slot with a correct leader commits.

`Uexcl` runs six rounds over `Fin 4` with `f = 1`, so `|Correct| = 3 = 2f+1`
**exactly** — the tightest possible case, with no margin to spare from round 2
onward:

```
  round 0   ids 0-3    genesis by validators 0,1,2,3
            id  4      a SECOND genesis by validator 0      -- the equivocation
  round 1   id  5      by 1, refs {0,1,2,3}                 -- the A branch
            id  6      by 2, refs {4,1,2,3}                 -- the B branch
            id  7      by 3, refs {1,2,3}                   -- neither
  round 2   ids 8-10   by 1,2,3, refs {5,6,7}               -- the MERGE
  round 3   ids 11-13  by 1,2,3, refs {8,9,10}
  round 4   ids 14-16  by 1,2,3, refs {11,12,13}
  round 5   ids 17-19  by 1,2,3, refs {14,15,16}
```

From round 2 the merge exposes validator 0, so no block may name it again
(D12). The three correct validators carry the DAG alone from there — and
`fairSlots` puts slot 1 at round 3, so **the commit happens entirely after the
exclusion has taken hold**, using rounds 3, 4 and 5. That is the point: the
protocol does not merely survive exclusion, it keeps deciding under it.

Note what is *not* claimed. `Uexcl` is finite, so it witnesses one commit
rather than commits forever; L6 needs a family indexed by the horizon, which is
6b's business once `Delivery` can be stated honestly for an equivocating DAG.
-/

namespace LeanDagTest

open LeanDag

/-! ## The model -/

def lkx : Fin 20 → Block (Fin 4) (Fin 20) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 4 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if (i : ℕ) = 5 then
    { round := 1, creator := 1, refs := {0, 1, 2, 3}, payload := () }
  else if (i : ℕ) = 6 then
    { round := 1, creator := 2, refs := {4, 1, 2, 3}, payload := () }
  else if (i : ℕ) = 7 then
    { round := 1, creator := 3, refs := {1, 2, 3}, payload := () }
  else if h : (i : ℕ) < 11 then
    { round := 2, creator := ⟨(i : ℕ) - 7, by omega⟩, refs := {5, 6, 7}, payload := () }
  else if h : (i : ℕ) < 14 then
    { round := 3, creator := ⟨(i : ℕ) - 10, by omega⟩, refs := {8, 9, 10}, payload := () }
  else if h : (i : ℕ) < 17 then
    { round := 4, creator := ⟨(i : ℕ) - 13, by omega⟩, refs := {11, 12, 13}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 16, by have := i.isLt; omega⟩,
      refs := {14, 15, 16}, payload := () }

def Uexcl : BlockUniverse (Fin 4) (Fin 20) Unit where
  ids := Finset.univ
  block := lkx
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## Exclusion bites from round 2 -/

-- Validator 0 equivocates; neither branch alone reveals it.
example : (Uexcl.block 0).creator = (Uexcl.block 4).creator := by decide
example : ¬ ExposedIn Uexcl 5 0 := by decide
example : ¬ ExposedIn Uexcl 6 0 := by decide

-- The merge does, and by D12 so does everything above it.
example : ExposedIn Uexcl 8 0 := by decide
example : ExposedIn Uexcl 11 0 := by decide
example : ExposedIn Uexcl 17 0 := by decide

/-- And nobody else is ever exposed: exclusion lands only on the guilty
(D15). -/
example : ∀ b ∈ Uexcl.ids, ∀ X : Fin 4, ExposedIn Uexcl b X → X = 0 := by decide

theorem uexcl_dosValid : DoSValid Uexcl := by decide

/-! ## D15a — the margin is gone, and that is the whole point

Validator 0 is the entire fault budget, so from round 2 the exposed set has
caught all of it and `creators_refs_eq_correct` applies: the references of
every block from round 3 on are **exactly** the correct validators. Not by
choice of the model — by theorem. -/

example : exposedTo Uexcl 11 = {0} := by decide
example : (exposedTo Uexcl 11).card = Faults.f (Fin 4) := by decide

/-- **D15a at the bound, applied.** -/
example : creatorsOf Uexcl.block (Uexcl.block 11).refs = (Correct : Finset (Fin 4)) :=
  creators_refs_eq_correct uexcl_dosValid (by decide) (by decide) (by decide)

example : (Correct : Finset (Fin 4)) = {1, 2, 3} := by decide

/-! ## D15b — and the threshold is still met

The correct blocks of each round carry a quorum of authors, none of them
excluded. This is what keeps the DAG buildable at zero margin. -/

theorem uexcl_populated (r : ℕ) (h : r ≤ 5) : Populated Uexcl r := by
  interval_cases r <;> decide

/-- **D15b applied**, at the round the commit's certificates come from. -/
example : (Fintype.card (Fin 4) - Faults.f (Fin 4)) ≤ (creatorsOf Uexcl.block (correctBlocksAt Uexcl 5)).card ∧
    ∀ i ∈ correctBlocksAt Uexcl 5, (Uexcl.block i).creator ∉ exposedTo Uexcl 17 :=
  correctBlocksAt_admissible_quorum (uexcl_populated 5 (by omega)) (by decide)

/-! ## And a commit, after the exclusion

`fairSlots` (from `LeanDagTest.Growth`) leads every slot with validator 1 and
puts slot `k` at round `3k`. Slot 1 therefore sits at round 3, and its three
rounds — 3, 4 and 5 — are all past the merge. L4 fires with `T = {1,2,3}`,
which is `2f+1` validators exactly. -/

theorem uexcl_synchronised : SynchronisedOn Uexcl {1, 2, 3} 0 := by
  -- `SynchronisedOn` quantifies over every round, so it is not decidable as
  -- stated; the content is a decidable fact about pairs of blocks.
  have key : ∀ b ∈ Uexcl.ids, ∀ a ∈ Uexcl.ids,
      (Uexcl.block a).round + 1 = (Uexcl.block b).round →
      (Uexcl.block b).creator ∈ ({1, 2, 3} : Finset (Fin 4)) →
      (Uexcl.block a).creator ∈ ({1, 2, 3} : Finset (Fin 4)) →
      a ∈ (Uexcl.block b).refs := by decide
  intro _ _ b hb hbr hbc a ha har hac
  exact key b hb a ha (by omega) hbc hac

/-- **The chain closes.** A slot whose rounds lie entirely after validator 0's
exclusion is still directly committed, by L4, with the correct validators
supplying the whole quorum. -/
theorem uexcl_commits :
    ∃ L, IsLeaderBlock Uexcl 1 L ∧ DirectCommit Uexcl L (fairSlots.slotRound 1) :=
  directCommit_of_leader_mem (T := {1, 2, 3}) (by decide) uexcl_synchronised (by decide)
    (uexcl_populated 3 (by omega) |>.mono (by decide))
    (uexcl_populated 4 (by omega) |>.mono (by decide))
    (uexcl_populated 5 (by omega) |>.mono (by decide))
    (by decide)

/-- And as a decision, which is what a reconfiguration would be carried by. -/
theorem uexcl_decided :
    ∃ L, IsLeaderBlock Uexcl 1 L ∧ Decided Uexcl (View.full Uexcl) 1 (some L) :=
  decided_of_leader_mem (T := {1, 2, 3}) (by decide) uexcl_synchronised (by decide)
    (uexcl_populated 3 (by omega) |>.mono (by decide))
    (uexcl_populated 4 (by omega) |>.mono (by decide))
    (uexcl_populated 5 (by omega) |>.mono (by decide))
    (by decide)

#print axioms uexcl_dosValid
#print axioms uexcl_commits
#print axioms uexcl_decided

end LeanDagTest
