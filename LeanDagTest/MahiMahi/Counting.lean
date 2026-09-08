import LeanDagTest.Mysticeti.Model
import LeanDag.MahiMahi.Counting.Statement
/-!
# Mahi-Mahi witnesses — the counting lemma on data

`goodAt`, the common core, and the statement hypotheses of
`Counting/Statement.lean` settled by `decide` on the **aiming pattern**
of `mahi-mahi.md` §5.1: an adversary that knows slot `1`'s leader keeps
that leader's block out of every cone it can. Two witnesses:

* `aim4` — at `w = 4` the targeted leader is exactly the validator that
  is not good, and the survivors are the common core's neighbourhood; at
  `w = 5` the extra round reaches the starved block again;
* `multi` — three distinct leaders per round (`2f + 1 = 3`) always include
  a good one, the conclusion of MM2b as an explicit slot.

Same committee as `Model.lean` (validator `0` Byzantine, `f = 1`, quorum
`3`); the schedules are local instances.
-/

namespace LeanDagTest

open LeanDag

/-- Round-robin, one leader per round. -/
local instance mmSlotsC : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-! ## `aim4` — the aiming pattern against slot `1` -/

/-- Block `4m + v` is validator `v`'s round-`m` block. The target is
block `5`, validator `1`'s round-`1` block. Round `2`: only validator
`1` itself references `5` (its self-parent); the others reference
`{4, 6, 7}`. Round `3`: validator `1` must reference its own block `9`
and so reaches `5`; the others reference `{8, 10, 11}` and do not.
Rounds `4` and `5` reference the whole round below. -/
def mmAimBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩,
      refs := {0, 1, 2, 3}, payload := () }
  else if h : (i : ℕ) = 9 then
    { round := 2, creator := 1, refs := {4, 5, 6}, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩,
      refs := {4, 6, 7}, payload := () }
  else if h : (i : ℕ) = 13 then
    { round := 3, creator := 1, refs := {9, 10, 11}, payload := () }
  else if h : (i : ℕ) < 16 then
    { round := 3, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := {8, 10, 11}, payload := () }
  else if h : (i : ℕ) < 20 then
    { round := 4, creator := ⟨(i : ℕ) - 16, by omega⟩,
      refs := {12, 13, 14, 15}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 20, by have := i.isLt; omega⟩,
      refs := {16, 17, 18, 19}, payload := () }

/-- The aiming pattern is a valid universe: every block references a
quorum including its own author's, and nobody equivocates. Validity is
what makes the pattern available to an asynchronous adversary. -/
def aim4 : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := mmAimBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ### The target at `w = 4` -/

-- Slot `1` is led by validator `1`, whose block is `5`.
example : IsLeaderBlock aim4 1 5 := by decide

-- Only validator `1`'s round-`3` block votes for it; the other three blame
-- the slot, so it is not committed — it is directly skipped.
example : MahiMahi.Votes aim4 13 5 := by decide
example : MahiMahi.Blames aim4 12 1 1 := by decide
example : ¬ MahiMahi.DirectCommit aim4 4 5 1 := by decide
example : MahiMahi.DirectSkip aim4 4 1 1 := by decide

-- The good validators at round `1` are everyone but the target: the
-- leader round-robin names is exactly the one the adversary starved.
example : MahiMahi.goodAt aim4 4 1 = {0, 2, 3} := by decide
example : (1 : Fin 4) ∉ MahiMahi.goodAt aim4 4 1 := by decide
example : MahiMahi.good aim4 4 1 = {0, 2, 3} := by decide

/-! ### The common core on data -/

-- Block `6` (validator `2`, round `1`) is referenced by every round-`2`
-- block, and so lies in the cone of every block at every round `≥ 3`.
example : ∀ c : Fin 24, 3 ≤ (aim4.block c).round → 6 ∈ history aim4 c := by decide

-- Its author is correct and good — the witness `GoodNonempty` names.
example : (2 : Fin 4) ∈ MahiMahi.goodAt aim4 4 1 ∩ (Correct : Finset (Fin 4)) := by decide

/-! ### Five rounds reach the starved block again -/

-- At `w = 5` the voting round is `4`, every round-`4` block reaches `5`
-- through block `13`, and the target is committed: `good` is everyone.
example : MahiMahi.DirectCommit aim4 5 5 1 := by decide
example : MahiMahi.goodAt aim4 5 1 = Finset.univ := by decide

/-! ### The statement hypotheses hold on `aim4` -/

-- Population at the rounds the statements read, for the reliable set
-- `T = Correct = {1, 2, 3}`.
example : PopulatedOn aim4 (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide
example : PopulatedOn aim4 (Correct : Finset (Fin 4)) 4 := by
  unfold PopulatedOn; decide
example : PopulatedOn aim4 (Correct : Finset (Fin 4)) 5 := by
  unfold PopulatedOn; decide
example : MahiMahi.decisionRoundAt 4 1 = 4 := by decide
example : MahiMahi.decisionRoundAt 5 1 = 5 := by decide

-- `GoodCard` at `w = 5`, on data: `3 ≤ |good ∩ Correct| + |byzantine|`.
example : quorumCard (Fin 4) ≤
    (MahiMahi.goodAt aim4 5 1 ∩ (Correct : Finset (Fin 4))).card +
      (Faults.byzantine (Validator := Fin 4)).card := by
  decide

/-! ## `multi` — three leaders per round -/

/-- Three slots per round, led by validators `0`, `1`, `2` in turn:
slots `3k, 3k+1, 3k+2` sit at round `k`. The `hblock` obligation is that
the three leaders of a round are distinct, which `k % 3` supplies. -/
@[reducible] def mmMultiSlots : Slots (Fin 4) :=
  Slots.uniform 1 3 (by omega) (by omega) (fun k => ⟨k % 3, by omega⟩)
    (fun k₁ k₂ h₁ h₂ => by
      have : k₁ % 3 = k₂ % 3 := by simpa using congrArg Fin.val h₂
      omega)

-- At round `1` the slots are `3, 4, 5`, led by `0, 1, 2`; slot `3` is good
-- at `w = 5` (and, on this DAG, already at `w = 4`).
example : mmMultiSlots.slotRound 3 = 1 ∧ mmMultiSlots.leader 3 = 0 := by decide
example : mmMultiSlots.leader 3 ∈ MahiMahi.good (S := mmMultiSlots) aim4 5 3 := by decide
example : mmMultiSlots.leader 3 ∈ MahiMahi.good (S := mmMultiSlots) aim4 4 3 := by decide

-- The conclusion of `MultiLeader` as an explicit slot.
example : ∃ k, mmMultiSlots.slotRound k = 1 ∧
    mmMultiSlots.leader k ∈ MahiMahi.good (S := mmMultiSlots) aim4 5 k :=
  ⟨3, by decide, by decide⟩

/-! ## Axioms -/

#print axioms aim4

end LeanDagTest
