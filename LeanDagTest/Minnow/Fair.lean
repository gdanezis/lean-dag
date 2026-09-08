import LeanDagTest.Minnow.Deadlock
import Mathlib.Data.Fin.VecNotation
/-!
# Minnow — the dead zone is a defect of the pair, not of the rule alone

The witness of `report.md` §19.5. `Deadlock` exhibits a DAG in which
`crs*` commits nothing; this file holds that DAG fixed and varies only
the leader sequence.

The habit of the Byzantine process is unchanged: every vertex it issues
reaches process `1` alone, so every vertex it issues sits in the dead
zone — two pointers of four, too few to commit and too many to skip. What
changes is `leaders`. `report.md` §19.4 takes round robin at `l = 2`,
which puts the Byzantine process in a leader slot **every other round**;
here it is round robin at `l = 1`, which puts it in one round in four.

A dead slot is out of reach for exactly two rounds of leaders — its own,
where there is no causal path either way, and the one above, whose
leaders need not hold it. From two rounds up it lies in every causal
past, because a vertex references `2f + 1` of the `3f + 1` below it and
the dead vertex has `f + 1` pointers there, so the two sets meet. A
schedule that offers two consecutive rounds whose leader slots are all
correct therefore commits at the second of them, and `l = 1` round robin
offers three such rounds after every Byzantine one.

That is what is checked below: the round-1 leader is blocked by the dead
slot exactly as in the report's §19.4, and the round-2 leader commits.

**What this costs the finding, and what it does not.** It costs the word
*outright*: Live-Commit fails for `crs*` paired with a multi-leader round
robin rather than for `crs*` alone. It does not cost the finding. The
paper's Lemma 11 claims each leader slot is eventually *decided*, and the
dead slot is decided in no view under any schedule. And the escape that
rescues liveness here is the causal-past disjunct — a slot resolved by a
vertex that is never committed — which is exactly the disjunct that
`report.md` §19.3 shows to be unsound where a slot holds two vertices.
The rule is live under a fair schedule by the mechanism that costs it
safety under an equivocating one.
-/

namespace LeanDagTest

namespace Minnow

open LeanDag LeanDag.Minnow

set_option maxRecDepth 4000000

/-- **Round robin at `l = 1`**, one leader a round. The offset is chosen
so that the round-1 leader is a process the Byzantine one did **not**
send to — the case `report.md` §19.4 arranges at every round, and the
one this file has to survive to be worth stating. -/
def mFair (k : ℕ) : Slot (Fin 4) := (![0, 2, 3, 1] ⟨k % 4, Nat.mod_lt _ (by omega)⟩, k)

/-- It is a genuine rotation: every window of four consecutive rounds
gives every process the lead exactly once. -/
example : ∀ k ∈ Finset.range 8,
    Finset.image (fun i => (mFair (k + i)).1) (Finset.range 4) = Finset.univ := by decide

/-- The slots it names over the six rounds of `Dm`. -/
example : slotBlocks Dm (mFair 0) = {0} ∧ slotBlocks Dm (mFair 1) = {6} ∧
    slotBlocks Dm (mFair 2) = {11} ∧ slotBlocks Dm (mFair 3) = {13} := by decide

/-! ## The DAG is the one of `report.md` §19.4, and the slot is still dead

Nothing about the Byzantine process's habit changes, so nothing about the
dead zone changes either. -/

example : pointers Dm 0 1 = {0, 1} ∧ ¬ Quorum Dm 0 ∧ ¬ Skipped Dm 0 := by decide

/-! ## The first correct leader after it is blocked, exactly as before

Process `2` never received the dead vertex, so it is not in the causal
past of process `2`'s round-1 vertex, and the slot is neither committed
nor skipped. This is the report's §19.4 step 4, and the fair schedule does not
escape it. -/

example : ¬ Reaches Dm 6 0 := by decide

example : ¬ CommittedAt Dm mFair 1 6 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

/-! ## The second commits

Two rounds up, the dead vertex is in every causal past — through process
`1`'s round-1 vertex, which did point to it — and the round-1 slot is in
the round-2 leader's causal past directly. Both disjuncts of the second
condition are met without either slot being decided. -/

example : Reaches Dm 11 0 ∧ Reaches Dm 11 6 ∧ Quorum Dm 11 := by decide

/-- **The round-2 leader commits**, with the dead slot below it still
undecided in every view. -/
example : CommittedAt Dm mFair 2 11 := by
  simp only [CommittedAt]
  refine ⟨by decide, ?_⟩
  intro j hj
  interval_cases j
  · exact ⟨0, by decide, Or.inl (by decide)⟩
  · exact ⟨6, by decide, Or.inl (by decide)⟩

/-- And so does the one after it, so this is a chain and not one commit.
-/
example : CommittedAt Dm mFair 3 13 := by
  simp only [CommittedAt]
  refine ⟨by decide, ?_⟩
  intro j hj
  interval_cases j
  · exact ⟨0, by decide, Or.inl (by decide)⟩
  · exact ⟨6, by decide, Or.inl (by decide)⟩
  · exact ⟨11, by decide, Or.inl (by decide)⟩

/-- So `crs*` on this DAG delivers a non-empty output, which is what
the report's §19.4 schedule denies it. -/
example : CommittedAt Dm mFair 2 11 ∧ CommittedAt Dm mFair 3 13 ∧
    ¬ CommittedAt Dm mFair 1 6 :=
  ⟨by
    simp only [CommittedAt]
    refine ⟨by decide, ?_⟩
    intro j hj
    interval_cases j
    · exact ⟨0, by decide, Or.inl (by decide)⟩
    · exact ⟨6, by decide, Or.inl (by decide)⟩,
   by
    simp only [CommittedAt]
    refine ⟨by decide, ?_⟩
    intro j hj
    interval_cases j
    · exact ⟨0, by decide, Or.inl (by decide)⟩
    · exact ⟨6, by decide, Or.inl (by decide)⟩
    · exact ⟨11, by decide, Or.inl (by decide)⟩,
   not_committedAt_of_dead (j := 0) (by omega) (by decide)⟩

end Minnow

end LeanDagTest
