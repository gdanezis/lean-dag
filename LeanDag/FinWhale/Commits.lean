import LeanDag.FinWhale.Model.Liveness
import LeanDag.FinWhale.Decision
/-!
# FinWhale — the commits §10's liveness carries

`CommitsCorrectLeaders` gives a committed block at every reliably led
slot in range, and `SeesCommits` is the same read by a validator holding
the whole universe. Both are statements about the DAG and the direct
rules; no verdict assignment appears.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId]
variable {Payload : Type} {D : Dag Validator BlockId Payload} {S : Slots Validator}

/-- The commit the interface carries. -/
theorem directCommit_of_commits {R N : ℕ} (h : CommitsCorrectLeaders S D R N) {s : ℕ}
    (hR : R ≤ S.slotRound s) (hN : S.slotRound s + 2 ≤ N)
    (hlead : S.leader s ∈ (Correct : Finset Validator)) :
    ∃ l ∈ slotBlocks S D s, DirectCommit D l := by
  obtain ⟨l, hslot, hby⟩ := h s hR hN hlead
  exact ⟨l, hslot, Or.inr (spCommit_of_spCommitBy hby)⟩

/-- A validator reading the whole universe sees them all. -/
theorem sees_of_commits {R N : ℕ} (h : CommitsCorrectLeaders S D R N) :
    SeesCommits S D (fun r l => l ∈ slotBlocks S D r ∧ DirectCommit D l) R N := by
  intro s hR hN hlead
  obtain ⟨l, hslot, hcom⟩ := directCommit_of_commits h hR hN hlead
  exact ⟨l, hslot, hslot, hcom⟩

end FinWhale

end LeanDag
