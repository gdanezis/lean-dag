import LeanDag.FinWhale.Model.Skip
import Mathlib.Data.Fintype.Powerset
import LeanDag.Common.Leader

/-!
# FinWhale — the direct decision rule

A slot is decided directly by one of two verdicts. It is **committed**
when a block of the slot carries `n − p` votes one round up (the fast
path) or a quorum of SP-certificates two rounds up (the slow path), and
**skipped** when both halves of `Model/Skip.lean` hold at once.
`slotBlocks` names the blocks a slot holds, of which there is more than
one where the leader equivocates.

`SPCommitBy` is `SPCommit` with its certificates confined to a named set
of validators. The liveness routes produce it at `T = Correct`, which is
what a validator's view can be shown to hold.

`Decision.lean` proves what these verdicts exclude.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- The blocks of the leader slot of round `r`. There may be several, if
the leader equivocates. -/
abbrev slotBlocks (S : Slots Validator) (D : Dag Validator BlockId Payload) (k : ℕ) :
    Finset BlockId :=
  leaderBlocksAt (S := S) D k

/-- **The slow-path direct commit**: a quorum of SP-certificates from
distinct validators at round `r + 2`. -/
def SPCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  ∃ certs : Finset Validator, spQuorum Validator ≤ certs.card ∧
    ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l

set_option synthInstance.maxSize 1000 in
instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (SPCommit D l) := by unfold SPCommit; infer_instance

/-- **A slow-path commit witnessed by `T`**: the certificates it counts
are blocks of validators in `T`. `SPCommit` is this without the
restriction; the liveness routes produce it at `T = Correct`, which is
what a validator's view can be shown to hold. -/
def SPCommitBy (D : Dag Validator BlockId Payload) (l : BlockId) (T : Finset Validator) : Prop :=
  ∃ certs ⊆ T, spQuorum Validator ≤ certs.card ∧
    ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l

/-- **The direct commit rule**: either path. -/
def DirectCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  FastCommit D l ∨ SPCommit D l

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (DirectCommit D l) := inferInstanceAs (Decidable (_ ∨ _))

/-- **The direct skip rule**: an SP-skip pattern at every block of the
slot, and a quorum of Non-FP-evidence blocks at round `r + 2`. -/
def DirectSkip (S : Slots Validator) (D : Dag Validator BlockId Payload) (k : ℕ) : Prop :=
  (∀ l ∈ slotBlocks S D k, SPSkip D l) ∧
    ∃ nonev : Finset Validator, spQuorum Validator ≤ nonev.card ∧
      ∀ v ∈ nonev, ∃ b ∈ blocksAt D (S.slotRound k + 2),
        (D.block b).creator = v ∧ NonFPEvidence D b (slotBlocks S D k)

set_option synthInstance.maxSize 1000 in
instance (S : Slots Validator) (D : Dag Validator BlockId Payload) (k : ℕ) :
    Decidable (DirectSkip S D k) := by unfold DirectSkip; infer_instance

end FinWhale

end LeanDag
