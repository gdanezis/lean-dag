import LeanDag.Checkpoint.CommitSpec

/-!
# Machine-checked commit-to-checkpoint derivations

This file proves the claims stated at the end of `CommitSpec.lean`.
Every statement here is either one of those claims or an internal
construction; nothing in this file needs human review beyond the claim
names it proves.
-/

namespace LeanDag.Checkpoint

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} {Value : Type*}
variable {R : DagRule Validator BlockId Payload}

namespace SigningFaults

variable (M : SigningFaults Validator)

namespace Execution

variable (E : M.Execution Value)
variable {S : Slots Validator} {U : R.Universe}
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

/-- The tie between a commit and a proposal: a validator that settled
the slot on its own view proposed the checkpoint of the given commit,
because agreement makes its verdict equal the commit. -/
theorem emitted_of_decided (ha : Agree R) (P : SigningRule M E R S U vm)
    {V : R.View U} {slot : ℕ} {block : BlockId}
    (commit : R.Decided S V slot (some block))
    {v : Validator} (hv : v ∈ M.recoveryCorrect) {b : BlockId}
    (hb : R.Decided S (P.view v) slot (some b)) :
    E.emitted ⟨v, vm.checkpointAfterCommit slot block⟩ := by
  have heq : b = block := Option.some.inj (ha S (P.view v) V slot _ _ hb commit)
  subst heq
  exact P.proposes v hv hb

/-- Construction behind `CommitCertified`: the online correct validators
are the signers, each by `emitted_of_decided`. -/
def checkpointQCOfDecided (ha : Agree R) (P : SigningRule M E R S U vm)
    {V : R.View U} {slot : ℕ} {block : BlockId}
    (commit : R.Decided S V slot (some block))
    (hall : ∀ v ∈ M.recoveryCorrect, ∃ b, R.Decided S (P.view v) slot (some b)) :
    SigningFaults.Execution.CheckpointQC M E
      (vm.checkpointAfterCommit slot block) where
  signers := M.recoveryCorrect
  quorum := P.quorum
  messages := by
    intro v hv
    obtain ⟨b, hb⟩ := hall v hv
    exact emitted_of_decided M E vm ha P commit hv hb

/-- Construction behind `CommitFinalized`: every signer of the
certificate above also witnesses it, by the rule's second clause. -/
def finalityQCOfDecided (ha : Agree R) (P : SigningRule M E R S U vm)
    {V : R.View U} {slot : ℕ} {block : BlockId}
    (commit : R.Decided S V slot (some block))
    (hall : ∀ v ∈ M.recoveryCorrect, ∃ b, R.Decided S (P.view v) slot (some b)) :
    SigningFaults.Execution.FinalityQC M E
      (vm.checkpointAfterCommit slot block) :=
  let Q := checkpointQCOfDecided M E vm ha P commit hall
  { checkpointQC := Q
    witnesses := M.recoveryCorrect
    quorum := P.quorum
    messages := fun v hv =>
      (P.witnesses v hv (Q.messages v hv) Q).1
    sender_eq := fun v hv =>
      (P.witnesses v hv (Q.messages v hv) Q).2 }

/-- Proof of `CommitCertified`. -/
theorem commitCertified : CommitCertified M E R vm := by
  intro ha S U P V slot block commit hall
  exact ⟨checkpointQCOfDecided M E vm ha P commit hall⟩

/-- Proof of `CommitFinalized`. -/
theorem commitFinalized : CommitFinalized M E R vm := by
  intro ha S U P V slot block commit hall
  exact ⟨finalityQCOfDecided M E vm ha P commit hall⟩

/-- Proof of `LiveCommitFinalized`: `Commits` on the leader's own view
supplies the commit, and on each online correct validator's view
supplies the settled-everywhere hypothesis. -/
theorem liveCommitFinalized (sp : Support R) (rel : Reliability Validator) :
    LiveCommitFinalized M E R sp rel vm := by
  intro ha hcand hc S U P slot hq hpop hcert hcov hlead
  obtain ⟨L, hL⟩ := hc S (P.view (S.leader slot)) M.recoveryCorrect slot hq hpop hcert
    (hcov _ hlead) hlead
  refine ⟨L, hcand S U _ slot L hL.toDecided, ?_⟩
  refine commitFinalized M E vm ha S P hL.toDecided ?_
  intro v hv
  obtain ⟨b, hb⟩ := hc S (P.view v) M.recoveryCorrect slot hq hpop hcert (hcov v hv) hlead
  exact ⟨b, hb.toDecided⟩

end Execution

end SigningFaults

/-- Proof of `CommitCheckpointUnique`: rewrite with agreement. -/
theorem commitCheckpointUnique
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) :
    CommitCheckpointUnique R vm := by
  intro ha S U V₁ V₂ slot block₁ block₂ commit₁ commit₂
  rw [Option.some.inj (ha S V₁ V₂ slot _ _ commit₁ commit₂)]

end LeanDag.Checkpoint
