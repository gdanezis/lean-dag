import LeanDag.Hybrid.Checkpoint.CommitSpec

/-!
# Machine-checked commit-to-checkpoint derivations

This file proves the claims stated at the end of `CommitSpec.lean`.
Every statement here is either one of those claims or an internal
construction; nothing in this file needs human review beyond the claim
names it proves.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator BlockId Payload Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable [LinearOrder BlockId]
variable [S : Slots Validator]

namespace FlexibleFaults

variable (M : FlexibleFaults Validator Value)

namespace Execution

variable (E : M.Execution Value)
variable {U : BlockUniverse Validator BlockId Payload}
variable {k : ℕ}
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

omit S in
/-- Proof of `RecoveryCorrectQuorum`: with no AbC population,
`RecoveryCorrect` is the base `Correct` set, and `card_correct` counts. -/
theorem recoveryCorrect_quorum : RecoveryCorrectQuorum M := by
  intro hno
  have hcorrect := card_correct (Validator := Validator)
  unfold RecoveryCorrect ReliableSigner
  rw [hno]
  simp only [Finset.union_empty]
  have heq :
      H.byzantineᶜ \ H.crash = (Correct : Finset Validator) := by
    ext validator
    simp [Correct]
  rw [heq]
  simpa [Hybrid.q] using hcorrect

/-- The tie between a commit and a proposal: a validator that settled
the slot on its own view proposed the checkpoint of the given commit,
because base safety makes its verdict agree with the commit. -/
theorem emitted_of_decided (P : SigningRule M E U k vm)
    (hne : HonestNoEquiv U) (hk : Hybrid.Admissible Validator k)
    {V : View Validator BlockId Payload U} {slot : ℕ} {block : BlockId}
    (commit : Hybrid.Decided k U V slot (some block))
    {v : Validator} (hv : v ∈ M.RecoveryCorrect) {b : BlockId}
    (hb : Hybrid.Decided k U (P.view v) slot (some b)) :
    E.emitted ⟨v, vm.checkpointAfterCommit slot block⟩ := by
  have heq : b = block := Hybrid.safety hne hk hb commit
  subst heq
  exact P.proposes v hv hb

/-- Construction behind `CommitCertified`: the online correct validators
are the signers, each by `emitted_of_decided`. -/
def checkpointQCOfDecided (P : SigningRule M E U k vm)
    (hne : HonestNoEquiv U) (hk : Hybrid.Admissible Validator k)
    {V : View Validator BlockId Payload U} {slot : ℕ} {block : BlockId}
    (commit : Hybrid.Decided k U V slot (some block))
    (hall : ∀ v ∈ M.RecoveryCorrect,
      ∃ b, Hybrid.Decided k U (P.view v) slot (some b)) :
    FlexibleFaults.Execution.CheckpointQC M E
      (vm.checkpointAfterCommit slot block) where
  signers := M.RecoveryCorrect
  quorum := recoveryCorrect_quorum M P.noAbC
  messages := by
    intro v hv
    obtain ⟨b, hb⟩ := hall v hv
    exact emitted_of_decided M E vm P hne hk commit hv hb

/-- Construction behind `CommitFinalized`: every signer of the
certificate above also witnesses it, by the rule's second clause. -/
def finalityQCOfDecided (P : SigningRule M E U k vm)
    (hne : HonestNoEquiv U) (hk : Hybrid.Admissible Validator k)
    {V : View Validator BlockId Payload U} {slot : ℕ} {block : BlockId}
    (commit : Hybrid.Decided k U V slot (some block))
    (hall : ∀ v ∈ M.RecoveryCorrect,
      ∃ b, Hybrid.Decided k U (P.view v) slot (some b)) :
    FlexibleFaults.Execution.FinalityQC M E
      (vm.checkpointAfterCommit slot block) :=
  let Q := checkpointQCOfDecided M E vm P hne hk commit hall
  { checkpointQC := Q
    witnesses := M.RecoveryCorrect
    quorum := recoveryCorrect_quorum M P.noAbC
    messages := fun v hv =>
      (P.witnesses v hv (Q.messages v hv) Q).1
    sender_eq := fun v hv =>
      (P.witnesses v hv (Q.messages v hv) Q).2 }

/-- Proof of `CommitCertified`. -/
theorem commitCertified : CommitCertified M E Payload vm := by
  intro U k P hne hk V slot block commit hall
  exact ⟨checkpointQCOfDecided M E vm P hne hk commit hall⟩

/-- Proof of `CommitFinalized`. -/
theorem commitFinalized : CommitFinalized M E Payload vm := by
  intro U k P hne hk V slot block commit hall
  exact ⟨finalityQCOfDecided M E vm P hne hk commit hall⟩

/-- Proof of `LiveCommitFinalized`: `Hybrid.decided_of_leader_mem` on the
full view supplies the commit, and on each online correct validator's
own view supplies the settled-everywhere hypothesis. -/
theorem liveCommitFinalized : LiveCommitFinalized M E Payload vm := by
  intro U k P R slot hne hk hs hR hpop0 hpop1 hcov hlead
  have hcard := recoveryCorrect_quorum M P.noAbC
  obtain ⟨L, hL, hdec⟩ :=
    Hybrid.decided_of_leader_mem (k := k) hcard hs hR hpop0 hpop1
      (View.full U) (View.coversUpto_full U _) hlead
  refine ⟨L, hL, ?_⟩
  refine commitFinalized M E vm P hne hk hdec ?_
  intro v hv
  obtain ⟨b, -, hb⟩ :=
    Hybrid.decided_of_leader_mem (k := k) hcard hs hR hpop0 hpop1
      (P.view v) (hcov v hv) hlead
  exact ⟨b, hb⟩

/-- Proof of `CommitCheckpointUnique`: rewrite with `Hybrid.safety`. -/
theorem checkpointAfterCommit_eq :
    CommitCheckpointUnique (Validator := Validator) Payload vm := by
  intro U k hne hk V₁ V₂ slot block₁ block₂ commit₁ commit₂
  rw [Hybrid.safety hne hk commit₁ commit₂]

end Execution

end FlexibleFaults

end LeanDag.Hybrid.Checkpoint
