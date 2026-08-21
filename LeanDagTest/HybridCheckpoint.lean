import LeanDag.Hybrid.Checkpoint.RecoveryProofs

/-!
# Adversarial checkpoint and recovery witnesses

The model contains Byzantine and AbC double-signing, a competing fork,
certificates at two heights, an unrecorded lower certificate, and one
recovery transition.  Seven-member quorums intersect outside validators
`0` and `1`, forcing the certified branch to remain `[0,1]`; the next
epoch then certifies the strict extension `[0,1,2]`.
-/

namespace LeanDagTest

open LeanDag LeanDag.Hybrid LeanDag.Hybrid.Checkpoint

instance checkpointFaults : HybridFaults (Fin 9) where
  fb := 1
  fc := 1
  byzantine := {0}
  crash := {8}
  disjoint := by decide
  card_byzantine := by decide
  card_crash := by decide
  card_validators := by decide

/-- One Byzantine and one AbC validator may violate signing rules. -/
def checkpointModel : Model (Fin 9) ℕ where
  fabc := 1
  abc := {1}
  disjoint_byzantine := by decide
  disjoint_crash := by decide
  card_abc := by decide
  resilient := by decide

/-- The initial checkpoint. -/
def genesisCheckpoint : CheckpointData ℕ :=
  { height := 0, epoch := 0, history := [] }

/-- A lower, unrecorded certificate candidate. -/
def checkpointOne : CheckpointData ℕ :=
  { height := 1, epoch := 0, history := [0] }

/-- The finalized checkpoint before recovery. -/
def checkpointTwo : CheckpointData ℕ :=
  { height := 2, epoch := 0, history := [0, 1] }

/-- A competing same-height history emitted only by equivocators. -/
def forkTwo : CheckpointData ℕ :=
  { height := 2, epoch := 0, history := [9, 9] }

/-- A syntactically malformed height binding that only a faulty sender
may emit in the concrete execution. -/
def malformedHeight : CheckpointData ℕ :=
  { height := 99, epoch := 0, history := [9] }

/-- The first checkpoint certified after recovery. -/
def checkpointThree : CheckpointData ℕ :=
  { height := 3, epoch := 1, history := [0, 1, 2] }

/-- Canonical local state is a height-indexed prefix of a fixed history. -/
def checkpointLocal (_ : Fin 9) (_ : ℕ) (height : ℕ) : History ℕ :=
  [0, 1, 2].take height

/-- Emission permits validators `0` and `1` to double-sign, while every
other sender is bound to its unique canonical local state. -/
def checkpointEmitted (m : ChkProp (Fin 9) ℕ) : Prop :=
  (m.sender ∈ ({0, 1} : Finset (Fin 9)) ∨
      m.checkpoint.history.length = m.checkpoint.height) ∧
    (m.sender ∈ ({0, 1} : Finset (Fin 9)) ∨
      m.checkpoint.history =
        checkpointLocal m.sender m.checkpoint.epoch m.checkpoint.height) ∧
    (m.sender ∈ ({0, 1} : Finset (Fin 9)) ∨
      m.checkpoint.epoch = 0 ∨ 2 ≤ m.checkpoint.height)

/-- Only the height-two canonical checkpoint is recorded in this run. -/
def checkpointRecorded (_ : Fin 9) (checkpoint : CheckpointData ℕ) : Prop :=
  checkpoint = checkpointTwo

/-- Taking a shorter prefix of one list yields a prefix of a longer
take. -/
private theorem take_prefix_of_le {α : Type*} {l : List α} {h₁ h₂ : ℕ}
    (hh : h₁ ≤ h₂) : l.take h₁ <+: l.take h₂ := by
  have heq : h₂ = h₁ + (h₂ - h₁) := by omega
  rw [heq, List.take_add]
  exact List.prefix_append _ _

/-- The concrete protocol execution, including the genesis adopted after
the recovery epoch. -/
def checkpointExecution : checkpointModel.Execution ℕ where
  genesis := fun epoch => if epoch = 0 then [] else [0, 1]
  localHistory := checkpointLocal
  emitted := checkpointEmitted
  recorded := checkpointRecorded
  genesis_prefix := by
    intro m hm hv
    rcases hm with ⟨hlen, hstate, hepoch⟩
    have hv' :
        m.sender ≠ 1 ∧ m.sender ∉ checkpointFaults.byzantine := by
      simpa [checkpointModel, Model.ReliableSigner] using hv
    have hgood : m.sender ∉ ({0, 1} : Finset (Fin 9)) := by
      have h1 : m.sender ≠ 1 := hv'.1
      have h0 : m.sender ≠ 0 := by
        have hb := hv'.2
        change m.sender ∉ ({0} : Finset (Fin 9)) at hb
        simpa using hb
      simp [h0, h1]
    have hs := hstate.resolve_left hgood
    have he := hepoch.resolve_left hgood
    by_cases hz : m.checkpoint.epoch = 0
    · simp [hz]
    · simp only [hz, if_false]
      have hh : 2 ≤ m.checkpoint.height := he.resolve_left hz
      rw [hs]
      rw [List.prefix_iff_eq_take]
      change [0, 1] =
        List.take 2 (List.take m.checkpoint.height [0, 1, 2])
      rw [List.take_take, Nat.min_eq_left hh]
      rfl
  local_extension := by
    intro v e h₁ h₂ hv hh
    exact take_prefix_of_le hh
  emitted_from_state := by
    intro m hm hv
    have hv' :
        m.sender ≠ 1 ∧ m.sender ∉ checkpointFaults.byzantine := by
      simpa [checkpointModel, Model.ReliableSigner] using hv
    have hgood : m.sender ∉ ({0, 1} : Finset (Fin 9)) := by
      have h1 : m.sender ≠ 1 := hv'.1
      have h0 : m.sender ≠ 0 := by
        have hb := hv'.2
        change m.sender ∉ ({0} : Finset (Fin 9)) at hb
        simpa using hb
      simp [h0, h1]
    exact hm.2.1.resolve_left hgood
  local_height := by
    intro m hm hv
    have hv' :
        m.sender ≠ 1 ∧ m.sender ∉ checkpointFaults.byzantine := by
      simpa [checkpointModel, Model.ReliableSigner] using hv
    have hgood : m.sender ∉ ({0, 1} : Finset (Fin 9)) := by
      have h1 : m.sender ≠ 1 := hv'.1
      have h0 : m.sender ≠ 0 := by
        have hb := hv'.2
        change m.sender ∉ ({0} : Finset (Fin 9)) at hb
        simpa using hb
      simp [h0, h1]
    have hs := hm.2.1.resolve_left hgood
    rw [← hs]
    exact hm.1.resolve_left hgood

/-- Seven senders form the lower, deliberately unrecorded certificate. -/
def checkpointOneQC :
    Model.Execution.CheckpointQC checkpointModel checkpointExecution
      checkpointOne where
  signers := {0, 1, 2, 3, 4, 5, 6}
  quorum := by decide
  messages := by
    intro v hv
    simp [checkpointExecution, checkpointEmitted, checkpointOne,
      checkpointLocal]

/-- Seven senders form the finalized height-two certificate. -/
def checkpointTwoQC :
    Model.Execution.CheckpointQC checkpointModel checkpointExecution
      checkpointTwo where
  signers := {0, 1, 2, 3, 4, 5, 6}
  quorum := by decide
  messages := by
    intro v hv
    simp [checkpointExecution, checkpointEmitted, checkpointTwo,
      checkpointLocal]

/-- A competing signer set certifies the same canonical height-two
checkpoint, exercising quorum intersection rather than identical sets. -/
def checkpointTwoAltQC :
    Model.Execution.CheckpointQC checkpointModel checkpointExecution
      checkpointTwo where
  signers := {0, 1, 2, 3, 4, 7, 8}
  quorum := by decide
  messages := by
    intro v hv
    simp [checkpointExecution, checkpointEmitted, checkpointTwo,
      checkpointLocal]

/-- Certified height binding is derived from a reliable quorum signer;
it is not imposed on Byzantine or AbC emissions. -/
example : checkpointTwo.history.length = checkpointTwo.height :=
  Model.Execution.checkpointQC_height_bound checkpointModel
    checkpointExecution checkpointTwoQC

/-- The next epoch certifies a strict extension of the recovered state. -/
def checkpointThreeQC :
    Model.Execution.CheckpointQC checkpointModel checkpointExecution
      checkpointThree where
  signers := {0, 1, 2, 3, 4, 5, 6}
  quorum := by decide
  messages := by
    intro v hv
    simp [checkpointExecution, checkpointEmitted, checkpointThree,
      checkpointLocal]

/-- The second quorum consists of concrete messages whose senders have
recorded `checkpointTwoQC`. -/
def checkpointFinality :
    Model.Execution.FinalityQC checkpointModel checkpointExecution
      checkpointTwo where
  checkpointQC := checkpointTwoQC
  witnesses := {0, 1, 2, 3, 4, 5, 6}
  quorum := by decide
  messages := by
    intro v hv
    exact
      { sender := v
        certificate := checkpointTwoQC
        recorded := fun _ => rfl }
  sender_eq := by simp

/-- Byzantine and AbC validators both emit the competing fork. -/
example :
    checkpointExecution.emitted ⟨0, forkTwo⟩ ∧
      checkpointExecution.emitted ⟨1, forkTwo⟩ := by
  change checkpointEmitted ⟨0, forkTwo⟩ ∧
    checkpointEmitted ⟨1, forkTwo⟩
  simp [checkpointEmitted, forkTwo]

/-- Faulty senders may emit malformed height bindings, while a
reliable sender cannot emit the same checkpoint. -/
example :
    checkpointExecution.emitted ⟨0, malformedHeight⟩ ∧
      ¬checkpointExecution.emitted ⟨2, malformedHeight⟩ := by
  change checkpointEmitted ⟨0, malformedHeight⟩ ∧
    ¬checkpointEmitted ⟨2, malformedHeight⟩
  simp [checkpointEmitted, malformedHeight]

/-- A reliable validator cannot emit the competing same-height fork. -/
example : ¬ checkpointExecution.emitted ⟨2, forkTwo⟩ := by
  change ¬checkpointEmitted ⟨2, forkTwo⟩
  simp [checkpointEmitted, forkTwo, checkpointLocal]

/-- Any attempted fork certificate conflicts with the canonical QC and
is therefore impossible: quorum intersection supplies a reliable signer. -/
example
    (forkQC : Model.Execution.CheckpointQC checkpointModel
      checkpointExecution forkTwo) : False := by
  have heq :=
    Model.Execution.checkpointQC_eq_of_same_height checkpointModel
      checkpointExecution forkQC checkpointTwoQC rfl rfl
  have hne : forkTwo ≠ checkpointTwo := by decide
  exact hne heq

/-- The two nonidentical concrete quorums intersect in a reliable signer. -/
example :
    ∃ v ∈ checkpointTwoQC.signers ∩ checkpointTwoAltQC.signers,
      v ∈ checkpointModel.ReliableSigner :=
  checkpointModel.exists_reliableSigner_mem_inter
    checkpointTwoQC.quorum checkpointTwoAltQC.quorum

/-- The two certified heights have a strict, non-reflexive prefix. -/
example :
    checkpointOne.history <+: checkpointTwo.history ∧
      checkpointOne.history ≠ checkpointTwo.history := by
  decide

/-- Concrete lower certificate payload, including every signer. -/
def checkpointOnePayload :
    Model.Execution.CertificatePayload (Validator := Fin 9) (Value := ℕ) where
  checkpoint := checkpointOne
  signers := checkpointOneQC.signers

/-- Concrete finalized certificate payload. -/
def checkpointTwoPayload :
    Model.Execution.CertificatePayload (Validator := Fin 9) (Value := ℕ) where
  checkpoint := checkpointTwo
  signers := checkpointTwoQC.signers

/-- Malformed recovery payload: Byzantine and AbC signers emitted this
fork, but the payload falsely claims five additional reliable signers. -/
def invalidForkPayload :
    Model.Execution.CertificatePayload (Validator := Fin 9) (Value := ℕ) where
  checkpoint := forkTwo
  signers := {0, 1, 2, 3, 4, 5, 6}

/-- Both canonical wire certificates pass explicit local verification. -/
example :
    Model.Execution.CertificatePayload.Valid checkpointModel checkpointExecution
        checkpointOnePayload ∧
      Model.Execution.CertificatePayload.Valid checkpointModel checkpointExecution
        checkpointTwoPayload := by
  constructor
  · constructor
    · exact checkpointOneQC.quorum
    · intro v hv
      simp [checkpointExecution, checkpointEmitted, checkpointOnePayload,
        checkpointOne, checkpointLocal]
  · constructor
    · exact checkpointTwoQC.quorum
    · intro v hv
      simp [checkpointExecution, checkpointEmitted, checkpointTwoPayload,
        checkpointTwo, checkpointLocal]

/-- The explicit verifier rejects the concrete fork payload. -/
theorem invalid_fork_payload_rejected :
    ¬Model.Execution.validateCertificate checkpointModel checkpointExecution
      0 invalidForkPayload := by
  intro hvalid
  have hem := hvalid.2.2 (2 : Fin 9) (by simp [invalidForkPayload])
  simpa [invalidForkPayload, checkpointExecution, checkpointEmitted,
    forkTwo, checkpointLocal] using hem

/-- Broadcast transports only authenticated inputs; no validity or
storage predicate occurs in this channel contract. -/
def checkpointBroadcast :
    Model.Execution.AuthenticatedBroadcast checkpointModel where
  input := fun sender payload =>
    payload = checkpointOnePayload ∨ payload = checkpointTwoPayload ∨
      (sender = 0 ∧ payload = invalidForkPayload)
  delivered := fun _ sender payload =>
    payload = checkpointOnePayload ∨ payload = checkpointTwoPayload ∨
      (sender = 0 ∧ payload = invalidForkPayload)
  integrity := by aesop
  agreement := by simp
  delivery := by aesop

/-- Correct handlers submit recorded certificates and retain exactly the
two delivered payloads accepted by explicit validation.  The malformed
Byzantine payload is delivered but excluded. -/
def checkpointRecovery :
    Model.Execution.RecoveryRound checkpointModel checkpointExecution
      checkpointBroadcast 0 where
  validated := fun _ => {checkpointOne, checkpointTwo}
  submits_recorded := by
    intro sender checkpoint hs hr
    subst checkpoint
    refine ⟨checkpointTwoPayload, rfl, ?_, Or.inr (Or.inl rfl)⟩
    constructor
    · rfl
    · constructor
      · exact checkpointTwoQC.quorum
      · intro v hv
        simp [checkpointExecution, checkpointEmitted, checkpointTwoPayload,
          checkpointTwo, checkpointLocal]
  validated_spec := by
    intro receiver checkpoint
    constructor
    · intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · refine ⟨2, checkpointOnePayload, Or.inl rfl, ?_, rfl⟩
        constructor
        · rfl
        · constructor
          · exact checkpointOneQC.quorum
          · intro v hv
            simp [checkpointExecution, checkpointEmitted, checkpointOnePayload,
              checkpointOne, checkpointLocal]
      · refine ⟨2, checkpointTwoPayload, Or.inr (Or.inl rfl), ?_, rfl⟩
        constructor
        · rfl
        · constructor
          · exact checkpointTwoQC.quorum
          · intro v hv
            simp [checkpointExecution, checkpointEmitted, checkpointTwoPayload,
              checkpointTwo, checkpointLocal]
    · rintro ⟨sender, payload, hd, hvalid, rfl⟩
      simp only [checkpointBroadcast] at hd
      rcases hd with rfl | rfl | ⟨rfl, rfl⟩
      · simp [checkpointOnePayload]
      · simp [checkpointTwoPayload]
      · exact (invalid_fork_payload_rejected hvalid).elim

/-- A Byzantine sender's malformed concrete payload is genuinely
delivered to a correct handler, but cannot enter validated state. -/
example :
    checkpointBroadcast.delivered 2 0 invalidForkPayload ∧
      forkTwo ∉ checkpointRecovery.validated 2 := by
  constructor
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp [checkpointRecovery, forkTwo, checkpointOne, checkpointTwo]

/-- Recovery really selects the higher certificate. -/
theorem concrete_selection_eq :
    Model.Execution.RecoveryRound.select checkpointModel checkpointExecution
      checkpointRecovery genesisCheckpoint 2 = checkpointTwo := by
  have hs : (checkpointRecovery.validated 2).Nonempty :=
    ⟨checkpointOne, by simp [checkpointRecovery]⟩
  have hm :
      Model.Execution.RecoveryRound.select checkpointModel
          checkpointExecution checkpointRecovery genesisCheckpoint 2 ∈
        checkpointRecovery.validated 2 :=
    Model.Execution.RecoveryRound.select_mem
      checkpointModel checkpointExecution checkpointRecovery
        (genesis := genesisCheckpoint) (receiver := (2 : Fin 9)) hs
  apply Model.Execution.RecoveryRound.eq_of_validated_height
    checkpointModel checkpointExecution checkpointRecovery
  · exact hm
  · simp [checkpointRecovery]
  · apply Nat.le_antisymm
    · have hcases :
          Model.Execution.RecoveryRound.select checkpointModel
                checkpointExecution checkpointRecovery genesisCheckpoint 2 =
              checkpointOne ∨
            Model.Execution.RecoveryRound.select checkpointModel
                checkpointExecution checkpointRecovery genesisCheckpoint 2 =
              checkpointTwo := by
          simpa only [checkpointRecovery, Finset.mem_insert,
            Finset.mem_singleton] using hm
      rcases hcases with hcase | hcase
      · simpa [hcase, checkpointOne, checkpointTwo]
      · simp [hcase]
    · exact Model.Execution.RecoveryRound.height_le_select
        checkpointModel checkpointExecution checkpointRecovery hs
          (by simp [checkpointRecovery])

/-- The concrete epoch transition adopts the recovery selection as the
next genesis. -/
noncomputable def checkpointTransition :
    Model.Execution.RecoveryRound.EpochTransition checkpointModel
      checkpointExecution checkpointRecovery genesisCheckpoint 2 where
  receiver_correct := by decide
  selected :=
    Model.Execution.RecoveryRound.select checkpointModel
      checkpointExecution checkpointRecovery genesisCheckpoint 2
  selection :=
    Model.Execution.RecoveryRound.select_isSelected checkpointModel
      checkpointExecution checkpointRecovery genesisCheckpoint 2
  next_epoch := 1
  next_epoch_eq := rfl
  adopted := by
    rw [concrete_selection_eq]
    rfl

/-- Recovery preserves the finalized checkpoint and subsequent signing
strictly extends it in the next epoch. -/
theorem concrete_recovery_extends :
    checkpointTwo.history <+: checkpointThree.history :=
  Model.Execution.RecoveryRound.finalized_prefix_next_checkpoint
    checkpointModel checkpointExecution checkpointRecovery
      checkpointTransition checkpointFinality checkpointThreeQC rfl

example : checkpointTwo.history ≠ checkpointThree.history := by decide

#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.checkpointQC_eq_of_same_height
#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.checkpointQC_prefix
#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.finalityQC_compatible
#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.validateCertificate_sound
#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.RecoveryRound.validated_sound
#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.RecoveryRound.recovery_preserves_finality
#print axioms LeanDag.Hybrid.Checkpoint.Model.Execution.RecoveryRound.finalized_prefix_next_checkpoint
#print axioms concrete_recovery_extends

end LeanDagTest
