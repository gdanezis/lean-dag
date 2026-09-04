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
def checkpointFlexible : FlexibleFaults (Fin 9) ℕ where
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

/-- The reliable signers of this model are exactly the senders other
than `0` and `1`, which is the side condition every emission clause
below discharges. -/
private theorem reliable_not_faulty {v : Fin 9}
    (hv : v ∈ checkpointFlexible.ReliableSigner) :
    v ∉ ({0, 1} : Finset (Fin 9)) := by
  have hv' :
      v ≠ 1 ∧ v ∉ checkpointFaults.byzantine := by
    simpa [checkpointFlexible, FlexibleFaults.ReliableSigner] using hv
  have h0 : v ≠ 0 := by
    have hb := hv'.2
    change v ∉ ({0} : Finset (Fin 9)) at hb
    simpa using hb
  simp [h0, hv'.1]

/-- The concrete protocol execution, including the genesis adopted after
the recovery epoch. -/
def checkpointExecution : checkpointFlexible.Execution ℕ where
  genesis := fun epoch => if epoch = 0 then [] else [0, 1]
  localHistory := checkpointLocal
  emitted := checkpointEmitted
  recorded := checkpointRecorded
  genesis_prefix := by
    intro m hm hv
    rcases hm with ⟨hlen, hstate, hepoch⟩
    have hgood := reliable_not_faulty hv
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
    exact List.take_prefix_take_left hh
  emitted_from_state := by
    intro m hm hv
    have hgood := reliable_not_faulty hv
    exact hm.2.1.resolve_left hgood
  local_height := by
    intro m hm hv
    have hgood := reliable_not_faulty hv
    have hs := hm.2.1.resolve_left hgood
    rw [← hs]
    exact hm.1.resolve_left hgood

/-- Seven senders form the lower, deliberately unrecorded certificate. -/
def checkpointOneQC :
    FlexibleFaults.Execution.CheckpointQC checkpointFlexible checkpointExecution
      checkpointOne where
  signers := {0, 1, 2, 3, 4, 5, 6}
  quorum := by decide
  messages := by
    intro v hv
    simp [checkpointExecution, checkpointEmitted, checkpointOne,
      checkpointLocal]

/-- Seven senders form the finalized height-two certificate. -/
def checkpointTwoQC :
    FlexibleFaults.Execution.CheckpointQC checkpointFlexible checkpointExecution
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
    FlexibleFaults.Execution.CheckpointQC checkpointFlexible checkpointExecution
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
  FlexibleFaults.Execution.checkpointQC_height_bound checkpointFlexible
    checkpointExecution checkpointTwoQC

/-- The next epoch certifies a strict extension of the recovered state. -/
def checkpointThreeQC :
    FlexibleFaults.Execution.CheckpointQC checkpointFlexible checkpointExecution
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
    FlexibleFaults.Execution.FinalityQC checkpointFlexible checkpointExecution
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
    (forkQC : FlexibleFaults.Execution.CheckpointQC checkpointFlexible
      checkpointExecution forkTwo) : False := by
  have heq :=
    FlexibleFaults.Execution.checkpointQC_eq_of_same_height checkpointFlexible
      checkpointExecution forkQC checkpointTwoQC rfl rfl
  have hne : forkTwo ≠ checkpointTwo := by decide
  exact hne heq

/-- The two nonidentical concrete quorums intersect in a reliable signer. -/
example :
    ∃ v ∈ checkpointTwoQC.signers ∩ checkpointTwoAltQC.signers,
      v ∈ checkpointFlexible.ReliableSigner :=
  checkpointFlexible.exists_reliableSigner_mem_inter
    checkpointTwoQC.quorum checkpointTwoAltQC.quorum

/-- The two certified heights have a strict, non-reflexive prefix. -/
example :
    checkpointOne.history <+: checkpointTwo.history ∧
      checkpointOne.history ≠ checkpointTwo.history := by
  decide

/-- Concrete lower certificate payload, including every signer. -/
def checkpointOnePayload :
    FlexibleFaults.Execution.CertificatePayload (Validator := Fin 9) (Value := ℕ) where
  checkpoint := checkpointOne
  signers := checkpointOneQC.signers

/-- Concrete finalized certificate payload. -/
def checkpointTwoPayload :
    FlexibleFaults.Execution.CertificatePayload (Validator := Fin 9) (Value := ℕ) where
  checkpoint := checkpointTwo
  signers := checkpointTwoQC.signers

/-- Malformed recovery payload: Byzantine and AbC signers emitted this
fork, but the payload falsely claims five additional reliable signers. -/
def invalidForkPayload :
    FlexibleFaults.Execution.CertificatePayload (Validator := Fin 9) (Value := ℕ) where
  checkpoint := forkTwo
  signers := {0, 1, 2, 3, 4, 5, 6}

/-- Both canonical wire certificates pass explicit local verification. -/
example :
    FlexibleFaults.Execution.CertificatePayload.Valid checkpointFlexible checkpointExecution
        checkpointOnePayload ∧
      FlexibleFaults.Execution.CertificatePayload.Valid checkpointFlexible checkpointExecution
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
    ¬FlexibleFaults.Execution.validateCertificate checkpointFlexible checkpointExecution
      0 invalidForkPayload := by
  intro hvalid
  have hem := hvalid.2.2 (2 : Fin 9) (by simp [invalidForkPayload])
  simp [invalidForkPayload, checkpointExecution, checkpointEmitted,
    forkTwo, checkpointLocal] at hem

/-- Broadcast transports only authenticated inputs; no validity or
storage predicate occurs in this channel contract. -/
def checkpointBroadcast :
    FlexibleFaults.Execution.AuthenticatedBroadcast checkpointFlexible where
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
    FlexibleFaults.Execution.RecoveryRound checkpointFlexible checkpointExecution
      checkpointBroadcast 0 where
  validated := fun _ => {checkpointOne, checkpointTwo}
  submits_recorded := by
    intro sender checkpoint hs hr hepoch
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

/-- A later recovery round may retain old records without treating them
as certificates for the new closing epoch. -/
def emptyRecoveryBroadcast :
    FlexibleFaults.Execution.AuthenticatedBroadcast checkpointFlexible where
  input := fun _ _ => False
  delivered := fun _ _ _ => False
  integrity := by simp
  agreement := by simp
  delivery := by simp

/-- Multi-epoch regression witness: the execution still records the
epoch-0 checkpoint, while an epoch-1 round has no current-epoch input.
The stale record does not make the round contract inconsistent. -/
def retainedRecordRecovery :
    FlexibleFaults.Execution.RecoveryRound checkpointFlexible checkpointExecution
      emptyRecoveryBroadcast 1 where
  validated := fun _ => ∅
  submits_recorded := by
    intro sender checkpoint hs hrecorded hepoch
    have hc : checkpoint = checkpointTwo := by
      simpa [checkpointExecution, checkpointRecorded] using hrecorded
    subst checkpoint
    simp [checkpointTwo] at hepoch
  validated_spec := by
    simp [emptyRecoveryBroadcast]

/-- Empty recovery selects the canonical checkpoint induced by the
closing epoch's execution genesis, not caller-supplied data. -/
example :
    FlexibleFaults.Execution.RecoveryRound.select checkpointFlexible checkpointExecution
      retainedRecordRecovery 2 =
        FlexibleFaults.Execution.epochGenesis checkpointFlexible checkpointExecution 1 := by
  simp [FlexibleFaults.Execution.RecoveryRound.select, retainedRecordRecovery]

/-- Recovery really selects the higher certificate. -/
theorem concrete_selection_eq :
    FlexibleFaults.Execution.RecoveryRound.select checkpointFlexible checkpointExecution
      checkpointRecovery 2 = checkpointTwo := by
  have hs : (checkpointRecovery.validated 2).Nonempty :=
    ⟨checkpointOne, by simp [checkpointRecovery]⟩
  have hm :
      FlexibleFaults.Execution.RecoveryRound.select checkpointFlexible
          checkpointExecution checkpointRecovery 2 ∈
        checkpointRecovery.validated 2 :=
    FlexibleFaults.Execution.RecoveryRound.select_mem
      checkpointFlexible checkpointExecution checkpointRecovery
        (receiver := (2 : Fin 9)) hs
  apply FlexibleFaults.Execution.RecoveryRound.eq_of_validated_height
    checkpointFlexible checkpointExecution checkpointRecovery
  · exact hm
  · simp [checkpointRecovery]
  · apply Nat.le_antisymm
    · have hcases :
          FlexibleFaults.Execution.RecoveryRound.select checkpointFlexible
                checkpointExecution checkpointRecovery 2 =
              checkpointOne ∨
            FlexibleFaults.Execution.RecoveryRound.select checkpointFlexible
                checkpointExecution checkpointRecovery 2 =
              checkpointTwo := by
          simpa only [checkpointRecovery, Finset.mem_insert,
            Finset.mem_singleton] using hm
      rcases hcases with hcase | hcase
      · simp [hcase, checkpointOne, checkpointTwo]
      · simp [hcase]
    · exact FlexibleFaults.Execution.RecoveryRound.height_le_select
        checkpointFlexible checkpointExecution checkpointRecovery hs
          (by simp [checkpointRecovery])

/-- The concrete epoch transition adopts the recovery selection as the
next genesis. -/
noncomputable def checkpointTransition :
    FlexibleFaults.Execution.RecoveryRound.EpochTransition checkpointFlexible
      checkpointExecution checkpointRecovery 2 where
  receiver_correct := by decide
  selected :=
    FlexibleFaults.Execution.RecoveryRound.select checkpointFlexible
      checkpointExecution checkpointRecovery 2
  selection :=
    FlexibleFaults.Execution.RecoveryRound.select_isSelected checkpointFlexible
      checkpointExecution checkpointRecovery 2
  next_epoch := 1
  next_epoch_eq := rfl
  adopted := by
    rw [concrete_selection_eq]
    rfl

/-- Recovery preserves the finalized checkpoint and subsequent signing
strictly extends it in the next epoch. -/
theorem concrete_recovery_extends :
    checkpointTwo.history <+: checkpointThree.history :=
  FlexibleFaults.Execution.RecoveryRound.finalized_prefix_next_checkpoint
    checkpointFlexible checkpointExecution checkpointRecovery
      checkpointTransition checkpointFinality rfl checkpointThreeQC rfl

example : checkpointTwo.history ≠ checkpointThree.history := by decide

#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.checkpointQC_eq_of_same_height
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.checkpointQC_prefix
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.finalityQC_compatible
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.validateCertificate_sound
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.RecoveryRound.validated_sound
#print axioms
  LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.RecoveryRound.recovery_preserves_finality
#print axioms
  LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.RecoveryRound.finalized_prefix_next_checkpoint
#print axioms concrete_recovery_extends

end LeanDagTest
