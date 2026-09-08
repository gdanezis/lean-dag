import LeanDag.Hybrid.Checkpoint.SafetyProofs
import LeanDag.Hybrid.Checkpoint.RecoverySpec
import Mathlib.Data.Finset.Max

/-!
# Machine-checked recovery derivations

Human reviewers must inspect the theorem statements in this file to
confirm that they express the intended guarantees. Once those statements
and the two specification modules are accepted, the `by` bodies are
proof engineering checked by Lean and need not be trusted by inspection.

The concrete selector below implements `RecoveryRound.IsSelected`.
Recovery handlers agree on validated evidence, select a highest
checkpoint or the closing epoch's canonical genesis, and preserve
closing-epoch recorded and finalized histories into the next epoch.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

namespace FlexibleFaults

variable (M : FlexibleFaults Validator Value)

namespace Execution

variable (E : M.Execution Value)

/-- Validation soundness is constructive: accepted wire evidence
directly builds the corresponding checkpoint QC. -/
theorem validateCertificate_sound {epoch : ℕ}
    {payload : CertificatePayload (Validator := Validator) (Value := Value)}
    (valid : validateCertificate (M := M) (E := E) epoch payload) :
    Nonempty (FlexibleFaults.Execution.CheckpointQC M E payload.checkpoint) :=
  ⟨CertificatePayload.toCheckpointQC M E payload valid.2⟩

namespace RecoveryRound

variable {B : AuthenticatedBroadcast M} {epoch : ℕ}
variable (R : RecoveryRound M E B epoch)

/-- Correct recipients obtain identical finite validated checkpoint
sets from broadcast agreement and deterministic local verification. -/
theorem validated_agreement {v w : Validator}
    (hv : v ∈ M.RecoveryCorrect) (hw : w ∈ M.RecoveryCorrect) :
    R.validated v = R.validated w := by
  ext checkpoint
  rw [R.validated_spec, R.validated_spec]
  constructor
  · rintro ⟨sender, payload, hd, hvalid, heq⟩
    exact ⟨sender, payload, (B.agreement hv hw sender payload).mp hd,
      hvalid, heq⟩
  · rintro ⟨sender, payload, hd, hvalid, heq⟩
    exact ⟨sender, payload, (B.agreement hv hw sender payload).mpr hd,
      hvalid, heq⟩

/-- Membership in the validated set yields both a genuine checkpoint QC
and the round's closing epoch. -/
theorem validated_sound {receiver : Validator}
    {checkpoint : CheckpointData Value}
    (member : checkpoint ∈ R.validated receiver) :
    Nonempty (FlexibleFaults.Execution.CheckpointQC M E checkpoint) ∧
      checkpoint.epoch = epoch := by
  obtain ⟨sender, payload, delivered, valid, rfl⟩ :=
    R.validated_spec.mp member
  exact ⟨validateCertificate_sound M E valid, valid.1⟩

/-- Every nonempty finite checkpoint set has a highest member. -/
theorem exists_highest {s : Finset (CheckpointData Value)} (hs : s.Nonempty) :
    ∃ checkpoint, IsHighest s checkpoint :=
  Finset.exists_max_image s (·.height) hs

/-- Concrete highest-checkpoint selection. Classical choice implements
the human-reviewed `IsSelected` semantics from `RecoverySpec.lean`. -/
noncomputable def select (receiver : Validator) :
    CheckpointData Value :=
  if hs : (R.validated receiver).Nonempty then
    Classical.choose (exists_highest hs)
  else epochGenesis M E epoch

/-- The nonempty selection satisfies membership and maximality. -/
theorem select_spec {receiver : Validator}
    (hs : (R.validated receiver).Nonempty) :
    IsHighest (R.validated receiver) (select M E R receiver) := by
  simp only [select, dif_pos hs]
  exact Classical.choose_spec (exists_highest hs)

/-- The concrete selector refines the declarative selection semantics. -/
theorem select_isSelected (receiver : Validator) :
    IsSelected M E R receiver (select M E R receiver) := by
  by_cases hs : (R.validated receiver).Nonempty
  · simpa [IsSelected, hs] using
      (select_spec M E R hs)
  · simp [IsSelected, select, hs]

/-- Nonempty selection is one of the locally validated checkpoints. -/
theorem select_mem {receiver : Validator}
    (hs : (R.validated receiver).Nonempty) :
    select M E R receiver ∈ R.validated receiver := by
  exact (select_spec M E R hs).1

/-- The selected checkpoint has maximum height among all validated
checkpoints. -/
theorem height_le_select {receiver : Validator}
    (hs : (R.validated receiver).Nonempty)
    {checkpoint : CheckpointData Value}
    (hc : checkpoint ∈ R.validated receiver) :
    checkpoint.height ≤ (select M E R receiver).height := by
  exact (select_spec M E R hs).2 checkpoint hc

/-- Equal-height validated candidates are equal. Thus the
implementation's tie result is unique independently of set ordering. -/
theorem eq_of_validated_height {receiver : Validator}
    {x y : CheckpointData Value}
    (hx : x ∈ R.validated receiver) (hy : y ∈ R.validated receiver)
    (hh : x.height = y.height) : x = y := by
  obtain ⟨⟨QX⟩, hex⟩ := validated_sound M E R hx
  obtain ⟨⟨QY⟩, hey⟩ := validated_sound M E R hy
  exact checkpointQC_eq_of_same_height M E QX QY
    (hex.trans hey.symm) hh

/-- Any checkpoint satisfying `IsSelected` equals the concrete
selector's output. Same-height checkpoint uniqueness removes the
arbitrariness of classical choice. -/
theorem selected_eq_select {receiver : Validator}
    {checkpoint : CheckpointData Value}
    (hselected : IsSelected M E R receiver checkpoint) :
    checkpoint = select M E R receiver := by
  by_cases hs : (R.validated receiver).Nonempty
  · have hc : IsHighest (R.validated receiver) checkpoint := by
      simpa [IsSelected, hs] using hselected
    have hselect := select_spec M E R hs
    apply eq_of_validated_height M E R hc.1 hselect.1
    apply Nat.le_antisymm
    · exact hselect.2 checkpoint hc.1
    · exact hc.2 _ hselect.1
  · have hc : checkpoint = epochGenesis M E epoch := by
      simpa [IsSelected, hs] using hselected
    simpa [select, hs] using hc

/-- Correct recipients deterministically select the same recovery
checkpoint, including the canonical empty-set case. -/
theorem selection_agreement {v w : Validator}
    (hv : v ∈ M.RecoveryCorrect) (hw : w ∈ M.RecoveryCorrect) :
    select M E R v = select M E R w := by
  have hagree := validated_agreement M E R hv hw
  by_cases hs : (R.validated v).Nonempty
  · have hsw : (R.validated w).Nonempty := by
      obtain ⟨checkpoint, hc⟩ := hs
      exact ⟨checkpoint, by simpa [← hagree] using hc⟩
    have hsv := select_mem M E R (receiver := v) hs
    have hswm := select_mem M E R
      (receiver := w) hsw
    apply eq_of_validated_height M E R hsv
      (by simpa [← hagree] using hswm)
    apply Nat.le_antisymm
    · exact height_le_select M E R hsw
        (by simpa [← hagree] using hsv)
    · exact height_le_select M E R hs
        (by simpa [← hagree] using hswm)
  · have hsw : ¬(R.validated w).Nonempty := by
      intro hn
      obtain ⟨checkpoint, hc⟩ := hn
      exact hs ⟨checkpoint, by simpa [hagree] using hc⟩
    simp [select, hs, hsw]

/-- Every validated checkpoint is a prefix of the selected maximum. -/
theorem validated_prefix_select {receiver : Validator}
    (hs : (R.validated receiver).Nonempty)
    {checkpoint : CheckpointData Value}
    (hc : checkpoint ∈ R.validated receiver) :
    checkpoint.history.IsPrefix
      (select M E R receiver).history := by
  have hm := select_mem M E R hs
  obtain ⟨⟨QS⟩, hes⟩ := validated_sound M E R hm
  obtain ⟨⟨QC⟩, hec⟩ := validated_sound M E R hc
  exact checkpointQC_prefix M E QC QS
    (hec.trans hes.symm)
    (height_le_select M E R hs hc)

include R in
/-- What a closing-epoch record is: a recovery-correct handler holds one
only for a checkpoint some quorum certified. The `Execution` structure
does not say so — `submits_recorded` does, through the payload it
requires the handler to input, and `validateCertificate_sound` returns
that payload as a certificate. `R` is explicit because the fact belongs
to the round's submission contract rather than to the execution. -/
theorem recorded_certified {v : Validator} {checkpoint : CheckpointData Value}
    (hv : v ∈ M.RecoveryCorrect) (hrecorded : E.recorded v checkpoint)
    (hepoch : checkpoint.epoch = epoch) :
    Nonempty (FlexibleFaults.Execution.CheckpointQC M E checkpoint) := by
  obtain ⟨payload, heq, hvalid, _⟩ := R.submits_recorded hv hrecorded hepoch
  exact heq ▸ validateCertificate_sound M E hvalid

/-- A checkpoint recorded by a recovery-correct handler enters every
correct recipient's validated set through protocol submission,
broadcast delivery, and local certificate validation. -/
theorem recorded_mem_validated {sender receiver : Validator}
    (hs : sender ∈ M.RecoveryCorrect)
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (hrecorded : E.recorded sender checkpoint)
    (hepoch : checkpoint.epoch = epoch) :
    checkpoint ∈ R.validated receiver := by
  obtain ⟨payload, heq, hvalid, hin⟩ :=
    R.submits_recorded hs hrecorded hepoch
  have hdel := B.delivery hs hr hin
  exact R.validated_spec.mpr
    ⟨sender, payload, hdel, hvalid, heq⟩

/-- Highest-checkpoint recovery preserves every closing-epoch checkpoint
recorded by a recovery-correct participant, not only those later
finalized. Such a record is a certified checkpoint, by
`recorded_certified`. -/
theorem recovery_preserves_recorded {sender receiver : Validator}
    (hs : sender ∈ M.RecoveryCorrect)
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (hrecorded : E.recorded sender checkpoint)
    (hepoch : checkpoint.epoch = epoch) :
    checkpoint.history.IsPrefix
      (select M E R receiver).history := by
  have hm := recorded_mem_validated M E R hs hr hrecorded hepoch
  exact validated_prefix_select M E R ⟨checkpoint, hm⟩ hm

/-- A checkpoint finalized in the closing epoch is included in every
correct recipient's validated set: the finality quorum supplies a
recovery-correct recorder, and the recorded case supplies the rest. -/
theorem finalized_mem_validated {receiver : Validator}
    (hr : receiver ∈ M.RecoveryCorrect) {checkpoint : CheckpointData Value}
    (F : FlexibleFaults.Execution.FinalityQC M E checkpoint)
    (hepoch : checkpoint.epoch = epoch) :
    checkpoint ∈ R.validated receiver := by
  obtain ⟨sender, hs, hrec⟩ :=
    exists_recoveryCorrect_recorder M E F
  exact recorded_mem_validated M E R hs hr hrec hepoch

/-- Highest-checkpoint recovery preserves every checkpoint finalized in
the closing epoch: finality is the recorded case at the recorder the
finality quorum supplies. -/
theorem recovery_preserves_finality {receiver : Validator}
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (F : FlexibleFaults.Execution.FinalityQC M E checkpoint)
    (hepoch : checkpoint.epoch = epoch) :
    checkpoint.history.IsPrefix
      (select M E R receiver).history := by
  obtain ⟨sender, hs, hrec⟩ :=
    exists_recoveryCorrect_recorder M E F
  exact recovery_preserves_recorded M E R hs hr hrec hepoch

/-- A finalized checkpoint remains a prefix of the genesis adopted by
the human-reviewed recovery transition. -/
theorem finalized_prefix_next_genesis {receiver : Validator}
    (T : EpochTransition M E R receiver)
    {checkpoint : CheckpointData Value}
    (F : FlexibleFaults.Execution.FinalityQC M E checkpoint)
    (hepoch : checkpoint.epoch = epoch) :
    checkpoint.history.IsPrefix (E.genesis T.next_epoch) := by
  rw [T.adopted, selected_eq_select M E R T.selection]
  exact recovery_preserves_finality M E R T.receiver_correct F hepoch

/-- Subsequent checkpoint signing preserves finalized pre-recovery
state: the selected history becomes the next genesis, and every
reliable signer extends that genesis before emitting a new checkpoint. -/
theorem finalized_prefix_next_checkpoint {receiver : Validator}
    (T : EpochTransition M E R receiver)
    {old new : CheckpointData Value}
    (F : FlexibleFaults.Execution.FinalityQC M E old)
    (hold_epoch : old.epoch = epoch)
    (Q : FlexibleFaults.Execution.CheckpointQC M E new)
    (hne : new.epoch = T.next_epoch) :
    old.history.IsPrefix new.history := by
  obtain ⟨v, hv, hgood⟩ := M.exists_reliableSigner_mem Q.quorum
  have hem := Q.messages v hv
  have hg := E.genesis_prefix hem hgood
  have hold := finalized_prefix_next_genesis M E R T F hold_epoch
  exact hold.trans (by simpa [hne] using hg)

end RecoveryRound

end Execution

end FlexibleFaults

end LeanDag.Hybrid.Checkpoint
