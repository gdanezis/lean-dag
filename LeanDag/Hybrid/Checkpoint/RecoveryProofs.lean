import LeanDag.Hybrid.Checkpoint.SafetyProofs
import LeanDag.Hybrid.Checkpoint.RecoverySpec

/-!
# Machine-checked recovery derivations

Human reviewers must inspect the theorem statements in this file to
confirm that they express the intended guarantees. Once those statements
and the two specification modules are accepted, the `by` bodies are
proof engineering checked by Lean and need not be trusted by inspection.

The concrete selector below implements `RecoveryRound.IsSelected`.
Recovery handlers agree on validated evidence, select a highest
checkpoint or the explicit genesis, and preserve recorded and finalized
histories into the next epoch.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

namespace Model

variable (M : Model Validator Value)

namespace Execution

variable (E : M.Execution Value)

/-- Validation soundness is constructive: accepted wire evidence
directly builds the corresponding checkpoint QC. -/
theorem validateCertificate_sound {epoch : ℕ}
    {payload : CertificatePayload (Validator := Validator) (Value := Value)}
    (valid : validateCertificate (M := M) (E := E) epoch payload) :
    Nonempty (Model.Execution.CheckpointQC M E payload.checkpoint) :=
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
    Nonempty (Model.Execution.CheckpointQC M E checkpoint) ∧
      checkpoint.epoch = epoch := by
  obtain ⟨sender, payload, delivered, valid, rfl⟩ :=
    R.validated_spec.mp member
  exact ⟨validateCertificate_sound M E valid, valid.1⟩

/-- Every nonempty finite checkpoint set has a highest member. -/
theorem exists_highest {s : Finset (CheckpointData Value)} (hs : s.Nonempty) :
    ∃ checkpoint, IsHighest s checkpoint := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert checkpoint s hnot ih =>
      by_cases hse : s.Nonempty
      · obtain ⟨best, hbest, hmax⟩ := ih hse
        by_cases hle : checkpoint.height ≤ best.height
        · exact ⟨best, by
            refine ⟨Finset.mem_insert_of_mem hbest, ?_⟩
            intro other ho
            rcases Finset.mem_insert.mp ho with rfl | ho
            · exact hle
            · exact hmax other ho⟩
        · exact ⟨checkpoint, by
            refine ⟨Finset.mem_insert_self _ _, ?_⟩
            intro other ho
            rcases Finset.mem_insert.mp ho with rfl | ho
            · exact le_rfl
            · exact le_trans (hmax other ho)
                (Nat.le_of_lt (lt_of_not_ge hle))⟩
      · exact ⟨checkpoint, by
          refine ⟨Finset.mem_insert_self _ _, ?_⟩
          intro other ho
          rcases Finset.mem_insert.mp ho with rfl | ho
          · exact le_rfl
          · exact (hse ⟨other, ho⟩).elim⟩

/-- Concrete highest-checkpoint selection. Classical choice implements
the human-reviewed `IsSelected` semantics from `RecoverySpec.lean`. -/
noncomputable def select (genesis : CheckpointData Value) (receiver : Validator) :
    CheckpointData Value :=
  if hs : (R.validated receiver).Nonempty then
    Classical.choose (exists_highest hs)
  else genesis

/-- The nonempty selection satisfies membership and maximality. -/
theorem select_spec {genesis : CheckpointData Value} {receiver : Validator}
    (hs : (R.validated receiver).Nonempty) :
    IsHighest (R.validated receiver) (select M E R genesis receiver) := by
  simp only [select, dif_pos hs]
  exact Classical.choose_spec (exists_highest hs)

/-- The concrete selector refines the declarative selection semantics. -/
theorem select_isSelected (genesis : CheckpointData Value)
    (receiver : Validator) :
    IsSelected M E R genesis receiver (select M E R genesis receiver) := by
  by_cases hs : (R.validated receiver).Nonempty
  · simpa [IsSelected, hs] using
      (select_spec M E R (genesis := genesis) hs)
  · simp [IsSelected, select, hs]

/-- Nonempty selection is one of the locally validated checkpoints. -/
theorem select_mem {genesis : CheckpointData Value} {receiver : Validator}
    (hs : (R.validated receiver).Nonempty) :
    select M E R genesis receiver ∈ R.validated receiver := by
  exact (select_spec M E R hs).1

/-- The selected checkpoint has maximum height among all validated
checkpoints. -/
theorem height_le_select {genesis : CheckpointData Value}
    {receiver : Validator} (hs : (R.validated receiver).Nonempty)
    {checkpoint : CheckpointData Value}
    (hc : checkpoint ∈ R.validated receiver) :
    checkpoint.height ≤ (select M E R genesis receiver).height := by
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
theorem selected_eq_select {genesis : CheckpointData Value}
    {receiver : Validator} {checkpoint : CheckpointData Value}
    (hselected : IsSelected M E R genesis receiver checkpoint) :
    checkpoint = select M E R genesis receiver := by
  by_cases hs : (R.validated receiver).Nonempty
  · have hc : IsHighest (R.validated receiver) checkpoint := by
      simpa [IsSelected, hs] using hselected
    have hselect := select_spec M E R (genesis := genesis) hs
    apply eq_of_validated_height M E R hc.1 hselect.1
    apply Nat.le_antisymm
    · exact hselect.2 checkpoint hc.1
    · exact hc.2 _ hselect.1
  · have hc : checkpoint = genesis := by
      simpa [IsSelected, hs] using hselected
    simpa [select, hs] using hc

/-- Correct recipients deterministically select the same recovery
checkpoint, including the explicit empty-set case. -/
theorem selection_agreement (genesis : CheckpointData Value) {v w : Validator}
    (hv : v ∈ M.RecoveryCorrect) (hw : w ∈ M.RecoveryCorrect) :
    select M E R genesis v = select M E R genesis w := by
  have hagree := validated_agreement M E R hv hw
  by_cases hs : (R.validated v).Nonempty
  · have hsw : (R.validated w).Nonempty := by
      obtain ⟨checkpoint, hc⟩ := hs
      exact ⟨checkpoint, by simpa [← hagree] using hc⟩
    have hsv := select_mem M E R
      (genesis := genesis) (receiver := v) hs
    have hswm := select_mem M E R
      (genesis := genesis) (receiver := w) hsw
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
theorem validated_prefix_select {genesis : CheckpointData Value}
    {receiver : Validator} (hs : (R.validated receiver).Nonempty)
    {checkpoint : CheckpointData Value}
    (hc : checkpoint ∈ R.validated receiver) :
    checkpoint.history.IsPrefix
      (select M E R genesis receiver).history := by
  have hm := select_mem M E R (genesis := genesis) hs
  obtain ⟨⟨QS⟩, hes⟩ := validated_sound M E R hm
  obtain ⟨⟨QC⟩, hec⟩ := validated_sound M E R hc
  exact checkpointQC_prefix M E QC QS
    (hec.trans hes.symm)
    (height_le_select M E R hs hc)

/-- A checkpoint recorded by a recovery-correct handler enters every
correct recipient's validated set through protocol submission,
broadcast delivery, and local certificate validation. -/
theorem recorded_mem_validated {sender receiver : Validator}
    (hs : sender ∈ M.RecoveryCorrect)
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (hrecorded : E.recorded sender checkpoint) :
    checkpoint ∈ R.validated receiver := by
  obtain ⟨payload, heq, hvalid, hin⟩ :=
    R.submits_recorded hs hrecorded
  have hdel := B.delivery hs hr hin
  exact R.validated_spec.mpr
    ⟨sender, payload, hdel, hvalid, heq⟩

/-- Highest-checkpoint recovery preserves every checkpoint recorded by
a recovery-correct participant, not only those later finalized. -/
theorem recovery_preserves_recorded {genesis : CheckpointData Value}
    {sender receiver : Validator}
    (hs : sender ∈ M.RecoveryCorrect)
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (hrecorded : E.recorded sender checkpoint) :
    checkpoint.history.IsPrefix
      (select M E R genesis receiver).history := by
  have hm := recorded_mem_validated M E R hs hr hrecorded
  exact validated_prefix_select M E R ⟨checkpoint, hm⟩ hm

/-- A previously finalized checkpoint is included in every correct
recipient's validated set. This derives protocol submission, broadcast
delivery, and local validation in three separate steps. -/
theorem finalized_mem_validated {receiver : Validator}
    (hr : receiver ∈ M.RecoveryCorrect) {checkpoint : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E checkpoint) :
    checkpoint ∈ R.validated receiver := by
  obtain ⟨sender, hs, hrec⟩ :=
    exists_recoveryCorrect_recorder M E F
  obtain ⟨payload, heq, hvalid, hin⟩ :=
    R.submits_recorded hs hrec
  have hdel := B.delivery hs hr hin
  exact R.validated_spec.mpr
    ⟨sender, payload, hdel, hvalid, heq⟩

/-- Highest-checkpoint recovery preserves every checkpoint finalized in
the closing epoch. -/
theorem recovery_preserves_finality {genesis : CheckpointData Value}
    {receiver : Validator} (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E checkpoint) :
    checkpoint.history.IsPrefix
      (select M E R genesis receiver).history := by
  have hm := finalized_mem_validated M E R hr F
  exact validated_prefix_select M E R ⟨checkpoint, hm⟩ hm

/-- A finalized checkpoint remains a prefix of the genesis adopted by
the human-reviewed recovery transition. -/
theorem finalized_prefix_next_genesis {genesis : CheckpointData Value}
    {receiver : Validator}
    (T : EpochTransition M E R genesis receiver)
    {checkpoint : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E checkpoint) :
    checkpoint.history.IsPrefix (E.genesis T.next_epoch) := by
  rw [T.adopted, selected_eq_select M E R T.selection]
  exact recovery_preserves_finality M E R T.receiver_correct F

/-- Subsequent checkpoint signing preserves finalized pre-recovery
state: the selected history becomes the next genesis, and every
reliable signer extends that genesis before emitting a new checkpoint. -/
theorem finalized_prefix_next_checkpoint {genesis : CheckpointData Value}
    {receiver : Validator}
    (T : EpochTransition M E R genesis receiver)
    {old new : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E old)
    (Q : Model.Execution.CheckpointQC M E new)
    (hne : new.epoch = T.next_epoch) :
    old.history.IsPrefix new.history := by
  obtain ⟨v, hv, hgood⟩ :=
    M.exists_reliableSigner_mem_inter Q.quorum Q.quorum
  have hem := Q.messages v (Finset.mem_inter.mp hv).1
  have hg := E.genesis_prefix hem hgood
  have hold := finalized_prefix_next_genesis M E R T F
  exact hold.trans (by simpa [hne] using hg)

end RecoveryRound

end Execution

end Model

end LeanDag.Hybrid.Checkpoint
