import LeanDag.Hybrid.Checkpoint.BaseSpec

/-!
# Machine-checked checkpoint safety derivations

Human reviewers must inspect the theorem statements in this file to
confirm that they express the intended guarantees. Once those statements
and `BaseSpec.lean` are accepted, the `by` bodies are proof engineering
checked by Lean and need not be trusted by inspection.

Quorum arithmetic supplies a signer outside the Byzantine and AbC
classes. Authentication connects that signer to an emitted proposal;
the emission rule connects the proposal to the signer's unique local
state. Same-height uniqueness and within-epoch prefix consistency are
therefore consequences of protocol state.

Forked histories are permitted inputs to this checkpoint model. The
results do not invoke the DAG's non-equivocation or agreement theorems
and do not claim that the DAG model produces these inputs. They prove
that, once any such execution is supplied, conflicting branches cannot
both acquire checkpoint certificates under the stated AbC bound.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

namespace Model

variable (M : Model Validator Value)

/-- Reliable signing excludes precisely the two classes allowed to
equivocate. -/
@[simp]
theorem mem_reliableSigner {v : Validator} :
    v ∈ M.ReliableSigner ↔ v ∉ H.byzantine ∧ v ∉ M.abc := by
  simp [ReliableSigner]

/-- Recovery-correct membership excludes all three fault classes. -/
@[simp]
theorem mem_recoveryCorrect {v : Validator} :
    v ∈ M.RecoveryCorrect ↔
      v ∉ H.byzantine ∧ v ∉ H.crash ∧ v ∉ M.abc := by
  simp [RecoveryCorrect, ReliableSigner, and_assoc, and_left_comm, and_comm]

/-!
The next two counting arguments follow the same pattern as
`HybridFaults.exists_honest_mem_inter` in `Hybrid/Faults.lean` and
`exists_correct_of_card` in `Validators.lean`. They are restated here
because those lemmas exclude the base Byzantine or crash classes, while
checkpoint signing must additionally exclude `M.abc`; `M.resilient`
supplies the correspondingly stronger cardinal bounds.
-/

/-- Two hybrid quorums share a validator outside both classes allowed
to violate checkpoint signing rules. -/
theorem exists_reliableSigner_mem_inter {a b : Finset Validator}
    (ha : Hybrid.q Validator ≤ a.card)
    (hb : Hybrid.q Validator ≤ b.card) :
    ∃ v ∈ a ∩ b, v ∈ M.ReliableSigner := by
  have hlarge :
      Fintype.card Validator + (H.fb + M.fabc) < a.card + b.card := by
    have hbase := H.card_validators
    have hres := M.resilient
    unfold Hybrid.q at ha hb
    omega
  have hbad :
      (H.byzantine ∪ M.abc).card ≤ H.fb + M.fabc :=
    le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add H.card_byzantine M.card_abc)
  have hunion := Finset.card_union_add_card_inter a b
  have huniv := Finset.card_le_univ (a ∪ b)
  have hnsub : ¬ (a ∩ b) ⊆ H.byzantine ∪ M.abc := by
    intro hsub
    have hinter := Finset.card_le_card hsub
    omega
  obtain ⟨v, hv, hgood⟩ := Finset.not_subset.mp hnsub
  exact ⟨v, hv, by simpa [ReliableSigner] using hgood⟩

/-- Every hybrid quorum contains an available validator outside all
three fault classes. -/
theorem exists_recoveryCorrect_mem {a : Finset Validator}
    (ha : Hybrid.q Validator ≤ a.card) :
    ∃ v ∈ a, v ∈ M.RecoveryCorrect := by
  have hlarge : H.fb + H.fc + M.fabc < a.card := by
    have hbase := H.card_validators
    have hres := M.resilient
    unfold Hybrid.q at ha
    omega
  have hbad :
      (H.byzantine ∪ H.crash ∪ M.abc).card ≤
        H.fb + H.fc + M.fabc := by
    calc
      (H.byzantine ∪ H.crash ∪ M.abc).card
          ≤ (H.byzantine ∪ H.crash).card + M.abc.card :=
        Finset.card_union_le _ _
      _ ≤ (H.byzantine.card + H.crash.card) + M.abc.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ H.fb + H.fc + M.fabc :=
        Nat.add_le_add
          (Nat.add_le_add H.card_byzantine H.card_crash) M.card_abc
  have hnsub : ¬ a ⊆ H.byzantine ∪ H.crash ∪ M.abc := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨v, hv, hgood⟩ := Finset.not_subset.mp hnsub
  exact ⟨v, hv, M.mem_recoveryCorrect.mpr (by simpa using hgood)⟩

namespace Execution

variable (E : M.Execution Value)

namespace CertificatePayload

/-- A payload accepted by the verifier yields a genuine checkpoint QC. -/
def toCheckpointQC (payload : CertificatePayload (Validator := Validator)
    (Value := Value))
    (valid : CertificatePayload.Valid M E payload) :
    Model.Execution.CheckpointQC M E payload.checkpoint where
  signers := payload.signers
  quorum := valid.1
  messages := valid.2

end CertificatePayload

/-- A reliable sender's two messages at one epoch and height carry the
same content. -/
theorem checkpoint_eq_of_reliable_messages
    {v : Validator} {x y : CheckpointData Value}
    (hv : v ∈ M.ReliableSigner)
    (hx : E.emitted ⟨v, x⟩)
    (hy : E.emitted ⟨v, y⟩)
    (he : x.epoch = y.epoch) (hh : x.height = y.height) :
    x = y := by
  have hxstate := E.emitted_from_state hx hv
  have hystate := E.emitted_from_state hy hv
  cases x
  cases y
  subst he
  subst hh
  simp_all

/-- Checkpoint certificate content is unique at a fixed epoch and
height by quorum intersection and the protocol's one-state-per-slot
rule. -/
theorem checkpointQC_eq_of_same_height {x y : CheckpointData Value}
    (X : Model.Execution.CheckpointQC M E x)
    (Y : Model.Execution.CheckpointQC M E y)
    (he : x.epoch = y.epoch) (hh : x.height = y.height) : x = y := by
  obtain ⟨v, hv, hgood⟩ :=
    M.exists_reliableSigner_mem_inter X.quorum Y.quorum
  have hx := X.messages v (Finset.mem_inter.mp hv).1
  have hy := Y.messages v (Finset.mem_inter.mp hv).2
  exact checkpoint_eq_of_reliable_messages M E hgood hx hy he hh

/-- Every checkpoint certificate has a correctly bound global height.
Byzantine and AbC validators may emit arbitrary checkpoints; quorum
counting supplies one reliable signer whose local execution state fixes
the certified history length. -/
theorem checkpointQC_height_bound {x : CheckpointData Value}
    (X : Model.Execution.CheckpointQC M E x) :
    x.history.length = x.height := by
  obtain ⟨v, hv, hcorrect⟩ :=
    M.exists_recoveryCorrect_mem X.quorum
  have hclasses := M.mem_recoveryCorrect.mp hcorrect
  have hrel : v ∈ M.ReliableSigner :=
    M.mem_reliableSigner.mpr ⟨hclasses.1, hclasses.2.2⟩
  have hm := X.messages v hv
  calc
    x.history.length =
        (E.localHistory v x.epoch x.height).length :=
      congrArg List.length (E.emitted_from_state hm hrel)
    _ = x.height := E.local_height hm hrel

/-- A lower checkpoint certificate in one epoch is a prefix of a
higher certificate because their common reliable signer moved through
append-only local states. -/
theorem checkpointQC_prefix {x y : CheckpointData Value}
    (X : Model.Execution.CheckpointQC M E x)
    (Y : Model.Execution.CheckpointQC M E y)
    (he : x.epoch = y.epoch) (hh : x.height ≤ y.height) :
    x.history.IsPrefix y.history := by
  obtain ⟨v, hv, hgood⟩ :=
    M.exists_reliableSigner_mem_inter X.quorum Y.quorum
  have hx := X.messages v (Finset.mem_inter.mp hv).1
  have hy := Y.messages v (Finset.mem_inter.mp hv).2
  have hs := E.local_extension (e := x.epoch) hgood hh
  have hxs := E.emitted_from_state hx hgood
  have hys := E.emitted_from_state hy hgood
  rw [← he] at hys
  rw [← hxs, ← hys] at hs
  exact hs

/-- Any two checkpoint certificates from one epoch bind
prefix-consistent histories. -/
theorem checkpointQC_compatible {x y : CheckpointData Value}
    (X : Model.Execution.CheckpointQC M E x)
    (Y : Model.Execution.CheckpointQC M E y)
    (he : x.epoch = y.epoch) :
    Compatible x.history y.history := by
  rcases Nat.le_total x.height y.height with hxy | hyx
  · exact Or.inl (checkpointQC_prefix M E X Y he hxy)
  · exact Or.inr (checkpointQC_prefix M E Y X he.symm hyx)

/-- Two finality certificates in one epoch cannot finalize conflicting
histories. -/
theorem finalityQC_compatible {x y : CheckpointData Value}
    (X : Model.Execution.FinalityQC M E x)
    (Y : Model.Execution.FinalityQC M E y)
    (he : x.epoch = y.epoch) :
    Compatible x.history y.history :=
  checkpointQC_compatible M E X.checkpointQC Y.checkpointQC he

/-- A finality quorum yields a recovery-correct validator that recorded
the concrete checkpoint certificate before emitting its witness. -/
theorem exists_recoveryCorrect_recorder {x : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E x) :
    ∃ v ∈ M.RecoveryCorrect, E.recorded v x := by
  obtain ⟨v, hv, hcorrect⟩ :=
    M.exists_recoveryCorrect_mem F.quorum
  refine ⟨v, hcorrect, ?_⟩
  have hsender : (F.messages v hv).sender ∈ M.RecoveryCorrect := by
    simpa only [F.sender_eq v hv] using hcorrect
  simpa only [F.sender_eq v hv] using (F.messages v hv).recorded hsender

end Execution

end Model

end LeanDag.Hybrid.Checkpoint
