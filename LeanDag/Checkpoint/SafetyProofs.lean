import LeanDag.Checkpoint.BaseSpec
import LeanDag.Common.Counting
/-!
# Machine-checked checkpoint safety derivations

Human reviewers must inspect the theorem statements to confirm they
express the intended guarantees; once those and `BaseSpec.lean` are
accepted, the `by` bodies need not be trusted by inspection. Forked
histories are permitted inputs — the results prove that, given any
such execution, conflicting branches cannot both acquire checkpoint
certificates under the two bounds of `SigningFaults`, without invoking
any DAG rule's own non-equivocation or agreement theorems.
-/

namespace LeanDag.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]

namespace SigningFaults

variable (M : SigningFaults Validator)

/-- Two quorums share a reliable signer. -/
theorem exists_reliableSigner_mem_inter {a b : Finset Validator}
    (ha : M.q ≤ a.card) (hb : M.q ≤ b.card) :
    ∃ v ∈ a ∩ b, v ∈ M.reliableSigner := by
  have hint := M.intersect
  obtain ⟨v, hv, hgood⟩ := exists_mem_inter_notMem (A := a) (B := b) (Bad := M.reliableSignerᶜ)
    le_rfl (by omega)
  exact ⟨v, hv, by simpa using hgood⟩

/-- Every quorum contains a reliable signer. -/
theorem exists_reliableSigner_mem {a : Finset Validator}
    (ha : M.q ≤ a.card) :
    ∃ v ∈ a, v ∈ M.reliableSigner := by
  obtain ⟨v, hv, hgood⟩ := M.exists_reliableSigner_mem_inter ha ha
  exact ⟨v, (Finset.mem_inter.mp hv).1, hgood⟩

/-- Every quorum contains a recovery-correct validator. -/
theorem exists_recoveryCorrect_mem {a : Finset Validator}
    (ha : M.q ≤ a.card) :
    ∃ v ∈ a, v ∈ M.recoveryCorrect := by
  have hreach := M.reach
  have hnsub : ¬ a ⊆ M.recoveryCorrectᶜ := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨v, hv, hgood⟩ := Finset.not_subset.mp hnsub
  exact ⟨v, hv, by simpa using hgood⟩

namespace Execution

variable (E : M.Execution Value)

namespace CertificatePayload

/-- A payload accepted by the verifier yields a genuine checkpoint QC. -/
def toCheckpointQC (payload : CertificatePayload (Validator := Validator)
    (Value := Value))
    (valid : CertificatePayload.Valid M E payload) :
    SigningFaults.Execution.CheckpointQC M E payload.checkpoint where
  signers := payload.signers
  quorum := valid.1
  messages := valid.2

end CertificatePayload

/-- A reliable sender's two messages at one epoch and height carry the
same content. -/
theorem checkpoint_eq_of_reliable_messages
    {v : Validator} {x y : CheckpointData Value}
    (hv : v ∈ M.reliableSigner)
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
    (X : SigningFaults.Execution.CheckpointQC M E x)
    (Y : SigningFaults.Execution.CheckpointQC M E y)
    (he : x.epoch = y.epoch) (hh : x.height = y.height) : x = y := by
  obtain ⟨v, hv, hgood⟩ :=
    M.exists_reliableSigner_mem_inter X.quorum Y.quorum
  have hx := X.messages v (Finset.mem_inter.mp hv).1
  have hy := Y.messages v (Finset.mem_inter.mp hv).2
  exact checkpoint_eq_of_reliable_messages M E hgood hx hy he hh

/-- Every checkpoint certificate has a correctly bound global height.
Unreliable validators may emit arbitrary checkpoints; quorum counting
supplies one reliable signer whose local execution state fixes the
certified history length. -/
theorem checkpointQC_height_bound {x : CheckpointData Value}
    (X : SigningFaults.Execution.CheckpointQC M E x) :
    x.history.length = x.height := by
  obtain ⟨v, hv, hrel⟩ := M.exists_reliableSigner_mem X.quorum
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
    (X : SigningFaults.Execution.CheckpointQC M E x)
    (Y : SigningFaults.Execution.CheckpointQC M E y)
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
    (X : SigningFaults.Execution.CheckpointQC M E x)
    (Y : SigningFaults.Execution.CheckpointQC M E y)
    (he : x.epoch = y.epoch) :
    Compatible x.history y.history := by
  rcases Nat.le_total x.height y.height with hxy | hyx
  · exact Or.inl (checkpointQC_prefix M E X Y he hxy)
  · exact Or.inr (checkpointQC_prefix M E Y X he.symm hyx)

/-- Two finality certificates in one epoch cannot finalize conflicting
histories. -/
theorem finalityQC_compatible {x y : CheckpointData Value}
    (X : SigningFaults.Execution.FinalityQC M E x)
    (Y : SigningFaults.Execution.FinalityQC M E y)
    (he : x.epoch = y.epoch) :
    Compatible x.history y.history :=
  checkpointQC_compatible M E X.checkpointQC Y.checkpointQC he

/-- A finality quorum yields a recovery-correct validator that recorded
the concrete checkpoint certificate before emitting its witness. -/
theorem exists_recoveryCorrect_recorder {x : CheckpointData Value}
    (F : SigningFaults.Execution.FinalityQC M E x) :
    ∃ v ∈ M.recoveryCorrect, E.recorded v x := by
  obtain ⟨v, hv, hcorrect⟩ :=
    M.exists_recoveryCorrect_mem F.quorum
  refine ⟨v, hcorrect, ?_⟩
  have hsender : (F.messages v hv).sender ∈ M.recoveryCorrect := by
    simpa only [F.sender_eq v hv] using hcorrect
  simpa only [F.sender_eq v hv] using (F.messages v hv).recorded hsender

end Execution

end SigningFaults

end LeanDag.Checkpoint
