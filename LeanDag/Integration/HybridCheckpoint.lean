import LeanDag.Hybrid.Properties
import LeanDag.Checkpoint.CommitProofs

/-!
# Resilient checkpoints for Hybrid

The paper's flexible fault model is the hybrid Byzantine and crash
classes plus alive-but-corrupt signers, at the resilience bound
`fabc + 3·fb + 2·fc < n`. It is one `SigningFaults` instance: the quorum
is the hybrid `q`, the reliable signers are everyone outside the
Byzantine and AbC classes, and the recovery-correct validators are the
reliable signers that do not crash. The two counting laws are the
resilience bound read at the quorum.

At `abc = ∅` the recovery-correct validators are the fully-correct class
`Correct`, a quorum of both the signing threshold and the core
reliability. That is what the commit bridge asks of a run at
`hybridRule`, alongside `HybridProperties.agree` and
`voteSupport_commits`; `LeanDagTest/Hybrid/CheckpointCommit.lean`
assembles the four.
-/

namespace LeanDag

namespace Integration

open LeanDag.Checkpoint

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

/-- The flexible fault model: the imported `HybridFaults` classes plus
alive-but-corrupt validators. `H` supplies the Byzantine/crash classes
and their bounds; this structure adds the AbC class and the stronger
checkpoint resilience bound. Setting `abc = ∅` recovers the base
hybrid model without removing crash faults.

The disjointness fields preserve the paper's interpretation as distinct
fault classes. The counting laws do not consume them: their cardinality
arguments use union upper bounds and remain valid if classes overlap. -/
structure FlexibleFaults (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] [H : HybridFaults Validator] where
  /-- Alive-but-corrupt fault bound. -/
  fabc : ℕ
  /-- Validators that may violate the normal signing rules. -/
  abc : Finset Validator
  /-- Paper-faithfulness condition: Byzantine and AbC are distinct. -/
  disjoint_byzantine : Disjoint H.byzantine abc
  /-- Paper-faithfulness condition: crash-prone and AbC are distinct. -/
  disjoint_crash : Disjoint H.crash abc
  /-- The actual AbC population respects its bound. -/
  card_abc : abc.card ≤ fabc
  /-- The resilient quorum-intersection bound. -/
  resilient :
    fabc + 3 * H.fb + 2 * H.fc < Fintype.card Validator

namespace FlexibleFaults

variable (M : FlexibleFaults Validator)

/-- The Byzantine and AbC classes together stay under their bounds. -/
theorem card_byzantine_union_abc :
    (H.byzantine ∪ M.abc).card ≤ H.fb + M.fabc :=
  le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add H.card_byzantine M.card_abc)

/-- The flexible model as signing faults: the hybrid quorum, reliable
signers outside the Byzantine and AbC classes, and recovery-correct
validators that also do not crash. -/
def signing : SigningFaults Validator where
  q := Hybrid.q Validator
  reliableSigner := (H.byzantine ∪ M.abc)ᶜ
  recoveryCorrect := (H.byzantine ∪ M.abc)ᶜ \ H.crash
  recoveryCorrect_subset := Finset.sdiff_subset
  intersect := by
    rw [compl_compl]
    have := M.card_byzantine_union_abc
    have := M.resilient
    unfold Hybrid.q
    omega
  reach := by
    have heq : ((H.byzantine ∪ M.abc)ᶜ \ H.crash)ᶜ = H.byzantine ∪ M.abc ∪ H.crash := by
      ext v
      simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [heq]
    have hcard : (H.byzantine ∪ M.abc ∪ H.crash).card ≤ H.fb + M.fabc + H.fc :=
      le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add M.card_byzantine_union_abc H.card_crash)
    have := M.resilient
    unfold Hybrid.q
    omega

/-- Without an AbC population the recovery-correct validators are the
fully-correct class. -/
theorem recoveryCorrect_eq (hno : M.abc = ∅) :
    M.signing.recoveryCorrect = (Correct : Finset Validator) := by
  ext v
  simp [signing, hno, Correct]

/-- Without an AbC population the online correct validators form the
signing quorum, by the inherited `fb`, `fc` bounds through
`card_correct`. -/
theorem quorum_of_noAbC (hno : M.abc = ∅) :
    M.signing.q ≤ M.signing.recoveryCorrect.card := by
  rw [recoveryCorrect_eq M hno]
  have := card_correct (Validator := Validator)
  simpa [signing, Hybrid.q] using this

/-- Without an AbC population the online correct validators are a quorum
of the core reliability. -/
theorem isQuorum_of_noAbC (hno : M.abc = ∅) :
    (coreReliability Validator).IsQuorum M.signing.recoveryCorrect := by
  rw [recoveryCorrect_eq M hno]
  exact (coreReliability Validator).isQuorum_correct

end FlexibleFaults

end Integration

end LeanDag
