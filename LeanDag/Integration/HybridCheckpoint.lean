import LeanDag.Hybrid.Properties
import LeanDag.Checkpoint.CommitProofs
import LeanDag.Integration.FaultClasses

/-!
# Resilient checkpoints for Hybrid

The paper's flexible fault model is the hybrid Byzantine and crash
classes plus alive-but-corrupt signers, at the resilience bound
`fabc + 3·fb + 2·fc < n`. It is `FaultClasses` at Hybrid's classes
(`Integration/FaultClasses.lean`), so one `SigningFaults` instance: the
quorum is the hybrid `q`, the reliable signers are everyone outside the
Byzantine and AbC classes, the recovery-correct validators are the
reliable signers that do not crash, and the rule-following validators
are everyone outside the Byzantine and crash classes, AbC included. The
two counting laws are the resilience bound read at the quorum.

The rule-following validators are Hybrid's `Correct`, which under this
model contains the AbC validators. They are a signing quorum by the
hybrid bound alone (`quorum_alive`) and a quorum of the core reliability
(`isQuorum_alive`), so AbC validators complete checkpoint quorums and
count toward the liveness bridge's DAG premise.
`LeanDagTest/Hybrid/CheckpointCommit.lean` assembles the pieces.
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

/-- The flexible model as fault classes on plain sets: Hybrid's
Byzantine and crash classes and their bounds, with the AbC class. -/
def classes : FaultClasses Validator where
  f := H.fb
  c := H.fc
  fa := M.fabc
  byzantine := H.byzantine
  crash := H.crash
  abc := M.abc
  card_byzantine := H.card_byzantine
  card_crash := H.card_crash
  card_abc := M.card_abc
  resilient := by have := M.resilient; omega

/-- The flexible model as signing faults: the hybrid quorum, reliable
signers outside the Byzantine and AbC classes, recovery-correct
validators that also do not crash, and rule-following validators
outside the Byzantine and crash classes. It is `FaultClasses.signing`
at Hybrid's classes. -/
def signing : SigningFaults Validator := M.classes.signing

/-- The signing quorum is the hybrid quorum. -/
theorem signing_q : M.signing.q = Hybrid.q Validator := rfl

/-- The rule-following validators are Hybrid's `Correct`, the validators
outside the Byzantine and crash classes, whatever the AbC population:
AbC validators are among them. -/
theorem alive_eq : M.signing.alive = (Correct : Finset Validator) := by
  ext v
  simp [signing, classes, FaultClasses.signing, Correct]

/-- The rule-following validators form the signing quorum. AbC
validators count: this is the bridge's `quorum` with AbC present. -/
theorem quorum_alive : M.signing.q ≤ M.signing.alive.card :=
  M.classes.quorum_alive

/-- The rule-following validators are a quorum of the core reliability,
whatever the AbC population: the liveness bridge's DAG premise with AbC
present. -/
theorem isQuorum_alive :
    (coreReliability Validator).IsQuorum M.signing.alive := by
  rw [alive_eq]
  exact (coreReliability Validator).isQuorum_correct

end FlexibleFaults

end Integration

end LeanDag
