import LeanDag.Hybrid.Checkpoint.BaseSpec

/-!
# Human-reviewed recovery specification

Every declaration in this file is part of the trusted recovery model.
Human reviewers must check the authenticated-broadcast contract, local
validation predicate, handler-state obligations, selection semantics,
and epoch-transition requirements. Structure fields are contract
obligations: concrete instances must prove them, while generic recovery
theorems use them as assumptions. `RecoveryProofs.lean` constructs a
selector and machine-checks consequences of this specification.

`RecoveryCorrect` membership alone is not a recovery protocol. The
specification additionally requires correct certificate submission,
authenticated broadcast, local validation, deterministic selection,
and adoption of the selected history as the next epoch's genesis. It
recovers checkpoint state, not the discarded DAG or its runtime state.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

namespace FlexibleFaults

variable (M : FlexibleFaults Validator Value)

namespace Execution

variable (E : M.Execution Value)

/-- The Dolev--Strong-style contract used by recovery. It says nothing
about checkpoint validity or local certificate storage. -/
structure AuthenticatedBroadcast where
  /-- Authenticated protocol inputs, indexed by sender and payload. -/
  input : Validator →
    CertificatePayload (Validator := Validator) (Value := Value) → Prop
  /-- Messages delivered to a recipient with their authenticated sender. -/
  delivered : Validator → Validator →
    CertificatePayload (Validator := Validator) (Value := Value) → Prop
  /-- A delivered message was an actual input by its claimed sender. -/
  integrity :
    ∀ {receiver sender payload},
      delivered receiver sender payload → input sender payload
  /-- Correct recipients agree on every authenticated delivery. -/
  agreement :
    ∀ {v w}, v ∈ M.RecoveryCorrect → w ∈ M.RecoveryCorrect →
      ∀ sender payload,
        delivered v sender payload ↔ delivered w sender payload
  /-- An actual input from a correct sender reaches every correct
  recipient. -/
  delivery :
    ∀ {sender receiver payload},
      sender ∈ M.RecoveryCorrect → receiver ∈ M.RecoveryCorrect →
      input sender payload → delivered receiver sender payload

/-- Explicit local validation for a delivered recovery payload. The
closing epoch check rejects stale and future certificates; `Valid`
checks quorum size and every concrete signer proposal. -/
def validateCertificate (epoch : ℕ)
    (payload : CertificatePayload (Validator := Validator) (Value := Value)) :
    Prop :=
  payload.checkpoint.epoch = epoch ∧
    CertificatePayload.Valid M E payload

/-- The canonical checkpoint used when the closing epoch has no
validated certificate. It is determined by execution state rather than
supplied by the transition caller. -/
def epochGenesis (epoch : ℕ) : CheckpointData Value where
  height := (E.genesis epoch).length
  epoch := epoch
  history := E.genesis epoch

/-- Recovery-handler state separates protocol submission and local
certificate validation from the broadcast channel. -/
structure RecoveryRound (B : AuthenticatedBroadcast M) (epoch : ℕ) where
  /-- Finite set of checkpoint contents parsed and validated locally. -/
  validated : Validator → Finset (CheckpointData Value)
  /-- A correct handler inputs a concrete valid payload for every
  closing-epoch checkpoint certificate it recorded. Retained records
  from older epochs impose no submission obligation in this round.

  This clause carries two obligations. Requiring the payload to be
  input is submission; requiring it to validate is what makes a
  closing-epoch record a certified checkpoint, which is the reading
  `recorded_certified` extracts. -/
  submits_recorded :
    ∀ {sender checkpoint}, sender ∈ M.RecoveryCorrect →
      E.recorded sender checkpoint →
      checkpoint.epoch = epoch →
      ∃ payload, payload.checkpoint = checkpoint ∧
        validateCertificate (M := M) (E := E) epoch payload ∧
          B.input sender payload
  /-- Required handler-state invariant: the finite validated set
  contains exactly checkpoint contents of delivered payloads accepted
  by the explicit local verifier. -/
  validated_spec :
    ∀ {receiver checkpoint}, checkpoint ∈ validated receiver ↔
      ∃ sender payload, B.delivered receiver sender payload ∧
        validateCertificate (M := M) (E := E) epoch payload ∧
        payload.checkpoint = checkpoint

namespace RecoveryRound

variable {B : AuthenticatedBroadcast M} {epoch : ℕ}
variable (R : RecoveryRound M E B epoch)

/-- A checkpoint is highest in a finite set when it belongs to the set
and no member has greater height. -/
def IsHighest (s : Finset (CheckpointData Value))
    (checkpoint : CheckpointData Value) :
    Prop :=
  checkpoint ∈ s ∧ ∀ other ∈ s, other.height ≤ checkpoint.height

/-- Declarative recovery-selection semantics. A nonempty validated set
selects one of its highest checkpoints; an empty set retains the
canonical genesis of the closing epoch. Concrete selection code belongs
in the proof layer and must satisfy this predicate. -/
def IsSelected (receiver : Validator)
    (checkpoint : CheckpointData Value) : Prop :=
  if (R.validated receiver).Nonempty then
    IsHighest (R.validated receiver) checkpoint
  else
    checkpoint = epochGenesis M E epoch

/-- Recovery-transition contract: adopt a checkpoint satisfying
`IsSelected` as the genesis used by the next epoch's signing state. -/
structure EpochTransition (receiver : Validator) where
  /-- The receiver follows the recovery protocol. -/
  receiver_correct : receiver ∈ M.RecoveryCorrect
  /-- Checkpoint chosen according to the recovery selection semantics. -/
  selected : CheckpointData Value
  /-- The chosen checkpoint is highest, or genesis when none validates. -/
  selection : IsSelected M E R receiver selected
  /-- The next epoch is the successor of the closing epoch. -/
  next_epoch : ℕ
  /-- Epoch numbering advances once. -/
  next_epoch_eq : next_epoch = epoch + 1
  /-- Subsequent checkpoint state starts from the selected history. -/
  adopted :
    E.genesis next_epoch = selected.history

end RecoveryRound

end Execution

end FlexibleFaults

end LeanDag.Hybrid.Checkpoint
