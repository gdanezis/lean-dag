import LeanDag.Hybrid.Rules
/-!
# Human-reviewed base specification for resilient checkpoints

Every declaration here is part of the trusted protocol model; human
reviewers must check that its types, predicates, fault bounds and
structure fields express the intended checkpoint protocol, since proof
files can only check consequences of these declarations, not that they
match an implementation or paper. Checkpoint signatures come from
per-validator protocol state, and histories are compared by equality —
the minimal abstraction of collision-resistant content binding, with no
cryptographic conclusion assumed.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

/-- A history is the content committed by a checkpoint state root. -/
abbrev History (Value : Type*) := List Value

/-- Content bound by a checkpoint proposal. -/
structure CheckpointData (Value : Type*) where
  /-- Global application height. -/
  height : ℕ
  /-- Recovery epoch containing the checkpoint. -/
  epoch : ℕ
  /-- Content bound by the checkpoint state root. -/
  history : History Value
  deriving DecidableEq

/-- An authenticated checkpoint proposal message. -/
structure ChkProp (Validator Value : Type*) where
  /-- Authenticated sender. -/
  sender : Validator
  /-- Proposed checkpoint content. -/
  checkpoint : CheckpointData Value
  deriving DecidableEq

/-- Checkpoint-specific extension of the imported `HybridFaults` model:
`H` supplies the Byzantine/crash classes and bounds, this structure adds
the AbC class and the stronger checkpoint resilience bound. The
disjointness fields are unused by current safety derivations, whose
cardinality arguments use union upper bounds valid even if classes
overlap. -/
structure Model (Validator Value : Type*) [Fintype Validator]
    [DecidableEq Validator] [H : HybridFaults Validator] where
  /-- Alive-but-corrupt fault bound. -/
  fabc : ℕ
  /-- Validators that may violate the normal signing rules. -/
  abc : Finset Validator
  /-- Paper-faithfulness condition: Byzantine and AbC are distinct.
  This condition is not required by the current safety derivations. -/
  disjoint_byzantine : Disjoint H.byzantine abc
  /-- Paper-faithfulness condition: crash-prone and AbC are distinct.
  This condition is not required by the current safety derivations. -/
  disjoint_crash : Disjoint H.crash abc
  /-- The actual AbC population respects its bound. -/
  card_abc : abc.card ≤ fabc
  /-- The resilient quorum-intersection bound. -/
  resilient :
    fabc + 3 * H.fb + 2 * H.fc < Fintype.card Validator

namespace Model

variable (M : Model Validator Value)

/-- Validators whose checkpoint protocol state is enforced. -/
def ReliableSigner : Finset Validator :=
  (H.byzantine ∪ M.abc)ᶜ

/-- Reliable signers that also remain available during recovery.
Membership identifies eligible recovery participants; it does not by
itself imply that checkpoint recovery occurs. -/
def RecoveryCorrect : Finset Validator :=
  M.ReliableSigner \ H.crash

/-- A protocol execution exposes local checkpoint state, emitted
messages, and recorded certificates — required execution invariants,
not conclusions proved by this structure; signatures inherit safety
from the state clauses through `emitted_from_state`. -/
structure Execution (Value : Type*) where
  /-- Genesis history adopted for each recovery epoch. -/
  genesis : ℕ → History Value
  /-- Local application history at each epoch and global height. -/
  localHistory : Validator → ℕ → ℕ → History Value
  /-- Authenticated checkpoint-proposal messages emitted in the run. -/
  emitted : ChkProp Validator Value → Prop
  /-- Concrete checkpoint certificates stored by a validator. -/
  recorded : Validator → CheckpointData Value → Prop
  /-- Every reliable proposal extends the genesis adopted for its epoch. -/
  genesis_prefix :
    ∀ {m}, emitted m → m.sender ∈ M.ReliableSigner →
      (genesis m.checkpoint.epoch).IsPrefix m.checkpoint.history
  /-- Reliable local state evolves only by history extension within an
  epoch. -/
  local_extension :
    ∀ {v e h₁ h₂}, v ∈ M.ReliableSigner → h₁ ≤ h₂ →
      (localHistory v e h₁).IsPrefix (localHistory v e h₂)
  /-- A reliable sender emits only the checkpoint proposal represented
  by its unique local state at that `(epoch,height)`. -/
  emitted_from_state :
    ∀ {m}, emitted m → m.sender ∈ M.ReliableSigner →
      m.checkpoint.history =
        localHistory m.sender m.checkpoint.epoch m.checkpoint.height
  /-- A reliable validator's local history is indexed by its actual
  global height. Byzantine and AbC emissions remain unconstrained. -/
  local_height :
    ∀ {m}, emitted m → m.sender ∈ M.ReliableSigner →
      (localHistory m.sender m.checkpoint.epoch
        m.checkpoint.height).length = m.checkpoint.height

namespace Execution

variable (E : M.Execution Value)

/-- A first-phase certificate is a quorum of actual authenticated
`ChkProp` messages matching one checkpoint. -/
structure CheckpointQC (checkpoint : CheckpointData Value) where
  /-- Distinct authenticated senders. -/
  signers : Finset Validator
  /-- The checkpoint phase uses the hybrid quorum. -/
  quorum : Hybrid.q Validator ≤ signers.card
  /-- Every signer emitted a proposal for this exact checkpoint. -/
  messages :
    ∀ v ∈ signers, E.emitted ⟨v, checkpoint⟩

/-- Concrete recovery wire payload for a checkpoint certificate.
The payload carries the checkpoint and its signer set. Validity is
checked separately, so authenticated broadcast may also carry malformed
payloads. -/
structure CertificatePayload where
  /-- Checkpoint content claimed by the certificate. -/
  checkpoint : CheckpointData Value
  /-- Distinct authenticated proposal senders claimed by the certificate. -/
  signers : Finset Validator

namespace CertificatePayload

/-- Explicit certificate verifier semantics. It checks the quorum and
every signer-indexed authenticated proposal contained in the payload;
this predicate is local protocol logic, not a broadcast assumption. -/
def Valid (payload : CertificatePayload (Validator := Validator)
    (Value := Value)) : Prop :=
  Hybrid.q Validator ≤ payload.signers.card ∧
    ∀ v ∈ payload.signers,
      E.emitted ⟨v, payload.checkpoint⟩

end CertificatePayload

/-- A second-phase witness says `sender` received and validated a
concrete first-phase certificate for exactly `checkpoint`, retained in
the message object so later proofs can inspect it directly. For a
recovery-correct sender, `recorded` requires durable storage before the
witness is emitted, so a finality quorum yields an honest, available
resubmitter during recovery; other sender classes make no such
promise. -/
structure ChkWitness (checkpoint : CheckpointData Value) where
  /-- Authenticated validator claiming to have validated the certificate. -/
  sender : Validator
  /-- The concrete first-phase certificate received by the sender. Its
  dependent type binds the witness to this exact `checkpoint`. -/
  certificate : Model.Execution.CheckpointQC M E checkpoint
  /-- If the sender follows recovery and remains available, it stored
  the checkpoint before witnessing it. No condition is imposed when the
  sender is outside `RecoveryCorrect`. -/
  recorded :
    sender ∈ M.RecoveryCorrect → E.recorded sender checkpoint

/-- A finality certificate is a quorum of actual witness messages for
one checkpoint, rather than an arbitrary possession predicate. -/
structure FinalityQC (checkpoint : CheckpointData Value) where
  /-- A concrete first-phase certificate for the finalized content. -/
  checkpointQC : Model.Execution.CheckpointQC M E checkpoint
  /-- Distinct witness senders. -/
  witnesses : Finset Validator
  /-- The witness phase uses the hybrid quorum. -/
  quorum : Hybrid.q Validator ≤ witnesses.card
  /-- Every listed sender emitted a concrete validated witness. -/
  messages :
    ∀ v ∈ witnesses, Model.Execution.ChkWitness M E checkpoint
  /-- Witness authentication binds each message to its listed sender. -/
  sender_eq : ∀ v (hv : v ∈ witnesses), (messages v hv).sender = v

end Execution

end Model

/-- Two checkpoint histories are consistent when either extends the
other. -/
def Compatible (x y : History Value) : Prop :=
  x.IsPrefix y ∨ y.IsPrefix x

end LeanDag.Hybrid.Checkpoint
