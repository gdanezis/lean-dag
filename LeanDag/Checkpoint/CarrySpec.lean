import LeanDag.Checkpoint.CommitSpec

/-!
# Human-reviewed specification for proposals carried in blocks

This file closes the gap between abstract checkpoint emissions and the DAG.
A `content` map reads an optional checkpoint proposal off every block payload,
making emission equivalent to block authorship. Proposals become DAG data:
decidable, disseminated with blocks, and auditable.

`CarryProofs.lean` uses these clauses to construct the `Execution` and
`SigningRule`. The `Execution` invariants are not weakened: they are
restated here per block (`content_from_state`, `local_extension`) so that
emission is a definition on DAG data rather than an abstract predicate.

**Trust boundary:** The VM remains an abstract deterministic map. The storage
clauses (`content_from_state`, `local_extension`, `stores`) are contracts
representing the crash-recovery substrate's obligations. `proposes` is the
sole protocol rule: a rule-following validator (`M.alive`) writes the
checkpoint of every slot it settles into a block it authors. The witness phase still reads storage
rather than a second block round.
-/

namespace LeanDag.Checkpoint

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} {Value : Type*}

namespace SigningFaults

variable (M : SigningFaults Validator)

/-- **A signing run whose proposals ride in blocks.** Over a rule's
universe, a `content` map exposes each block's optional proposal; the
clauses tie reliable signers' block contents to their durable state and
oblige rule-following validators to carry what they settle. Emission is
defined from authorship in `CarryProofs.lean`. -/
structure CarriedSigning (R : DagRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (vm : DeterministicVM (BlockId := BlockId) (Value := Value))
    (content : Payload → Option (CheckpointData Value)) where
  /-- Genesis history adopted for each recovery epoch. -/
  genesis : ℕ → History Value
  /-- Durable local application history at each epoch and height.
  Supplied by the storage layer: crash recovery restores it. -/
  localHistory : Validator → ℕ → ℕ → History Value
  /-- Durably stored checkpoints. Supplied by the storage layer. -/
  recorded : Validator → CheckpointData Value → Prop
  /-- Each validator's local DAG. -/
  view : Validator → R.View U
  /-- The validators following the rule form a signing quorum, as in
  `SigningRule`. -/
  quorum : M.q ≤ M.alive.card
  /-- **Storage contract.** A reliable signer's carried proposal matches
  its durable state: genesis-extending, state-valued, and indexed by height. -/
  content_from_state : ∀ b ∈ R.ids U, (R.block U b).creator ∈ M.reliableSigner →
    ∀ x, content (R.block U b).payload = some x →
      (genesis x.epoch).IsPrefix x.history ∧
      x.history = localHistory (R.block U b).creator x.epoch x.height ∧
      (localHistory (R.block U b).creator x.epoch x.height).length = x.height
  /-- **Storage contract.** Durable state extends with height. -/
  local_extension : ∀ {v e h₁ h₂}, v ∈ M.reliableSigner → h₁ ≤ h₂ →
    (localHistory v e h₁).IsPrefix (localHistory v e h₂)
  /-- **The protocol rule**: sign what you commit, as block content — a
  rule-following validator authors a block carrying the checkpoint of
  every slot it has settled on its own view. -/
  proposes : ∀ v ∈ M.alive, ∀ {slot : ℕ} {block : BlockId},
    R.Decided S (view v) slot (some block) →
      ∃ b ∈ R.ids U, (R.block U b).creator = v ∧
        content ((R.block U b).payload) = some (vm.checkpointAfterCommit slot block)
  /-- **Storage contract.** An available signer retains every certified
  checkpoint it carried: once a signing quorum of blocks carries `x` and
  its own block does, `x` is recorded. Recording is conditioned on the
  quorum because recovery (`RecoveryRound.submits_recorded`) must
  produce a valid certificate for every recorded checkpoint. -/
  stores : ∀ v ∈ M.recoveryCorrect, ∀ {x : CheckpointData Value} {S : Finset Validator},
    M.q ≤ S.card →
    (∀ w ∈ S, ∃ b ∈ R.ids U, (R.block U b).creator = w ∧
      content ((R.block U b).payload) = some x) →
    (∃ b ∈ R.ids U, (R.block U b).creator = v ∧
      content ((R.block U b).payload) = some x) →
    recorded v x

end SigningFaults

end LeanDag.Checkpoint
