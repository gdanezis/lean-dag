import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Agree
import LeanDag.Checkpoint.BaseSpec

/-!
# Human-reviewed commit-to-checkpoint specification

This file is the trust boundary between a DAG rule and checkpoint
signing. The rule fixes the committed block at each slot through its
carrier's `Decided`; `DeterministicVM` abstracts deterministic execution
of that commit into checkpoint content. `SigningRule` states the
checkpoint protocol as a rule over a whole run rather than as a promise
about one commit: a correct online validator proposes the checkpoint of
every slot it has settled on its own view, and witnesses a first-phase
certificate for every checkpoint it proposed.

Nothing here names a protocol. The bridge reads a `DagRule` and the
properties beside it: `Agree` ties every validator's own verdict to the
commit, and a `Support` with `Commits` supplies the verdicts from
production and certification. A protocol that shows those properties
has the bridge; `Integration/HybridCheckpoint.lean` is Hybrid's
instance.

The VM and the rule are contract obligations, not consequences of the
DAG rule. The claims at the end of this file are the bridge's theorem
statements; `CommitProofs.lean` proves them. Reviewing this file
reviews the whole bridge.
-/

namespace LeanDag.Checkpoint

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} {Value : Type*}

/-- Deterministic execution interface mapping a slot and block to one
checkpoint value. Settlement is imposed by the claims that use this
interface; the VM implementation and its application-state semantics
remain outside this model. -/
structure DeterministicVM where
  /-- Application state after executing the committed block for a slot. -/
  checkpointAfterCommit : ℕ → BlockId → CheckpointData Value

namespace SigningFaults

variable (M : SigningFaults Validator)

namespace Execution

variable (E : M.Execution Value)

/-- The checkpoint signing protocol, as a rule over one universe of a
DAG rule.

`proposes` ties a proposal to the proposer's own decision: the
hypothesis is the validator's verdict on its own view, so a proposal
cannot be owed for a slot the validator has not settled. `witnesses`
ties the second phase to the first: a validator owes a witness for a
certificate of a checkpoint it proposed itself. Both are obligations,
not restrictions: the rule does not say what a validator does with a
certificate for a checkpoint it did not propose, and `Execution` has no
witness-emission predicate over which such a restriction could be
stated. `quorum` is the secure-base regime: the online correct
validators alone reach the signing threshold. -/
structure SigningRule (R : DagRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) where
  /-- The online correct validators form a signing quorum. -/
  quorum : M.q ≤ M.recoveryCorrect.card
  /-- Each validator's local DAG. -/
  view : Validator → R.View U
  /-- Sign what you commit. -/
  proposes :
    ∀ v ∈ M.recoveryCorrect, ∀ {slot : ℕ} {block : BlockId},
      R.Decided S (view v) slot (some block) →
        E.emitted ⟨v, vm.checkpointAfterCommit slot block⟩
  /-- Witness a certificate for what you proposed. -/
  witnesses :
    ∀ v ∈ M.recoveryCorrect, ∀ {checkpoint : CheckpointData Value},
      E.emitted ⟨v, checkpoint⟩ →
        SigningFaults.Execution.CheckpointQC M E checkpoint →
          { witness : SigningFaults.Execution.ChkWitness M E checkpoint //
            witness.sender = v }

/-! ## Claims

The propositions below are the theorem statements of this bridge. They
are stated here so that the review boundary is this file alone;
`CommitProofs.lean` proves each one and its bodies need no reading. -/

/-- Claim: under agreement, a commit that every online correct validator
has settled on its own view has a first-phase certificate. Agreement
makes the validators' verdicts equal the given commit, so the rule's
proposals are all for the same checkpoint. -/
def CommitCertified (R : DagRule Validator BlockId Payload)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  Agree R →
  ∀ (S : Slots Validator) {U : R.Universe} (P : SigningRule M E R S U vm)
    {V : R.View U} {slot : ℕ} {block : BlockId},
    R.Decided S V slot (some block) →
    (∀ v ∈ M.recoveryCorrect, ∃ b, R.Decided S (P.view v) slot (some b)) →
    Nonempty (SigningFaults.Execution.CheckpointQC M E
      (vm.checkpointAfterCommit slot block))

/-- Claim: under agreement, a commit that every online correct validator
has settled on its own view has a finality certificate. -/
def CommitFinalized (R : DagRule Validator BlockId Payload)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  Agree R →
  ∀ (S : Slots Validator) {U : R.Universe} (P : SigningRule M E R S U vm)
    {V : R.View U} {slot : ℕ} {block : BlockId},
    R.Decided S V slot (some block) →
    (∀ v ∈ M.recoveryCorrect, ∃ b, R.Decided S (P.view v) slot (some b)) →
    Nonempty (SigningFaults.Execution.FinalityQC M E
      (vm.checkpointAfterCommit slot block))

/-- Claim: liveness delivers a finalized checkpoint. Under `Commits` for
the rule's support at a reliability whose quorum the online correct
validators form, a slot they lead, populated across the wave and with
every candidate certified, reaches checkpoint finality on views caught
up to the wave. No commit is assumed; the proof derives the decisions it
needs from the support's law. -/
def LiveCommitFinalized (R : DagRule Validator BlockId Payload) (sp : Support R)
    (rel : Reliability Validator)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  Agree R → CommitsCandidate R → sp.Commits rel →
  ∀ (S : Slots Validator) {U : R.Universe} (P : SigningRule M E R S U vm) {slot : ℕ},
    rel.IsQuorum M.recoveryCorrect →
    (∀ n, S.slotRound slot ≤ n → n ≤ S.slotRound slot + sp.waveAt (S.kind slot) →
      Properties.PopulatedOn R U M.recoveryCorrect n) →
    (∀ L, R.IsCandidate S U slot L →
      sp.certifiesAt U M.recoveryCorrect (S.slotRound slot) (S.kind slot) L) →
    (∀ v ∈ M.recoveryCorrect,
      Properties.CoversUpto R (P.view v) (S.slotRound slot + sp.waveAt (S.kind slot))) →
    S.leader slot ∈ M.recoveryCorrect →
    ∃ L, R.IsCandidate S U slot L ∧
      Nonempty (SigningFaults.Execution.FinalityQC M E
        (vm.checkpointAfterCommit slot L))

end Execution

end SigningFaults

/-- Claim: agreement rules out a checkpoint fork. Commits for one slot in
any two views yield the same checkpoint content. This claim is about the
VM and the rule alone, so it mentions neither the fault model nor an
execution. -/
def CommitCheckpointUnique (R : DagRule Validator BlockId Payload)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  Agree R →
  ∀ (S : Slots Validator) {U : R.Universe} {V₁ V₂ : R.View U} {slot : ℕ}
    {block₁ block₂ : BlockId},
    R.Decided S V₁ slot (some block₁) →
    R.Decided S V₂ slot (some block₂) →
    vm.checkpointAfterCommit slot block₁ =
      vm.checkpointAfterCommit slot block₂

end LeanDag.Checkpoint
