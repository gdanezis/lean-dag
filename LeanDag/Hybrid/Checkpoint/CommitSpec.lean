import LeanDag.Hybrid.Liveness
import LeanDag.Hybrid.Checkpoint.BaseSpec

/-!
# Human-reviewed commit-to-checkpoint specification

This file is the trust boundary between base consensus and checkpoint
signing. Base consensus fixes the committed block at each slot;
`DeterministicVM` abstracts deterministic execution of that commit into
checkpoint content. `SigningRule` states the checkpoint protocol as a
rule over a whole run rather than as a promise about one commit: a
correct online validator proposes the checkpoint of every slot it has
settled on its own view, and witnesses a first-phase certificate for
every checkpoint it proposed.

The VM and the rule are contract obligations, not consequences of base
consensus. The claims at the end of this file are the bridge's theorem
statements; `CommitProofs.lean` proves them. Reviewing this file
reviews the whole bridge.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator BlockId Payload Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable [LinearOrder BlockId]
variable [S : Slots Validator]

/-- Deterministic execution interface mapping a slot and block to one
checkpoint value. Settlement is imposed by the claims that use this
interface; the VM implementation and its application-state semantics
remain outside this model. -/
structure DeterministicVM where
  /-- Application state after executing the committed block for a slot. -/
  checkpointAfterCommit : ℕ → BlockId → CheckpointData Value

namespace FlexibleFaults

variable (M : FlexibleFaults Validator Value)

namespace Execution

variable (E : M.Execution Value)

/-- The checkpoint signing protocol, as a rule over one DAG universe.

`proposes` ties a proposal to the proposer's own decision: the
hypothesis is the validator's `Decided` verdict on its own view, so a
proposal cannot be owed for a slot the validator has not settled.
`witnesses` ties the second phase to the first: a validator owes a
witness for a certificate of a checkpoint it proposed itself. Both are
obligations, not restrictions: the rule does not say what a validator
does with a certificate for a checkpoint it did not propose, and
`Execution` has no witness-emission predicate over which such a
restriction could be stated. Both fields are protocol rules, of the
same status as `Delivery.includes`; they are implementable but not
derived here. The inherited base model still contains Byzantine and
crash faults, and neither class is obliged to anything. -/
structure SigningRule (U : BlockUniverse Validator BlockId Payload) (k : ℕ)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) where
  /-- Byzantine and crash faults remain governed by `HybridFaults`; only
  the additional AbC checkpoint-fork class is disabled. -/
  noAbC : M.abc = ∅
  /-- Each validator's local DAG. -/
  view : Validator → View Validator BlockId Payload U
  /-- Sign what you commit. -/
  proposes :
    ∀ v ∈ M.RecoveryCorrect, ∀ {slot : ℕ} {block : BlockId},
      Hybrid.Decided k U (view v) slot (some block) →
        E.emitted ⟨v, vm.checkpointAfterCommit slot block⟩
  /-- Witness a certificate for what you proposed. -/
  witnesses :
    ∀ v ∈ M.RecoveryCorrect, ∀ {checkpoint : CheckpointData Value},
      E.emitted ⟨v, checkpoint⟩ →
        FlexibleFaults.Execution.CheckpointQC M E checkpoint →
          { witness : FlexibleFaults.Execution.ChkWitness M E checkpoint //
            witness.sender = v }

/-! ## Claims

The propositions below are the theorem statements of this bridge. They
are stated here so that the review boundary is this file alone;
`CommitProofs.lean` proves each one and its bodies need no reading. -/

/-- Claim: with no AbC population, the online correct validators form a
checkpoint quorum. This is the only counting fact the bridge derives;
it comes from the inherited `fb`, `fc` bounds through `card_correct`. -/
def RecoveryCorrectQuorum : Prop :=
  M.abc = ∅ → Hybrid.q Validator ≤ M.RecoveryCorrect.card

/-- Claim: a commit that every online correct validator has settled on
its own view has a first-phase certificate. Base safety makes the
validators' verdicts agree with the given commit, so the rule's
proposals are all for the same checkpoint. -/
def CommitCertified (Payload : Type*)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  ∀ {U : BlockUniverse Validator BlockId Payload} {k : ℕ}
    (P : SigningRule M E U k vm),
    HonestNoEquiv U → Hybrid.Admissible Validator k →
    ∀ {V : View Validator BlockId Payload U} {slot : ℕ} {block : BlockId},
      Hybrid.Decided k U V slot (some block) →
      (∀ v ∈ M.RecoveryCorrect,
        ∃ b, Hybrid.Decided k U (P.view v) slot (some b)) →
      Nonempty (FlexibleFaults.Execution.CheckpointQC M E
        (vm.checkpointAfterCommit slot block))

/-- Claim: a commit that every online correct validator has settled on
its own view has a finality certificate. -/
def CommitFinalized (Payload : Type*)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  ∀ {U : BlockUniverse Validator BlockId Payload} {k : ℕ}
    (P : SigningRule M E U k vm),
    HonestNoEquiv U → Hybrid.Admissible Validator k →
    ∀ {V : View Validator BlockId Payload U} {slot : ℕ} {block : BlockId},
      Hybrid.Decided k U V slot (some block) →
      (∀ v ∈ M.RecoveryCorrect,
        ∃ b, Hybrid.Decided k U (P.view v) slot (some b)) →
      Nonempty (FlexibleFaults.Execution.FinalityQC M E
        (vm.checkpointAfterCommit slot block))

/-- Claim: DAG liveness delivers a finalized checkpoint. Under the
hypotheses of `Hybrid.decided_of_leader_mem` over the online correct
validators, a slot led by one of them reaches checkpoint finality. No
commit is assumed; the proof derives the decisions it needs from
production, synchrony, and caught-up views. -/
def LiveCommitFinalized (Payload : Type*)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  ∀ {U : BlockUniverse Validator BlockId Payload} {k : ℕ}
    (P : SigningRule M E U k vm) {R slot : ℕ},
    HonestNoEquiv U → Hybrid.Admissible Validator k →
    SynchronisedOn U M.RecoveryCorrect R → R ≤ S.slotRound slot →
    PopulatedOn U M.RecoveryCorrect (S.slotRound slot) →
    PopulatedOn U M.RecoveryCorrect (S.slotRound slot + 1) →
    (∀ v ∈ M.RecoveryCorrect,
      (P.view v).CoversUpto (S.slotRound slot + 1)) →
    S.leader slot ∈ M.RecoveryCorrect →
    ∃ L, IsLeaderBlock U slot L ∧
      Nonempty (FlexibleFaults.Execution.FinalityQC M E
        (vm.checkpointAfterCommit slot L))

end Execution

end FlexibleFaults

variable (Validator)

/-- Claim: base-consensus safety rules out a checkpoint fork. Under the
hypotheses of `Hybrid.safety`, commits for one slot in any two views
yield the same checkpoint content. This claim is about the VM and base
consensus alone, so it mentions neither the fault model nor an
execution. -/
def CommitCheckpointUnique (Payload : Type*)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) : Prop :=
  ∀ {U : BlockUniverse Validator BlockId Payload} {k : ℕ},
    HonestNoEquiv U → Hybrid.Admissible Validator k →
    ∀ {V₁ V₂ : View Validator BlockId Payload U} {slot : ℕ}
      {block₁ block₂ : BlockId},
      Hybrid.Decided k U V₁ slot (some block₁) →
      Hybrid.Decided k U V₂ slot (some block₂) →
      vm.checkpointAfterCommit slot block₁ =
        vm.checkpointAfterCommit slot block₂

end LeanDag.Hybrid.Checkpoint
