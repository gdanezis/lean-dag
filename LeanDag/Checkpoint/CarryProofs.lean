import LeanDag.Checkpoint.CarrySpec
import LeanDag.Checkpoint.CommitProofs

/-!
# Machine-checked derivations for proposals carried in blocks

A `CarriedSigning` run yields an `Execution` whose `emitted` is block
authorship, with each execution invariant read off the storage
contract's per-block clauses, and a `SigningRule` over it whose
`proposes` is the content rule and whose witness promise is storage of
the certified checkpoint. The commit bridge's claims then apply
unchanged; `commitFinalized` is restated here for carried runs.
-/

namespace LeanDag.Checkpoint

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} {Value : Type*}

namespace SigningFaults

variable {M : SigningFaults Validator}
variable {R : DagRule Validator BlockId Payload} {S : Slots Validator} {U : R.Universe}
variable {vm : DeterministicVM (BlockId := BlockId) (Value := Value)}
variable {content : Payload → Option (CheckpointData Value)}

namespace CarriedSigning

variable (C : M.CarriedSigning R S U vm content)

/-- **The execution a carried run defines**: a proposal is emitted
exactly when a block of the DAG carries it. The invariants are the
storage contract's clauses, read through that definition. -/
def execution : M.Execution Value where
  genesis := C.genesis
  localHistory := C.localHistory
  emitted := fun m =>
    ∃ b ∈ R.ids U, (R.block U b).creator = m.sender ∧
      content ((R.block U b).payload) = some m.checkpoint
  recorded := C.recorded
  genesis_prefix := by
    intro m hm hrel
    obtain ⟨b, hb, hc, hx⟩ := hm
    exact (C.content_from_state b hb (hc ▸ hrel) _ hx).1
  local_extension := C.local_extension
  emitted_from_state := by
    intro m hm hrel
    obtain ⟨b, hb, hc, hx⟩ := hm
    have h := (C.content_from_state b hb (hc ▸ hrel) _ hx).2.1
    rwa [hc] at h
  local_height := by
    intro m hm hrel
    obtain ⟨b, hb, hc, hx⟩ := hm
    have h := (C.content_from_state b hb (hc ▸ hrel) _ hx).2.2
    rwa [hc] at h

/-- **The signing rule a carried run follows**: `proposes` is the content
rule read through authorship-as-emission, and the witness promise is
storage of the certified checkpoint: the certificate's signers are the
quorum of carrying blocks `stores` asks for. -/
def rule : SigningFaults.Execution.SigningRule M C.execution R S U vm where
  quorum := C.quorum
  view := C.view
  proposes := fun v hv _ _ hdec => C.proposes v hv hdec
  witnesses := fun v _ _ he Q =>
    ⟨{ sender := v
       certificate := Q
       recorded := fun hv' => C.stores v hv' Q.quorum (fun w hw => Q.messages w hw) he },
     rfl⟩

/-- **A carried run finalizes every settled commit**: the commit bridge
at the derived execution and rule. -/
theorem commitFinalized (ha : Agree R) {V : R.View U} {slot : ℕ} {block : BlockId}
    (commit : R.Decided S V slot (some block))
    (hall : ∀ v ∈ M.alive,
      ∃ b, R.Decided S (C.view v) slot (some b)) :
    Nonempty (SigningFaults.Execution.FinalityQC M C.execution
      (vm.checkpointAfterCommit slot block)) :=
  SigningFaults.Execution.commitFinalized M C.execution vm ha S C.rule commit hall

end CarriedSigning

end SigningFaults

end LeanDag.Checkpoint
