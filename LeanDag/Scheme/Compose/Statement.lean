import LeanDag.Scheme.Model.Crash
import LeanDag.Checkpoint.CommitSpec
/-!
# The mechanisms composed — statement

`docs/mechanisms.md` M5. How the mechanisms over the family compose.

* **Checkpoints over a responsive run** (`CheckpointsResponsive`): at a
  tolerated row whose quorum meets the commit and certificate thresholds,
  when the validators following the signing rule run the family
  responsively past GST and their views are caught up to a slot's wave,
  a slot one of them leads reaches second-tier finality: some candidate of
  it gets a finality certificate.
* **Checkpoints with crashes** (`CheckpointsCrash`): the same, when they
  run the family with crashes and restarts, past `max gst tr`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Compose

open Checkpoint

/-- **Checkpoints over a responsive run.** -/
def CheckpointsResponsive : Prop :=
  ∀ (Validator BlockId Payload Value : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (q f : ℕ) [P.Quorate q]
    (M : SigningFaults Validator) (E : M.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) (rel : Reliability Validator),
    p.Tolerates honest f q → p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ (S : Slots Validator) (U : (schemeRule p σ).Universe)
      (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm)
      (V : (schemeRule p σ).View U) (slot : ℕ),
      reactiveLive p σ rel S V M.alive slot (slot + 1) →
      (∀ v ∈ M.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
        (S.slotRound slot + (p.waveLength - 1))) →
      S.leader slot ∈ M.alive →
      ∃ L, (schemeRule p σ).IsCandidate S U slot L ∧
        Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit slot L))

/-- **Checkpoints with crashes and restarts.** -/
def CheckpointsCrash : Prop :=
  ∀ (Validator BlockId Payload Value : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (q f : ℕ) [P.Quorate q]
    (M : SigningFaults Validator) (E : M.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) (rel : Reliability Validator),
    p.Tolerates honest f q → p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ (S : Slots Validator) (U : (schemeRule p σ).Universe)
      (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm)
      (V : (schemeRule p σ).View U) (slot : ℕ),
      crashLive p σ rel S V M.alive slot (slot + 1) →
      (∀ v ∈ M.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
        (S.slotRound slot + (p.waveLength - 1))) →
      S.leader slot ∈ M.alive →
      ∃ L, (schemeRule p σ).IsCandidate S U slot L ∧
        Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit slot L))

/-- The mechanisms composed. -/
def Statement : Prop := CheckpointsResponsive ∧ CheckpointsCrash

end Compose

end Scheme

end LeanDag
