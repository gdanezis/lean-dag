import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.Hydrozoan.DirectSafety.Statement
/-!
# Optimal-Hydrozoan: direct-rule safety — statement

Hydrozoan's `DirectSafety`, over an `OptUniverse`: certificate uniqueness
and slow/slow agreement are Hydrozoan's claims applied unchanged to
`U.toBlockRecord`; fast/fast, fast/slow and commit/skip read the Optimal
rules, each resting on a row of `Optimal/ThresholdArithmetic`.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace DirectSafety

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- **Fast/fast agreement**: two Optimal fast commits for one slot, in any
two views, name the same block. -/
def FastFastAgreement (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (k : ℕ) (L₁ L₂ : BlockId),
    IsLeaderBlock U.toBlockRecord k L₁ → IsLeaderBlock U.toBlockRecord k L₂ →
    FastCommitOptInView U.toBlockRecord V₁ L₁ (S.slotRound k) →
    FastCommitOptInView U.toBlockRecord V₂ L₂ (S.slotRound k) → L₁ = L₂

/-- **Certificate uniqueness**: Hydrozoan's claim, on the underlying
universe — LeanDag.Hydrozoan.certificates are unchanged. -/
def CertUniqueness (U : OptUniverse Replica BlockId) : Prop :=
  Hydrozoan.DirectSafety.CertUniqueness U.toBlockRecord

/-- **Slow/slow agreement**: Hydrozoan's claim, on the underlying
universe — the slow path is unchanged. -/
def SlowSlowAgreement (U : OptUniverse Replica BlockId) : Prop :=
  Hydrozoan.DirectSafety.SlowSlowAgreement U.toBlockRecord

/-- **Fast/slow agreement**: an Optimal fast commit and a slow commit for
one slot, across views, name the same block. -/
def FastSlowAgreement (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (k : ℕ) (L₁ L₂ : BlockId),
    IsLeaderBlock U.toBlockRecord k L₁ → IsLeaderBlock U.toBlockRecord k L₂ →
    FastCommitOptInView U.toBlockRecord V₁ L₁ (S.slotRound k) →
    SlowCommitInView U.toBlockRecord V₂ L₂ (S.slotRound k) → L₁ = L₂

/-- **Commit/skip exclusion**: a slot committed by either direct route in
any view is never directly skipped in any view. -/
def CommitSkipExclusion (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (k : ℕ) (L : BlockId),
    IsLeaderBlock U.toBlockRecord k L →
    (FastCommitOptInView U.toBlockRecord V₁ L (S.slotRound k) ∨
      SlowCommitInView U.toBlockRecord V₁ L (S.slotRound k)) →
    ¬ SkippedLeaderOptInView U.toBlockRecord V₂ k

/-- Slot safety for the Optimal direct rules, over every fault
configuration, schedule, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    FastFastAgreement U ∧ CertUniqueness U ∧ SlowSlowAgreement U ∧
      FastSlowAgreement U ∧ CommitSkipExclusion U

end DirectSafety

end OptimalHydrozoan

end LeanDag
