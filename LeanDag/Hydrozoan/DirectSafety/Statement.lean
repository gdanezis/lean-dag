import LeanDag.Hydrozoan.Model.DirectRules
/-!
# Direct-rule safety — statement

The direct decision rules never disagree about a slot: five claims, one
per way two verdicts could meet. The commit-agreement claims are
view-level; certificate uniqueness is universe-level. Each rests on a
quorum-intersection invariant of `ThresholdArithmetic`. Statements only;
the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Hydrozoan

namespace DirectSafety

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica] [S : Slots Replica]

/-- **Fast/fast agreement**: two fast commits for one slot, in any two
views, name the same block (`2·q_fast > n + f`). -/
def FastFastAgreement (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : View U) (k : ℕ) (L₁ L₂ : BlockId),
    IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ →
    FastCommitInView U V₁ L₁ (S.slotRound k) →
    FastCommitInView U V₂ L₂ (S.slotRound k) → L₁ = L₂

/-- **Certificate uniqueness**: two certified candidates for one slot
are the same block, universe-level, from `2·q_cert > n + f`. -/
def CertUniqueness (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (k : ℕ) (L₁ L₂ : BlockId),
    IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ →
    (certificates U L₁ (S.slotRound k)).Nonempty →
    (certificates U L₂ (S.slotRound k)).Nonempty → L₁ = L₂

/-- **Slow/slow agreement**: two slow commits for one slot, in any two
views, name the same block (via certificate uniqueness). -/
def SlowSlowAgreement (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : View U) (k : ℕ) (L₁ L₂ : BlockId),
    IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ →
    SlowCommitInView U V₁ L₁ (S.slotRound k) →
    SlowCommitInView U V₂ L₂ (S.slotRound k) → L₁ = L₂

/-- **Fast/slow agreement**: a fast commit and a slow commit for one
slot, across views, name the same block. -/
def FastSlowAgreement (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : View U) (k : ℕ) (L₁ L₂ : BlockId),
    IsLeaderBlock U k L₁ → IsLeaderBlock U k L₂ →
    FastCommitInView U V₁ L₁ (S.slotRound k) →
    SlowCommitInView U V₂ L₂ (S.slotRound k) → L₁ = L₂

/-- **Commit/skip exclusion**: a slot committed by either direct route
in any view is never skipped in any view. -/
def CommitSkipExclusion (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : View U) (k : ℕ) (L : BlockId),
    IsLeaderBlock U k L →
    (FastCommitInView U V₁ L (S.slotRound k) ∨
      SlowCommitInView U V₁ L (S.slotRound k)) →
    ¬ SkippedLeaderInView U V₂ k

/-- Slot safety for the direct rules, over every fault configuration,
schedule, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.Hydrozoan.Faults Replica] [Slots Replica]
    (U : BlockUniverse Replica BlockId),
    FastFastAgreement U ∧ CertUniqueness U ∧ SlowSlowAgreement U ∧
      FastSlowAgreement U ∧ CommitSkipExclusion U

end DirectSafety

end Hydrozoan

end LeanDag
