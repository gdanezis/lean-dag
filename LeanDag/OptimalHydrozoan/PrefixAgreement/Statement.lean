import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.Hydrozoan.PrefixAgreement.Statement
/-!
# Optimal-Hydrozoan: prefix agreement — statement

Hydrozoan's `PrefixAgreement` read over `DecidedOpt`: `commitSeq` and
`ledger`, generic in the verdict function, are reused as they are;
`DecidesBelow` and the three claims (sequence agreement, prefix
consistency, ledger prefix consistency) are re-stated over an
`OptUniverse`. A harvest of `OptimalHydrozoan.SlotAgreement`; no
arithmetic row enters directly.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace PrefixAgreement

open LeanDag.Hydrozoan.PrefixAgreement (ledger)

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- `g` records a decided verdict for every slot below `n`, as judged
from `V`. -/
def DecidesBelow (U : OptUniverse Replica BlockId) (V : LeanDag.Hydrozoan.View U.toBlockRecord)
    (g : ℕ → Option BlockId) (n : ℕ) : Prop :=
  ∀ k < n, DecidedOpt U V k (g k)

/-- **Sequence agreement**: at equal horizons, two replicas output the
same committed-leader sequence. -/
def SeqAgreement (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (g₁ g₂ : ℕ → Option BlockId) (n : ℕ),
    DecidesBelow U V₁ g₁ n → DecidesBelow U V₂ g₂ n →
    commitSeq g₁ n = commitSeq g₂ n

/-- **Prefix consistency**: at different horizons, the shorter output
is a prefix of the longer. -/
def PrefixConsistency (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (g₁ g₂ : ℕ → Option BlockId) (n₁ n₂ : ℕ),
    n₁ ≤ n₂ → DecidesBelow U V₁ g₁ n₁ → DecidesBelow U V₂ g₂ n₂ →
    commitSeq g₁ n₁ <+: commitSeq g₂ n₂

/-- **Ledger prefix consistency**, for every memoryless per-leader
linearizer. -/
def LedgerPrefixConsistency (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (lin : BlockId → List BlockId) (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord)
    (g₁ g₂ : ℕ → Option BlockId) (n₁ n₂ : ℕ),
    n₁ ≤ n₂ → DecidesBelow U V₁ g₁ n₁ → DecidesBelow U V₂ g₂ n₂ →
    ledger lin g₁ n₁ <+: ledger lin g₂ n₂

/-- Output safety over every fault configuration, schedule, and universe
the Optimal model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    SeqAgreement U ∧ PrefixConsistency U ∧ LedgerPrefixConsistency U

end PrefixAgreement

end OptimalHydrozoan

end LeanDag
