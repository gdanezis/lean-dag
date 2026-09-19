import LeanDag.OptimalHydrozoan.PrefixAgreement.Statement
import LeanDag.Hydrozoan.Delivery.Statement
/-!
# Optimal-Hydrozoan: delivery — statement

Hydrozoan's `Delivery` read over `DecidedOpt`. `delivered`, `Integrity`
and `Faithful` speak of lists alone and are reused as they are;
delivered prefix consistency is re-stated over an `OptUniverse` and this
arc's `DecidesBelow`.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace Delivery

open LeanDag.Hydrozoan.Delivery (delivered Integrity Faithful)
open LeanDag.OptimalHydrozoan.PrefixAgreement (DecidesBelow)

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- **Delivered prefix consistency**: two replicas, from any two views
and at any two horizons, deliver sequences of which the shorter is a
prefix of the longer. -/
def DeliveredPrefixConsistency (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (key : BlockId → κ) (lin : BlockId → List BlockId)
    (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (g₁ g₂ : ℕ → Option BlockId) (n₁ n₂ : ℕ),
    n₁ ≤ n₂ → DecidesBelow U V₁ g₁ n₁ → DecidesBelow U V₂ g₂ n₂ →
    delivered key lin g₁ n₁ <+: delivered key lin g₂ n₂

/-- Delivery safety over every fault configuration, schedule, and universe
the Optimal model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    Integrity BlockId ∧ DeliveredPrefixConsistency U ∧ Faithful BlockId

end Delivery

end OptimalHydrozoan

end LeanDag
