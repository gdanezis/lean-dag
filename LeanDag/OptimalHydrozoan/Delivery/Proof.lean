import LeanDag.OptimalHydrozoan.Delivery.Statement
import LeanDag.OptimalHydrozoan.PrefixAgreement.Proof
import LeanDag.Hydrozoan.Delivery.Proof
/-!
# Optimal-Hydrozoan: delivery — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace Delivery

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]
  {U : OptUniverse Replica BlockId}

theorem deliveredPrefixConsistency : DeliveredPrefixConsistency U := by
  intro κ _ key lin V₁ V₂ g₁ g₂ n₁ n₂ hle h₁ h₂
  exact dedupBy_prefix key
    (PrefixAgreement.ledgerPrefixConsistency lin V₁ V₂ g₁ g₂ n₁ n₂ hle h₁ h₂)

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ U
  exact ⟨LeanDag.Hydrozoan.Delivery.integrity, deliveredPrefixConsistency,
    LeanDag.Hydrozoan.Delivery.faithful⟩

end Delivery

end OptimalHydrozoan

end LeanDag
