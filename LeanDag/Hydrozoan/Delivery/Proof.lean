import LeanDag.Hydrozoan.Delivery.Statement
import LeanDag.Hydrozoan.PrefixAgreement.Proof
import LeanDag.Common.DedupLemmas
/-!
# Delivery — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

namespace Delivery

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica] {U : BlockUniverse Replica BlockId}

theorem integrity {BlockId : Type*} : Integrity BlockId :=
  fun _ _ key _ _ _ => dedupBy_nodup_key key _

theorem deliveredPrefixConsistency : DeliveredPrefixConsistency U := by
  intro κ _ key lin V₁ V₂ g₁ g₂ n₁ n₂ hle h₁ h₂
  exact dedupBy_prefix key
    (PrefixAgreement.ledgerPrefixConsistency lin V₁ V₂ g₁ g₂ n₁ n₂ hle h₁ h₂)

theorem faithful {BlockId : Type*} : Faithful BlockId :=
  fun _ _ key _ _ _ => ⟨dedupBy_sublist key _, fun _ hb => dedupBy_key_mem key hb⟩

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ _ U
  exact ⟨integrity, deliveredPrefixConsistency, faithful⟩

end Delivery

end Hydrozoan

end LeanDag
