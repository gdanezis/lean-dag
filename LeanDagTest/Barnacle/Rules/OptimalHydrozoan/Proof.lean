import LeanDagTest.Barnacle.Rules.OptimalHydrozoan.Statement
import LeanDag.Barnacle.Helpers.Anchored
/-!
# Barnacle over Optimal-Hydrozoan — proof

Unaudited.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoan

theorem holds : Laws := by
  intro Replica BlockId _ _ _ _
  exact ofAnchoredVia_laws LeanDag.OptimalHydrozoan.SlotAgreement.optimalLaws
    (fun S U => LeanDag.OptimalHydrozoan.OptUniverse.leader_excluded (S := S) U)

end OptimalHydrozoan

end Barnacle

end LeanDag
