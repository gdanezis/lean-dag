import LeanDag.Barnacle.OptimalHydrozoan.Statement
import LeanDag.Barnacle.Helpers.Anchored
/-!
# Barnacle over Optimal-Hydrozoan — proof

Unaudited.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoan

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _
  exact ofAnchoredOn_laws LeanDag.OptimalHydrozoan.SlotAgreement.optimalLaws
    (fun S U h => LeanDag.OptimalHydrozoan.leaderExcluded_of_all (S := S) U h)

end OptimalHydrozoan

end Barnacle

end LeanDag
