import LeanDagTest.Barnacle.Rules.Hydrozoan.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Hydrozoan.SlotAgreement.Proof
/-!
# Barnacle over Hydrozoan — proof

Unaudited.
-/

namespace LeanDag

namespace Barnacle

namespace Hydrozoan

theorem holds : Laws := by
  intro Replica BlockId _ _ _ _
  exact ofAnchored_laws LeanDag.Hydrozoan.SlotAgreement.hydrozoanLaws

end Hydrozoan

end Barnacle

end LeanDag
