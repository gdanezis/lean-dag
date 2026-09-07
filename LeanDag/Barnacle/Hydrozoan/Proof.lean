import LeanDag.Barnacle.Hydrozoan.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Hydrozoan.SlotAgreement.Proof
/-!
# Barnacle over Hydrozoan — proof

Unaudited. The laws are `ofAnchored_laws` at HZ3's laws.
-/

namespace LeanDag

namespace Barnacle

namespace Hydrozoan

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _
  exact ofAnchored_laws LeanDag.Hydrozoan.SlotAgreement.hydrozoanLaws

end Hydrozoan

end Barnacle

end LeanDag
