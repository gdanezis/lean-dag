import LeanDag.Hydrozoan.IndirectLiveness.Statement
import LeanDag.Hydrozoan.Helpers.IndirectLiveness
/-!
# Proof: indirect liveness

Generated.
-/

namespace LeanDag

namespace Hydrozoan
namespace IndirectLiveness

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ _ U
  exact ⟨AnchoredRule.total_of_least exists_least, AnchoredRule.decidedBelowRun_of_least exists_least⟩

end IndirectLiveness
end Hydrozoan

end LeanDag
