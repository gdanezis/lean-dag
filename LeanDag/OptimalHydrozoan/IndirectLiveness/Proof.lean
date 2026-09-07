import LeanDag.OptimalHydrozoan.IndirectLiveness.Statement
import LeanDag.OptimalHydrozoan.Helpers.Decided
import LeanDag.Common.Anchored.Bounded
/-!
# Optimal-Hydrozoan: indirect liveness — proof

Generated. Totality and the descent are the relation's
`exists_decided_of_anchor` and `decided_below_of_committed_run` at the
rule's rung choices, the latter at the run's last slot `n := b + c - 1`.
-/

namespace LeanDag

namespace OptimalHydrozoan
namespace IndirectLiveness

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ U
  exact ⟨AnchoredRule.total_of_least exists_least, AnchoredRule.decidedBelowRun_of_least exists_least⟩

end IndirectLiveness
end OptimalHydrozoan

end LeanDag
