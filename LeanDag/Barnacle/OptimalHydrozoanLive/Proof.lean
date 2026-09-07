import LeanDag.Barnacle.OptimalHydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
/-!
# Barnacle over Optimal-Hydrozoan — the live rule, proof

Unaudited.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoanLive

theorem descent : Descent := by
  intro Replica BlockId _ _ _ _
  exact descent_of_support (optimalHydrozoanLive (Replica := Replica) (BlockId := BlockId))
    LeanDag.OptimalHydrozoanProperties.optSupport
    LeanDag.OptimalHydrozoanProperties.optSupport_ofCoverage
    LeanDag.OptimalHydrozoanProperties.optSupport_commits
    LeanDag.OptimalHydrozoanProperties.indirect (by change 2 ≤ 2 + 1; omega) fun _ _ _ h => h

theorem roundRobinLive : RoundRobinLive := by
  intro n hn BlockId _ _ hb w hk m hm hmax
  have hbound : (optimalHydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength
      * (LeanDag.Hydrozoan.Faults.f (Fin n) + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n := by
    change 3 * (LeanDag.Hydrozoan.Faults.f (Fin n)
      + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n
    exact hb
  have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId) (Nat.succ_pos 2) hbound hk m hm hmax
  have hw3 : (optimalHydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength = 3 := rfl
  rw [hw3] at h
  simpa using h

theorem holds : Statement := ⟨descent, roundRobinLive⟩

end OptimalHydrozoanLive

end Barnacle

end LeanDag
