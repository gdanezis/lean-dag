import LeanDag.Barnacle.HydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Hydrozoan.Helpers.Commit
/-!
# Barnacle over Hydrozoan — the live rule, proof

Unaudited.
-/

namespace LeanDag

namespace Barnacle

namespace HydrozoanLive

theorem descent : Descent := by
  intro Replica BlockId _ _ _ F
  exact descent_of_support (hydrozoanLive (Replica := Replica) (BlockId := BlockId))
    LeanDag.Hydrozoan.hzSupport LeanDag.Hydrozoan.hzSupport_ofCoverage
    LeanDag.Hydrozoan.hzSupport_commits LeanDag.Hydrozoan.indirect (by change 2 ≤ 2 + 1; omega) fun _ _ _ h => h

theorem roundRobinLive : RoundRobinLive := by
  intro n hn BlockId _ F hck w hk m hm hmax
  have hbound : (hydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength * (F.f + F.c) + 1 ≤ n := by
    change 3 * (F.f + F.c) + 1 ≤ n
    exact hck
  have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId) (Nat.succ_pos 2) hbound hk m hm hmax
  have hw3 : (hydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength = 3 := rfl
  rw [hw3] at h
  simpa using h

theorem holds : Statement := ⟨descent, roundRobinLive⟩

end HydrozoanLive

end Barnacle

end LeanDag
