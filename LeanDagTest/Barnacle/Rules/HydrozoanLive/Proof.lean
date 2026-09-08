import LeanDagTest.Barnacle.Rules.HydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
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
  exact LeanDag.Hydrozoan.descent

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
