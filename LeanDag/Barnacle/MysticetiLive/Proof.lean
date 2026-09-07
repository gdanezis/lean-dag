import LeanDag.Barnacle.MysticetiLive.Statement
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Mysticeti.Properties
/-!
# Mysticeti liveness — proof

Generated proof layer; not part of the audit surface. The bound
`3f + 1 ≤ n` is `Faults.card_validators`.
-/

namespace LeanDag

namespace Barnacle

namespace MysticetiLive

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ F _
  exact descent_of_support (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    MysticetiProperties.coreSupport
    MysticetiProperties.coreSupport_ofCoverage MysticetiProperties.coreSupport_commits
    MysticetiProperties.indirect (by change 2 ≤ 2 + 1; omega) fun _ _ _ h => h

theorem holds : Statement := by
  refine ⟨descent, ?_⟩
  intro n hn F BlockId Payload _ w hk m hm hmax
  have hbound : (mysticetiLive (Validator := Fin n) (BlockId := BlockId)
      (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
    have := F.card_validators
    rw [Fintype.card_fin] at this
    change 3 * F.f + 1 ≤ n
    omega
  exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload) (Nat.succ_pos 2) hbound hk m hm
    hmax

end MysticetiLive

end Barnacle

end LeanDag
