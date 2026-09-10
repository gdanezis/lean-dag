import LeanDagTest.Barnacle.Rules.Odontoceti.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Odontoceti.Properties
/-!
# Barnacle over Odontoceti — proof

Generated proof layer; not part of the audit surface. The bound
`2f + 1 ≤ n` is the committee bound.
-/

namespace LeanDag

namespace Barnacle

namespace Odontoceti

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ F _
  exact OdontocetiProperties.descent

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _ _
    exact ofAnchored_laws LeanDag.Odontoceti.odontocetiLaws
  · intro n hn F BlockId Payload _ C hC
    have hbound : (odontocetiLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      change 2 * F.f + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload) (Nat.succ_pos 1) hbound C hC

end Odontoceti

end Barnacle

end LeanDag
