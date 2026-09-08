import LeanDag.Barnacle.FinWhale.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Heads
/-!
# Barnacle over FinWhale — proof

Not part of the audit surface. FinWhale's support is its slow path, at
wave two under the rule's wave of three.
-/

namespace LeanDag

namespace Barnacle

namespace FinWhale

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ F _ _
  exact FinWhaleProperties.descent

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ _
    exact ofAnchored_laws LeanDag.FinWhale.finWhaleLaws
  · intro n hn F P BlockId Payload _ W hk m hm hmax
    have hbound : (finWhaleLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      change 3 * F.f + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload) (Nat.succ_pos 2) hbound hk m
      hm hmax

end FinWhale

end Barnacle

end LeanDag
