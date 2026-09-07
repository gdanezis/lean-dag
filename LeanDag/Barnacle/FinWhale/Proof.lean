import LeanDag.Barnacle.FinWhale.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Barnacle.Helpers.Heads
/-!
# Barnacle over FinWhale — proof

Not part of the audit surface. The laws are `ofAnchored_laws` at
FinWhale's laws; the descent laws are `descent_of_support` at its slow
path, a support at wave two under the rule's wave of three; round-robin
liveness is at slack `f` with `3f + 1 ≤ n` from the committee bound.
-/

namespace LeanDag

namespace Barnacle

namespace FinWhale

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ F _ _
  exact descent_of_support (finWhaleLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    FinWhaleProperties.fwSupport FinWhaleProperties.fwSupport_ofCoverage
    FinWhaleProperties.fwSupport_commits FinWhaleProperties.indirect (by change 2 ≤ 2 + 1; omega) fun _ _ _ h => h

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
