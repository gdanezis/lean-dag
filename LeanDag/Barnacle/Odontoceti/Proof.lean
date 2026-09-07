import LeanDag.Barnacle.Odontoceti.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Odontoceti.Properties
/-!
# Barnacle over Odontoceti — proof

Generated proof layer; not part of the audit surface. The laws are
`ofAnchored_laws` at O5's laws; the descent laws are
`descent_of_support` at the vote support; round-robin liveness is BN9e
at slack `f` and wave length `2`, with `2f + 1 ≤ n` from the committee
bound.
-/

namespace LeanDag

namespace Barnacle

namespace Odontoceti

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ F _
  exact descent_of_support (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (Properties.voteSupport _) (Timed.voteSupport_ofCoverage _)
    OdontocetiProperties.voteSupport_commits OdontocetiProperties.indirect (by change 1 ≤ 1 + 1; omega)
    fun _ _ _ h => h

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _ _
    exact ofAnchored_laws LeanDag.Odontoceti.odontocetiLaws
  · intro n hn F BlockId Payload _ w hk m hm hmax
    have hbound : (odontocetiLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      change 2 * F.f + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload) (Nat.succ_pos 1) hbound hk m
      hm hmax

end Odontoceti

end Barnacle

end LeanDag
