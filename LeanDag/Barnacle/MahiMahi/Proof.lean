import LeanDag.Barnacle.MahiMahi.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.MahiMahi.Properties
/-!
# Barnacle over Mahi-Mahi — proof

Not part of the audit surface. The laws are `ofAnchored_laws` at MM2's
laws; the descent laws are `descent_of_support` at Mahi-Mahi's support,
whose eligibility is restated from `w` to the anchored rule's
`(w − 1) + 1`; round-robin liveness takes its bound as a hypothesis.
-/

namespace LeanDag

namespace Barnacle

namespace MahiMahi

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ F _ w hw
  exact descent_of_support (mahiMahiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)
    (MahiMahiProperties.mmSupport w)
    (MahiMahiProperties.mmSupport_ofCoverage hw)
    (MahiMahiProperties.mmSupport_commits (by omega))
    ((MahiMahiProperties.indirect (by omega)).congr fun sr i j => by
      change sr i + w ≤ sr j ↔ sr i + (w - 1 + 1) ≤ sr j
      omega)
    (by change w - 1 ≤ w - 1 + 1; omega) fun _ _ _ h => h

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ w hw
    exact ofAnchored_laws (LeanDag.MahiMahi.mahiMahiLaws hw)
  · intro n hn F BlockId Payload _ w hw hbound W hk m hm hmax
    have hwave : (mahiMahiLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload) w).waveLength = w := by
      change w - 1 + 1 = w
      omega
    have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload w hw) (by omega)
      (by rw [hwave]; exact hbound) hk m hm hmax
    rwa [hwave] at h

end MahiMahi

end Barnacle

end LeanDag
