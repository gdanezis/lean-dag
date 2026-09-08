import LeanDagTest.Barnacle.Rules.Orcaella.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Hybrid.Properties
/-!
# Barnacle over Orcaella — proof

Generated proof layer; not part of the audit surface. The bound
`2·(fb + fc) + 1 ≤ n` is read off the admissible threshold.
-/

namespace LeanDag

namespace Barnacle

namespace Orcaella

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ H _ k _
  exact HybridProperties.descent k

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ k hk
    exact ofAnchoredOn_laws (Hybrid.hybridLaws hk) (fun _ _ h => h)
  · intro n hn H BlockId Payload _ k hadm w hkey m hm hmax
    have hbound : (orcaellaLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload) k).waveLength * (H.fb + H.fc) + 1 ≤ n := by
      have hcommittee := Hybrid.committee_bound_of_admissible hadm
      rw [Fintype.card_fin] at hcommittee
      change 2 * (H.fb + H.fc) + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload k hadm) (Nat.succ_pos 1) hbound
      hkey m hm hmax

end Orcaella

end Barnacle

end LeanDag
