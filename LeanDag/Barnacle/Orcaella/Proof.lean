import LeanDag.Barnacle.Orcaella.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Hybrid.Properties
/-!
# Barnacle over Orcaella — proof

Generated proof layer; not part of the audit surface. The laws are
`ofAnchoredOn_laws` at the hybrid laws under the bundled invariant; the
descent laws are `descent_of_support` at the vote support, consuming no
admissibility; round-robin liveness is BN9e at slack `fb + fc` and wave
length `2`, with `2·(fb + fc) + 1 ≤ n` from the committee bound, itself
read off the admissible threshold.
-/

namespace LeanDag

namespace Barnacle

namespace Orcaella

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ H _ k _
  exact descent_of_support (orcaellaLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k)
    (Properties.voteSupport _) (Timed.voteSupport_ofCoverage _)
    (HybridProperties.voteSupport_commits k) (HybridProperties.indirect k) (by change 1 ≤ 1 + 1; omega)
    fun _ _ _ h => h

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
