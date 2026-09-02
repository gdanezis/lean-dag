import LeanDag.Barnacle.OptimalHydrozoan.Statement
import LeanDag.OptimalHydrozoan.SlotAgreement.Proof

/-!
# Barnacle over Optimal-Hydrozoan — proof

Unaudited. As for Hydrozoan: six of the seven laws are read off the
`View` structure and the `DecidedOpt` constructors, and `agree` is OH3
applied. The carrier's exclusion field is consumed only by
`optUniverseOf`, which turns it into the `OptUniverse` the decision
relation needs at whatever schedule the interface supplies.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoan

set_option maxHeartbeats 1000000 in
-- unification works through two layers at once here: the carrier is a
-- subtype, and `optUniverseOf` rebuilds an `OptUniverse` from its field
-- at every constructor the laws inspect
theorem holds : Statement := by
  intro Replica BlockId _ _ _ _
  refine
    { view_subset := fun V => V.subset_ids
      view_complete := fun V => V.complete
      full_ids := fun _ => rfl
      historyView_ids := fun _ _ _ => rfl
      agree := ?_
      decided_of_directCommitIn := ?_
      candidates := ?_ }
  · intro S U V₁ V₂ k v₁ v₂ h₁ h₂
    letI := slotsOf S
    exact LeanDag.OptimalHydrozoan.SlotAgreement.holds Replica BlockId
      (OptimalHydrozoan.optUniverseOf U.val U.property) V₁ V₂ k v₁ v₂ h₁ h₂
  · intro S U V k L hL hc
    letI := slotsOf S
    rcases hc with h | h
    · exact LeanDag.OptimalHydrozoan.DecidedOpt.directFast hL h
    · exact LeanDag.OptimalHydrozoan.DecidedOpt.directSlow hL h
  · intro S U V k L h
    letI := slotsOf S
    cases h with
    | directFast hL _ => exact hL
    | directSlow hL _ => exact hL
    | indirectCert _ _ _ _ hL _ => exact hL
    | indirectEvidence _ _ _ _ _ hL _ => exact hL

end OptimalHydrozoan

end Barnacle

end LeanDag
