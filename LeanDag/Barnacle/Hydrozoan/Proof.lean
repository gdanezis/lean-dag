import LeanDag.Barnacle.Hydrozoan.Statement
import LeanDag.Hydrozoan.SlotAgreement.Proof

/-!
# Barnacle over Hydrozoan — proof

Unaudited. Six of the seven laws are read off the `View` structure and
the `Decided` constructors; the seventh, `agree`, is HZ3 applied.

`historyView_ids` and `full_ids` are `rfl`, which is what defining the
history view *with* `historyFrom` as its ids was for
(`Helpers/Hydrozoan.lean`). `view_complete` is Hydrozoan's own field
because `(adaptBlk U i).refs` reduces to `(U.block i).parents`.
-/

namespace LeanDag

namespace Barnacle

namespace Hydrozoan

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
    exact LeanDag.Hydrozoan.SlotAgreement.holds Replica BlockId U V₁ V₂ k v₁ v₂ h₁ h₂
  · intro S U V k L hL hc
    letI := slotsOf S
    exact hc.elim (LeanDag.Hydrozoan.Decided.directFast hL)
      (LeanDag.Hydrozoan.Decided.directSlow hL)
  · intro S U V k L h
    letI := slotsOf S
    cases h with
    | directFast hL _ => exact hL
    | directSlow hL _ => exact hL
    | indirectCert _ _ _ _ hL _ => exact hL
    | indirectWeak _ _ _ _ _ hL _ _ => exact hL

end Hydrozoan

end Barnacle

end LeanDag
