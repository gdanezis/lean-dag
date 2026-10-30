import LeanDag.Node.Sync.Statement
import LeanDag.Node.Sync.Helpers.Exposure
/-!
# Sync by causal streams — proofs

`docs/sync.md` §4. Each failing pass adds an equivocator to the detected
authors within two passes (`card_ge_of_fails`), so `2e + 1` passes
suffice. A node is clean (`run_clean`), so its pending blocks are its
targets of other nodes not detected (`pending_subset`). The entry lemma
(`entry`) gives no amplification (`card_outside_le`), and the rate bound
follows (`fromOutside_le`). Each exposed author holds at most two blocks
a round on the disk from the round its exposure is complete
(`run_count`), and each other author at most one (`card_round_le`).
-/

namespace LeanDag

namespace Node

namespace Sync

/-- **A sync completes.** -/
theorem completes : Completes := by
  intro Validator BlockId Payload _ _ blk R t s hR ht
  by_contra hnot
  have h := card_ge_of_fails hR ht _ hnot
  have := Finset.card_le_card (Finset.inter_subset_right (s₁ :=
    ((pass blk R t)^[2 * (equivocators blk R s.held).card + 2] s).detected)
    (s₂ := equivocators blk R s.held))
  omega

/-- **Pending is bounded.** -/
theorem pendingBounded : PendingBounded := by
  intro Validator BlockId Payload _ _ _ blk ev f me ins
  exact Finset.card_le_card (pending_subset (run_clean _ ins (init_clean me)))

/-- **No amplification.** -/
theorem noAmplification : NoAmplification := by
  intro Validator BlockId Payload _ _ _ blk ev f H tr hfaith v hv i
  exact card_outside_le hfaith hv i

/-- **The rate bound.** -/
theorem rateBound : RateBound := by
  intro Validator BlockId Payload _ _ _ blk ev f H tr time k t hfaith hrate v hv i ht
  exact (card_outside_le hfaith hv i).trans (fromOutside_le hrate ht)

/-- **The exposure bound.** -/
theorem exposureBound : ExposureBound := by
  intro Validator BlockId Payload _ _ _ blk ev f H me ins m k hHc hmin hme hhon hexp hk
  exact card_round_le hHc hmin hme hhon hexp hk

/-- **Sync by causal streams.** -/
theorem holds : Statement :=
  ⟨completes, pendingBounded, noAmplification, rateBound, exposureBound⟩

end Sync

end Node

end LeanDag
