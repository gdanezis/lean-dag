import LeanDag.Hydrozoan.Model.IndirectRules
import LeanDag.Common.History
/-!
# Indirect-rule instances and the history characterizations

Generated: the decidable characterizations of both rung tests through the computable
`history` surrogate — this is what lets witness models settle
`CertifiedIn` / `WeakLinked` (positively and negatively) by `decide`.
Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  {U : BlockUniverse Replica BlockId}

/-- Rung 2 through the history surrogate: the anchor-linked vote filter
is the canonical witness set, so the existential form collapses to a
decidable cardinality bound. -/
theorem weakLinked_iff_history {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) :
    WeakLinked U A L r ↔
      qWeak Replica ≤ (creatorsOf U.block ((blocksAt U (r + 1)).filter
        fun b => IsVote U b L ∧ b ∈ history U A)).card := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine le_trans hcard (Finset.card_le_card (Finset.image_subset_image ?_))
    intro b hb
    obtain ⟨h1, h2, h3⟩ := hs b hb
    exact Finset.mem_filter.mpr ⟨h1, h2, (mem_history_iff hA).mpr h3⟩
  · intro h
    refine ⟨(blocksAt U (r + 1)).filter fun b => IsVote U b L ∧ b ∈ history U A,
      fun b hb => ?_, h⟩
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hb
    exact ⟨h1, h2, (mem_history_iff hA).mp h3⟩

end Hydrozoan

end LeanDag
