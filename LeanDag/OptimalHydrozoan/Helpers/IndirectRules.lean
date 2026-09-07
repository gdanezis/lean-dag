import LeanDag.OptimalHydrozoan.Model.IndirectRules
import LeanDag.OptimalHydrozoan.Helpers.DirectRules
import LeanDag.Hydrozoan.Helpers.IndirectRules
/-!
# Optimal-Hydrozoan: the evidence rung through the history surrogate

Generated proof infrastructure over `Optimal/Model/IndirectRules.lean`;
not part of the audit surface. `evidenceLinked_iff_history` is the mirror
of `weakLinked_iff_history`: the anchor-linked evidence filter is the
canonical witness set, so the existential form collapses to a decidable
cardinality bound on concrete data. No `Decidable (EvidenceLinked …)`
instance — the bridge needs `A ∈ U.ids`, so witnesses go through the iff.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [Fintype BlockId] [O : OptimalFaults Replica]
  [S : Slots Replica] {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- Rung 2 through the history surrogate. -/
theorem evidenceLinked_iff_history {A L : BlockId} {k : ℕ} (hA : A ∈ U.ids) :
    EvidenceLinked U A L k ↔
      qCert Replica ≤ (creatorsOf U.block ((blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
        fun b => IsFastEvidence U k b L ∧ b ∈ history U A)).card := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine le_trans hcard (Finset.card_le_card (Finset.image_subset_image ?_))
    intro b hb
    obtain ⟨h1, h2, h3⟩ := hs b hb
    exact Finset.mem_filter.mpr ⟨h1, h2, (mem_history_iff hA).mpr h3⟩
  · intro h
    refine ⟨(blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
      fun b => IsFastEvidence U k b L ∧ b ∈ history U A, fun b hb => ?_, h⟩
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hb
    exact ⟨h1, h2, (mem_history_iff hA).mp h3⟩

omit S [Fintype BlockId] in
/-- The evidence rung reads the schedule only at its slot. -/
theorem evidenceLinked_congr {S₁ S₂ : Slots Replica} {k : ℕ} {A L : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    EvidenceLinked (S := S₁) U A L k ↔ EvidenceLinked (S := S₂) U A L k := by
  have hdr₁ : LeanDag.Hydrozoan.decisionRound (S := S₁) Replica k = S₁.slotRound k + 2 := rfl
  have hdr₂ : LeanDag.Hydrozoan.decisionRound (S := S₂) Replica k = S₂.slotRound k + 2 := rfl
  have hfe := fun C : BlockId => isFastEvidence_congr (U := U) (C := C) (L := L) hround hk
  unfold EvidenceLinked
  constructor <;> rintro ⟨s, hs, hcard⟩ <;> refine ⟨s, fun b hb => ?_, hcard⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    have hbr : (U.block b).round = S₁.slotRound k + 2 := (Finset.mem_filter.mp hbA).2
    exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbA).1, by omega⟩,
      (hfe b).mp hbe, hbre⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    have hbr : (U.block b).round = S₂.slotRound k + 2 := (Finset.mem_filter.mp hbA).2
    exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbA).1, by omega⟩,
      (hfe b).mpr hbe, hbre⟩


end OptimalHydrozoan

end LeanDag
