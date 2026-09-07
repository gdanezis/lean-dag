import LeanDag.OptimalHydrozoan.Model.DirectRules
import LeanDag.OptimalHydrozoan.Helpers.Universe
import LeanDag.Hydrozoan.Helpers.DirectRules
/-!
# Optimal-Hydrozoan: direct-rule instances and bridges

Generated proof infrastructure over `Optimal/Model/DirectRules.lean`; not
part of the audit surface. `Decidable` instances so the witness models can
`decide` the rules, the filter characterizations of the existential
quorums (the canonical witness set is the filter), and the plain-case
reading of fast evidence when no equivocation is witnessed.

The quorum instances go through `decidable_of_iff` on the filter form on
purpose: an `unfold; infer_instance` on `∃ s : Finset BlockId, …` would
also succeed — enumerating every subset of `BlockId` — and `decide` would
never terminate.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]
  {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- Hydrozoan's certificate, read through `votersOf`. -/
theorem isCertificate_iff_votesFor (C L : BlockId) :
    LeanDag.Hydrozoan.IsCertificate U C L ↔ qCert Replica ≤ (votersOf U C L).card :=
  Iff.rfl

instance decidableFastCommitOpt (L : BlockId) (r : ℕ) :
    Decidable (FastCommitOpt U L r) :=
  inferInstanceAs (Decidable (qFastOpt Replica ≤ (supporters U L (r + 1)).card))

section Slots

variable [S : Slots Replica]

/-- Fast evidence when no equivocation is witnessed: just the plain-case
threshold. -/
theorem isFastEvidence_iff_plain {k : ℕ} {C L : BlockId}
    (h : ¬ WitnessesEquivocation U k C) :
    IsFastEvidence U k C L ↔ tPlain Replica ≤ (votersOf U C L).card :=
  ⟨fun hE => hE.1 h, fun ht => ⟨fun _ => ht, fun hw => absurd hw h⟩⟩

variable [Fintype BlockId]

instance decidableIsFastEvidence (k : ℕ) (C L : BlockId) :
    Decidable (IsFastEvidence U k C L) := by
  unfold IsFastEvidence; infer_instance

instance decidableIsNoFastEvidence (k : ℕ) (C : BlockId) :
    Decidable (IsNoFastEvidence U k C) := by
  unfold IsNoFastEvidence; infer_instance

/-- The no-evidence quorum through its canonical witness set: the filter
of no-evidence decision-round blocks. -/
theorem noEvidenceQuorum_iff_filter {k : ℕ} :
    NoEvidenceQuorum U k ↔
      qCert Replica ≤ (creatorsOf U.block ((blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
        fun b => IsNoFastEvidence U k b)).card := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine le_trans hcard (Finset.card_le_card (Finset.image_subset_image ?_))
    intro b hb
    obtain ⟨h1, h2⟩ := hs b hb
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  · intro h
    refine ⟨(blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter fun b => IsNoFastEvidence U k b,
      fun b hb => ?_, h⟩
    exact Finset.mem_filter.mp hb

/-- The in-view no-evidence quorum through its canonical witness set. -/
theorem noEvidenceQuorumInView_iff_filter {V : LeanDag.Hydrozoan.View U} {k : ℕ} :
    NoEvidenceQuorumInView U V k ↔
      qCert Replica ≤ (creatorsOf U.block ((blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
        fun b => b ∈ V.ids ∧ IsNoFastEvidence U k b)).card := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine le_trans hcard (Finset.card_le_card (Finset.image_subset_image ?_))
    intro b hb
    obtain ⟨h1, h2, h3⟩ := hs b hb
    exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
  · intro h
    refine ⟨(blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
      fun b => b ∈ V.ids ∧ IsNoFastEvidence U k b, fun b hb => ?_, h⟩
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hb
    exact ⟨h1, h2, h3⟩

instance decidableNoEvidenceQuorum (k : ℕ) : Decidable (NoEvidenceQuorum U k) :=
  decidable_of_iff _ noEvidenceQuorum_iff_filter.symm

instance decidableNoEvidenceQuorumInView (V : LeanDag.Hydrozoan.View U) (k : ℕ) :
    Decidable (NoEvidenceQuorumInView U V k) :=
  decidable_of_iff _ noEvidenceQuorumInView_iff_filter.symm

instance decidableSkippedLeaderOpt (k : ℕ) : Decidable (SkippedLeaderOpt U k) :=
  inferInstanceAs (Decidable (qCert Replica ≤ (slotBlames U k).card ∧ NoEvidenceQuorum U k))

instance decidableSkippedLeaderOptInView (V : LeanDag.Hydrozoan.View U) (k : ℕ) :
    Decidable (SkippedLeaderOptInView U V k) :=
  inferInstanceAs
    (Decidable (qCert Replica ≤ (slotBlamesIn U V k).card ∧ NoEvidenceQuorumInView U V k))

end Slots

/-! ## Views only grow -/

section ViewMono

variable [S : Slots Replica]

/-- A larger view holds every no-evidence block the smaller one does. -/
theorem noEvidenceQuorumInView_mono {V V' : LeanDag.Hydrozoan.View U} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} (h : NoEvidenceQuorumInView U V k) : NoEvidenceQuorumInView U V' k := by
  obtain ⟨s, hs, hcard⟩ := h
  exact ⟨s, fun b hb => ⟨(hs b hb).1, hsub (hs b hb).2.1, (hs b hb).2.2⟩, hcard⟩

/-- A larger view holds every blame and no-evidence block the smaller
one does. -/
theorem skippedLeaderOptInView_mono {V V' : LeanDag.Hydrozoan.View U} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} (h : SkippedLeaderOptInView U V k) : SkippedLeaderOptInView U V' k :=
  ⟨HoldsAtLeast.mono hsub h.1, noEvidenceQuorumInView_mono hsub h.2⟩

end ViewMono

/-! ## The fast path reads the schedule at one slot

The fast path's rules consult the leaders only at the slot being
decided, so two schedules naming the same round and leader there agree
on them. This is what the relation's laws ask (`skip_congr`,
`link_congr`) and the tightness `Properties.Indirect` needs. -/

section Congr

variable {S₁ S₂ : Slots Replica} {k : ℕ}

theorem witnessesEquivocation_congr {b : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    WitnessesEquivocation (S := S₁) U k b ↔ WitnessesEquivocation (S := S₂) U k b := by
  unfold WitnessesEquivocation
  constructor <;> rintro ⟨L₁, L₂, hL₁, hL₂, hne, hv₁, hv₂⟩
  · exact ⟨L₁, L₂, isLeaderBlock_congr hround hk hL₁, isLeaderBlock_congr hround hk hL₂,
      hne, hv₁, hv₂⟩
  · exact ⟨L₁, L₂, isLeaderBlock_congr hround.symm hk.symm hL₁,
      isLeaderBlock_congr hround.symm hk.symm hL₂, hne, hv₁, hv₂⟩

theorem isFastEvidence_congr {C L : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    IsFastEvidence (S := S₁) U k C L ↔ IsFastEvidence (S := S₂) U k C L := by
  have hw := witnessesEquivocation_congr (U := U) (b := C) hround hk
  unfold IsFastEvidence
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨fun hnw => hp (fun hx => hnw (hw.mp hx)), fun hx => ?_⟩
    obtain ⟨hc, hriv⟩ := hq (hw.mpr hx)
    exact ⟨hc, fun L' hL' hne => hriv L' (isLeaderBlock_congr hround.symm hk.symm hL') hne⟩
  · rintro ⟨hp, hq⟩
    refine ⟨fun hnw => hp (fun hx => hnw (hw.mpr hx)), fun hx => ?_⟩
    obtain ⟨hc, hriv⟩ := hq (hw.mp hx)
    exact ⟨hc, fun L' hL' hne => hriv L' (isLeaderBlock_congr hround hk hL') hne⟩

theorem isNoFastEvidence_congr {C : BlockId} (hround : S₁.slotRound k = S₂.slotRound k)
    (hk : S₁.leader k = S₂.leader k) :
    IsNoFastEvidence (S := S₁) U k C ↔ IsNoFastEvidence (S := S₂) U k C := by
  unfold IsNoFastEvidence
  constructor
  · intro h L hL he
    exact h L (isLeaderBlock_congr hround.symm hk.symm hL)
      ((isFastEvidence_congr hround hk).mpr he)
  · intro h L hL he
    exact h L (isLeaderBlock_congr hround hk hL) ((isFastEvidence_congr hround hk).mp he)

theorem noEvidenceQuorumInView_congr {V : LeanDag.Hydrozoan.View U}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : NoEvidenceQuorumInView (S := S₁) U V k) : NoEvidenceQuorumInView (S := S₂) U V k := by
  have hdr₁ : LeanDag.Hydrozoan.decisionRound (S := S₁) Replica k = S₁.slotRound k + 2 := rfl
  have hdr₂ : LeanDag.Hydrozoan.decisionRound (S := S₂) Replica k = S₂.slotRound k + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := h
  refine ⟨s, fun b hb => ?_, hcard⟩
  obtain ⟨hbA, hbV, hbn⟩ := hs b hb
  have hbr : (U.block b).round = S₁.slotRound k + 2 := (Finset.mem_filter.mp hbA).2
  exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbA).1, by omega⟩, hbV,
    (isNoFastEvidence_congr hround hk).mp hbn⟩

/-- The direct skip reads the schedule only at its slot. -/
theorem skippedLeaderOptInView_congr {V : LeanDag.Hydrozoan.View U}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : SkippedLeaderOptInView (S := S₁) U V k) : SkippedLeaderOptInView (S := S₂) U V k :=
  ⟨by have := h.1; rwa [slotBlamers_congr hround hk] at this,
    noEvidenceQuorumInView_congr hround hk h.2⟩

end Congr

end OptimalHydrozoan

end LeanDag
