import LeanDag.KPartialSparse.Model.Rule
import LeanDag.KPartialSparse.Helpers.Avail
/-!
# Sparse K-partial DAG — the commit rule, helpers

`docs/kpartial-sparse.md` §4. A direct commit names a certified block
(`certified_of_commit`), a link from a certified anchor does too
(`certified_of_link`), two certified blocks of one author and round are one
(`eq_of_certified`), a certified block is not directly skipped
(`not_certified_skip`), and the laws of an anchored rule (`sRule_laws`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable {U : SRecord Validator BlockId Payload} {p : Params}

omit Cr Ld [LinearOrder BlockId] [ClaimFormat BlockId Payload] in
/-- Among more than `f` authors one is correct. -/
theorem exists_correct_of_lt {X : Finset Validator} (h : F.f < X.card) :
    ∃ w ∈ X, w ∈ (Correct : Finset Validator) := by
  have hsplit := card_le_card_inter_correct_add_byzantine X
  have hb := F.card_byzantine
  obtain ⟨w, hw⟩ : (X ∩ (Correct : Finset Validator)).Nonempty := by
    rw [← Finset.card_pos]; omega
  exact ⟨w, (Finset.mem_inter.mp hw).1, (Finset.mem_inter.mp hw).2⟩

/-- **A direct commit names a certified block**: among the claimers one is
correct, and it claims truthfully. -/
theorem certified_of_commit (hrow : Row Validator p) {t : ℕ} (ht : Truthful U t) {L : BlockId}
    {ρ : ℕ} (h : p.commitThreshold ≤ (creatorsOf U.block (claimersOf U L ρ)).card) :
    Certified U t L := by
  obtain ⟨-, -, -, -, -, hq⟩ := hrow
  have : F.f < (creatorsOf U.block (claimersOf U L ρ)).card := by omega
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt this
  obtain ⟨C, hC, rfl⟩ := mem_creatorsOf.mp hw
  obtain ⟨hCb, hCL⟩ := Finset.mem_filter.mp hC
  exact ht C (mem_blocksAt.mp hCb).1 hwC L hCL

omit [ClaimFormat BlockId Payload] in
/-- **A certified block has a correct voter**, which references it. -/
theorem exists_correct_voter (hrow : Row Validator p) {A : BlockId}
    (h : Certified U p.certThreshold A) :
    ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs := by
  obtain ⟨-, -, -, h2, -, -⟩ := hrow
  have := F.card_validators
  have : F.f < (supporters U A ((U.block A).round + 1)).card := by unfold Certified at h; omega
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt this
  obtain ⟨z, hz, -, hAz, rfl⟩ := mem_supporters.mp hw
  exact ⟨z, hz, hwC, hAz⟩

/-- **A link from a certified anchor names a certified block**: the claim lies
in the sub-DAG, where a correct author checked it. -/
theorem certified_of_link (hrow : Row Validator p) {K : ℕ} (hK : 1 ≤ K)
    (hck : Checks U K p.certThreshold) {A L : BlockId} (hA : Certified U p.certThreshold A)
    {r : ℕ} (h : ClaimLinked U K A L r) : Certified U p.certThreshold L := by
  obtain ⟨C, hC, -, hCL⟩ := h
  exact backed hK hck (exists_correct_voter hrow hA) hC hCL

omit [ClaimFormat BlockId Payload] in
/-- **Two certified blocks of one author and round are one**: their voters
share a correct author, whose one block there references one block of each
author. -/
theorem eq_of_certified (hrow : Row Validator p) {L₁ L₂ : BlockId}
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round)
    (c₁ : Certified U p.certThreshold L₁) (c₂ : Certified U p.certThreshold L₂) : L₁ = L₂ := by
  obtain ⟨-, -, -, h2, -, -⟩ := hrow
  unfold Certified at c₁ c₂
  rw [← hr] at c₂
  set X := supporters U L₁ ((U.block L₁).round + 1)
  set Y := supporters U L₂ ((U.block L₁).round + 1)
  have hu := Finset.card_union_add_card_inter X Y
  have huniv : (X ∪ Y).card ≤ Fintype.card Validator := Finset.card_le_univ _
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt (X := X ∩ Y) (by omega)
  obtain ⟨q₁, hq₁, hq₁r, hL₁q, hq₁w⟩ := mem_supporters.mp (Finset.mem_inter.mp hw).1
  obtain ⟨q₂, hq₂, hq₂r, hL₂q, hq₂w⟩ := mem_supporters.mp (Finset.mem_inter.mp hw).2
  have : q₁ = q₂ := U.no_equivocation q₁ hq₁ q₂ hq₂ (hq₁w ▸ hwC) (hq₁w.trans hq₂w.symm)
    (hq₁r.trans hq₂r.symm)
  subst this
  exact (U.valid q₁ hq₁).distinct L₁ hL₁q L₂ hL₂q hc

omit [ClaimFormat BlockId Payload] in
/-- **A certified block is not directly skipped**: its voters and the blamers
share a correct author, whose one block there would both reference it and
not. -/
theorem not_certified_skip (hrow : Row Validator p) {L : BlockId} {r : ℕ}
    (hr : (U.block L).round = r) (c : Certified U p.certThreshold L)
    (hs : p.skipThreshold ≤ (creatorsOf U.block (omissionsOf U L (r + 1))).card) : False := by
  obtain ⟨-, -, -, -, h3, -⟩ := hrow
  unfold Certified at c
  rw [hr] at c
  set X := supporters U L (r + 1)
  set Y := creatorsOf U.block (omissionsOf U L (r + 1))
  have hu := Finset.card_union_add_card_inter X Y
  have huniv : (X ∪ Y).card ≤ Fintype.card Validator := Finset.card_le_univ _
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt (X := X ∩ Y) (by omega)
  obtain ⟨q₁, hq₁, hq₁r, hLq, hq₁w⟩ := mem_supporters.mp (Finset.mem_inter.mp hw).1
  obtain ⟨q₂, hq₂O, hq₂w⟩ := mem_creatorsOf.mp (Finset.mem_inter.mp hw).2
  obtain ⟨hq₂, hq₂r, hLq₂⟩ := mem_omissionsOf.mp hq₂O
  have : q₁ = q₂ := U.no_equivocation q₁ hq₁ q₂ hq₂ (hq₁w ▸ hwC) (hq₁w.trans hq₂w.symm)
    (hq₁r.trans hq₂r.symm)
  exact hLq₂ (this ▸ hLq)

/-- **The laws of an anchored rule** hold of the commit rule at a row, under the
spreading condition, at `K ≥ 6`, on a disciplined schedule and record. -/
theorem sRule_laws (hrow : Row Validator p) (hsp : Spread Validator) {K : ℕ} (hK : 6 ≤ K) :
    (sRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) p K).Laws
      (Disciplined K p.certThreshold) where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ hI hL₁ hL₂ h₁ h₂
    exact eq_of_certified hrow (hL₁.2.2.trans hL₂.2.2.symm) (hL₁.2.1.trans hL₂.2.1.symm)
      (certified_of_commit hrow hI.2.2.2 h₁.le) (certified_of_commit hrow hI.2.2.2 h₂.le)
  commit_skip := by
    intro S U V₁ V₂ k L hI hL h hskip
    exact not_certified_skip hrow hL.2.1 (certified_of_commit hrow hI.2.2.2 h.le)
      (hskip.le.trans (Finset.card_le_card
        (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL))))
  commit_link := by
    intro S U V k j L A hI _ h hA _ helig
    have he := (sRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
      p K).eligible_iff.mp helig
    change S.slotRound k + 2 + 1 ≤ S.slotRound j at he
    obtain ⟨-, -, -, -, -, hq⟩ := hrow
    refine ⟨0, Nat.one_pos, ?_⟩
    have hAl : (U.block A).creator ∈ Ld.leaders (U.block A).round := by
      rw [hA.2.2, hA.2.1]; exact hI.1 j
    exact linked hsp hK hI.2.1 hA.1 hAl (by rw [hA.2.1]; omega) hq h.le
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hI hL₁ hL₂ h _ hanc _ _ _ hlink _
    exact eq_of_certified hrow (hL₁.2.2.trans hL₂.2.2.symm) (hL₁.2.1.trans hL₂.2.1.symm)
      (certified_of_commit hrow hI.2.2.2 h.le)
      (certified_of_link hrow (by omega) hI.2.2.1 hanc hlink)
  skip_link := by
    intro S U V k i L A hI hskip hL _ hanc hlink
    exact not_certified_skip hrow hL.2.1 (certified_of_link hrow (by omega) hI.2.2.1 hanc hlink)
      (hskip.le.trans (Finset.card_le_card
        (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL))))
  link_unique := by
    intro S U k j i L₁ L₂ A hI hL₁ hL₂ _ hanc _ _ _ hl₁ hl₂ _ _
    exact eq_of_certified hrow (hL₁.2.2.trans hL₂.2.2.symm) (hL₁.2.1.trans hL₂.2.1.symm)
      (certified_of_link hrow (by omega) hI.2.2.1 hanc hl₁)
      (certified_of_link hrow (by omega) hI.2.2.1 hanc hl₂)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk _ h => blameSkip_congr hround hk h
  link_congr := (sRule p K).linkCongr_of_round (fun _ U A L r => ClaimLinked U K A L r)
    fun _ _ _ _ _ _ => rfl
  anchor_commit := by
    intro S U V k L hI _ h
    exact certified_of_commit hrow hI.2.2.2 h.le
  anchor_link := by
    intro S U k j i A L hI _ hanc _ _ _ hlink
    exact certified_of_link hrow (by omega) hI.2.2.1 hanc hlink

end KPartialSparse

end LeanDag
