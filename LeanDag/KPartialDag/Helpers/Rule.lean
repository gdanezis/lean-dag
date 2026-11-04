import LeanDag.KPartialDag.Helpers.Avail
/-!
# The commit rule's laws

`docs/kpartial.md` §4. Two certificates for blocks of one author at one
round certify the same block: their votes come from two quorums, so a
correct author's one block of the round above references both, and it
references one block of each author (`eq_of_certificates`). A direct commit
yields a certificate, a slot skip a direct skip of each candidate, and the
link one certificate; with the visibility of `linked` and the exclusion of
`not_directSkip`, these are the laws of the anchored rule (`kRule_laws`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload}

/-- **Two certificates for blocks of one author at one round certify one
block.** -/
theorem eq_of_certificates {L₁ L₂ C₁ C₂ : BlockId} {r : ℕ}
    (hC₁ : C₁ ∈ certificatesAt U (IsVote U) (quorumCard Validator) L₁ (r + 2))
    (hC₂ : C₂ ∈ certificatesAt U (IsVote U) (quorumCard Validator) L₂ (r + 2))
    (hc : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ := by
  obtain ⟨hC₁i, hC₁r, hv₁⟩ := mem_certificatesAt.mp hC₁
  obtain ⟨hC₂i, hC₂r, hv₂⟩ := mem_certificatesAt.mp hC₂
  have hn := F.card_validators
  obtain ⟨c, hcI, hcB⟩ := exists_mem_inter_notMem (Bad := F.byzantine) (m := F.f)
    (A := creatorsOf U.block (carriedVotes U (IsVote U) C₁ L₁))
    (B := creatorsOf U.block (carriedVotes U (IsVote U) C₂ L₂)) F.card_byzantine
    (by unfold CarriesVotes at hv₁ hv₂; omega)
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_inter.mp hcI
  obtain ⟨b₁, hb₁, hb₁c⟩ := mem_creatorsOf.mp hc₁
  obtain ⟨b₂, hb₂, hb₂c⟩ := mem_creatorsOf.mp hc₂
  obtain ⟨hb₁C, hb₁L⟩ := mem_carriedVotes.mp hb₁
  obtain ⟨hb₂C, hb₂L⟩ := mem_carriedVotes.mp hb₂
  have hb₁i := U.complete C₁ hC₁i b₁ hb₁C
  have hb₂i := U.complete C₂ hC₂i b₂ hb₂C
  have hb₁r := (U.valid C₁ hC₁i).predecessor b₁ hb₁C
  have hb₂r := (U.valid C₂ hC₂i).predecessor b₂ hb₂C
  have hb : b₁ = b₂ := U.eq_of_creator_eq hb₁i hb₂i (mem_correct.mpr hcB) hb₁c hb₂c (by omega)
  subst hb
  exact (U.valid b₁ hb₁i).clause L₁ hb₁L L₂ hb₂L hc

/-- A certificate exists for a directly committed block. -/
theorem exists_certificate {L : BlockId} {r : ℕ} (h : DirectCommit U L r) :
    ∃ C, C ∈ certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2) := by
  have hn := F.card_validators
  obtain ⟨c, hc⟩ : (creatorsOf U.block
      (certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2))).Nonempty :=
    Finset.card_pos.mp (by unfold DirectCommit at h; omega)
  obtain ⟨C, hC, -⟩ := mem_creatorsOf.mp hc
  exact ⟨C, hC⟩

variable [S : Slots Validator]

/-- **A slot skip, read on a view, directly skips each candidate.** -/
theorem directSkip_of_blameSkip {V : U.View} {k : ℕ} {L : BlockId}
    (h : blameSkip (S := S) (quorumCard Validator) U V k) (hL : IsLeaderBlock U k L) :
    DirectSkip U L (S.slotRound k) :=
  h.le.trans (Finset.card_le_card (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL)))

omit S in
/-- **The laws of the commit rule**, at `K ≥ 2`. -/
theorem kRule_laws {K : ℕ} (hK : 2 ≤ K) : (kRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) K).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ _ hL₁ hL₂ h₁ h₂
    obtain ⟨C₁, hC₁⟩ := exists_certificate h₁.le
    obtain ⟨C₂, hC₂⟩ := exists_certificate h₂.le
    exact eq_of_certificates hC₁ hC₂ (hL₁.2.2.trans hL₂.2.2.symm)
  commit_skip := by
    intro S U V₁ V₂ k L _ hL h hskip
    obtain ⟨C, hC⟩ := exists_certificate h.le
    exact not_directSkip hC (directSkip_of_blameSkip hskip hL)
  commit_link := by
    intro S U V k j L A _ _ h hA _ helig
    refine ⟨0, Nat.one_pos, linked hK hA.1 ?_ h.le⟩
    have := (kRule K).eligible_iff.mp helig
    change S.slotRound k + 2 + 1 ≤ S.slotRound j at this
    rw [hA.2.1]
    omega
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ _ hlink _
    obtain ⟨C₁, hC₁⟩ := exists_certificate h.le
    obtain ⟨C₂, hC₂, -⟩ := hlink
    exact eq_of_certificates hC₁ hC₂ (hL₁.2.2.trans hL₂.2.2.symm)
  skip_link := by
    intro S U V k i L A _ hskip hL _ _ hlink
    obtain ⟨C, hC, -⟩ := hlink
    exact not_directSkip hC (directSkip_of_blameSkip hskip hL)
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ _ _
    obtain ⟨C₁, hC₁, -⟩ := hl₁
    obtain ⟨C₂, hC₂, -⟩ := hl₂
    exact eq_of_certificates hC₁ hC₂ (hL₁.2.2.trans hL₂.2.2.symm)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk _ h => blameSkip_congr hround hk h
  link_congr := (kRule K).linkCongr_of_round (fun _ U A L r => AvailLinked U K A L r)
    fun _ _ _ _ _ _ => rfl

end KPartialDag

end LeanDag
