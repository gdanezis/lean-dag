import LeanDag.KPartialDag.Helpers.Avail
/-!
# The commit rule's laws

`docs/kpartial.md` §4. Two certificates for blocks of one author at one
round certify one block (`eq_of_certificates`), and the commit rule obeys
the laws of an anchored rule at `K ≥ 3` (`kRule_laws`).
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
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block U.noEquivOn_honest card_compl_correct_le
    (s := carriedVotes U (IsVote U) C₁ L₁) (t := carriedVotes U (IsVote U) C₂ L₂)
    (fun b hb => (mem_carriedVotes_spec (n := r + 1) hC₁i hC₁r hb).imp_right And.left)
    (fun b hb => (mem_carriedVotes_spec (n := r + 1) hC₂i hC₂r hb).imp_right And.left)
    (by have := F.card_validators; unfold CarriesVotes at hv₁ hv₂; omega)
  exact (U.valid b (mem_carriedVotes_spec (n := r + 1) hC₁i hC₁r hb₁).1).clause L₁
    (mem_carriedVotes.mp hb₁).2 L₂ (mem_carriedVotes.mp hb₂).2 hc

/-- A certificate exists for a directly committed block. -/
theorem exists_certificate {L : BlockId} {r : ℕ} (h : DirectCommit U L r) :
    ∃ C, C ∈ certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2) := by
  have hn := F.card_validators
  exact nonempty_of_creatorsOf_card_pos (blk := U.block)
    (s := certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2))
    (by unfold DirectCommit at h; omega)

variable [S : Slots Validator]

/-- **A slot skip, read on a view, directly skips each candidate.** -/
theorem directSkip_of_blameSkip {V : U.View} {k : ℕ} {L : BlockId}
    (h : blameSkip (S := S) (quorumCard Validator) U V k) (hL : IsLeaderBlock U k L) :
    DirectSkip U L (S.slotRound k) :=
  h.le.trans (Finset.card_le_card (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL)))

omit S in
/-- **The laws of the commit rule**, at `K ≥ 3`. -/
theorem kRule_laws {K : ℕ} (hK : 3 ≤ K) : (kRule (Validator := Validator) (BlockId := BlockId)
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
    obtain ⟨C₂, hC₂, -, -⟩ := hlink
    exact eq_of_certificates hC₁ hC₂ (hL₁.2.2.trans hL₂.2.2.symm)
  skip_link := by
    intro S U V k i L A _ hskip hL _ _ hlink
    obtain ⟨C, hC, -, -⟩ := hlink
    exact not_directSkip hC (directSkip_of_blameSkip hskip hL)
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ _ _
    obtain ⟨C₁, hC₁, -, -⟩ := hl₁
    obtain ⟨C₂, hC₂, -, -⟩ := hl₂
    exact eq_of_certificates hC₁ hC₂ (hL₁.2.2.trans hL₂.2.2.symm)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk _ h => blameSkip_congr hround hk h
  link_congr := (kRule K).linkCongr_of_round (fun _ U A L r => AvailLinked U K A L r)
    fun _ _ _ _ _ _ => rfl

end KPartialDag

end LeanDag
