import LeanDag.KPartialDag.Helpers.Avail
/-!
# The commit rule's laws

`docs/kpartial.md` §4. Votes for two blocks of one slot from more than
`n + f` authors name one block (`eq_of_votes`), as do two certificates when
two certificate thresholds exceed `n + f` (`eq_of_certs`), and the commit
rule obeys the laws of an anchored rule at a row and `K ≥ 3`
(`kRule_laws`).
-/

namespace LeanDag

namespace KPartialDag

open Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {p : Params}

/-- **Votes for two blocks of one author at one round** from more than
`n + f` authors together name one block, at a wave of two. -/
theorem eq_of_votes (hv : p.voteIsCert = true) (hw : p.waveLength = 2) {L₁ L₂ : BlockId}
    {r : ℕ} {X₁ X₂ : Finset BlockId} (hX₁ : X₁ ⊆ certsFor p U L₁ r)
    (hX₂ : X₂ ⊆ certsFor p U L₂ r) (hc : (U.block L₁).creator = (U.block L₂).creator)
    (h : Fintype.card Validator + F.f <
      (creatorsOf U.block X₁).card + (creatorsOf U.block X₂).card) : L₁ = L₂ := by
  have hvote : ∀ {L X}, X ⊆ certsFor p U L r → ∀ b ∈ X,
      b ∈ U.ids ∧ (U.block b).round = r + 1 ∧ L ∈ (U.block b).refs := fun {L X} hX b hb => by
    have hb' := hX hb
    unfold certsFor at hb'
    rw [if_pos hv, hw] at hb'
    exact mem_votesFor.mp hb'
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block U.noEquivOn_honest card_compl_correct_le
    (fun b hb => ⟨(hvote hX₁ b hb).1, (hvote hX₁ b hb).2.1⟩)
    (fun b hb => ⟨(hvote hX₂ b hb).1, (hvote hX₂ b hb).2.1⟩) h
  exact (U.valid b (hvote hX₁ b hb₁).1).clause L₁ (hvote hX₁ b hb₁).2.2 L₂
    (hvote hX₂ b hb₂).2.2 hc

/-- **Two certificates for blocks of one author at one round certify one
block**, at a wave of three, when two certificate thresholds exceed
`n + f`. -/
theorem eq_of_certs (hv : p.voteIsCert = false) (hw : p.waveLength = 3)
    (hcert : Fintype.card Validator + F.f < 2 * p.certThreshold) {L₁ L₂ C₁ C₂ : BlockId} {r : ℕ}
    (hC₁ : C₁ ∈ certsFor p U L₁ r) (hC₂ : C₂ ∈ certsFor p U L₂ r)
    (hc : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ := by
  unfold certsFor at hC₁ hC₂
  rw [if_neg (by simp [hv]), hw] at hC₁ hC₂
  obtain ⟨hC₁i, hC₁r, hv₁⟩ := mem_certificatesAt.mp hC₁
  obtain ⟨hC₂i, hC₂r, hv₂⟩ := mem_certificatesAt.mp hC₂
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block U.noEquivOn_honest card_compl_correct_le
    (s := carriedVotes U (IsVote U) C₁ L₁) (t := carriedVotes U (IsVote U) C₂ L₂)
    (fun b hb => (mem_carriedVotes_spec (n := r + 1) hC₁i hC₁r hb).imp_right And.left)
    (fun b hb => (mem_carriedVotes_spec (n := r + 1) hC₂i hC₂r hb).imp_right And.left)
    (by unfold CarriesVotes at hv₁ hv₂; omega)
  exact (U.valid b (mem_carriedVotes_spec (n := r + 1) hC₁i hC₁r hb₁).1).clause L₁
    (mem_carriedVotes.mp hb₁).2 L₂ (mem_carriedVotes.mp hb₂).2 hc

variable [S : Slots Validator]

/-- **A slot skip, read on a view, directly skips each candidate.** -/
theorem directSkip_of_blameSkip {V : U.View} {k : ℕ} {L : BlockId}
    (h : blameSkip (S := S) p.skipThreshold U V k) (hL : IsLeaderBlock U k L) :
    DirectSkip p U L (S.slotRound k) :=
  h.le.trans (Finset.card_le_card (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL)))

omit S in
/-- **Two certificate sets, at a row, name one block**: two sets of
certificates for blocks of one author at one round, from `a` and `b`
authors, the first at least the link threshold and `a + b` past `n + f` at
a wave of two, name one block. -/
theorem eq_of_certsFor (hrow : Row Validator p) {L₁ L₂ : BlockId} {r : ℕ}
    {X₁ X₂ : Finset BlockId} (hX₁ : X₁ ⊆ certsFor p U L₁ r) (hX₂ : X₂ ⊆ certsFor p U L₂ r)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (h₁ : p.linkSize ≤ (creatorsOf U.block X₁).card)
    (h₂ : p.linkSize ≤ (creatorsOf U.block X₂).card)
    (h : p.voteIsCert = true → Fintype.card Validator + F.f <
      (creatorsOf U.block X₁).card + (creatorsOf U.block X₂).card) : L₁ = L₂ := by
  rcases hrow with ⟨hv, hw, -, -⟩ | ⟨hv, hw, hl, ha, -, -⟩
  · exact eq_of_votes hv hw hX₁ hX₂ hc (h hv)
  · obtain ⟨C₁, hC₁⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := X₁) (by omega)
    obtain ⟨C₂, hC₂⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := X₂) (by omega)
    exact eq_of_certs hv hw (by omega) (hX₁ hC₁) (hX₂ hC₂) hc

omit S in
/-- At a row, a direct commit's certificates meet the link threshold, and
together with a link's they number more than `n + f` authors. -/
theorem row_arith (hrow : Row Validator p) {c l : ℕ} (hc : p.commitThreshold ≤ c)
    (hl : p.linkSize ≤ l) :
    p.linkSize ≤ c ∧ (p.voteIsCert = true → Fintype.card Validator + F.f < c + l) := by
  have := F.card_validators
  rcases hrow with ⟨hv, -, -, -, hb, hc'⟩ | ⟨hv, -, hl1, -, -, hc'⟩
  · exact ⟨by omega, fun _ => by omega⟩
  · exact ⟨by omega, fun h => absurd (hv.symm.trans h) (by simp)⟩

omit S in
/-- **Certificates from `linkSize` authors make a block voted**, at a row:
there are `f + 1` of them, votes, when votes are certificates, and one
carrying `f + 1` votes or more otherwise. -/
theorem voted_of_certs (hrow : Row Validator p) {A : BlockId} {X : Finset BlockId}
    (hX : X ⊆ certsFor p U A (U.block A).round) (hn : p.linkSize ≤ (creatorsOf U.block X).card) :
    Voted U A := by
  have := F.card_validators
  unfold Voted
  rcases hrow with ⟨hv, hw, hl, -⟩ | ⟨hv, hw, hl1, ha, -, -⟩
  · refine hl.trans (hn.trans (Finset.card_le_card (Finset.image_subset_image fun C hC => ?_)))
    have hC := hX hC
    unfold certsFor at hC
    rwa [if_pos hv, hw] at hC
  · obtain ⟨C, hC⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := X) (by omega)
    have hC := hX hC
    unfold certsFor at hC
    rw [if_neg (by simp [hv]), hw] at hC
    obtain ⟨hCi, hCr, hcv⟩ := mem_certificatesAt.mp hC
    unfold CarriesVotes at hcv
    exact (by omega : F.f + 1 ≤ p.certThreshold).trans (hcv.trans (Finset.card_le_card
      (creatorsOf_carriedVotes_subset_supporters hCi hCr)))

omit S in
/-- **The laws of the commit rule**, at a row and `K ≥ 3`. -/
theorem kRule_laws (hrow : Row Validator p) {K : ℕ} (hK : 3 ≤ K) :
    (kRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) p K).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ _ hL₁ hL₂ h₁ h₂
    have a₁ := row_arith hrow h₁.le le_rfl
    have a₂ := row_arith hrow h₂.le le_rfl
    exact eq_of_certsFor hrow subset_rfl subset_rfl (hL₁.2.2.trans hL₂.2.2.symm) a₁.1 a₂.1
      fun hv => by have := a₁.2 hv; have := a₂.1; omega
  commit_skip := by
    intro S U V₁ V₂ k L _ hL h hskip
    have hs := directSkip_of_blameSkip hskip hL
    unfold DirectSkip at hs
    have hc := h.le
    have := F.card_validators
    rcases hrow with ⟨hv, hw, -, ha, -, hc'⟩ | ⟨hv, hw, -, -, hb, hc'⟩
    · have := card_votes_add_blames_le hv hw (subset_refl (certsFor p U L (S.slotRound k)))
      omega
    · obtain ⟨C, hC⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block)
        (s := certsFor p U L (S.slotRound k)) (by have := F.card_validators; omega)
      have := card_cert_add_blames_le hv hw hC
      omega
  commit_link := by
    intro S U V k j L A _ _ h hA _ helig
    refine ⟨0, Nat.one_pos, linked hrow hK hA.1 ?_ h.le⟩
    have := (kRule p K).eligible_iff.mp helig
    change S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound j at this
    have : 2 ≤ p.waveLength := by rcases hrow with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    rw [hA.2.1]
    omega
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ _ hlink _
    obtain ⟨X, hX, -, hXn⟩ := hlink
    have a := row_arith hrow h.le hXn
    exact eq_of_certsFor hrow subset_rfl hX (hL₁.2.2.trans hL₂.2.2.symm) a.1 hXn a.2
  skip_link := by
    intro S U V k i L A _ hskip hL _ _ hlink
    exact not_directSkip hrow hlink (directSkip_of_blameSkip hskip hL)
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ hm₁ hm₂
    exact le_antisymm (not_lt.mp (hm₁ L₂ hL₂ hl₂)) (not_lt.mp (hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk _ h => blameSkip_congr hround hk h
  link_congr := (kRule p K).linkCongr_of_round (fun _ U A L r => AvailLinked p U K A L r)
    fun _ _ _ _ _ _ => rfl

end KPartialDag

end LeanDag
