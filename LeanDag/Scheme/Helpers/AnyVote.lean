import LeanDag.Scheme.Helpers.Rows
/-!
# Mahi-Mahi-shaped rows at every vote

At a row with `Params.QuorumRow`, the decider has the anchored rule's
laws at every vote-selection rule. The proofs read the vote through two
facts only: a block selects at most one block of a slot, and a block
that selects a block of a slot does not blame it. Two quorums of
vote-round blocks share a block, which settles certificate uniqueness and
the exclusion of a certificate by a direct skip; a direct commit's
certificates are reached from every block above the decision round.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [F : Faults Validator] {U : BlockUniverse Validator BlockId Payload}
variable (σ : VoteSel Validator BlockId Payload ValidWrt Correct) {p : Params}

/-- **A block votes for at most one block of a slot.** -/
theorem VoteSel.eq_of_votes {q L₁ L₂ : BlockId} (h₁ : σ.Votes U q L₁) (h₂ : σ.Votes U q L₂)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  unfold VoteSel.Votes at h₁ h₂
  rw [hc, hr, h₂] at h₁
  exact (Option.some.inj h₁).symm

theorem voteOffset_eq (hp : p.QuorumRow (Fintype.card Validator) F.f) :
    p.voteOffset = p.waveLength - 2 := by
  obtain ⟨hv, hw, -⟩ := hp
  simp only [Params.voteOffset, hv, Bool.false_eq_true, if_false]
  omega

/-- A certificate is a decision-round block whose votes come from a quorum. -/
theorem mem_certsAt (hp : p.QuorumRow (Fintype.card Validator) F.f) {C L : BlockId} {r : ℕ}
    (hC : C ∈ certsAt p σ U L r) :
    C ∈ U.ids ∧ (U.block C).round = r + (p.waveLength - 1) ∧
      quorumCard Validator ≤ (creatorsOf U.block (carriedVotes U (σ.Votes U) C L)).card := by
  obtain ⟨hb, hcert⟩ := Finset.mem_filter.mp hC
  obtain ⟨hid, hr⟩ := mem_blocksAt.mp hb
  obtain ⟨hv, -, -, ht, -⟩ := hp
  simp only [IsCert, hv, Bool.false_eq_true, if_false, CarriesVotes, ht] at hcert
  exact ⟨hid, hr, hcert⟩

/-- A vote a certificate carries is a vote-round block. -/
theorem mem_carriedVotes_round (hp : p.QuorumRow (Fintype.card Validator) F.f)
    {C L q : BlockId} {r : ℕ} (hC : C ∈ U.ids) (hCr : (U.block C).round = r + (p.waveLength - 1))
    (hq : q ∈ carriedVotes U (σ.Votes U) C L) :
    q ∈ U.ids ∧ (U.block q).round = r + p.voteOffset := by
  rw [mem_carriedVotes] at hq
  refine ⟨U.complete C hC q hq.1, ?_⟩
  have := U.round_of_mem_refs hC hq.1
  rw [voteOffset_eq hp]
  have := hp.2.1
  omega

/-- **Certificate uniqueness**, at every vote. -/
theorem eq_of_certsAt_nonempty (hp : p.QuorumRow (Fintype.card Validator) F.f)
    {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certsAt p σ U L₁ r).Nonempty) (h₂ : (certsAt p σ U L₂ r).Nonempty)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  obtain ⟨hC₁U, hC₁r, hq₁⟩ := mem_certsAt σ hp hC₁
  obtain ⟨hC₂U, hC₂r, hq₂⟩ := mem_certsAt σ hp hC₂
  obtain ⟨q, hv₁, hv₂⟩ := U.exists_common_mem_of_quorums (n := r + p.voteOffset)
    (fun q hq => mem_carriedVotes_round σ hp hC₁U hC₁r hq)
    (fun q hq => mem_carriedVotes_round σ hp hC₂U hC₂r hq) hq₁ hq₂
  exact σ.eq_of_votes (mem_carriedVotes.mp hv₁).2 (mem_carriedVotes.mp hv₂).2 hc hr

variable [S : Slots Validator]

/-- **A direct skip excludes every certificate**, at every vote. -/
theorem certsAt_eq_empty_of_skip (hp : p.QuorumRow (Fintype.card Validator) F.f)
    {V : U.View} {k : ℕ} {L : BlockId}
    (hs : HoldsAtLeast U V p.skipThreshold (blamersAt p σ U k)) (hL : IsLeaderBlock U k L) :
    certsAt p σ U L (S.slotRound k) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  obtain ⟨hCU, hCr, hq⟩ := mem_certsAt σ hp hC
  have hsk : quorumCard Validator ≤ (creatorsOf U.block (blamersAt p σ U k)).card :=
    le_trans hp.2.2.2.2.2 hs.le
  obtain ⟨q, hv, hb⟩ := U.exists_common_mem_of_quorums (n := S.slotRound k + p.voteOffset)
    (fun q hq => mem_carriedVotes_round σ hp hCU hCr hq)
    (fun q hq => mem_blocksAt.mp (Finset.mem_filter.mp hq).1) hq hsk
  have hvote := (mem_carriedVotes.mp hv).2
  have hnone := (Finset.mem_filter.mp hb).2
  unfold VoteSel.Votes at hvote
  rw [hL.2.2, hL.2.1, hnone] at hvote
  exact absurd hvote (by simp)

omit S in
/-- A direct commit holds a certificate. -/
theorem certsAt_nonempty_of_commit {V : U.View} {L : BlockId} {r : ℕ}
    (h : HoldsAtLeast U V (quorumCard Validator) (certsAt p σ U L r)) :
    (certsAt p σ U L r).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have := h.le
  rw [hempty] at this
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at this
  have := F.card_validators
  omega

omit S in
/-- **A direct commit's certificates are reached from above**: every block
above the decision round reaches one. -/
theorem exists_certsAt_reaches (hp : p.QuorumRow (Fintype.card Validator) F.f)
    {V : U.View} {L : BlockId} {r : ℕ}
    (h : HoldsAtLeast U V (quorumCard Validator) (certsAt p σ U L r)) {c : BlockId}
    (hc : c ∈ U.ids) (hcr : r + (p.waveLength - 1) + 1 ≤ (U.block c).round) :
    ∃ C ∈ certsAt p σ U L r, Reaches U c C := by
  have hbase : ∀ c' ∈ U.ids, (U.block c').round = r + (p.waveLength - 1) + 1 →
      ∃ C, C ∈ certsAt p σ U L r ∧ Reaches U c' C := by
    intro c' hc' hc'r
    set T := creatorsOf U.block (certsAt p σ U L r) ∩ (Correct : Finset Validator) with hT_def
    have hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = r + (p.waveLength - 1) ∧
        q ∈ certsAt p σ U L r ∧ (U.block q).creator = v := by
      intro v hv
      rw [hT_def, Finset.mem_inter, mem_creatorsOf] at hv
      obtain ⟨⟨q, hq_cert, hq_creator⟩, _⟩ := hv
      obtain ⟨hq_ids, hq_round, -⟩ := mem_certsAt σ hp hq_cert
      exact ⟨q, hq_ids, hq_round, hq_cert, hq_creator⟩
    have hTc : ∀ v ∈ T, v ∈ (Correct : Finset Validator) :=
      fun _ hv => Finset.mem_of_mem_inter_right hv
    have hcard : F.f + 1 ≤ T.card := card_inter_correct_of_quorum h.le
    obtain ⟨C, hC_mem, hC_cert⟩ :=
      exists_mem_refs_of_honest_support_of_card
        (Q := fun q => q ∈ certsAt p σ U L r) hT hTc (lt_card_add_quorumCard hcard) hc' hc'r
    exact ⟨C, hC_cert, Reaches.single hC_mem⟩
  exact reaches_pred_of_round_le hbase hc hcr

/-- The row's link is a certificate in the anchor's history. -/
theorem link_iff (hp : p.QuorumRow (Fintype.card Validator) F.f) {i k : ℕ} {A L : BlockId}
    (hA : A ∈ U.ids) :
    (schemeAnchored p σ).Link i U A L S k ↔ LinkedVia U A (certsAt p σ U L (S.slotRound k)) := by
  show p.linkSize ≤ _ ↔ _
  rw [hp.2.2.2.2.1]
  exact one_le_card_iff_linkedVia hA _

omit S in
/-- **A Mahi-Mahi-shaped row has the anchored laws at every vote.** -/
theorem quorumRowLaws (hp : p.QuorumRow (Fintype.card Validator) F.f) :
    (schemeAnchored p σ).Laws where
  commit_unique := fun {S U V₁ V₂ k L₁ L₂} _ hL₁ hL₂ h₁ h₂ => by
    have h₁' : HoldsAtLeast U V₁ (quorumCard Validator) (certsAt p σ U L₁ (S.slotRound k)) :=
      hp.2.2.1 ▸ h₁
    have h₂' : HoldsAtLeast U V₂ (quorumCard Validator) (certsAt p σ U L₂ (S.slotRound k)) :=
      hp.2.2.1 ▸ h₂
    exact eq_of_certsAt_nonempty σ hp (certsAt_nonempty_of_commit σ h₁')
      (certsAt_nonempty_of_commit σ h₂') (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  commit_skip := fun {S U V₁ V₂ k L} _ hL h hs => by
    have h' : HoldsAtLeast U V₁ (quorumCard Validator) (certsAt p σ U L (S.slotRound k)) :=
      hp.2.2.1 ▸ h
    have hne := certsAt_nonempty_of_commit σ h'
    rw [certsAt_eq_empty_of_skip σ hp hs hL] at hne
    exact Finset.not_nonempty_empty hne
  commit_link := fun {S U V k j L A} _ _ h hA _ helig => by
    have h' : HoldsAtLeast U V (quorumCard Validator) (certsAt p σ U L (S.slotRound k)) :=
      hp.2.2.1 ▸ h
    have hround := (schemeAnchored p σ).anchor_round_le hA helig
    simp only [schemeAnchored] at hround
    obtain ⟨C, hC, hreach⟩ := exists_certsAt_reaches σ hp h' hA.1 hround
    exact ⟨0, Nat.one_pos, (link_iff σ hp hA.1).mpr ⟨C, hC, hreach⟩⟩
  commit_link_unique := fun {S U V k j i L₁ L₂ A} _ hL₁ hL₂ h hA _ _ _ _ hlink _ => by
    have h' : HoldsAtLeast U V (quorumCard Validator) (certsAt p σ U L₁ (S.slotRound k)) :=
      hp.2.2.1 ▸ h
    exact eq_of_certsAt_nonempty σ hp (certsAt_nonempty_of_commit σ h')
      ((link_iff σ hp hA.1).mp hlink).nonempty (by rw [hL₁.2.2, hL₂.2.2])
      (by rw [hL₁.2.1, hL₂.2.1])
  skip_link := fun {S U V k i L A} _ hs hL _ _ hlink => by
    have hpos : 1 ≤ (creatorsOf U.block ((certsAt p σ U L (S.slotRound k)).filter
        (fun C => C ∈ history U A))).card := hp.2.2.2.2.1 ▸ hlink
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    obtain ⟨C, hC, -⟩ := mem_creatorsOf.mp hv
    have hC' := (Finset.mem_filter.mp hC).1
    rw [certsAt_eq_empty_of_skip σ hp hs hL] at hC'
    exact Finset.notMem_empty C hC'
  link_unique := fun {S U k j i L₁ L₂ A} _ hL₁ hL₂ hA _ _ _ _ hl₁ hl₂ _ _ =>
    eq_of_certsAt_nonempty σ hp ((link_iff σ hp hA.1).mp hl₁).nonempty
      ((link_iff σ hp hA.1).mp hl₂).nonempty (by rw [hL₁.2.2, hL₂.2.2])
      (by rw [hL₁.2.1, hL₂.2.1])
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun {S₁ S₂ U V k} _ hround hk _ h => by
    change HoldsAtLeast U V p.skipThreshold (blamersAt (S := S₁) p σ U k) at h
    show HoldsAtLeast U V p.skipThreshold (blamersAt (S := S₂) p σ U k)
    unfold blamersAt at h ⊢
    rw [← hround, ← hk]
    exact h
  link_congr := (schemeAnchored p σ).linkCongr_of_round
    (fun _ U A L r => p.linkSize ≤ (creatorsOf U.block ((certsAt p σ U L r).filter
      (fun C => C ∈ history U A))).card) fun _ _ _ _ _ _ => rfl

end Scheme

end LeanDag
