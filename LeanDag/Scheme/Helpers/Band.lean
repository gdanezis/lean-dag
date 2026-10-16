import LeanDag.Scheme.Helpers.Local
/-!
# The decider's band laws

At a local vote, a wave of at least two, and positive link and
certificate thresholds, the decider carries its direct commit, its
direct skip and its link across a band: a vote reads the voter's
history from the slot's round up, which the band keeps; a certificate
reads votes one round below it, strictly above the floor, where the band
keeps references; and a certificate in an old anchor's history reaches
back to the band. A candidate the band adds is linked from no old
anchor: its votes would put it in the anchor's history in the old
record.
-/

namespace LeanDag

namespace Scheme

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {R : AnchoredRule Validator BlockId Payload P honest}
variable {U U' : BlockRecord Validator BlockId Payload P honest} {lo hi g g' : ℕ}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest}

/-- A vote, across a band. -/
theorem votes_band (hσ : σ.Local) (h : AgreeBand R.toDagRule U U' lo hi g g') {b L : BlockId}
    (hb : b ∈ U.ids) (hblo : lo ≤ (U.block b).round + g) (hbhi : (U.block b).round + g ≤ hi)
    (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g) (hLhi : (U.block L).round + g ≤ hi) :
    σ.Votes U' b L ↔ σ.Votes U b L := by
  have hLb := AnchoredRule.band_block h hL hLlo hLhi
  unfold VoteSel.Votes
  rw [hLb.2, hσ R h hb hblo hbhi hLlo hLb.1.symm]

theorem creatorsOf_band (h : AgreeBand R.toDagRule U U' lo hi g g') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round + g ∧ (U.block b).round + g ≤ hi) :
    creatorsOf U'.block s = creatorsOf U.block s :=
  Finset.image_congr fun b hb => by
    obtain ⟨hbU, h1, h2⟩ := hs b hb
    exact (AnchoredRule.band_block h hbU h1 h2).2

/-- **A certificate, across a band.** -/
theorem isCert_band (hσ : σ.Local) (h : AgreeBand R.toDagRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : (U.block L).round < (U.block C).round)
    (hChi : (U.block C).round + g ≤ hi) (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g) :
    IsCert p σ U' C L ↔ IsCert p σ U C L := by
  unfold IsCert
  split
  · exact votes_band hσ h hC (by omega) hChi hL hLlo (by omega)
  · unfold CarriesVotes carriedVotes
    rw [AnchoredRule.band_refs h hC (by omega) hChi]
    have hset : (U.block C).refs.filter (fun b => σ.Votes U' b L) =
        (U.block C).refs.filter (fun b => σ.Votes U b L) := by
      refine Finset.filter_congr fun b hb => ?_
      have hbU := U.complete C hC b hb
      have hbr := U.round_of_mem_refs hC hb
      exact votes_band hσ h hbU (by omega) (by omega) hL hLlo (by omega)
    rw [hset, creatorsOf_band h fun b hb => by
      have hb' := (Finset.mem_filter.mp hb).1
      have hbU := U.complete C hC b hb'
      have hbr := U.round_of_mem_refs hC hb'
      exact ⟨hbU, by omega, by omega⟩]

/-- **Certificates carry into the band's other side.** -/
theorem certsAt_subset_band (hσ : σ.Local) (hw : 2 ≤ p.waveLength)
    (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId} {r r' : ℕ} (hL : L ∈ U.ids)
    (hLr : (U.block L).round = r) (hlo : lo ≤ r + g) (hrr : r + g = r' + g')
    (hhi : r + (p.waveLength - 1) + g ≤ hi) :
    certsAt p σ U L r ⊆ certsAt p σ U' L r' := by
  intro C hC
  obtain ⟨hCb, hcert⟩ := Finset.mem_filter.mp hC
  obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hCb
  have hCb' := AnchoredRule.band_block h hCU (by omega) (by omega)
  refine Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨AnchoredRule.band_mem h hCU (by omega)
    (by omega), by omega⟩, (isCert_band hσ h hCU (by omega) (by omega) hL (by omega)).mpr hcert⟩

/-- A certificate in an old anchor's history, across a band, is one
there was. -/
theorem certsAt_history_band (hσ : σ.Local) (hw : 2 ≤ p.waveLength)
    (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi) (hL : L ∈ U.ids)
    (hLr : (U.block L).round = r) (hlo : lo ≤ r + g) (hrr : r + g = r' + g')
    (hhi : r + (p.waveLength - 1) + g ≤ hi) :
    (certsAt p σ U' L r').filter (fun C => C ∈ history U' A) =
      (certsAt p σ U L r).filter (fun C => C ∈ history U A) := by
  have hA' := AnchoredRule.band_mem h hA hAlo hAhi
  ext C
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hC', hCh'⟩
    obtain ⟨hCb', hcert'⟩ := Finset.mem_filter.mp hC'
    obtain ⟨-, hCr'⟩ := mem_blocksAt.mp hCb'
    obtain ⟨hCU, hre, hreq⟩ := AgreeBand.reaches_old h hA hAlo hAhi
      ((mem_history_iff (U := U') hA').mp hCh') (by show lo ≤ (U'.block C).round + g'; omega)
    have hreq' : (U.block C).round + g = (U'.block C).round + g' := hreq
    refine ⟨Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hCU, by omega⟩,
      (isCert_band hσ h hCU (by omega) (by omega) hL (by omega)).mp hcert'⟩,
      (mem_history_iff (U := U) hA).mpr hre⟩
  · rintro ⟨hC, hCh⟩
    obtain ⟨hCb, -⟩ := Finset.mem_filter.mp hC
    obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hCb
    exact ⟨certsAt_subset_band hσ hw h hL hLr hlo hrr hhi hC,
      (mem_history_iff (U := U') hA').mpr (AgreeBand.reaches_of h hA hAhi
        ((mem_history_iff (U := U) hA).mp hCh) (by show lo ≤ (U.block C).round + g; omega))⟩

variable [S : Slots Validator] {S' : Slots Validator}

/-- **Blames carry into the band's other side.** -/
theorem blamersAt_subset_band (hσ : σ.Local) (hw : 2 ≤ p.waveLength)
    (h : AgreeBand R.toDagRule U U' lo hi g g') {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlk : S.leader k = S'.leader k')
    (hlo : lo ≤ S.slotRound k + g) (hhi : S.slotRound k + (p.waveLength - 1) + g ≤ hi) :
    blamersAt (S := S) p σ U k ⊆ blamersAt (S := S') p σ U' k' := by
  have hoff : p.voteOffset ≤ p.waveLength - 1 := by
    unfold Params.voteOffset; split <;> omega
  intro b hb
  obtain ⟨hbb, hnone⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hbb
  have hbb' := AnchoredRule.band_block h hbU (by omega) (by omega)
  refine Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨AnchoredRule.band_mem h hbU (by omega)
    (by omega), by omega⟩, ?_⟩
  rw [← hlk, hσ R h hbU (by omega) (by omega) hlo hkk]
  exact hnone

omit S in
/-- **The decider's band laws.** -/
theorem schemeBandLaws (hσ : σ.Local) (hw : 2 ≤ p.waveLength) (hl : 1 ≤ p.linkSize)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) : (schemeAnchored p σ).BandLaws where
  commit_band := fun {S S' U U' lo hi g g' V V' k k' L} h hkk hlk _ hlo hhi hV hL hcommit => by
    have hw' : (schemeAnchored p σ).waveAt (S.kind k) = p.waveLength - 1 := rfl
    have h' : AgreeBand (schemeAnchored p σ).toDagRule U U' lo hi g g' := h
    exact AnchoredRule.holdsAtLeast_band h' hV (fun C hC => by
        obtain ⟨hCb, -⟩ := Finset.mem_filter.mp hC
        obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hCb
        exact ⟨hCU, by omega, by omega⟩)
      (certsAt_subset_band hσ hw h hL.1 hL.2.1 (by omega) hkk (by omega)) hcommit
  skip_band := fun {S S' U U' lo hi g g' V V' k k'} h hkk hlk _ hlo hhi hV hskip => by
    have hw' : (schemeAnchored p σ).waveAt (S.kind k) = p.waveLength - 1 := rfl
    have hoff : p.voteOffset ≤ p.waveLength - 1 := by
      unfold Params.voteOffset; split <;> omega
    exact AnchoredRule.holdsAtLeast_band h hV (fun b hb => by
        obtain ⟨hbb, -⟩ := Finset.mem_filter.mp hb
        obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hbb
        exact ⟨hbU, by omega, by omega⟩)
      (blamersAt_subset_band (S := S) hσ hw h hkk hlk (by omega) (by omega)) hskip
  link_band := fun {S S' U U' lo hi g g' A L k k' i} h hA hAlo hAhi hkk hlk _ hlo hhi _ hL => by
    have hw' : (schemeAnchored p σ).waveAt (S.kind k) = p.waveLength - 1 := rfl
    show p.linkSize ≤ _ ↔ p.linkSize ≤ _
    rw [certsAt_history_band hσ hw h hA hAlo hAhi hL.1 hL.2.1 hlo hkk (by omega),
      creatorsOf_band h fun C hC => by
        obtain ⟨hCc, hCh⟩ := Finset.mem_filter.mp hC
        obtain ⟨hCb, -⟩ := Finset.mem_filter.mp hCc
        obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hCb
        exact ⟨hCU, by omega, by omega⟩]
  link_novel := fun {S S' U U' lo hi g g' A L k k' i} h hA _ hAlo hAhi hkk hlk _ hlo hhi _ hL
      hLo hlink => by
    have hw' : (schemeAnchored p σ).waveAt (S.kind k) = p.waveLength - 1 := rfl
    have hA' := AnchoredRule.band_mem h hA hAlo hAhi
    have hlink' : p.linkSize ≤ (creatorsOf U'.block ((certsAt p σ U' L (S'.slotRound k')).filter
        (fun C => C ∈ history U' A))).card := hlink
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hl hlink')
    obtain ⟨C, hC, -⟩ := mem_creatorsOf.mp hv
    obtain ⟨hCc, hCh⟩ := Finset.mem_filter.mp hC
    obtain ⟨hCb, hcert⟩ := Finset.mem_filter.mp hCc
    obtain ⟨hCU', hCr'⟩ := mem_blocksAt.mp hCb
    -- the candidate lies in the anchor's history in the new record
    have hLh : L ∈ history U' A := by
      have hCA := hCh
      unfold IsCert at hcert
      split at hcert
      · exact history_subset_of_reaches hA' ((mem_history_iff hA').mp hCA)
          (σ.sound U' C _ _ L hcert).1
      · rename_i hv
        obtain ⟨b, hb, hbL⟩ := exists_vote_of_carriesVotes (hc (by simpa using hv)) hcert
        have hbh : b ∈ history U' A := history_subset_of_reaches hA'
          ((mem_history_iff hA').mp hCA) (mem_history_of_mem_refs hCU' hb)
        exact history_subset_of_reaches hA' ((mem_history_iff hA').mp hbh)
          (σ.sound U' b _ _ L hbL).1
    obtain ⟨hLU, -, -⟩ := AgreeBand.reaches_old h hA hAlo hAhi ((mem_history_iff hA').mp hLh)
      (by show lo ≤ (U'.block L).round + g'; rw [hL.2.1]; omega)
    exact hLo hLU

end Scheme

end LeanDag
