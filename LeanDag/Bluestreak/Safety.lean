import LeanDag.Bluestreak.Rule
import LeanDag.Common.History
/-!
# Bluestreak: safety

The laws of the anchored rule, under `Disciplined`. Every case reduces
to certification: a direct commit certifies its candidate, since a
quorum of claimers has an honest member whose claim is backed; an
anchor's link certifies the linked candidate, since a quorum of the
anchor's voters has an honest member whose cone holds the claim; and
two certified candidates of one slot are one block, as are a certified
candidate and a quorum of omissions impossible together. Visibility is
the descent along an honest self-chain from the anchor's references to
the claimer at `r + 2`. Agreement, monotonicity and the ledger are then
the relation's, at `bluestreakLaws`.
-/

namespace LeanDag

namespace Bluestreak

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload} [ClaimMap BlockId]

/-! ## Claims and certification -/

/-- A claim carried by votes is certified: the votes are in the record. -/
theorem certified_of_carriesVotes {B L : BlockId} (hB : B ∈ U.ids)
    (hr : (U.block B).round = (U.block L).round + 2)
    (h : CarriesVotes U (IsVote U) (quorumCard Validator) B L) : Certified U L :=
  le_trans h (Finset.card_le_card (creatorsOf_carriedVotes_subset_supporters hB hr))

/-- **A claim in an honest block's cone is certified**: explicitly by the
discipline, implicitly by the votes it carries. -/
theorem certified_of_claimers_of_honest [S : Slots Validator] (hI : Disciplined U)
    {B X L : BlockId} (hB : B ∈ U.ids) (hc : (U.block B).creator ∈ (Correct : Finset Validator))
    (hBX : Reaches U B X) (hX : X ∈ claimers U L) : Certified U L := by
  obtain ⟨hXm, hcl⟩ := Finset.mem_filter.mp hX
  obtain ⟨hXi, hXr⟩ := mem_blocksAt.mp hXm
  rcases hcl with hcl | hcl
  · exact hI.honest_backed B hB hc X hBX L hcl
  · exact certified_of_carriesVotes hXi hXr hcl

/-- **B.2.** A directly committed candidate is certified. -/
theorem certified_of_directCommitIn [S : Slots Validator] (hI : Disciplined U) {V : U.View}
    {L : BlockId} (h : DirectCommitIn U V L) : Certified U L := by
  have hf : F.f + 1 ≤ (heldAuthors U V (claimers U L)).card := by
    have := F.card_validators; change quorumCard Validator ≤ _ at h; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hf
  obtain ⟨X, hX, -, hXv⟩ := mem_heldAuthors.mp hv
  have hXi : X ∈ U.ids := (mem_blocksAt.mp (Finset.mem_filter.mp hX).1).1
  exact certified_of_claimers_of_honest hI hXi (hXv ▸ hvc) Reaches.refl hX

/-- **B.3.** A candidate claimed in a certified anchor's cone is
certified: an honest voter for the anchor holds the claim in its cone. -/
theorem certified_of_claimedIn [S : Slots Validator] (hI : Disciplined U) {A L : BlockId}
    (hA : Certified U A) (h : ClaimedIn U A L) : Certified U L := by
  obtain ⟨X, hX, hAX⟩ := h
  have hf : F.f + 1 ≤ (supporters U A ((U.block A).round + 1)).card := by
    have := F.card_validators; change quorumCard Validator ≤ _ at hA; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hf
  obtain ⟨b, hb, -, hbA, hbv⟩ := mem_supporters.mp hv
  exact certified_of_claimers_of_honest hI hb (hbv ▸ hvc)
    ((Reaches.single hbA).trans hAX) hX

/-! ## Two certified candidates, and certification against omission -/

/-- **B.1.** Two certified candidates of one slot are one block. -/
theorem eq_of_certified [S : Slots Validator] {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : Certified U L₁) (h₂ : Certified U L₂) : L₁ = L₂ := by
  unfold Certified at h₁ h₂
  rw [hL₂.2.1, ← hL₁.2.1] at h₂
  exact eq_of_card_supporters U.noEquivOn_honest card_compl_correct_le
    (n := (U.block L₁).round + 1) (by rw [hL₁.2.2, hL₂.2.2])
    (by have := F.card_validators; have := F.card_byzantine; omega)

/-- **B.6.** A certified candidate is not omitted by a quorum of any view. -/
theorem not_holds_omissions_of_certified {V : U.View} {L : BlockId} {r : ℕ}
    (hr : (U.block L).round = r) (h : Certified U L)
    (ho : HoldsAtLeast U V (quorumCard Validator) (omissionsOf U L (r + 1))) : False := by
  unfold Certified at h
  rw [hr] at h
  have hb : quorumCard Validator ≤ (blames U L (r + 1)).card :=
    le_trans ho (Finset.card_le_card heldAuthors_subset)
  have := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  have := F.card_validators; have := F.card_byzantine
  omega

/-! ## Visibility: the self-chain descent -/

/-- A block reaches a block of its own author at every round below it. -/
theorem exists_reaches_self {b : BlockId} (hb : b ∈ U.ids) {t : ℕ}
    (ht : t ≤ (U.block b).round) :
    ∃ c ∈ U.ids, (U.block c).creator = (U.block b).creator ∧ (U.block c).round = t ∧
      Reaches U b c := by
  induction hd : (U.block b).round - t generalizing b with
  | zero => exact ⟨b, hb, rfl, by omega, Reaches.refl⟩
  | succ d ih =>
    obtain ⟨i, hi, hic⟩ := (U.valid b hb).clause.2 (by omega)
    have hir := U.round_of_mem_refs hb hi
    obtain ⟨c, hc, hcc, hcr, hreach⟩ := ih (U.complete b hb i hi) (by omega) (by omega)
    exact ⟨c, hc, hcc.trans hic, hcr, (Reaches.single hi).trans hreach⟩

/-- **B.8.** A directly committed candidate is claimed in the cone of
every candidate anchor of an eligible slot: the anchor's quorum of
references and the quorum of claimers share an honest validator, whose
self-chain descends from the referenced block to its claim. -/
theorem claimedIn_of_directCommitIn_at_anchor [S : Slots Validator] (hI : Disciplined U)
    {V : U.View} {k j : ℕ} {L A : BlockId} (h : DirectCommitIn U V L)
    (hL : IsLeaderBlock U k L) (hA : IsLeaderBlock U j A)
    (helig : (bluestreakAnchored Validator BlockId Payload).Eligible k j) :
    ClaimedIn U A L := by
  have hround := (bluestreakAnchored Validator BlockId Payload).anchor_round_le hA helig
  simp only [bluestreakAnchored_waveAt] at hround
  have hq := hI.leader_quorum j A hA (by omega)
  obtain ⟨v, hv, hvc⟩ := exists_correct_mem_creators_inter hq
    (le_trans h (Finset.card_le_card heldAuthors_subset))
  obtain ⟨a, ha, hav⟩ := mem_creatorsOf.mp (Finset.mem_inter.mp hv).1
  obtain ⟨X, hX, hXv⟩ := mem_creatorsOf.mp (Finset.mem_inter.mp hv).2
  obtain ⟨hXm, -⟩ := Finset.mem_filter.mp hX
  obtain ⟨hXi, hXr⟩ := mem_blocksAt.mp hXm
  have har := U.round_of_mem_refs hA.1 ha
  obtain ⟨c, hc, hcc, hcr, hreach⟩ :=
    exists_reaches_self (U.complete A hA.1 a ha) (t := (U.block L).round + 2)
      (by rw [hL.2.1] at hXr ⊢; omega)
  have hcX : c = X :=
    U.no_equivocation c hc X hXi (by rw [hcc, hav]; exact hvc) (by rw [hcc, hav, hXv])
      (by rw [hcr, hXr])
  exact ⟨X, hX, (Reaches.single ha).trans (hcX ▸ hreach)⟩

/-! ## The discipline on data -/

/-- `Disciplined` in the form a concrete model decides: leader blocks
found at their own round under an identity-round schedule, and claims
read off `history`. -/
theorem Disciplined.of_decide [S : Slots Validator] (hid : ∀ k, S.slotRound k = k)
    (hq : ∀ L, IsLeaderBlock U ((U.block L).round) L → 0 < (U.block L).round →
      quorumCard Validator ≤ (creators U.block (U.block L)).card)
    (hb : ∀ B ∈ U.ids, (U.block B).creator ∈ (Correct : Finset Validator) →
      ∀ X ∈ history U B, ∀ L, claim X = some L → Certified U L) :
    Disciplined U where
  leader_quorum := fun k L hL h0 => hq L (by rw [hL.2.1, hid]; exact hL) h0
  honest_backed := fun B hB hc X hBX L hcl =>
    hb B hB hc X ((mem_history_iff hB).mpr hBX) L hcl

/-! ## The laws -/

/-- The discipline, as the laws' invariant. -/
abbrev Invariant (S : Slots Validator) (U : Universe Validator BlockId Payload) : Prop :=
  Disciplined (S := S) U

/-- **Bluestreak's laws**, under `Disciplined`: every case by
certification. -/
theorem bluestreakLaws :
    (bluestreakAnchored Validator BlockId Payload).Laws
      (Invariant (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  commit_unique := fun hI hL₁ hL₂ h₁ h₂ =>
    eq_of_certified hL₁ hL₂ (certified_of_directCommitIn hI h₁) (certified_of_directCommitIn hI h₂)
  commit_skip := fun hI hL h hskip =>
    not_holds_omissions_of_certified hL.2.1 (certified_of_directCommitIn hI h)
      (hskip.2 _ (mem_leaderBlocksAt.mpr hL))
  commit_link := fun hI hL h hA helig => ⟨0, Nat.one_pos,
    claimedIn_of_directCommitIn_at_anchor hI h hL hA helig⟩
  commit_link_unique := fun hI hL₁ hL₂ h _ hanc _ _ _ hlink _ =>
    eq_of_certified hL₁ hL₂ (certified_of_directCommitIn hI h) (certified_of_claimedIn hI hanc hlink)
  skip_link := fun hI hskip hL _ hanc hlink =>
    not_holds_omissions_of_certified hL.2.1 (certified_of_claimedIn hI hanc hlink)
      (hskip.2 _ (mem_leaderBlocksAt.mpr hL))
  link_unique := fun hI hL₁ hL₂ _ hanc _ _ _ hl₁ hl₂ _ _ =>
    eq_of_certified hL₁ hL₂ (certified_of_claimedIn hI hanc hl₁) (certified_of_claimedIn hI hanc hl₂)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h =>
    ⟨HoldsAtLeast.mono hsub h.1, fun L hL => HoldsAtLeast.mono hsub (h.2 L hL)⟩
  skip_congr := by
    intro S₁ S₂ U V k _ hround hk _ h
    have hlb : leaderBlocksAt (S := S₁) U k = leaderBlocksAt (S := S₂) U k := by
      ext L; simp only [mem_leaderBlocksAt, IsLeaderBlock, hround, hk]
    change DirectSkipIn (S := S₂) U V k
    unfold DirectSkipIn
    rw [← hround, ← hlb]
    exact h
  link_congr := (bluestreakAnchored Validator BlockId Payload).linkCongr_of_round
    (fun _ U A L _ => ClaimedIn U A L) fun _ _ _ _ _ _ => rfl
  anchor_commit := fun hI _ h => certified_of_directCommitIn hI h
  anchor_link := fun hI _ hanc _ _ _ hlink => certified_of_claimedIn hI hanc hlink

end Bluestreak

end LeanDag
