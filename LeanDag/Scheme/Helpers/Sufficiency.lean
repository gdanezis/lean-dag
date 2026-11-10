import LeanDag.Scheme.Helpers.Votes
import LeanDag.Common.Anchored
import LeanDag.Common.History
/-!
# The table's inequalities suffice

On a record whose blocks reference `q` distinct authors one round down,
and whose validators outside `Hon` (at most `f` of them) never
equivocate, every row meeting its family's inequalities has the anchored
laws at every vote-selection rule. Each step is one of two counts:

* two sets of blocks at one round whose authors number more than `n + f`
  together share a block (`exists_common_block`), and a block selects at
  most one block of a slot and does not blame a slot it selects in;
* every block above the decision round holds in its history at least
  `c + q − n − f` authors of any `c`-author set of decision-round blocks.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {q : ℕ} [P.Quorate q]
variable {U : BlockRecord Validator BlockId Payload P honest}
variable (σ : VoteSel Validator BlockId Payload P honest) {p : Params}
variable {Hon : Finset Validator} {f : ℕ}

omit [Fintype Validator] [LinearOrder BlockId] [P.Mechanised] in
theorem one_le_card_nonempty {s : Finset BlockId} (h : 1 ≤ (creatorsOf U.block s).card) :
    s.Nonempty := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  obtain ⟨b, hb, -⟩ := mem_creatorsOf.mp hv
  exact ⟨b, hb⟩

omit [Fintype Validator] [P.Mechanised] in
theorem mem_certsAt_iff {C L : BlockId} {r : ℕ} :
    C ∈ certsAt p σ U L r ↔
      C ∈ U.ids ∧ (U.block C).round = r + (p.waveLength - 1) ∧ IsCert p σ U C L := by
  simp only [certsAt, Finset.mem_filter, mem_blocksAt, and_assoc]

omit [LinearOrder BlockId] [P.Mechanised] [P.Quorate q] in
/-- **Where nobody equivocates, a slot has one block**: two blocks of one
author and round are one block. -/
theorem eq_of_noEquiv_all (hne : U.NoEquivOn Hon) (hHon : Honᶜ.card ≤ 0) {L₁ L₂ : BlockId}
    (h₁ : L₁ ∈ U.ids) (h₂ : L₂ ∈ U.ids) (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ :=
  hne L₁ h₁ L₂ h₂ (by
    by_contra h
    have := Finset.card_pos.mpr ⟨_, Finset.mem_compl.mpr h⟩
    omega) hc hr

variable [S : Slots Validator]

/-! ## The laws every row has

Monotonicity, the skip's and the link's reading of the schedule, and
visibility at an inequality of the form `link + n + f ≤ commit + q`, which
every covered family meets. -/

section Common

variable {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}

omit [Fintype Validator] [P.Quorate q] S in
theorem schemeCommitMono : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V V' : U.View} {L : BlockId} {r κ : ℕ}, I S U → V.ids ⊆ V'.ids →
    (schemeAnchored p σ).Commit U V L r κ → (schemeAnchored p σ).Commit U V' L r κ :=
  fun _ hsub h => HoldsAtLeast.mono hsub h

omit [Fintype Validator] [P.Quorate q] S in
theorem schemeSkipMono : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V V' : U.View} {k : ℕ}, I S U → V.ids ⊆ V'.ids →
    (schemeAnchored p σ).Skip U V S k → (schemeAnchored p σ).Skip U V' S k :=
  fun _ hsub h => HoldsAtLeast.mono hsub h

omit [Fintype Validator] [P.Quorate q] S in
theorem schemeSkipCongr : ∀ {S₁ S₂ : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {V : U.View} {k : ℕ}, I S₁ U →
    S₁.slotRound k = S₂.slotRound k → S₁.leader k = S₂.leader k → S₁.kind k = S₂.kind k →
    (schemeAnchored p σ).Skip U V S₁ k → (schemeAnchored p σ).Skip U V S₂ k := by
  intro S₁ S₂ U V k _ hround hk _ h
  change HoldsAtLeast U V p.skipThreshold (blamersAt (S := S₁) p σ U k) at h
  change HoldsAtLeast U V p.skipThreshold (blamersAt (S := S₂) p σ U k)
  unfold blamersAt at h ⊢
  rw [← hround, ← hk]
  exact h

omit [Fintype Validator] [P.Quorate q] S in
theorem schemeLinkCongr : (schemeAnchored p σ).LinkCongr :=
  (schemeAnchored p σ).linkCongr_of_round
    (fun _ U A L r => p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L r)).card)
    fun _ _ _ _ _ _ => rfl

end Common

omit [Fintype Validator] [P.Quorate q] S in
theorem linkCerts_subset {A L : BlockId} {r : ℕ} : linkCerts p σ U A L r ⊆ certsAt p σ U L r :=
  Finset.filter_subset _ _

omit S in
/-- **Visibility**, at `link + n + f ≤ commit + q`: a direct commit's
certificates in any anchor's history meet the link threshold. -/
theorem schemeCommitLink (hHon : Honᶜ.card ≤ f)
    (hineq : p.linkSize + Fintype.card Validator + f ≤ p.commitThreshold + q) :
    ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
      {V : U.View} {k j : ℕ} {L A : BlockId},
      U.NoEquivOn Hon → IsLeaderBlock U k L →
      (schemeAnchored p σ).Commit U V L (S.slotRound k) (S.kind k) →
      IsLeaderBlock U j A → (schemeAnchored p σ).Anchor U A → (schemeAnchored p σ).Eligible k j →
      ∃ i, i < (schemeAnchored p σ).rungs ∧ (schemeAnchored p σ).Link i U A L S k := by
  intro S U V k j L A hne hL h hA _ helig
  have hround := (schemeAnchored p σ).anchor_round_le hA helig
  simp only [schemeAnchored] at hround
  have hvis := card_inHistory_ge hne hHon (X := certsAt p σ U L (S.slotRound k))
    (fun b hb => let h := (mem_certsAt_iff σ).mp hb; ⟨h.1, h.2.1⟩)
    ((U.block A).round - (S.slotRound k + (p.waveLength - 1)) - 1) A hA.1 (by omega)
  have := h.le
  refine ⟨0, Nat.one_pos, ?_⟩
  change p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card
  simp only [linkCerts]
  omega

/-! ## Votes as certificates: the two-round family -/

section TwoRound

variable (hv : p.voteIsCert = true) (hw : 2 ≤ p.waveLength)
include hv

omit [Fintype Validator] [P.Mechanised] S in
theorem mem_certsAt_two {C L : BlockId} {r : ℕ} :
    C ∈ certsAt p σ U L r ↔
      C ∈ U.ids ∧ (U.block C).round = r + (p.waveLength - 1) ∧ σ.Votes U C L := by
  rw [mem_certsAt_iff, isCert_iff_votes σ p hv]

omit [P.Mechanised] S in
/-- Two sets of votes for two blocks of a slot, past `n + f` authors, name
one block. -/
theorem eq_of_votes_two (hne : U.NoEquivOn Hon) (hHon : Honᶜ.card ≤ f)
    {L₁ L₂ : BlockId} {r : ℕ} {s t : Finset BlockId}
    (hs : s ⊆ certsAt p σ U L₁ r) (ht : t ⊆ certsAt p σ U L₂ r)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round)
    (h : Fintype.card Validator + f < (creatorsOf U.block s).card + (creatorsOf U.block t).card) :
    L₁ = L₂ := by
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block hne hHon
    (n := r + (p.waveLength - 1))
    (fun b hb => let h := (mem_certsAt_two σ hv).mp (hs hb); ⟨h.1, h.2.1⟩)
    (fun b hb => let h := (mem_certsAt_two σ hv).mp (ht hb); ⟨h.1, h.2.1⟩) h
  exact σ.eq_of_votes ((mem_certsAt_two σ hv).mp (hs hb₁)).2.2
    ((mem_certsAt_two σ hv).mp (ht hb₂)).2.2 hc hr

omit [P.Mechanised] in
/-- Votes for a candidate and the slot's blames, past `n + f` authors,
cannot both hold. -/
theorem not_votes_blames_two (hne : U.NoEquivOn Hon) (hHon : Honᶜ.card ≤ f)
    {L : BlockId} {k : ℕ} {s : Finset BlockId} (hL : IsLeaderBlock U k L)
    (hs : s ⊆ certsAt p σ U L (S.slotRound k))
    (h : Fintype.card Validator + f <
      (creatorsOf U.block s).card + (creatorsOf U.block (blamersAt p σ U k)).card) : False := by
  have hoff := Params.voteOffset_of_true hv
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block hne hHon
    (n := S.slotRound k + (p.waveLength - 1))
    (fun b hb => let h := (mem_certsAt_two σ hv).mp (hs hb); ⟨h.1, h.2.1⟩)
    (fun b hb => by
      obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hb).1
      exact ⟨hbU, hoff ▸ hbr⟩) h
  have hvote := ((mem_certsAt_two σ hv).mp (hs hb₁)).2.2
  have hnone := (Finset.mem_filter.mp hb₂).2
  unfold VoteSel.Votes at hvote
  rw [hL.2.2, hL.2.1, hnone] at hvote
  exact absurd hvote (by simp)

omit S in
/-- **A two-round row meeting its inequalities has the anchored laws**, at
every vote, on records where validators outside `Hon` do not equivocate. -/
theorem twoRoundLaws (hHon : Honᶜ.card ≤ f) (hq : q ≤ Fintype.card Validator)
    (hineq : p.TwoRound (Fintype.card Validator) f q) :
    (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) where
  commit_unique := fun {S U V₁ V₂ k L₁ L₂} hne hL₁ hL₂ h₁ h₂ => by
    have := h₁.le; have := h₂.le
    obtain ⟨ha, hb, hc⟩ := hineq
    exact eq_of_votes_two σ hv hne hHon (r := S.slotRound k) subset_rfl subset_rfl
      (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1]) (by omega)
  commit_skip := fun {S U V₁ V₂ k L} hne hL h hs => by
    have := h.le; have := hs.le
    obtain ⟨ha, hb, hc⟩ := hineq
    exact not_votes_blames_two σ hv hne hHon hL subset_rfl (by omega)
  commit_link := schemeCommitLink σ hHon (by obtain ⟨-, -, hc⟩ := hineq; omega)
  commit_link_unique := fun {S U V k j i L₁ L₂ A} hne hL₁ hL₂ h _ _ _ _ _ hlink _ => by
    have := h.le
    have hl : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L₂ (S.slotRound k))).card := hlink
    obtain ⟨ha, hb, hc⟩ := hineq
    exact eq_of_votes_two σ hv hne hHon (r := S.slotRound k) subset_rfl
      (linkCerts_subset σ (A := A))
      (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1]) (by omega)
  skip_link := fun {S U V k i L A} hne hs hL _ _ hlink => by
    have := hs.le
    have hl : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card := hlink
    obtain ⟨ha, hb, hc⟩ := hineq
    exact not_votes_blames_two σ hv hne hHon hL (linkCerts_subset σ (A := A)) (by omega)
  link_unique := fun {S U k j i L₁ L₂ A} _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ hm₁ hm₂ =>
    le_antisymm (not_lt.mp (hm₁ L₂ hL₂ hl₂)) (not_lt.mp (hm₂ L₁ hL₁ hl₁))
  commit_mono := fun {S} => schemeCommitMono σ (I := fun _ U => U.NoEquivOn Hon) (S := S)
  skip_mono := schemeSkipMono σ (I := fun _ U => U.NoEquivOn Hon)
  skip_congr := schemeSkipCongr σ (I := fun _ U => U.NoEquivOn Hon)
  link_congr := schemeLinkCongr σ

omit S in
/-- **A two-round row meeting its inequalities where nobody equivocates has
the anchored laws**, at every vote: the two blocks the uniqueness laws
compare are one block of one slot. -/
theorem twoRoundCrashLaws (hHon : Honᶜ.card ≤ 0) (hq : q ≤ Fintype.card Validator)
    (hineq : p.TwoRoundCrash (Fintype.card Validator) q) :
    (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) where
  commit_unique := fun {S U V₁ V₂ k L₁ L₂} hne hL₁ hL₂ _ _ =>
    eq_of_noEquiv_all hne hHon hL₁.1 hL₂.1 (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  commit_skip := fun {S U V₁ V₂ k L} hne hL h hs => by
    have := h.le; have := hs.le
    obtain ⟨ha, hc⟩ := hineq
    exact not_votes_blames_two σ hv hne hHon hL subset_rfl (by omega)
  commit_link := schemeCommitLink σ hHon (by obtain ⟨-, hc⟩ := hineq; omega)
  commit_link_unique := fun {S U V k j i L₁ L₂ A} hne hL₁ hL₂ _ _ _ _ _ _ _ _ =>
    eq_of_noEquiv_all hne hHon hL₁.1 hL₂.1 (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  skip_link := fun {S U V k i L A} hne hs hL _ _ hlink => by
    have := hs.le
    have hl : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card := hlink
    obtain ⟨ha, hc⟩ := hineq
    exact not_votes_blames_two σ hv hne hHon hL (linkCerts_subset σ (A := A))
      (by omega)
  link_unique := fun {S U k j i L₁ L₂ A} _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ hm₁ hm₂ =>
    le_antisymm (not_lt.mp (hm₁ L₂ hL₂ hl₂)) (not_lt.mp (hm₂ L₁ hL₁ hl₁))
  commit_mono := fun {S} => schemeCommitMono σ (I := fun _ U => U.NoEquivOn Hon) (S := S)
  skip_mono := schemeSkipMono σ (I := fun _ U => U.NoEquivOn Hon)
  skip_congr := schemeSkipCongr σ (I := fun _ U => U.NoEquivOn Hon)
  link_congr := schemeLinkCongr σ

end TwoRound

/-! ## Certificates of votes: the three-round family -/

section ThreeRound

variable (hv : p.voteIsCert = false) (hw : 3 ≤ p.waveLength)
include hv hw

omit [Fintype Validator] [P.Mechanised] S hw in
theorem mem_certsAt_three {C L : BlockId} {r : ℕ} :
    C ∈ certsAt p σ U L r ↔
      C ∈ U.ids ∧ (U.block C).round = r + (p.waveLength - 1) ∧
        p.certThreshold ≤ (creatorsOf U.block (carriedVotes U (σ.Votes U) C L)).card := by
  rw [mem_certsAt_iff, isCert_iff_carries σ p hv]
  rfl

omit [Fintype Validator] S in
theorem mem_carriedVotes_three {C L b : BlockId} {r : ℕ} (hC : C ∈ certsAt p σ U L r)
    (hb : b ∈ carriedVotes U (σ.Votes U) C L) :
    b ∈ U.ids ∧ (U.block b).round = r + p.voteOffset := by
  obtain ⟨hCU, hCr, -⟩ := (mem_certsAt_three σ hv).mp hC
  rw [mem_carriedVotes] at hb
  refine ⟨U.complete C hCU b hb.1, ?_⟩
  have := U.round_of_mem_refs hCU hb.1
  simp only [Params.voteOffset, hv, Bool.false_eq_true, if_false]
  omega

omit S in
/-- **Certificates are unique** when two certificate thresholds exceed
`n + f`. -/
theorem eq_of_certs_three (hne : U.NoEquivOn Hon) (hHon : Honᶜ.card ≤ f)
    (hcert : Fintype.card Validator + f < 2 * p.certThreshold)
    {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certsAt p σ U L₁ r).Nonempty) (h₂ : (certsAt p σ U L₂ r).Nonempty)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  have k₁ := ((mem_certsAt_three σ hv).mp hC₁).2.2
  have k₂ := ((mem_certsAt_three σ hv).mp hC₂).2.2
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block hne hHon (n := r + p.voteOffset)
    (fun b hb => mem_carriedVotes_three σ hv hw hC₁ hb)
    (fun b hb => mem_carriedVotes_three σ hv hw hC₂ hb) (by omega)
  exact σ.eq_of_votes (mem_carriedVotes.mp hb₁).2 (mem_carriedVotes.mp hb₂).2 hc hr

/-- **A certificate and the slot's blames** cannot both hold when the
skip and certificate thresholds exceed `n + f`. -/
theorem not_cert_blames_three (hne : U.NoEquivOn Hon) (hHon : Honᶜ.card ≤ f)
    {L : BlockId} {k : ℕ} (hL : IsLeaderBlock U k L)
    (hC : (certsAt p σ U L (S.slotRound k)).Nonempty)
    (h : Fintype.card Validator + f <
      p.certThreshold + (creatorsOf U.block (blamersAt p σ U k)).card) : False := by
  obtain ⟨C, hC⟩ := hC
  have k₁ := ((mem_certsAt_three σ hv).mp hC).2.2
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_block hne hHon (n := S.slotRound k + p.voteOffset)
    (s := carriedVotes U (σ.Votes U) C L) (t := blamersAt p σ U k)
    (fun b hb => mem_carriedVotes_three σ hv hw hC hb)
    (fun b hb => mem_blocksAt.mp (Finset.mem_filter.mp hb).1) (by omega)
  have hvote := (mem_carriedVotes.mp hb₁).2
  have hnone := (Finset.mem_filter.mp hb₂).2
  unfold VoteSel.Votes at hvote
  rw [hL.2.2, hL.2.1, hnone] at hvote
  exact absurd hvote (by simp)

omit S in
/-- **A three-round row meeting its inequalities has the anchored laws**,
with a link of one certificate, at every vote, on records where validators
outside `Hon` do not equivocate. -/
theorem threeRoundLaws (hHon : Honᶜ.card ≤ f) (hq : q ≤ Fintype.card Validator)
    (hl : p.linkSize = 1) (hineq : p.ThreeRound (Fintype.card Validator) f q) :
    (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) where
  commit_unique := fun {S U V₁ V₂ k L₁ L₂} hne hL₁ hL₂ h₁ h₂ => by
    have := h₁.le; have := h₂.le
    obtain ⟨ha, hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (certsAt p σ U L₁ (S.slotRound k))).card := by omega
    have g₂ : 1 ≤ (creatorsOf U.block (certsAt p σ U L₂ (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + f < 2 * p.certThreshold := by omega
    exact eq_of_certs_three σ hv hw hne hHon g (one_le_card_nonempty g₁) (one_le_card_nonempty g₂)
      (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  commit_skip := fun {S U V₁ V₂ k L} hne hL h hs => by
    have := h.le; have := hs.le
    obtain ⟨ha, hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (certsAt p σ U L (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + f <
        p.certThreshold + (creatorsOf U.block (blamersAt p σ U k)).card := by omega
    exact not_cert_blames_three σ hv hw hne hHon hL (one_le_card_nonempty g₁) g
  commit_link := schemeCommitLink σ hHon (by obtain ⟨-, -, hc⟩ := hineq; omega)
  commit_link_unique := fun {S U V k j i L₁ L₂ A} hne hL₁ hL₂ h _ _ _ _ _ hlink _ => by
    have := h.le
    have hlk : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L₂ (S.slotRound k))).card := hlink
    obtain ⟨ha, hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (certsAt p σ U L₁ (S.slotRound k))).card := by omega
    have g₂ : 1 ≤ (creatorsOf U.block (linkCerts p σ U A L₂ (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + f < 2 * p.certThreshold := by omega
    exact eq_of_certs_three σ hv hw hne hHon g (one_le_card_nonempty g₁)
      ((one_le_card_nonempty g₂).mono (Finset.filter_subset _ _))
      (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  skip_link := fun {S U V k i L A} hne hs hL _ _ hlink => by
    have := hs.le
    have hlk : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card := hlink
    obtain ⟨ha, hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + f <
        p.certThreshold + (creatorsOf U.block (blamersAt p σ U k)).card := by omega
    exact not_cert_blames_three σ hv hw hne hHon hL
      ((one_le_card_nonempty g₁).mono (Finset.filter_subset _ _)) g
  link_unique := fun {S U k j i L₁ L₂ A} hne hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ _ _ => by
    have hk₁ : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L₁ (S.slotRound k))).card := hl₁
    have hk₂ : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L₂ (S.slotRound k))).card := hl₂
    obtain ⟨ha, hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (linkCerts p σ U A L₁ (S.slotRound k))).card := by omega
    have g₂ : 1 ≤ (creatorsOf U.block (linkCerts p σ U A L₂ (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + f < 2 * p.certThreshold := by omega
    exact eq_of_certs_three σ hv hw hne hHon g
      ((one_le_card_nonempty g₁).mono (Finset.filter_subset _ _))
      ((one_le_card_nonempty g₂).mono (Finset.filter_subset _ _))
      (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  commit_mono := fun {S} => schemeCommitMono σ (I := fun _ U => U.NoEquivOn Hon) (S := S)
  skip_mono := schemeSkipMono σ (I := fun _ U => U.NoEquivOn Hon)
  skip_congr := schemeSkipCongr σ (I := fun _ U => U.NoEquivOn Hon)
  link_congr := schemeLinkCongr σ

omit S in
/-- **A three-round row meeting its inequalities where nobody equivocates
has the anchored laws**, with a link of one certificate, at every vote: the
two blocks the uniqueness laws compare are one block of one slot. -/
theorem threeRoundCrashLaws (hHon : Honᶜ.card ≤ 0) (hq : q ≤ Fintype.card Validator)
    (hl : p.linkSize = 1) (hineq : p.ThreeRoundCrash (Fintype.card Validator) q) :
    (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) where
  commit_unique := fun {S U V₁ V₂ k L₁ L₂} hne hL₁ hL₂ _ _ =>
    eq_of_noEquiv_all hne hHon hL₁.1 hL₂.1 (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  commit_skip := fun {S U V₁ V₂ k L} hne hL h hs => by
    have := h.le; have := hs.le
    obtain ⟨hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (certsAt p σ U L (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + 0 <
        p.certThreshold + (creatorsOf U.block (blamersAt p σ U k)).card := by omega
    exact not_cert_blames_three σ hv hw hne hHon hL (one_le_card_nonempty g₁) g
  commit_link := schemeCommitLink σ hHon (by obtain ⟨-, hc⟩ := hineq; omega)
  commit_link_unique := fun {S U V k j i L₁ L₂ A} hne hL₁ hL₂ _ _ _ _ _ _ _ _ =>
    eq_of_noEquiv_all hne hHon hL₁.1 hL₂.1 (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  skip_link := fun {S U V k i L A} hne hs hL _ _ hlink => by
    have := hs.le
    have hlk : p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card := hlink
    obtain ⟨hb, hc⟩ := hineq
    have g₁ : 1 ≤ (creatorsOf U.block (linkCerts p σ U A L (S.slotRound k))).card := by omega
    have g : Fintype.card Validator + 0 <
        p.certThreshold + (creatorsOf U.block (blamersAt p σ U k)).card := by omega
    exact not_cert_blames_three σ hv hw hne hHon hL
      ((one_le_card_nonempty g₁).mono (Finset.filter_subset _ _)) g
  link_unique := fun {S U k j i L₁ L₂ A} hne hL₁ hL₂ _ _ _ _ _ _ _ _ _ =>
    eq_of_noEquiv_all hne hHon hL₁.1 hL₂.1 (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
  commit_mono := fun {S} => schemeCommitMono σ (I := fun _ U => U.NoEquivOn Hon) (S := S)
  skip_mono := schemeSkipMono σ (I := fun _ U => U.NoEquivOn Hon)
  skip_congr := schemeSkipCongr σ (I := fun _ U => U.NoEquivOn Hon)
  link_congr := schemeLinkCongr σ

end ThreeRound

omit [Fintype Validator] [P.Mechanised] S in
/-- Laws under an invariant every record has are laws. -/
theorem laws_of_forall {R : AnchoredRule Validator BlockId Payload P honest}
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hl : R.Laws I) (hI : ∀ S U, I S U) : R.Laws where
  commit_unique := fun _ => hl.commit_unique (hI _ _)
  commit_skip := fun _ => hl.commit_skip (hI _ _)
  commit_link := fun _ => hl.commit_link (hI _ _)
  commit_link_unique := fun _ => hl.commit_link_unique (hI _ _)
  skip_link := fun _ => hl.skip_link (hI _ _)
  link_unique := fun _ => hl.link_unique (hI _ _)
  commit_mono := fun {S U _ _ _ _ _} _ => hl.commit_mono (hI S U)
  skip_mono := fun _ => hl.skip_mono (hI _ _)
  skip_congr := fun _ => hl.skip_congr (hI _ _)
  link_congr := hl.link_congr
  anchor_commit := fun _ => hl.anchor_commit (hI _ _)
  anchor_link := fun _ => hl.anchor_link (hI _ _)

omit S in
/-- The rows the inequalities cover (`Params.Covered`), at non-equivocation
on `Hon`, have positive thresholds and their laws. -/
theorem coveredLawsOn (hHon : Honᶜ.card ≤ f)
    (hq : q ≤ Fintype.card Validator)
    (hfam : p.Covered (Fintype.card Validator) f q) :
    1 ≤ p.linkSize ∧ 1 ≤ p.commitThreshold ∧ (p.voteIsCert = false → 1 ≤ p.certThreshold) ∧
      (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) := by
  rcases hfam with ⟨hv, -, hl, hineq⟩ | ⟨hv, hw, hl, hineq⟩ | ⟨hv, -, hl, rfl, hineq⟩ |
    ⟨hv, hw, hl, hc1, rfl, hineq⟩
  · obtain ⟨-, -, hc⟩ := id hineq
    exact ⟨hl, by omega, fun h => absurd (hv.symm.trans h) (by simp),
      twoRoundLaws σ hv hHon hq hineq⟩
  · obtain ⟨ha, -, hc⟩ := id hineq
    exact ⟨by omega, by omega, fun _ => by omega, threeRoundLaws σ hv hw hHon hq hl hineq⟩
  · obtain ⟨-, hc⟩ := id hineq
    exact ⟨hl, by omega, fun h => absurd (hv.symm.trans h) (by simp),
      twoRoundCrashLaws σ hv hHon hq hineq⟩
  · obtain ⟨-, hc⟩ := id hineq
    exact ⟨by omega, by omega, fun _ => hc1, threeRoundCrashLaws σ hv hw hHon hq hl hineq⟩

omit S in
/-- **A row that tolerates the record's faults** has positive thresholds
and its laws. -/
theorem coveredLaws (h : p.Tolerates honest f q) :
    1 ≤ p.linkSize ∧ 1 ≤ p.commitThreshold ∧ (p.voteIsCert = false → 1 ≤ p.certThreshold) ∧
      (schemeAnchored p σ).Laws := by
  obtain ⟨hl, hc, hcv, hlaws⟩ := coveredLawsOn σ (Hon := honest) h.1 h.2.1 h.2.2
  exact ⟨hl, hc, hcv, laws_of_forall hlaws fun _ U => U.noEquivOn_honest⟩

end Scheme

end LeanDag
