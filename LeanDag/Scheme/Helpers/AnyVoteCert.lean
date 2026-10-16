import LeanDag.Scheme.Helpers.AnyVote
import LeanDag.Odontoceti.Rules
/-!
# The Blue Bottle Async row at every vote

At `n ≥ 5f + 1` the Blue Bottle Async row has the anchored rule's laws at
every vote-selection rule. As for Async BlueBottle, a correct validator
has one decision-round block, which selects at most one block of a slot
and does not blame a slot it selects in; so the supporters of two twins,
or the supporters and the blamers of a slot, meet only in the Byzantine
set, and the counting of Async BlueBottle goes through.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [F : Faults5 Validator] {U : BlockUniverse Validator BlockId Payload}
variable (σ : VoteSel Validator BlockId Payload ValidWrt Correct)

local notation "bb" => Params.blueBottleAsync (Fintype.card Validator) F.f

theorem mem_certsAt_bb {C L : BlockId} {r : ℕ} :
    C ∈ certsAt bb σ U L r ↔ C ∈ U.ids ∧ (U.block C).round = r + 2 ∧ σ.Votes U C L := by
  simp only [certsAt, IsCert, Params.blueBottleAsync, if_true, Finset.mem_filter, mem_blocksAt]
  tauto

/-- The validators whose decision-round block votes for `L`. -/
abbrev supportersBB (L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block (certsAt bb σ U L r)

/-- The validators whose decision-round vote for `L` lies in `A`'s history. -/
abbrev coneSupportersBB (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block ((certsAt bb σ U L r).filter (fun C => C ∈ history U A))

theorem coneSupportersBB_subset {A L : BlockId} {r : ℕ} :
    coneSupportersBB (U := U) σ A L r ⊆ supportersBB (U := U) σ L r :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- **The supporters of two twins number at most `n + f`.** -/
theorem card_supportersBB_add_le {L₁ L₂ : BlockId} {r : ℕ} (hd : L₁ ≠ L₂)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) :
    (supportersBB (U := U) σ L₁ r).card + (supportersBB (U := U) σ L₂ r).card ≤
      Fintype.card Validator + F.f :=
  card_add_card_le_of_inter_subset F.card_byzantine fun v hv => by
    obtain ⟨h₁, h₂⟩ := Finset.mem_inter.mp hv
    obtain ⟨q₁, hq₁, hc₁⟩ := mem_creatorsOf.mp h₁
    obtain ⟨q₂, hq₂, hc₂⟩ := mem_creatorsOf.mp h₂
    obtain ⟨hq₁U, hq₁r, hv₁⟩ := (mem_certsAt_bb σ).mp hq₁
    obtain ⟨hq₂U, hq₂r, hv₂⟩ := (mem_certsAt_bb σ).mp hq₂
    by_contra hbad
    have hcor : v ∈ (Correct : Finset Validator) := mem_correct.mpr hbad
    have := U.eq_of_creator_eq hq₁U hq₂U hcor hc₁ hc₂ (by rw [hq₁r, hq₂r])
    subst this
    exact hd (σ.eq_of_votes hv₁ hv₂ hc hr)

variable [S : Slots Validator]

omit S in
theorem voteOffset_bb : (bb).voteOffset = 2 := rfl

/-- **The supporters and the blamers of a slot number at most `n + f`.** -/
theorem card_supportersBB_add_blamers_le {L : BlockId} {k : ℕ} (hL : IsLeaderBlock U k L) :
    (supportersBB (U := U) σ L (S.slotRound k)).card +
        (creatorsOf U.block (blamersAt bb σ U k)).card ≤ Fintype.card Validator + F.f :=
  card_add_card_le_of_inter_subset F.card_byzantine fun v hv => by
    obtain ⟨h₁, h₂⟩ := Finset.mem_inter.mp hv
    obtain ⟨q₁, hq₁, hc₁⟩ := mem_creatorsOf.mp h₁
    obtain ⟨q₂, hq₂, hc₂⟩ := mem_creatorsOf.mp h₂
    obtain ⟨hq₁U, hq₁r, hv₁⟩ := (mem_certsAt_bb σ).mp hq₁
    obtain ⟨hq₂s, hnone⟩ := Finset.mem_filter.mp hq₂
    obtain ⟨hq₂U, hq₂r⟩ := mem_blocksAt.mp hq₂s
    by_contra hbad
    have hcor : v ∈ (Correct : Finset Validator) := mem_correct.mpr hbad
    have := U.eq_of_creator_eq hq₁U hq₂U hcor hc₁ hc₂ (by rw [hq₁r, hq₂r, voteOffset_bb])
    subst this
    unfold VoteSel.Votes at hv₁
    rw [hL.2.2, hL.2.1, hnone] at hv₁
    exact absurd hv₁ (by simp)

omit S in
/-- **A direct commit passes the weak test at every block three rounds
up**: one hop by quorum intersection less the Byzantine authors, further
by the nesting of histories. -/
theorem weakLink_bb {L : BlockId} {r : ℕ}
    (h : Fintype.card Validator - F.f ≤ (supportersBB (U := U) σ L r).card) :
    ∀ d, ∀ A, A ∈ U.ids → (U.block A).round = r + 3 + d →
      Fintype.card Validator - 3 * F.f ≤ (coneSupportersBB (U := U) σ A L r).card := by
  intro d
  induction d with
  | zero =>
      intro A hA hround
      have hq : quorumCard Validator ≤ (creatorsOf U.block (U.block A).refs).card :=
        U.creators_quorum hA (by omega)
      have hsub : (creatorsOf U.block (U.block A).refs ∩ supportersBB (U := U) σ L r) ∩
          (Correct : Finset Validator) ⊆ coneSupportersBB (U := U) σ A L r := by
        intro v hv
        obtain ⟨hvPS, hvC⟩ := Finset.mem_inter.mp hv
        obtain ⟨hvP, hvS⟩ := Finset.mem_inter.mp hvPS
        obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hvP
        obtain ⟨q, hq, hqc⟩ := mem_creatorsOf.mp hvS
        obtain ⟨hq_ids, hq_round, hqv⟩ := (mem_certsAt_bb σ).mp hq
        have hp_ids : p ∈ U.ids := U.complete A hA p hp
        have hp_round : (U.block p).round = r + 2 := by
          have := U.round_of_mem_refs hA hp
          omega
        have hpq : p = q := U.eq_of_creator_eq hp_ids hq_ids hvC hpc hqc (by omega)
        subst hpq
        exact mem_creatorsOf.mpr ⟨p, Finset.mem_filter.mpr ⟨hq, mem_history_of_mem_refs hA hp⟩,
          hpc⟩
      have h1 := Finset.card_union_add_card_inter
        (creatorsOf U.block (U.block A).refs) (supportersBB (U := U) σ L r)
      have h2 := Finset.card_le_univ
        (creatorsOf U.block (U.block A).refs ∪ supportersBB (U := U) σ L r)
      have h3 := card_le_card_inter_correct_add_byzantine
        (creatorsOf U.block (U.block A).refs ∩ supportersBB (U := U) σ L r)
      have h4 := Finset.card_le_card hsub
      have h5 := F.card_byzantine
      omega
  | succ d ih =>
      intro A hA hround
      obtain ⟨p, hp⟩ := U.refs_nonempty hA (by omega)
      have hp_ids : p ∈ U.ids := U.complete A hA p hp
      have hp_round : (U.block p).round = r + 3 + d := by
        have := U.round_of_mem_refs hA hp
        omega
      refine le_trans (ih p hp_ids hp_round)
        (Finset.card_le_card (Finset.image_subset_image fun C hC => ?_))
      rw [Finset.mem_filter] at hC ⊢
      exact ⟨hC.1, history_subset_of_reaches hA (Reaches.single hp) hC.2⟩

omit S in
/-- **A direct commit excludes every twin passing the weak test**: `n − f`
and `n − 3f` supporters overlap in a correct author at `n ≥ 5f + 1`. -/
theorem eq_of_commit_of_weakLink_bb {L₁ L₂ A : BlockId} {r : ℕ}
    (h₁ : Fintype.card Validator - F.f ≤ (supportersBB (U := U) σ L₁ r).card)
    (ht : Fintype.card Validator - 3 * F.f ≤ (coneSupportersBB (U := U) σ A L₂ r).card)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  by_contra hne
  have := card_supportersBB_add_le σ (r := r) hne hc hr
  have h2 := Finset.card_le_card (coneSupportersBB_subset σ (U := U) (A := A) (L := L₂) (r := r))
  have h5 := F.card_validators5
  omega

omit S in
/-- **The Blue Bottle Async row has the anchored laws at every vote.** -/
theorem blueBottleAsyncLaws : (schemeAnchored bb σ).Laws where
  commit_unique := fun {S U V₁ V₂ k L₁ L₂} _ hL₁ hL₂ h₁ h₂ => by
    by_contra hne
    have := card_supportersBB_add_le σ (U := U) (r := S.slotRound k) hne
      (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])
    have h₁' : Fintype.card Validator - F.f ≤
        (supportersBB (U := U) σ L₁ (S.slotRound k)).card := h₁.le
    have h₂' : Fintype.card Validator - F.f ≤
        (supportersBB (U := U) σ L₂ (S.slotRound k)).card := h₂.le
    have := F.card_validators
    omega
  commit_skip := fun {S U V₁ V₂ k L} _ hL h hs => by
    have := card_supportersBB_add_blamers_le σ hL
    have h' : Fintype.card Validator - F.f ≤
        (supportersBB (U := U) σ L (S.slotRound k)).card := h.le
    have hs' : Fintype.card Validator - F.f ≤
        (creatorsOf U.block (blamersAt bb σ U k)).card := hs.le
    have := F.card_validators
    omega
  commit_link := fun {S U V k j L A} _ _ h hA _ helig => by
    have hround := (schemeAnchored bb σ).anchor_round_le hA helig
    simp only [schemeAnchored, Params.blueBottleAsync] at hround
    refine ⟨0, Nat.one_pos, ?_⟩
    exact weakLink_bb σ h.le _ A hA.1 (by omega : (U.block A).round = _ + 3 + ((U.block A).round
      - (S.slotRound k + 3)))
  commit_link_unique := fun {S U V k j i L₁ L₂ A} _ hL₁ hL₂ h _ _ _ _ _ hlink _ =>
    eq_of_commit_of_weakLink_bb σ h.le hlink (by rw [hL₁.2.2, hL₂.2.2])
      (by rw [hL₁.2.1, hL₂.2.1])
  skip_link := fun {S U V k i L A} _ hs hL _ _ hlink => by
    have := card_supportersBB_add_blamers_le σ hL
    have hs' : Fintype.card Validator - F.f ≤
        (creatorsOf U.block (blamersAt bb σ U k)).card := hs.le
    have h2 := Finset.card_le_card (coneSupportersBB_subset σ (U := U) (A := A) (L := L)
      (r := S.slotRound k))
    have := F.card_validators5
    have hl : Fintype.card Validator - 3 * F.f ≤
        (coneSupportersBB (U := U) σ A L (S.slotRound k)).card := hlink
    omega
  link_unique := fun {S U k j i L₁ L₂ A} _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ hm₁ hm₂ =>
    le_antisymm (not_lt.mp (hm₁ L₂ hL₂ hl₂)) (not_lt.mp (hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun {S₁ S₂ U V k} _ hround hk _ h => by
    change HoldsAtLeast U V _ (blamersAt (S := S₁) bb σ U k) at h
    show HoldsAtLeast U V _ (blamersAt (S := S₂) bb σ U k)
    unfold blamersAt at h ⊢
    rw [← hround, ← hk]
    exact h
  link_congr := (schemeAnchored bb σ).linkCongr_of_round
    (fun _ U A L r => (bb).linkSize ≤ (creatorsOf U.block ((certsAt bb σ U L r).filter
      (fun C => C ∈ history U A))).card) fun _ _ _ _ _ _ => rfl

end Scheme

end LeanDag
