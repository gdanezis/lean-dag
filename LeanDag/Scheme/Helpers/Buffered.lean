import LeanDag.Scheme.Helpers.Transfer
import LeanDag.Scheme.Helpers.Rows
import LeanDag.Scheme.Model.LeastSel
import LeanDag.Scheme.Model.Variants
import LeanDag.MahiMahi.Helpers.Decision
import LeanDag.AsyncBlueBottle.Model.Decision
import LeanDag.DoS.SelfParent
/-!
# The rows with buffer rounds, at the least vote

Any vote-selection rule blames a slot exactly when the voter's history
holds no block of it, and the least vote is Mahi-Mahi's vote, so at the
least vote each row counts the blocks its rule counts:

* **Mahi-Mahi** at wave `w ≥ 3` reads as `mahiMahiAnchored w`; a linked
  candidate is unique by certificate uniqueness, so the scheme's least
  choice is that candidate.
* **Blue Bottle Async** reads as `asyncBlueBottleAnchored`.
* **Cordial Miners Async** reads as `cordialAsyncAnchored 5`: the
  leader's vote-round block holds the leader's own candidate-round block
  in its history, so `n` blames never occur. It has Mahi-Mahi's laws.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
section Core

variable [F : Faults Validator] {U : BlockUniverse Validator BlockId Payload}

/-- Below the voter, the slot's blocks in its history are Mahi-Mahi's
candidates. -/
theorem slotIn_eq_candidatesAt {b : BlockId} {a : Validator} {r : ℕ} (hb : b ∈ U.ids)
    (hr : r < (U.block b).round) : slotIn U b a r = MahiMahi.candidatesAt U b a r := by
  ext x
  simp only [slotIn, show ¬ (U.block b).round ≤ r by omega, if_false, Finset.mem_filter,
    MahiMahi.mem_candidatesAt]
  exact ⟨fun ⟨hx, hc, hxr⟩ => ⟨history_subset_ids hb hx, hxr, hc, hx⟩,
    fun ⟨_, hxr, hc, hx⟩ => ⟨hx, hc, hxr⟩⟩

/-- **The least vote is Mahi-Mahi's vote**, below the voter. -/
theorem leastSel_votes_iff {b L : BlockId} (hb : b ∈ U.ids)
    (hr : (U.block L).round < (U.block b).round) :
    (leastSel (P := ValidWrt) (honest := Correct)).Votes U b L ↔ MahiMahi.Votes U b L := by
  unfold VoteSel.Votes MahiMahi.Votes
  simp only [leastSel]
  rw [slotIn_eq_candidatesAt hb hr]
  set s := MahiMahi.candidatesAt U b (U.block L).creator (U.block L).round
  constructor
  · intro h
    by_cases hs : s.Nonempty
    · rw [dif_pos hs, Option.some.injEq] at h
      exact ⟨h ▸ s.min'_mem hs, fun L' hL' hlt => absurd (h ▸ s.min'_le L' hL') (not_le.mpr hlt)⟩
    · rw [dif_neg hs] at h
      exact absurd h (by simp)
  · intro ⟨hL, hmin⟩
    have hs : s.Nonempty := ⟨L, hL⟩
    rw [dif_pos hs, Option.some.injEq]
    exact le_antisymm (s.min'_le L hL) (s.le_min' hs L fun y hy => not_lt.mp (hmin y hy))

/-- **Any vote-selection rule blames as Mahi-Mahi blames**, below the voter. -/
theorem sel_eq_none_iff_blames (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    {b : BlockId} {a : Validator} {r : ℕ} (hb : b ∈ U.ids) (hr : r < (U.block b).round) :
    σ.sel U b a r = none ↔ MahiMahi.Blames U b a r := by
  rw [MahiMahi.Blames, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    obtain ⟨-, hxr, hxc, hxh⟩ := MahiMahi.mem_candidatesAt.mp hx
    exact σ.complete U b a r hr h x hxh hxc hxr
  · intro h
    cases hs : σ.sel U b a r with
    | none => rfl
    | some x =>
      obtain ⟨hx, hxc, hxr⟩ := σ.sound U b a r x hs
      exact absurd (MahiMahi.mem_candidatesAt.mpr ⟨history_subset_ids hb hx, hxr, hxc, hx⟩)
        (h x)

variable {w : ℕ}

/-- The row's certificates are Mahi-Mahi's. -/
theorem certsAt_mahiMahi (hw : 3 ≤ w) {L : BlockId} {r : ℕ} (hL : (U.block L).round = r) :
    certsAt (Params.mahiMahi w (Fintype.card Validator) F.f) leastSel U L r =
      MahiMahi.certificates U w L r := by
  unfold certsAt MahiMahi.certificates certificatesAt
  simp only [Params.mahiMahi, MahiMahi.decisionRoundAt]
  rw [show r + (w - 1) = r + w - 1 by omega]
  refine Finset.filter_congr fun C hC => ?_
  obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hC
  simp only [IsCert, Bool.false_eq_true, if_false, CarriesVotes, carriedVotes]
  have : (U.block C).refs.filter (fun b => (leastSel (P := ValidWrt) (honest := Correct)).Votes U b L) =
      (U.block C).refs.filter (fun b => MahiMahi.Votes U b L) := by
    refine Finset.filter_congr fun b hb => ?_
    have hbU := U.complete C hCU b hb
    have hbr := Validity.Mechanised.pred U.block (U.block C) (U.valid C hCU) b hb
    exact leastSel_votes_iff hbU (by omega)
  rw [this]

/-- The row's blamers are Mahi-Mahi's. -/
theorem blamersAt_mahiMahi [S : Slots Validator] (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (hw : 3 ≤ w) (k : ℕ) :
    blamersAt (Params.mahiMahi w (Fintype.card Validator) F.f) σ U k =
      (blocksAt U (MahiMahi.votingRound w (S.slotRound k))).filter
        (fun q => MahiMahi.Blames U q (S.leader k) (S.slotRound k)) := by
  unfold blamersAt Params.voteOffset
  simp only [Params.mahiMahi, Bool.false_eq_true, if_false, MahiMahi.votingRound]
  rw [show S.slotRound k + max 1 (w - 2) = S.slotRound k + w - 2 by omega]
  refine Finset.filter_congr fun b hb => ?_
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hb
  exact sel_eq_none_iff_blames σ hbU (by omega)

variable [S : Slots Validator]

/-- The row's link is Mahi-Mahi's. -/
theorem link_mahiMahi (hw : 3 ≤ w) {i k : ℕ} {A L : BlockId} (hL : IsLeaderBlock U k L)
    (hA : A ∈ U.ids) :
    (schemeAnchored (Params.mahiMahi w (Fintype.card Validator) F.f) leastSel).Link i U A L S k ↔
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).Link i U A L S k := by
  show _ ≤ (creatorsOf U.block ((certsAt _ _ U L _).filter _)).card ↔ _
  rw [certsAt_mahiMahi hw hL.2.1]
  exact one_le_card_iff_linkedVia hA _

/-- **The Mahi-Mahi row reads as `mahiMahiAnchored`**, at the least vote. -/
theorem readAlike_mahiMahi (hw : 3 ≤ w) (U : BlockUniverse Validator BlockId Payload) :
    ReadAlike (schemeAnchored (Params.mahiMahi w (Fintype.card Validator) F.f) leastSel)
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload w) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    show HoldsAtLeast U V _ (certsAt _ _ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_mahiMahi hw hL.2.1]
    rfl
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt _ _ U k) ↔ HoldsAtLeast U V _ _
    rw [blamersAt_mahiMahi _ hw k]
    rfl
  link := fun _ hL hA _ => link_mahiMahi hw hL hA.1
  least := fun {i k j A L} _ hL hA _ hl => by
    constructor
    · exact fun _ _ _ _ h => h
    · intro _ L' hL' hl' hlt
      have hc := MahiMahi.certificates_nonempty_of_certifiedIn ((link_mahiMahi hw hL hA.1).mp hl)
      have hc' := MahiMahi.certificates_nonempty_of_certifiedIn
        ((link_mahiMahi (i := i) hw hL' hA.1).mp hl')
      exact lt_irrefl L (MahiMahi.eq_of_hasCertificate (by omega) hL hL' hc hc' ▸ hlt)

/-- **On the core's universe no slot is blamed by every validator**, at a
vote round at or above the slot: the leader's vote-round block holds a
block of the leader at the slot's round. -/
theorem not_holdsAtLeast_card_blames (hw : 3 ≤ w) (U : BlockUniverse Validator BlockId Payload)
    (V : U.View) (k : ℕ) :
    ¬ HoldsAtLeast U V (Fintype.card Validator)
      ((blocksAt U (MahiMahi.votingRound w (S.slotRound k))).filter
        (fun q => MahiMahi.Blames U q (S.leader k) (S.slotRound k))) := by
  intro h
  set s := (blocksAt U (MahiMahi.votingRound w (S.slotRound k))).filter
    (fun q => MahiMahi.Blames U q (S.leader k) (S.slotRound k))
  have huniv : heldAuthors U V s = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)
  obtain ⟨b, hb, -, hbc⟩ := mem_heldAuthors.mp (huniv ▸ Finset.mem_univ (S.leader k))
  obtain ⟨hbs, hbl⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hbs
  obtain ⟨i, hi, hic, hir⟩ := exists_self_ancestor hbU (t := S.slotRound k)
    (by unfold MahiMahi.votingRound at hbr; omega)
  have hmem : i ∈ MahiMahi.candidatesAt U b (S.leader k) (S.slotRound k) :=
    MahiMahi.mem_candidatesAt.mpr ⟨history_subset_ids hbU hi, hir, hic.trans hbc, hi⟩
  rw [MahiMahi.Blames] at hbl
  rw [hbl] at hmem
  simp at hmem

omit S in
/-- **Cordial Miners Async has Mahi-Mahi's laws**, the skip cases being
empty. -/
theorem cordialAsyncLaws (hw : 2 ≤ w) : (cordialAsyncAnchored Validator BlockId Payload w).Laws where
  commit_unique := (MahiMahi.mahiMahiLaws (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) hw).commit_unique
  commit_skip := fun _ _ _ h => h.elim
  commit_link := (MahiMahi.mahiMahiLaws hw).commit_link
  commit_link_unique := (MahiMahi.mahiMahiLaws hw).commit_link_unique
  skip_link := fun _ h _ _ _ => h.elim
  link_unique := (MahiMahi.mahiMahiLaws hw).link_unique
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ _ h => h
  skip_congr := fun _ _ _ _ h => h
  link_congr := (cordialAsyncAnchored Validator BlockId Payload w).linkCongr_of_round
    (fun _ U A L r => MahiMahi.CertifiedIn U w A L r) fun _ _ _ _ _ _ => rfl

/-- **The Cordial Miners Async row reads as `cordialAsyncAnchored 5`**, at
the least vote: its skip threshold `n` is never met on the core's
universe. -/
theorem readAlike_cordialAsync (U : BlockUniverse Validator BlockId Payload) :
    ReadAlike (schemeAnchored (Params.cordialMinersAsync (Fintype.card Validator) F.f) leastSel)
      (cordialAsyncAnchored Validator BlockId Payload 5) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := (readAlike_mahiMahi (w := 5) (by omega) U).commit
  skip := fun V k => by
    change HoldsAtLeast U V _
      (blamersAt (Params.mahiMahi 5 (Fintype.card Validator) F.f) leastSel U k) ↔ False
    rw [blamersAt_mahiMahi _ (by omega) k]
    exact iff_false_intro (not_holdsAtLeast_card_blames (by omega) U V k)
  link := (readAlike_mahiMahi (w := 5) (by omega) U).link
  least := (readAlike_mahiMahi (w := 5) (by omega) U).least

end Core

section AsyncBlueBottle

variable [F : Faults5 Validator] {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

omit S in
/-- The row's certificates are Async BlueBottle's voters. -/
theorem certsAt_blueBottleAsync {L : BlockId} {r : ℕ} (hL : (U.block L).round = r) :
    certsAt (Params.blueBottleAsync (Fintype.card Validator) F.f) leastSel U L r =
      AsyncBlueBottle.voters U L r := by
  unfold certsAt AsyncBlueBottle.voters AsyncBlueBottle.decisionRoundAt
  refine Finset.filter_congr fun C hC => ?_
  obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hC
  simp only [IsCert, Params.blueBottleAsync, if_true]
  exact leastSel_votes_iff hCU (by simp only [Params.blueBottleAsync] at hCr; omega)

/-- The row's link is Async BlueBottle's weak link. -/
theorem link_blueBottleAsync {i k : ℕ} {A L : BlockId} (hL : IsLeaderBlock U k L) :
    (schemeAnchored (Params.blueBottleAsync (Fintype.card Validator) F.f) leastSel).Link
        i U A L S k ↔
      (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).Link i U A L S k := by
  show _ ≤ (creatorsOf U.block ((certsAt _ _ U L _).filter _)).card ↔ _
  rw [certsAt_blueBottleAsync hL.2.1]
  rfl

/-- **The Blue Bottle Async row reads as `asyncBlueBottleAnchored`**, at
the least vote. -/
theorem readAlike_blueBottleAsync (U : BlockUniverse Validator BlockId Payload) :
    ReadAlike (schemeAnchored (Params.blueBottleAsync (Fintype.card Validator) F.f) leastSel)
      (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    show HoldsAtLeast U V _ (certsAt _ _ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_blueBottleAsync hL.2.1]
    rfl
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt _ _ U k) ↔ HoldsAtLeast U V _ _
    unfold blamersAt Params.voteOffset AsyncBlueBottle.blamerBlocks AsyncBlueBottle.decisionRoundAt
    simp only [Params.blueBottleAsync, if_true]
    rw [show 3 - 1 = 2 from rfl]
    have : (blocksAt U (S.slotRound k + 2)).filter
        (fun b => (leastSel (P := ValidWrt) (honest := Correct)).sel U b (S.leader k)
          (S.slotRound k) = none) =
        (blocksAt U (S.slotRound k + 2)).filter
          (fun q => MahiMahi.Blames U q (S.leader k) (S.slotRound k)) := by
      refine Finset.filter_congr fun b hb => ?_
      obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hb
      exact sel_eq_none_iff_blames _ hbU (by omega)
    rw [this]
  link := fun _ hL _ _ => link_blueBottleAsync hL
  least := fun {i k j A L} _ _ _ _ _ =>
    ⟨fun h L' hL' hl' => h L' hL' ((link_blueBottleAsync (i := i) hL').mpr hl'),
      fun h L' hL' hl' => h L' hL' ((link_blueBottleAsync (i := i) hL').mp hl')⟩

end AsyncBlueBottle

end Scheme

end LeanDag
