import LeanDag.AsyncBlueBottle.Carrier
import LeanDag.AsyncBlueBottle.Helpers.Counting
import LeanDag.MahiMahi.Properties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.FromBand
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# Async BlueBottle's band, and the two liveness properties

The one transport the cone vote needs is Mahi-Mahi's: `candidatesAt`
agrees across a shifted universe, so `Votes` and `Blames` do
(`MahiMahiProperties.votes_band`, `blames_band`), and the band is read
through the same `ids` and `block` fields. What is this arc's own is the
in-cone voter set of the weak test, whose transport is Odontoceti's
`coneSupporters_band` with the reference replaced by the vote.
-/

namespace LeanDag

namespace AsyncBlueBottleProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U U' : BlockUniverse Validator BlockId Payload} {lo hi g g' : ℕ}

/-! ## The band, across a shifted universe -/

/-- A band of this carrier is a band of Mahi-Mahi's: both read the
record's `ids` and `block`. -/
theorem agreeBand_mm
    (h : AgreeBand (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule
      U U' lo hi g g') :
    AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload 3).toDagRule U U' lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **The voters for a candidate are the voters they were**: each reads a
cone the band settles. -/
theorem voters_band
    (h : AgreeBand (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule
      U U' lo hi g g')
    {L : BlockId} (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g)
    (hLhi : (U.block L).round + g ≤ hi) {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + 2 + g ≤ hi) :
    AsyncBlueBottle.voters U L r ⊆ AsyncBlueBottle.voters U' L r' := by
  intro q hq
  obtain ⟨hqU, hqr, hqv⟩ := AsyncBlueBottle.mem_voters.mp hq
  have hb := AnchoredRule.band_block h hqU (by omega) (by omega)
  exact AsyncBlueBottle.mem_voters.mpr ⟨AnchoredRule.band_mem h hqU (by omega) (by omega),
    by omega, (MahiMahiProperties.votes_band (agreeBand_mm h) hqU (by omega) (by omega)
      hL hLlo hLhi).mpr hqv⟩

/-- **And so does the direct commit.** -/
theorem directCommitIn_band
    (h : AgreeBand (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule
      U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ}
    (hLr : (U.block L).round = r) (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + 2 + g ≤ hi) (hc : AsyncBlueBottle.DirectCommitIn U V L r) :
    AsyncBlueBottle.DirectCommitIn U' V' L r' :=
  AnchoredRule.holdsAtLeast_band h hV
    (fun q hq => by
      obtain ⟨hqU, hqr⟩ := AsyncBlueBottle.voters_spec hq
      exact ⟨hqU, by omega, by omega⟩)
    (voters_band h hL (by omega) (by omega) hrr hr hhi) hc

/-- **And the direct skip.** A blamer stays a blamer, and a candidate
the band added changes nothing: the blame reads the blamer's cone, which
the band settles both ways. -/
theorem directSkipIn_band
    (h : AgreeBand (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule
      U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {a : Validator} {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + 2 + g ≤ hi) (hs : AsyncBlueBottle.DirectSkipIn U V a r) :
    AsyncBlueBottle.DirectSkipIn U' V' a r' := by
  refine le_trans hs (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqU, hqr, hqb⟩ := AsyncBlueBottle.mem_blamerBlocks.mp hqf
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨AsyncBlueBottle.mem_blamerBlocks.mpr
    ⟨AnchoredRule.band_mem h hqU (by omega) (by omega), ?_, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · have := AnchoredRule.band_block h hqU (by omega) (by omega); omega
  · exact (MahiMahiProperties.blames_band (agreeBand_mm h) hqU (by omega) (by omega)
      hrr hr (by omega)).mpr hqb
  · rw [(AnchoredRule.band_block h hqU (by omega) (by omega)).2]; exact hqv

/-! ## The anchored test

Both directions, and the clause a one-directional band forces: a
candidate the band did not carry has no voter in an old anchor's cone,
because a voter for it would hold it in its own cone, and an old cone
holds only old blocks. -/

/-- **The anchor's cone of voters is the cone it was.** -/
theorem coneSupporters_band
    (h : AgreeBand (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule
      U U' lo hi g g')
    {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g)
    (hLhi : (U.block L).round + g ≤ hi) {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + 2 + g ≤ hi) :
    AsyncBlueBottle.coneSupporters U' A L r' = AsyncBlueBottle.coneSupporters U A L r := by
  have hA' : A ∈ U'.ids := AnchoredRule.band_mem h hA hAlo hAhi
  have hset : (AsyncBlueBottle.voters U' L r').filter (fun q => q ∈ history U' A) =
      (AsyncBlueBottle.voters U L r).filter (fun q => q ∈ history U A) := by
    ext q
    simp only [Finset.mem_filter, AsyncBlueBottle.mem_voters]
    constructor
    · rintro ⟨⟨hqU', hqr', hqv⟩, hqh⟩
      have hqre : ReachesFrom U'.block A q := (mem_history_iff (U := U') hA').mp hqh
      obtain ⟨hqU, hqreU, hqeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hqre
        (by change lo ≤ (U'.block q).round + g'; omega)
      have hqeq' : (U.block q).round + g = (U'.block q).round + g' := hqeq
      exact ⟨⟨hqU, by omega, (MahiMahiProperties.votes_band (agreeBand_mm h) hqU (by omega)
        (by omega) hL hLlo hLhi).mp hqv⟩, (mem_history_iff (U := U) hA).mpr hqreU⟩
    · rintro ⟨⟨hqU, hqr, hqv⟩, hqh⟩
      have hqre : ReachesFrom U.block A q := (mem_history_iff (U := U) hA).mp hqh
      have hb := AnchoredRule.band_block h hqU (by omega) (by omega)
      exact ⟨⟨AnchoredRule.band_mem h hqU (by omega) (by omega), by omega,
        (MahiMahiProperties.votes_band (agreeBand_mm h) hqU (by omega) (by omega)
          hL hLlo hLhi).mpr hqv⟩,
        (mem_history_iff (U := U') hA').mpr (AgreeBand.reaches_of h hA hAhi hqre
          (by change lo ≤ (U.block q).round + g; omega))⟩
  unfold AsyncBlueBottle.coneSupporters
  rw [hset]
  refine AnchoredRule.creatorsOf_band h fun b hb => ?_
  obtain ⟨hbU, hbr, -⟩ := AsyncBlueBottle.mem_voters.mp (Finset.mem_filter.mp hb).1
  exact ⟨hbU, by omega, by omega⟩

/-- The weak threshold is positive: `Faults5` asks for `5f + 1`
validators, so `n − 3f ≥ 2f + 1`. -/
theorem weakLink_threshold_pos : 0 < Fintype.card Validator - 3 * F.f := by
  have := F.card_validators5
  omega

/-- **A candidate the band did not carry has no voter in an old anchor's
cone**: the voter is old, so its cone is, and a candidate in it is old. -/
theorem not_weakLink_band_novel
    (h : AgreeBand (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule
      U U' lo hi g g')
    {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    {L : BlockId} (hLo : L ∉ U.ids) {r r' : ℕ} (hLr : (U'.block L).round = r')
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 2 + g ≤ hi) :
    ¬ AsyncBlueBottle.WeakLink U' A L r' := by
  intro ht
  unfold AsyncBlueBottle.WeakLink at ht
  have hpos : 0 < (AsyncBlueBottle.coneSupporters U' A L r').card :=
    lt_of_lt_of_le weakLink_threshold_pos ht
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  obtain ⟨q, hqU', hqr', hqv, hqh, -⟩ := AsyncBlueBottle.mem_coneSupporters.mp hv
  have hA' : A ∈ U'.ids := AnchoredRule.band_mem h hA hAlo hAhi
  -- the voter is old
  obtain ⟨hqU, -, hqeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi
    ((mem_history_iff (U := U') hA').mp hqh) (by change lo ≤ (U'.block q).round + g'; omega)
  have hqeq' : (U.block q).round + g = (U'.block q).round + g' := hqeq
  -- so is what its cone holds
  obtain ⟨hLU, -, -⟩ := AgreeBand.reaches_old h hqU
    (by change lo ≤ (U.block q).round + g; omega)
    (by change (U.block q).round + g ≤ hi; omega)
    ((mem_history_iff (U := U') hqU').mp hqv.mem_history)
    (by change lo ≤ (U'.block L).round + g'; omega)
  exact hLo hLU

/-- **What Async BlueBottle owes the band**: its direct commit, its slot
blame and the weak link carry across a band covering the slot's wave,
and a candidate the band did not carry is linked from no old anchor. -/
theorem asyncBlueBottleBandLaws :
    (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).BandLaws where
  commit_band := fun h hkk _ _ hlo hhi hV hL hc =>
    directCommitIn_band h hV hL.1 hL.2.1 hkk (by omega)
      (by simp only [AsyncBlueBottle.asyncBlueBottleAnchored_waveAt] at hhi; omega) hc
  skip_band := fun h hkk hlk _ hlo hhi hV hs => by
    change AsyncBlueBottle.DirectSkipIn _ _ _ _
    rw [← hlk]
    exact directSkipIn_band h hV hkk (by omega)
      (by simp only [AsyncBlueBottle.asyncBlueBottleAnchored_waveAt] at hhi; omega) hs
  link_band := fun h hA hAlo hAhi hkk _ _ hlo hhi _ hL => by
    simp only [AsyncBlueBottle.asyncBlueBottleAnchored_waveAt] at hhi
    change AsyncBlueBottle.WeakLink _ _ _ _ ↔ AsyncBlueBottle.WeakLink _ _ _ _
    unfold AsyncBlueBottle.WeakLink
    rw [coneSupporters_band h hA hAlo hAhi hL.1 (by rw [hL.2.1]; exact hlo)
      (by rw [hL.2.1]; omega) hkk hlo (by omega)]
  link_novel := fun h hA _ hAlo hAhi hkk _ _ hlo hhi _ hL hLo => by
    simp only [AsyncBlueBottle.asyncBlueBottleAnchored_waveAt] at hhi
    exact not_weakLink_band_novel h hA hAlo hAhi hLo hL.2.1 hkk hlo (by omega)

/-- **Async BlueBottle reads a band.** -/
theorem banded : Banded (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.banded asyncBlueBottleBandLaws fun _ _ => trivial

/-! ## The two liveness properties

`Descends` follows from `Indirect` by the generic induction of
`Properties/Derived/Descent.lean`. As in the Mahi-Mahi arc, the
precondition is the direct commit itself: `good U k` is a fact about the
DAG, and what `LeaderCommits` adds is that the verdict survives any
reassignment of the leaders of other slots. -/

/-- **Async BlueBottle's support**: certifiers at the decision round,
certification the cone vote. -/
def abbSupport : Support (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  waveAt := fun _ => 2
  Certifies := fun U C L => MahiMahi.Votes U C L

/-- **Law 1**: `votes_band` at the band a `RebasedAbove` is. -/
theorem abbSupport_local :
    Support.Local (R := asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) abbSupport := by
  intro U U' G R₀ h c L _ hc hcr hL hLr
  change R₀ + 2 ≤ (BlockRecord.block U c).round at hcr
  change (BlockRecord.block U L).round + 2 = (BlockRecord.block U c).round at hLr
  exact MahiMahiProperties.votes_band
    (agreeBand_mm (agreeBand_of_rebasedAbove h (BlockRecord.block U c).round R₀ le_rfl))
    hc (by omega) (by omega) hL (by omega) (by omega)

/-- **Law 2**: every block at the decision round reaches the candidate —
coverage toward it at the first layer, quorum intersection after — and
reaching a correct candidate is voting for it. -/
theorem abbSupport_ofCoverage :
    Timed.OfCoverage (R := asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) abbSupport (coreReliability Validator) := by
  intro U T hq r _ L hpop hct hL hLr hLc C hC hCc hCr
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  have hT : T ⊆ (Correct : Finset Validator) := hq.1
  have hLr' : (BlockRecord.block U L).round = r := hLr
  have hLc' : (BlockRecord.block U L).creator ∈ T := hLc
  have hCr' : (BlockRecord.block U C).round = r + 2 := hCr
  have hvotes : ∀ q ∈ BlockRecord.ids U, (BlockRecord.block U q).round = r + 1 →
      (BlockRecord.block U q).creator ∈ T → L ∈ (BlockRecord.block U q).refs := by
    intro q hq hqr hqc
    exact hct r le_rfl (by change r < r + 2; omega) q hq hqc hqr L hL hLc' hLr'
      Relation.ReflTransGen.refl
  have hreach := MahiMahi.reaches_of_votes hT hcard
    (hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega)) hL hLr' hLc' hvotes
  change MahiMahi.Votes U C L
  exact MahiMahi.votes_of_reaches hC hL (hT hLc') (hreach C hC (by omega))

/-- **Law 3**: a quorum's votes at the decision round are the direct
commit, which a view caught up to that round sees. -/
theorem abbSupport_commits :
    Support.Commits (R := asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) abbSupport (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : Slots Validator := S
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hLr' : (BlockRecord.block U L).round = S.slotRound k := hLr
  have hLc' : (BlockRecord.block U L).creator = S.leader k := hLc
  have hdc : AsyncBlueBottle.DirectCommit U L (S.slotRound k) := by
    unfold AsyncBlueBottle.DirectCommit AsyncBlueBottle.supporters
    refine le_trans hcard (Finset.card_le_card ?_)
    intro v hv
    obtain ⟨C, hC, hCc, hCr⟩ := hpop (S.slotRound k + 2) (by omega) le_rfl v hv
    rw [mem_creatorsOf]
    exact ⟨C, AsyncBlueBottle.mem_voters.mpr ⟨hC, hCr, hcert L ⟨hLmem, hLr, hLc⟩ v hv C hC hCc hCr⟩,
      hCc⟩
  have hin : AsyncBlueBottle.DirectCommitIn U V L (S.slotRound k) :=
    AsyncBlueBottle.directCommitIn_of_coversUpto hdc hcov
  refine ⟨L, by omega, AsyncBlueBottle.Decided.directCommit ⟨hLmem, hLr', hLc'⟩ hin, ?_⟩
  intro S' hround hlead' _
  refine AsyncBlueBottle.Decided.directCommit (S := S') ⟨hLmem, ?_, ?_⟩ ?_
  · rw [hround]; exact hLr'
  · rw [hlead' k (by omega)]; exact hLc'
  · change AsyncBlueBottle.DirectCommitIn U V L (S'.slotRound k)
    rw [hround]; exact hin

open Classical in
/-- **The indirect property**: the relation's, at the wave's gap of three
rounds, the tie broken by the order. -/
theorem indirect :
    Indirect (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S i j => S.slotRound i + 3 ≤ S.slotRound j) :=
  (AnchoredRule.indirect AsyncBlueBottle.asyncBlueBottleLaws.link_congr
    fun hi h => AsyncBlueBottle.exists_least hi h).congr
    (fun _ _ _ => by simp only [AsyncBlueBottle.asyncBlueBottleAnchored_waveAt])

/-- **Async BlueBottle has the descent laws** at the core fault model's
slack, at its three-round wave. -/
theorem descent :
    Properties.Descent (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))
      (Timed.Good (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)) (coreReliability Validator))
      3 (coreReliability Validator).slack :=
  Timed.descent_of_support _ _ _ abbSupport abbSupport_ofCoverage abbSupport_commits indirect
    (fun _ => Nat.le_succ 2) fun _ _ _ h => h

/-! ## The headlines -/

theorem safety : Properties.Safe (asyncBlueBottleRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

theorem liveness : Properties.Support.Lives (abbSupport (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload)) (coreReliability Validator) :=
  Properties.Support.liveness abbSupport_commits commitsCandidate selfParent noEquiv

end AsyncBlueBottleProperties

end LeanDag
