import LeanDag.Bluestreak.Liveness
import LeanDag.Common.Anchored.Band
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Support
/-!
# Bluestreak as a carrier

The universes are the disciplined records — both clauses of
`Disciplined` read the record alone, so the subtype is a carrier and
the laws hold at every schedule. What the arc shows: agreement, that a
commit names the slot's candidate, that a direct commit is a verdict,
the indirect rule, and a support whose certifier is a claim.

Two of the optional properties are **not** shown, and neither is an
omission. `Quorate` asks that every block reference a quorum, which is
what a sparse DAG is designed not to do, so chain quality does not
apply to it. And the record cells of `Properties/Arcs/Record.lean` need
the invariant to survive the cut, which it does not: the cut drops the
blocks a retained claim names, and with them the votes that back it
(`LeanDagTest/Bluestreak/Model.lean`).
-/

namespace LeanDag

namespace BluestreakProperties

open LeanDag.Properties LeanDag.Bluestreak

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} [ClaimMap BlockId]

/-- **Bluestreak as a carrier**: the disciplined records as universes. -/
def bluestreakRule : DagRule Validator BlockId Payload :=
  (bluestreakAnchored Validator BlockId Payload).toDagRuleOn Disciplined

@[simp] theorem bluestreakRule_ids (U : {U : Universe Validator BlockId Payload // Disciplined U}) :
    (bluestreakRule (Payload := Payload)).ids U = U.val.ids := rfl

@[simp] theorem bluestreakRule_block
    (U : {U : Universe Validator BlockId Payload // Disciplined U}) :
    (bluestreakRule (Payload := Payload)).block U = U.val.block := rfl

@[simp] theorem bluestreakRule_viewIds
    {U : {U : Universe Validator BlockId Payload // Disciplined U}} (V : U.val.View) :
    (bluestreakRule (Payload := Payload)).viewIds V = V.ids := rfl

/-- **Two views decide alike.** The laws at the subtype: the invariant
is a predicate on the record, so it holds at every schedule the carrier
is read under. -/
theorem agree : Agree (bluestreakRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.agreeOn bluestreakLaws fun _ _ h => h

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate : CommitsCandidate
    (bluestreakRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.commitsCandidateOn

/-- **A direct commit is a verdict**, at Bluestreak's own claim count. -/
theorem commitsDirect : CommitsDirect
    (bluestreakRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {U} V L _ _ => DirectCommitIn U.val V L) :=
  AnchoredRule.commitsDirectOn

/-- **The indirect rule.** One rung with no tie, so the choice at a
nonempty rung is any linked candidate. -/
theorem indirect : Indirect
    (bluestreakRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun S i j => S.slotRound i + 2 + 1 ≤ S.slotRound j) :=
  AnchoredRule.indirectOn bluestreakLaws.link_congr
    (fun _ ⟨L, hL, hl⟩ => ⟨L, hL, hl, AnchoredRule.least_of_no_tie fun _ _ h => h⟩)

/-- **Bluestreak's fault model, as a counting parameter.** -/
def bluestreakReliability (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [G : Faults Validator] : LeanDag.Reliability Validator where
  correct := (Correct : Finset Validator)
  slack := G.f
  covers := card_compl_correct_le
  minority := by have := G.card_validators; omega

/-- **One block per author per round**, for the correct validators: the
record's own clause. -/
theorem noEquiv : NoEquiv (bluestreakRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (bluestreakReliability Validator) := by
  intro U b c hb hc hcor heq hr
  exact U.val.no_equivocation b hb c hc hcor heq hr

/-- **Every non-genesis block references a block of its own author**:
the self-parent clause of Bluestreak's validity, which is what the
sparse chain is. -/
theorem selfParent : SelfParent (bluestreakRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun U b hb hr => (U.val.valid b hb).clause.2 hr

/-! ## The support: a claim is the certificate -/

/-- **Bluestreak's support**: certifiers sit two rounds above the
candidate, and to certify is to claim. -/
def bluestreakSupport : Support (bluestreakRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  waveAt := fun _ => 2
  Certifies := fun U C L => Claims U.val C L

/-- **Certification commits.** A quorum of claimers at the decision
round of a `T`-led slot, on a view caught up to it, is a verdict —
`Bluestreak.decided_of_leader_mem` under the property's name, bounded
one slot above. -/
theorem commits : (bluestreakSupport (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)).Commits (R := bluestreakRule) (bluestreakReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hw : (bluestreakSupport (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).waveAt (S.kind k) = 2 := rfl
  rw [hw] at hpop hcov
  obtain ⟨L, hLm, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U.val k L := ⟨hLm, hLr, hLc⟩
  have hclaims : ClaimsAt U.val T (S.slotRound k) L :=
    fun v hv c hc hcc hcr => hcert L hL v hv c hc hcc hcr
  have hdec : Decided U.val V k (some L) :=
    Decided.directCommit hL
      (directCommitIn_of_claimsAt (by exact hq.2) hL (hpop _ (by omega) le_rfl) hclaims
        (by exact hcov))
  exact ⟨L, Nat.lt_succ_self k, hdec, fun S' hround hlead' hkind => by
    have hround' : S'.slotRound k = S.slotRound k := congrFun hround k
    have hL' : IsLeaderBlock (S := S') U.val k L :=
      ⟨hLm, by rw [hround']; exact hLr, by rw [hlead' k (Nat.lt_succ_self k)]; exact hLc⟩
    refine Decided.directCommit (S := S') hL' ?_
    exact directCommitIn_of_claimsAt (S := S') (by exact hq.2) hL'
      (by rw [hround']; exact hpop _ (by omega) le_rfl)
      (by rw [hround']; exact hclaims) (by rw [hround']; exact hcov)⟩

/-- **Certification is local.** A claim reads the claiming block and its
references, both of which a band at or above the settling round
carries. -/
theorem supportLocal : (bluestreakSupport (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)).Local (R := bluestreakRule) := by
  intro U U' G R₀ hre C L κ hC hCr hL hLr
  have hw : (bluestreakSupport (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).waveAt κ = 2 := rfl
  rw [hw] at hCr hLr
  simp only [bluestreakRule_block] at hCr hLr
  have hab := agreeBand_of_rebasedAbove hre ((U.val.block C).round) R₀ le_rfl
  have hband : AgreeBand (bluestreakAnchored Validator BlockId Payload).toDagRule
      U.val U'.val R₀ ((U.val.block C).round) 0 G := ⟨hab.mem, hab.block, hab.refs⟩
  have hCb : R₀ < (U.val.block C).round + 0 := by simp only [Nat.add_zero]; omega
  have hvote := AnchoredRule.isVote_band_at hband (L := L) (n := (U.val.block C).round)
    (by omega) le_rfl C hC rfl
  have hcv := AnchoredRule.carriesVotes_band hband (t := quorumCard Validator) hC hCb le_rfl hvote
  exact ⟨fun h => h.imp id hcv.mp, fun h => h.imp id hcv.mpr⟩

/-! ## The band

A claim is read at the claiming block and its references, both two
rounds above the candidate and so inside any band a verdict reads. The
novelty clause is where Bluestreak differs from every rule before it: a
claim *names* its candidate rather than referencing it, so an old block
may carry a claim for a block only the wider universe holds, and what
rules that out is not the band but the anchor — a certified anchor's
cone carries only backed claims, and a backed claim's candidate has a
quorum of voters, which the band's old blocks would have to be. -/

variable {U U' : Universe Validator BlockId Payload} {lo hi g g' : ℕ}

/-- A claimer of `L` sits two rounds above it. -/
theorem mem_claimers_round {L C : BlockId} (hC : C ∈ claimers U L) :
    C ∈ U.ids ∧ (U.block C).round = (U.block L).round + 2 :=
  mem_blocksAt.mp (Finset.mem_filter.mp hC).1

/-- **The claimers of an in-band candidate transport.** The claim field
is the same map, and the votes a claiming block carries are the votes it
carried. -/
theorem claimers_band
    (h : AgreeBand (bluestreakAnchored Validator BlockId Payload).toDagRule U U' lo hi g g')
    {L : BlockId} (hL : L ∈ U.ids) (hlo : lo ≤ (U.block L).round + g)
    (hhi : (U.block L).round + 2 + g ≤ hi) : claimers U L ⊆ claimers U' L := by
  intro C hC
  obtain ⟨hCU, hCr⟩ := mem_claimers_round hC
  have hLr := (AnchoredRule.band_block h hL hlo (by omega)).1
  refine Finset.mem_filter.mpr ⟨mem_blocksAt.mpr
    ⟨AnchoredRule.band_mem h hCU (by omega) (by omega), ?_⟩, ?_⟩
  · have := (AnchoredRule.band_block h hCU (by omega) (by omega)).1
    omega
  · rcases (Finset.mem_filter.mp hC).2 with hcl | hcl
    · exact Or.inl hcl
    · exact Or.inr ((AnchoredRule.carriesVotes_band h hCU (by omega) (by omega)
        (AnchoredRule.isVote_band_at h (n := (U.block C).round) (by omega) (by omega)
          C hCU rfl)).mpr hcl)

/-- And back, for a claimer the anchor's cone reaches, whose round the
band has already placed. -/
theorem mem_claimers_of_band
    (h : AgreeBand (bluestreakAnchored Validator BlockId Payload).toDagRule U U' lo hi g g')
    {L C : BlockId} (hL : L ∈ U.ids) (hCU : C ∈ U.ids) (hlo : lo ≤ (U.block L).round + g)
    (hhi : (U.block L).round + 2 + g ≤ hi)
    (hCeq : (U.block C).round + g = (U'.block C).round + g')
    (hC : C ∈ claimers U' L) : C ∈ claimers U L := by
  obtain ⟨-, hCr'⟩ := mem_claimers_round hC
  have hLr := (AnchoredRule.band_block h hL hlo (by omega)).1
  have hCr : (U.block C).round = (U.block L).round + 2 := by omega
  refine Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hCU, hCr⟩, ?_⟩
  rcases (Finset.mem_filter.mp hC).2 with hcl | hcl
  · exact Or.inl hcl
  · exact Or.inr ((AnchoredRule.carriesVotes_band h hCU (by omega) (by omega)
      (AnchoredRule.isVote_band_at h (n := (U.block C).round) (by omega) (by omega)
        C hCU rfl)).mp hcl)

/-- **A candidate the band did not carry is claimed from no certified
anchor.** The anchor's cone reaches only old blocks in the band, and a
claim one of them carries is backed — the candidate is certified, so
`n − f` validators reference it one round up, which no old block does. -/
theorem not_claimedIn_novel
    (h : AgreeBand (bluestreakAnchored Validator BlockId Payload).toDagRule U U' lo hi g g')
    {A L : BlockId} (hA : A ∈ U.ids) (hanc : Backed U A)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hLnov : L ∉ U.ids) (hLlo : lo ≤ (U'.block L).round + g')
    (hLhi : (U'.block L).round + 2 + g' ≤ hi) : ¬ ClaimedIn U' A L := by
  rintro ⟨C, hC, hre⟩
  obtain ⟨-, hCr'⟩ := mem_claimers_round hC
  have hCrR : ((bluestreakAnchored Validator BlockId Payload).toDagRule.block U' C).round
      = (U'.block L).round + 2 := hCr'
  obtain ⟨hCU, hreU, hCeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
  have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
  -- the claim is not carried by votes: an old block's references are old
  have hnotVotes : ¬ CarriesVotes U' (IsVote U') (quorumCard Validator) C L := by
    intro hcv
    have hpos : 0 < quorumCard Validator := by have := F.card_validators; omega
    obtain ⟨b, hb, hv⟩ := exists_vote_of_carriesVotes hpos hcv
    rw [AnchoredRule.band_refs h hCU (by omega) (by omega)] at hb
    have hbU := U.complete C hCU b hb
    have := U.round_of_mem_refs hCU hb
    exact hLnov (U.complete b hbU L ((AnchoredRule.isVote_band h hbU (by omega) (by omega)).mp hv))
  -- so it is the claim field, which the discipline backs at the anchor's honest voter
  have hcl : claim C = some L := ((Finset.mem_filter.mp hC).2).resolve_right hnotVotes
  have hcert := hanc C hreU L hcl
  -- a certified candidate has a voter in `U`, and a voter references it
  obtain ⟨w, hw, -⟩ := exists_correct_of_card (S := supporters U L ((U.block L).round + 1))
    (by have := F.card_validators; change quorumCard Validator ≤ _ at hcert; omega)
  obtain ⟨c, hc, -, hcL, -⟩ := mem_supporters.mp hw
  exact hLnov (U.complete c hc L hcL)

/-- **Bluestreak's band laws.** The claim count and the omission counts
sit at `r+2` and `r+1`, inside every band a verdict reads; the link is
the claimers in the anchor's cone; and the novelty clause is
`not_claimedIn_novel`, which reads the anchor. -/
theorem bluestreakBandLaws : (bluestreakAnchored Validator BlockId Payload).BandLaws where
  commit_band := by
    intro S S' U U' lo hi g g' V V' k k' L h hkk _ _ hlo hhi hV hL hc
    simp only [bluestreakAnchored_waveAt] at hhi
    refine AnchoredRule.holdsAtLeast_band h hV (fun C hC => ?_) (claimers_band h hL.1 ?_ ?_) hc
    · obtain ⟨hCU, hCr⟩ := mem_claimers_round hC
      exact ⟨hCU, by rw [hCr, hL.2.1]; omega, by rw [hCr, hL.2.1]; omega⟩
    · rw [hL.2.1]; omega
    · rw [hL.2.1]; omega
  skip_band := by
    intro S S' U U' lo hi g g' V V' k k' h hkk hlk _ hlo hhi hV hs
    simp only [bluestreakAnchored_waveAt] at hhi
    refine ⟨AnchoredRule.holdsAtLeast_band h hV (fun b hb => ?_) ?_ hs.1, fun L hL => ?_⟩
    · obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hb
      exact ⟨hbU, by rw [hbr]; omega, by rw [hbr]; omega⟩
    · exact AnchoredRule.blocksAt_band h (by omega) (by omega) (by omega)
    · -- a candidate of the shifted slot is an old candidate, blamed as it was
      have hLc : IsLeaderBlock (S := S') U' k' L := mem_leaderBlocksAt.mp hL
      by_cases hold : L ∈ U.ids
      · have hL' : IsLeaderBlock (S := S) U k L :=
          AnchoredRule.isLeaderBlock_band_old h hkk hlk (by omega) (by omega) hold hLc
        refine AnchoredRule.holdsAtLeast_band h hV (fun b hb => ?_) ?_
          (hs.2 L (Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hL'.1, hL'.2.1⟩, hL'.2.2⟩))
        · obtain ⟨hbU, hbr, -⟩ := mem_omissionsOf.mp hb
          exact ⟨hbU, by rw [hbr]; omega, by rw [hbr]; omega⟩
        · intro b hb
          obtain ⟨hbU, hbr, hbn⟩ := mem_omissionsOf.mp hb
          refine mem_omissionsOf.mpr ⟨AnchoredRule.band_mem h hbU (by omega) (by omega), ?_, ?_⟩
          · have := (AnchoredRule.band_block h hbU (by omega) (by omega)).1; omega
          · rw [AnchoredRule.band_refs h hbU (by omega) (by omega)]; exact hbn
      · -- a novel candidate is omitted by every old voting-round block
        refine le_trans hs.1 (Finset.card_le_card (AnchoredRule.heldAuthors_band h hV
          (fun b hb => ?_) (fun b hb => ?_)))
        · obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hb
          exact ⟨hbU, by rw [hbr]; omega, by rw [hbr]; omega⟩
        · obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hb
          have hb1 : lo ≤ (U.block b).round + g := by rw [hbr]; omega
          have hb2 : (U.block b).round + g ≤ hi := by rw [hbr]; omega
          have hround := (AnchoredRule.band_block h hbU hb1 hb2).1
          refine mem_omissionsOf.mpr ⟨AnchoredRule.band_mem h hbU hb1 hb2, by omega, fun hv => ?_⟩
          exact hold (U.complete b hbU L
            ((AnchoredRule.isVote_band h hbU (by omega) hb2).mp hv))
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ _ hlo hhi _ hL
    simp only [bluestreakAnchored_waveAt] at hhi
    constructor
    · rintro ⟨C, hC, hre⟩
      obtain ⟨-, hCr'⟩ := mem_claimers_round hC
      have hCrR : ((bluestreakAnchored Validator BlockId Payload).toDagRule.block U' C).round
          = (U'.block L).round + 2 := hCr'
      have hLb := (AnchoredRule.band_block h hL.1 (by rw [hL.2.1]; omega)
        (by rw [hL.2.1]; omega)).1
      obtain ⟨hCU, hreU, hCeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
      exact ⟨C, mem_claimers_of_band h hL.1 hCU (by rw [hL.2.1]; omega)
        (by rw [hL.2.1]; omega) hCeq hC, hreU⟩
    · rintro ⟨C, hC, hre⟩
      obtain ⟨hCU, hCr⟩ := mem_claimers_round hC
      have hLr : (U.block L).round = S.slotRound k := hL.2.1
      have hCin : lo ≤ (U.block C).round + g := by omega
      exact ⟨C, claimers_band h hL.1 (by omega) (by omega) hC,
        AgreeBand.reaches_of h hA hAhi hre hCin⟩
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hanc hAlo hAhi hkk _ _ hlo hhi _ hL hLo
    simp only [bluestreakAnchored_waveAt] at hhi
    have hLr : (U'.block L).round = S'.slotRound k' := hL.2.1
    exact not_claimedIn_novel h hA hanc.2 hAlo hAhi hLo (by omega) (by omega)

/-- **Bluestreak reads a band**, over the disciplined universes. -/
theorem banded : Banded (bluestreakRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.bandedOn (hb := bluestreakBandLaws)
    (AnchoredRule.anchorsOn_of_laws bluestreakLaws) fun _ _ h => h

end BluestreakProperties

end LeanDag
