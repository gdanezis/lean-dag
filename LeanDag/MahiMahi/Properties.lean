import LeanDag.MahiMahi.Carrier
import LeanDag.Mysticeti.Properties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.FromBand
import LeanDag.Properties.Commit
import LeanDag.MahiMahi.Helpers.Liveness
import LeanDag.MahiMahi.Helpers.Synchrony
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# Mahi-Mahi's band, and the two liveness properties

Fills the one transport Mahi-Mahi's cone-based rules need:
`MahiMahi.candidatesAt` agrees across a shifted universe, from which
`Votes`, `Blames`, `Certifies` and `good`'s persistence all follow.
Every hypothesis below carries `2 ≤ w`, needed because `votingRound` and
`decisionRoundAt` use truncated `ℕ` subtraction; every Mahi-Mahi theorem
already assumes `3 ≤ w`, so this costs no consumer anything.
-/

namespace LeanDag

namespace MahiMahiProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U U' : BlockUniverse Validator BlockId Payload} {lo hi g g' w : ℕ}

/-! ## The band, across a shifted universe -/

/-- **The candidates a block's cone holds at a round are the ones it
held.** Both inclusions, by `reaches_old` and `reaches_of` — the
transport every Mahi-Mahi rule rests on, since votes, blames,
certificates and the indirect test all read this set. -/
theorem candidatesAt_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    {q : BlockId} (hq : q ∈ U.ids) (hqlo : lo ≤ (U.block q).round + g)
    (hqhi : (U.block q).round + g ≤ hi) {a : Validator} {r r' : ℕ}
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + g ≤ hi) :
    MahiMahi.candidatesAt U' q a r' = MahiMahi.candidatesAt U q a r := by
  have hq' : q ∈ U'.ids := AnchoredRule.band_mem h hq hqlo hqhi
  ext b
  simp only [MahiMahi.candidatesAt, Finset.mem_filter, mem_blocksAt]
  constructor
  · rintro ⟨⟨hbU', hbr'⟩, hba, hbh⟩
    have hbre : ReachesFrom U'.block q b := (mem_history_iff (U := U') hq').mp hbh
    obtain ⟨hbU, hbreU, hbeq⟩ :=
      AgreeBand.reaches_old h hq hqlo hqhi hbre
        (by show lo ≤ (U'.block b).round + g'; omega)
    have hbeq' : (U.block b).round + g = (U'.block b).round + g' := hbeq
    have hbb := AnchoredRule.band_block h hbU (by omega) (by omega)
    exact ⟨⟨hbU, by omega⟩, by rw [← hbb.2]; exact hba,
      (mem_history_iff (U := U) hq).mpr hbreU⟩
  · rintro ⟨⟨hbU, hbr⟩, hba, hbh⟩
    have hbre : ReachesFrom U.block q b := (mem_history_iff (U := U) hq).mp hbh
    have hbb := AnchoredRule.band_block h hbU (by omega) (by omega)
    refine ⟨⟨AnchoredRule.band_mem h hbU (by omega) (by omega), by omega⟩,
      by rw [hbb.2]; exact hba, ?_⟩
    exact (mem_history_iff (U := U') hq').mpr
      (AgreeBand.reaches_of h hq hqhi hbre
        (by show lo ≤ (U.block b).round + g; omega))

/-- **A vote is the vote it was.** Both clauses read the same cone, and
`candidatesAt_band` settles it as an equality rather than a
containment. -/
theorem votes_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    {q : BlockId} (hq : q ∈ U.ids) (hqlo : lo ≤ (U.block q).round + g)
    (hqhi : (U.block q).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g)
    (hLhi : (U.block L).round + g ≤ hi) :
    MahiMahi.Votes U' q L ↔ MahiMahi.Votes U q L := by
  have hLb := AnchoredRule.band_block h hL hLlo hLhi
  have hset : MahiMahi.candidatesAt U' q (U'.block L).creator (U'.block L).round
      = MahiMahi.candidatesAt U q (U.block L).creator (U.block L).round := by
    rw [hLb.2]
    exact candidatesAt_band h hq hqlo hqhi (by omega) hLlo hLhi
  unfold MahiMahi.Votes
  rw [hset]

/-- **And a blame is the blame it was.** The skip rule reads a *cone*
rather than the universe's candidates, settled by the band in both
directions, so a negative clause a larger DAG could falsify — the shape
`docs/target-properties.md` §3.2 flagged — does not arise here. -/
theorem blames_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    {q : BlockId} (hq : q ∈ U.ids) (hqlo : lo ≤ (U.block q).round + g)
    (hqhi : (U.block q).round + g ≤ hi) {a : Validator} {r r' : ℕ}
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + g ≤ hi) :
    MahiMahi.Blames U' q a r' ↔ MahiMahi.Blames U q a r := by
  unfold MahiMahi.Blames
  rw [candidatesAt_band h hq hqlo hqhi hrr hr hhi]

/-- **A certificate certifies what it certified.** Its votes are cast by
its own references, one round below it, and each of those reads a cone
the band settles. -/
theorem certifies_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    {C : BlockId} (hC : C ∈ U.ids) (hClo : lo < (U.block C).round + g)
    (hChi : (U.block C).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) (hLlo : lo ≤ (U.block L).round + g)
    (hLhi : (U.block L).round + g ≤ hi) :
    MahiMahi.Certifies U' C L ↔ MahiMahi.Certifies U C L :=
  AnchoredRule.carriesVotes_band h hC hClo hChi fun q hqm =>
    votes_band h (U.complete C hC q hqm)
      (by have := U.round_of_mem_refs hC hqm; omega)
      (by have := U.round_of_mem_refs hC hqm; omega) hL hLlo hLhi

/-! ## The direct rules

Forward only, as everywhere: a band may add blocks, and a quorum that
was met is met still. The skip needs no separate argument for a
candidate the band added, `blames_band` being an equivalence. -/

/-- Certificates survive the band. -/
theorem certificates_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    (hw : 2 ≤ w) {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ}
    (hLr : (U.block L).round = r) (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + w - 1 + g ≤ hi) :
    MahiMahi.certificates U w L r ⊆ MahiMahi.certificates U' w L r' :=
  AnchoredRule.certificatesAt_band h (by simp only [MahiMahi.decisionRoundAt]; omega)
    (by simp only [MahiMahi.decisionRoundAt]; omega) (by simp only [MahiMahi.decisionRoundAt]; omega)
    fun C hC hCr b hb =>
      votes_band h (U.complete C hC b hb)
        (by have := U.round_of_mem_refs hC hb; simp only [MahiMahi.decisionRoundAt] at hCr; omega)
        (by have := U.round_of_mem_refs hC hb; simp only [MahiMahi.decisionRoundAt] at hCr; omega)
        hL (by omega) (by omega)

/-- **And so does the direct commit.** -/
theorem directCommitIn_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    (hw : 2 ≤ w) {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ}
    (hLr : (U.block L).round = r) (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + w - 1 + g ≤ hi) (hc : MahiMahi.DirectCommitIn U V w L r) :
    MahiMahi.DirectCommitIn U' V' w L r' :=
  AnchoredRule.holdsAtLeast_band h hV
    (fun C hC => by
      obtain ⟨hCU, hCr, -⟩ := mem_certificatesAt.mp hC
      simp only [MahiMahi.decisionRoundAt] at hCr
      exact ⟨hCU, by omega, by omega⟩)
    (certificates_band h hw hL hLr hrr hr hhi) hc

/-- **And the direct skip.** A blamer stays a blamer, and a candidate
the band added changes nothing: the blame reads the blamer's cone, which
the band settles both ways. -/
theorem directSkipIn_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    (hw : 2 ≤ w) {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {a : Validator} {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g)
    (hhi : r + w - 2 + g ≤ hi) (hs : MahiMahi.DirectSkipIn U V w a r) :
    MahiMahi.DirectSkipIn U' V' w a r' := by
  refine le_trans hs (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqb⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.block q).round = MahiMahi.votingRound w r := (mem_blocksAt.mp hqA).2
  have hvr : MahiMahi.votingRound w r = r + w - 2 := rfl
  have hvr' : MahiMahi.votingRound w r' = r' + w - 2 := rfl
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨AnchoredRule.blocksAt_band h (by omega) (by omega) (by omega) hqA, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · exact (blames_band h hqU (by omega) (by omega) hrr hr (by omega)).mpr hqb
  · rw [(AnchoredRule.band_block h hqU (by omega) (by omega)).2]; exact hqv

/-! ## The anchored test

Both directions, and the clause a one-directional band forces: a
candidate the band did not carry is certified from no old anchor,
because the certificate would have to lie in the anchor's cone and an
old cone holds only old blocks. -/

theorem certifiedIn_band (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    (hw : 2 ≤ w) {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    {L : BlockId} (hL : L ∈ U.ids) {r r' : ℕ} (hLr : (U.block L).round = r)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + w - 1 + g ≤ hi) :
    MahiMahi.CertifiedIn U' w A L r' ↔ MahiMahi.CertifiedIn U w A L r :=
  AnchoredRule.linkedVia_certificatesAt_band h hA hAlo hAhi
    (by simp only [MahiMahi.decisionRoundAt]; omega) (by simp only [MahiMahi.decisionRoundAt]; omega)
    (by simp only [MahiMahi.decisionRoundAt]; omega) fun C hC hCr b hb =>
      votes_band h (U.complete C hC b hb)
        (by have := U.round_of_mem_refs hC hb; simp only [MahiMahi.decisionRoundAt] at hCr; omega)
        (by have := U.round_of_mem_refs hC hb; simp only [MahiMahi.decisionRoundAt] at hCr; omega)
        hL (by omega) (by omega)

theorem not_certifiedIn_band_novel
    (h : AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g')
    (hw : 2 ≤ w) {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    {L : BlockId} (hLo : L ∉ U.ids) {r r' : ℕ} (hLr : (U'.block L).round = r')
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + w - 1 + g ≤ hi) :
    ¬ MahiMahi.CertifiedIn U' w A L r' := by
  rintro ⟨C, hC, hre⟩
  have hdr' : MahiMahi.decisionRoundAt w r' = r' + w - 1 := rfl
  obtain ⟨-, hCr'', hCc⟩ := mem_certificatesAt.mp hC
  have hCr' : (U'.block C).round = r' + w - 1 := by omega
  obtain ⟨hCU, -, hCeq⟩ :=
    AgreeBand.reaches_old h hA hAlo hAhi hre
      (by show lo ≤ (U'.block C).round + g'; omega)
  have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
  have hCround : (U.block C).round = r + w - 1 := by omega
  -- the quorum is positive, so some old reference of `C` votes for `L`
  obtain ⟨q, hqm, hqv⟩ := exists_vote_of_carriesVotes
    (MysticetiProperties.quorumCard_pos (Validator := Validator)) hCc
  rw [AnchoredRule.band_refs h hCU
    (by show lo < (U.block C).round + g; omega)
    (by show (U.block C).round + g ≤ hi; omega)] at hqm
  have hqU : q ∈ U.ids := U.complete C hCU q hqm
  have hqr : (U.block q).round + 1 = (U.block C).round := U.round_of_mem_refs hCU hqm
  have hq' : q ∈ U'.ids := AnchoredRule.band_mem h hqU
    (by show lo ≤ (U.block q).round + g; omega)
    (by show (U.block q).round + g ≤ hi; omega)
  -- `L` is in an old block's cone, so `L` is old
  have hLh : L ∈ history U' q := (Finset.mem_filter.mp hqv.1).2.2
  obtain ⟨hLU, -, -⟩ :=
    AgreeBand.reaches_old h hqU
      (by show lo ≤ (U.block q).round + g; omega)
      (by show (U.block q).round + g ≤ hi; omega)
      ((mem_history_iff (U := U') hq').mp hLh) (by show lo ≤ (U'.block L).round + g'; omega)
  exact hLo hLU

/-- **What Mahi-Mahi owes the band** at a wave of at least two: its
direct commit, its slot blame and the certificate in the anchor's cone
carry across a band covering the slot's wave, and a candidate the band
did not carry is certified from no old anchor. -/
theorem mahiMahiBandLaws (hw : 2 ≤ w) :
    (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).BandLaws where
  commit_band := fun h hkk _ hlo hhi hV hL hc =>
    directCommitIn_band h hw hV hL.1 hL.2.1 hkk (by omega)
      (by simp only [MahiMahi.mahiMahiAnchored_waveAt] at hhi; omega) hc
  skip_band := fun h hkk hlk hlo hhi hV hs => by
    show MahiMahi.DirectSkipIn _ _ _ _ _
    rw [← hlk]
    exact directSkipIn_band h hw hV hkk (by omega)
      (by simp only [MahiMahi.mahiMahiAnchored_waveAt] at hhi; omega) hs
  link_band := fun h hA hAlo hAhi hkk _ hlo hhi _ hL =>
    certifiedIn_band h hw hA hAlo hAhi hL.1 hL.2.1 hkk hlo
      (by simp only [MahiMahi.mahiMahiAnchored_waveAt] at hhi; omega)
  link_novel := fun h hA hAlo hAhi hkk _ hlo hhi _ hL hLo =>
    not_certifiedIn_band_novel h hw hA hAlo hAhi hLo hL.2.1 hkk hlo
      (by simp only [MahiMahi.mahiMahiAnchored_waveAt] at hhi; omega)

/-- **Mahi-Mahi reads a band**, at every width its rules are stated
for. -/
theorem banded (hw : 2 ≤ w) :
    Banded (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  AnchoredRule.banded (mahiMahiBandLaws hw) (fun _ _ => rfl)

/-! ## The two liveness properties

`Descends` is not among them: it follows from `Indirect` by the generic
induction of `Properties/Derived/Descent.lean`.

**What Mahi-Mahi's precondition is, and why it is not the conclusion.**
Every other rule here takes synchrony and population and *derives* a
direct commit; Mahi-Mahi's liveness arc takes the direct commit as given
— `MM3a` is "if the slot's leader is in `good`, it commits" — and gets
its unpredictability results from there. `good U w k` is a fact about
the DAG, a quorum of certificates at the decision round, and says
nothing about verdicts. What `LeaderCommits` adds to it is the **bound**:
the verdict survives any reassignment of the leaders of other slots,
which is what a schedule mechanism reads and what MM3a does not
state. -/

/-- A view caught up to the decision round holds every certificate,
so it commits what the DAG commits. -/
theorem directCommitIn_of_coversUpto {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {w : ℕ} {L : BlockId} {r : ℕ}
    (h : MahiMahi.DirectCommit U w L r) (hV : V.CoversUpto (MahiMahi.decisionRoundAt w r)) :
    MahiMahi.DirectCommitIn U V w L r :=
  HoldsAtLeast.of_coversUpto (fun C hC => by
    obtain ⟨hCU, hCr, -⟩ := mem_certificatesAt.mp hC
    exact ⟨hCU, by omega⟩) hV h

/-! ## Mahi-Mahi's support shape

`Properties/Support.lean`, and the shape that tests `CoversToward`: the
certifier sits `w − 1` rounds up and certifies through its cone, so
what it needs of the candidate is not two reference layers but
reachability. Coverage toward the candidate at the first layer, quorum
intersection for every layer after (`reaches_of_votes`), and the rule's
own `certifies_of_refs_reach` do the rest. -/

/-- **Mahi-Mahi's support** at wave `w`: certifiers at the decision
round, certification the rule's own. -/
def mmSupport (w : ℕ) : Support (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) w) where
  waveAt := fun _ => w - 1
  Certifies := fun U C L => MahiMahi.Certifies U C L

/-- **Law 1**: `certifies_band` at the band a `RebasedAbove` is. -/
theorem mmSupport_local {w : ℕ} (hw : 2 ≤ w) :
    Support.Local (R := mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (mmSupport w) := by
  intro U U' G R₀ h c L hc hcr hL hLr
  change R₀ + (w - 1) ≤ (BlockRecord.block U c).round at hcr
  change (BlockRecord.block U L).round + (w - 1) = (BlockRecord.block U c).round at hLr
  exact certifies_band (agreeBand_of_rebasedAbove h (BlockRecord.block U c).round R₀ le_rfl)
    hc (by change R₀ < (BlockRecord.block U c).round + 0; omega)
    (by change (BlockRecord.block U c).round + 0 ≤ (BlockRecord.block U c).round; omega)
    hL (by change R₀ ≤ (BlockRecord.block U L).round + 0; omega)
    (by change (BlockRecord.block U L).round + 0 ≤ (BlockRecord.block U c).round; omega)

/-- **Law 2**: every block at the voting round reaches the candidate —
coverage toward it at the first layer, quorum intersection after — so
every quorum block at the decision round certifies. -/
theorem mmSupport_ofCoverage {w : ℕ} (hw : 4 ≤ w) :
    Timed.OfCoverage (R := mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (mmSupport w) (coreReliability Validator) := by
  intro U T hq r L hpop hct hL hLr hLc C hC hCc hCr
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  have hT : T ⊆ (Correct : Finset Validator) := hq.1
  have hLr' : (BlockRecord.block U L).round = r := hLr
  have hLc' : (BlockRecord.block U L).creator ∈ T := hLc
  have hCr' : (BlockRecord.block U C).round = r + (w - 1) := hCr
  have hvotes : ∀ q ∈ BlockRecord.ids U, (BlockRecord.block U q).round = r + 1 →
      (BlockRecord.block U q).creator ∈ T → L ∈ (BlockRecord.block U q).refs := by
    intro q hq hqr hqc
    exact hct r le_rfl (by change r < r + (w - 1); omega) q hq hqc hqr L hL hLc' hLr'
      Relation.ReflTransGen.refl
  have hreach := MahiMahi.reaches_of_votes hT hcard
    (hpop (r + 1) (by omega) (by change r + 1 ≤ r + (w - 1); omega)) hL hLr' hLc' hvotes
  change MahiMahi.Certifies U C L
  refine MahiMahi.certifies_of_refs_reach (w := w) (r := r) (by omega) hC
    (by unfold MahiMahi.decisionRoundAt; omega) hL (hT hLc') ?_
  intro q hq
  have hqids := BlockRecord.complete U C hC q hq
  have hqr := BlockRecord.round_of_mem_refs hC hq
  exact hreach q hqids (by omega)

/-- **Law 3**: a quorum's certificates at the decision round are the
direct commit, which a view caught up to that round sees. -/
theorem mmSupport_commits {w : ℕ} (hw : 2 ≤ w) :
    Support.Commits (R := mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (mmSupport w) (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : Slots Validator := S
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  have hdr : MahiMahi.decisionRoundAt w (S.slotRound k) = S.slotRound k + (w - 1) := by
    unfold MahiMahi.decisionRoundAt; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + (w - 1); omega) (S.leader k) hlead
  have hLr' : (BlockRecord.block U L).round = S.slotRound k := hLr
  have hLc' : (BlockRecord.block U L).creator = S.leader k := hLc
  have hdc : MahiMahi.DirectCommit U w L (S.slotRound k) := by
    unfold MahiMahi.DirectCommit
    refine le_trans hcard (Finset.card_le_card ?_)
    intro v hv
    obtain ⟨C, hC, hCc, hCr⟩ := hpop (S.slotRound k + (w - 1)) (by omega) le_rfl v hv
    have hCr' : (BlockRecord.block U C).round = MahiMahi.decisionRoundAt w (S.slotRound k) := by
      rw [hdr]; exact hCr
    rw [mem_creatorsOf]
    exact ⟨C, mem_certificatesAt.mpr
      ⟨hC, hCr', hcert L ⟨hLmem, hLr, hLc⟩ v hv C hC hCc hCr⟩, hCc⟩
  have hin : MahiMahi.DirectCommitIn U V w L (S.slotRound k) :=
    directCommitIn_of_coversUpto hdc (by rw [hdr]; exact hcov)
  refine ⟨L, by omega, MahiMahi.Decided.directCommit ⟨hLmem, hLr', hLc'⟩ hin, ?_⟩
  intro S' hround hlead'
  refine MahiMahi.Decided.directCommit (S := S') ⟨hLmem, ?_, ?_⟩ ?_
  · rw [hround]; exact hLr'
  · rw [hlead' k (by omega)]; exact hLc'
  · show MahiMahi.DirectCommitIn U V w L (S'.slotRound k)
    rw [hround]; exact hin

open Classical in
/-- **MM-A3 as a property**: the relation's indirect property, with no
tie to break — two certificates at one slot name the same candidate. -/
theorem indirect {w : ℕ} (hw : 1 ≤ w) :
    Indirect (mahiMahiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)
      (fun sr i j => sr i + w ≤ sr j) :=
  (AnchoredRule.indirect ((MahiMahi.mahiMahiAnchored Validator BlockId Payload w).linkCongr_of_round
    (fun _ U A L r => MahiMahi.CertifiedIn U w A L r) fun _ _ _ _ _ _ => rfl)
    fun hi h => MahiMahi.exists_least hi h).congr
    (fun _ _ _ => by simp only [MahiMahi.mahiMahiAnchored_waveAt]; omega)

/-- **Mahi-Mahi has the descent laws** at the core fault model's slack,
at its `w`-round wave. -/
theorem descent {w : ℕ} (hw : 4 ≤ w) :
    Properties.Descent (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
      (Timed.Good (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) w) (coreReliability Validator))
      (w - 1 + 1) (coreReliability Validator).slack :=
  Timed.descent_of_support _ _ _ (mmSupport w) (mmSupport_ofCoverage hw)
    (mmSupport_commits (by omega))
    ((indirect (by omega)).congr fun sr i j => by
      change sr i + w ≤ sr j ↔ sr i + (w - 1 + 1) ≤ sr j
      omega)
    (fun _ => by change w - 1 ≤ w - 1 + 1; omega) fun _ _ _ h => h

/-! ## The headlines -/

theorem safety (hw : 2 ≤ w) : Properties.Safe (mahiMahiRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) w) :=
  Properties.safety (banded hw) (agree hw) (commitsCandidate w)

theorem liveness (hw : 2 ≤ w) : Properties.Support.Lives (mmSupport (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) w) (coreReliability Validator) :=
  Properties.Support.liveness (mmSupport_commits hw) (commitsCandidate w) (selfParent w)
    (noEquiv w)

end MahiMahiProperties

end LeanDag
