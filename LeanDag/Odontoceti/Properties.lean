import LeanDag.Odontoceti.Carrier
import LeanDag.Mysticeti.Properties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Derived.Bounded
import LeanDag.Adaptive.Odontoceti
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# Odontoceti conforms to the target properties

`docs/target-properties.md` §11.2. The third rule to be put through the
properties at its own carrier, and the first not written for them.

**Why this rule and not another.** Odontoceti mirrors the core
constructor for constructor at a shorter wavelength —
`decisionRound k = slotRound k + 1`, no certificate round — so if the
six obligations are the right six, the differences it does have should
be the only work. That is what a third instance is for.

**All six, and the fifth found a defect on the way.**

`Decided.directSkip` used to quantify over the candidates the universe
holds, so a slot with no candidate was skipped *vacuously*.
`AgreeBand`'s membership clause runs one way — a block of `U` in the
band is a block of `U'` — because a band must admit universes that hold
*more*. A candidate present in `U'` and absent from `U` was therefore
beyond reach, and the goal `L ∈ U.ids` could not be closed.

That was the core's own defect, before its repair
(`docs/target-properties.md` §3.2), and the repair transferred without
change: Odontoceti's `DirectSkipIn` and the core's are the same
predicate, so `Decided.directSkip` now takes `DirectSkipSlotIn`.

What is Odontoceti's own, and what this file has to supply, is the
shorter wavelength — the direct rule counts supporters at
`slotRound k + 1` where the core counts certificates two rounds up —
and `ThickLink`, the indirect test, which counts supporters inside the
anchor's cone. Both needed their own band transport. The minimality
premise on `indirectCommit`, which the core has no analogue of, needed
`not_thickLink_band_novel`: a fresh candidate is thick-linked from no
old anchor, so it cannot undercut the least one.
-/

namespace LeanDag

namespace OdontocetiProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## What this file adds to `Odontoceti/Carrier.lean`

The carrier, `Causal`, `Agree`, `CommitsCandidate` and `CommitsDirect`
are there, upstream of every mechanism. Here is the band and everything
the band gives, plus the two liveness properties, which need the bounded
relation and so the adaptive arc.

## The band, across a shifted universe

Odontoceti shares the core's block vocabulary — `IsLeaderBlock`,
`blocksAt`, `slotBlamers` — so the core's band lemmas apply once the
carriers are identified, which `toCore` does by the three fields. What
is Odontoceti's own is the direct rule, which counts *supporters* at
`slotRound k + 1` rather than certificates two rounds up, and the
indirect test `ThickLink`, which counts supporters inside the anchor's
cone. Those need their own transport, and they are what follows. -/

section Band

variable {U U' : BlockUniverse Validator BlockId Payload} {lo hi g g' : ℕ}

/-- **Supporters survive the band.** A block one round above the slot
that referenced the candidate references it still, and it is a block of
the shifted universe at the shifted round. -/
theorem supportersIn_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} :
    supportersIn U V L (r + 1) ⊆ supportersIn U' V' L (r' + 1) := by
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  obtain ⟨hqA, hqL⟩ := Finset.mem_filter.mp hqf
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  have hqr : (U.block q).round = r + 1 := (mem_blocksAt.mp hqA).2
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩,
    hV q hqV (by omega) (by omega)⟩, ?_⟩
  · exact AnchoredRule.blocksAt_band h (by omega) (by omega) (by omega) hqA
  · rw [AnchoredRule.band_refs h hqU (by omega) (by omega)]; exact hqL
  · rw [(AnchoredRule.band_block h hqU (by omega) (by omega)).2]; exact hvq

/-- **And so does the direct commit.** -/
theorem directCommitIn_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} (hc : Odontoceti.DirectCommitIn U V L r) :
    Odontoceti.DirectCommitIn U' V' L r' :=
  le_trans hc (Finset.card_le_card (supportersIn_band h hrr hr hhi hV))

/-- **The anchor's cone of supporters is the cone it was.** Both
inclusions at once: a supporter inside an old anchor's history is old,
by `reaches_old`, and an old one stays inside it, by `reaches_of`. -/
theorem coneSupports_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Odontoceti.coneSupports U' A L r' = Odontoceti.coneSupports U A L r := by
  have hset : (blocksAt U' (r' + 1)).filter
        (fun q => L ∈ (U'.block q).refs ∧ q ∈ history U' A)
      = (blocksAt U (r + 1)).filter (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A) := by
    have hA' : A ∈ U'.ids := AnchoredRule.band_mem h hA hAlo hAhi
    ext q
    simp only [Finset.mem_filter, mem_blocksAt]
    constructor
    · rintro ⟨⟨hqU', hqr'⟩, hqL, hqh⟩
      have hqre : ReachesFrom U'.block A q := (mem_history_iff (U := U') hA').mp hqh
      have hqrR : (odontocetiRule.block U' q).round = r' + 1 := hqr'
      obtain ⟨hqU, hqreU, hqeq⟩ :=
        AgreeBand.reaches_old h hA hAlo hAhi hqre (by omega)
      have hqeq' : (U.block q).round + g = (U'.block q).round + g' := hqeq
      refine ⟨⟨hqU, by omega⟩, ?_, (mem_history_iff (U := U) hA).mpr hqreU⟩
      rwa [AnchoredRule.band_refs h hqU (by omega) (by omega)] at hqL
    · rintro ⟨⟨hqU, hqr⟩, hqL, hqh⟩
      have hqre : ReachesFrom U.block A q := (mem_history_iff (U := U) hA).mp hqh
      have hlink : (odontocetiRule.block U q).round
          = (U.block q).round := rfl
      refine ⟨?_, ?_, ?_⟩
      · exact mem_blocksAt.mp (AnchoredRule.blocksAt_band h
          (by omega) (by omega) (by omega) (mem_blocksAt.mpr ⟨hqU, hqr⟩))
      · rw [AnchoredRule.band_refs h hqU (by omega) (by omega)]; exact hqL
      · exact (mem_history_iff (U := U') hA').mpr
          (AgreeBand.reaches_of h hA hAhi hqre (by omega))
  unfold Odontoceti.coneSupports
  rw [hset]
  refine AnchoredRule.creatorsOf_band h ?_
  intro b hb
  obtain ⟨hbA, -⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.ids := (mem_blocksAt.mp hbA).1
  have hbr : (U.block b).round = r + 1 := (mem_blocksAt.mp hbA).2
  exact ⟨hbU, by omega, by omega⟩

/-- **So the indirect test reads the same.** -/
theorem thickLink_band (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Odontoceti.ThickLink U' A L r' ↔ Odontoceti.ThickLink U A L r := by
  unfold Odontoceti.ThickLink
  rw [coneSupports_band h hA hAlo hAhi hrr hr hhi]

/-- **A candidate the band did not carry is thick-linked from no old
anchor.** Its supporters would have to sit in the anchor's cone, which
is old, and an old block references only old blocks — so the cone
supports nothing, and the threshold is positive.

This is the premise `indirectSkip` needs and the one `indirectCommit`'s
minimality clause needs: a fresh candidate cannot undercut the least
one, because it passes no test at all. -/
theorem not_thickLink_band_novel
    (h : AgreeBand (odontocetiRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hL : L ∉ U.ids) (hpos : 0 < Fintype.card Validator - 3 * F.f) :
    ¬ Odontoceti.ThickLink U' A L r' := by
  intro ht
  rw [thickLink_band h hA hAlo hAhi hrr hr hhi] at ht
  unfold Odontoceti.ThickLink Odontoceti.coneSupports at ht
  have hempty : (blocksAt U (r + 1)).filter
      (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqA, hqL, -⟩ := Finset.mem_filter.mp hq
    exact hL (U.complete q (mem_blocksAt.mp hqA).1 L hqL)
  rw [hempty] at ht
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty, Nat.le_zero] at ht
  omega

end Band

/-- The thick-link threshold is positive: `Faults5` asks for `5f + 1`
validators, so `card − 3f ≥ 2f + 1`. -/
theorem thickLink_threshold_pos : 0 < Fintype.card Validator - 3 * F.f := by
  have := F.card_validators5
  omega

/-- **What Odontoceti owes the band**: its direct commit, the core's
slot-level skip and the thick link carry across a band covering the
slot's wave, and a candidate the band did not carry is thick-linked from
no old anchor. -/
theorem odontocetiBandLaws :
    (Odontoceti.odontocetiAnchored Validator BlockId Payload).BandLaws where
  commit_band := fun h hkk _ hlo hhi hV _ hc =>
    directCommitIn_band h hkk (by omega)
      (by simp only [Odontoceti.odontocetiAnchored_wave] at hhi; omega) hV hc
  skip_band := fun h hkk hlk hlo hhi hV hs =>
    le_trans hs (Finset.card_le_card (AnchoredRule.slotBlamesIn_band h hkk hlk hlo
      (by simp only [Odontoceti.odontocetiAnchored_wave] at hhi; omega) hV))
  link_band := fun h hA hAlo hAhi hkk _ hlo hhi _ _ =>
    thickLink_band h hA hAlo hAhi hkk hlo
      (by simp only [Odontoceti.odontocetiAnchored_wave] at hhi; omega)
  link_novel := fun h hA hAlo hAhi hkk _ hlo hhi _ _ hL =>
    not_thickLink_band_novel h hA hAlo hAhi hkk hlo
      (by simp only [Odontoceti.odontocetiAnchored_wave] at hhi; omega) hL
      thickLink_threshold_pos

/-- **Odontoceti is banded**: the relation's band at its laws. -/
theorem banded : Banded
    (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.banded odontocetiBandLaws

/-- **Odontoceti skips an unsupported slot from a correct quorum.**

The liveness half of the repair. Making the skip a count of blockers
rather than a vacuous quantification made it strictly harder to satisfy,
and a rule no quorum can ever trigger would be sound and useless. This
says the repaired rule is still reachable: a correct quorum whose
voting-round blocks reference no candidate skips the slot, without
waiting for an anchor.

The count is the core's, so the argument is too — `subset_blamers`
applies unchanged, the two carriers projecting identically. -/
theorem skipsUnsupported :
    SkipsUnsupported (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun T => quorumCard Validator ≤ T.card) :=
  fun S U V T k hq hpres huns =>
    Odontoceti.Decided.directSkip (S := S)
      (le_trans hq (Finset.card_le_card
        (MysticetiProperties.subset_blamers (S := S) hpres huns)))

/-! ## The bounded relation, and the two liveness properties

`Adaptive/Odontoceti.DecidedWithin` already names the slots a derivation
mentions, which is the tight information `LeaderCommits` and `Descends`
need. What is added here is the bridge to `DecidedBelow`, and then the
two properties are Odontoceti's own liveness results wearing them. -/

section Bounded

/-! Odontoceti's bounded relation lands in the derived one by the
relation's `decidedBelow_of_decidedWithin`. -/

/-- **Law 3 of `voteSupport`, for Odontoceti** (`Properties/Support.lean`):
a quorum referencing the candidate one round up is its direct commit,
which is `directCommit_of_votesAt`. -/
theorem voteSupport_commits :
    (voteSupport (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))).Commits (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hdc : Odontoceti.DirectCommit U L (S.slotRound k) :=
    Odontoceti.directCommit_of_votesAt hcard
      (hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega))
      (hcert L ⟨hLmem, hLr, hLc⟩)
  have hin : Odontoceti.DirectCommitIn U V L (S.slotRound k) :=
    Odontoceti.directCommitIn_of_coversUpto hdc hcov
  refine ⟨L, by omega, Odontoceti.Decided.directCommit ⟨hLmem, hLr, hLc⟩ hin, ?_⟩
  intro S' hround hlead'
  refine Odontoceti.Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-- **O-A3 as a property**: the relation's indirect property, committing
the least thick-linked candidate. -/
theorem indirect :
    Indirect (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (fun sr i j => sr i + (Odontoceti.odontocetiAnchored Validator BlockId Payload).wave + 1
        ≤ sr j) :=
  AnchoredRule.indirect Odontoceti.odontocetiLaws.link_congr fun hi h => Odontoceti.exists_least hi h

/-- **And a committed run decides everything below it.** Was a downward
induction carrying the bound by hand; it is now `Descends.of_indirect`,
with `Eligible` read as the round inequality. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : (Odontoceti.odontocetiAnchored Validator BlockId Payload).SpansEligible
      (S := S) c) :
    Descends (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c :=
  Descends.of_indirect indirect hc
    (fun b i hi => (Odontoceti.odontocetiAnchored Validator BlockId Payload).eligible_iff.mp
      (hspans b i hi))

end Bounded

end OdontocetiProperties

namespace Odontoceti

/-! ## O10 — liveness, composed

`Timed.decidedBelow_of_fairRun` at Odontoceti's vote support: the run
commits by `voteSupport_commits`, and `descends` clears what is under
it. The direct proof this replaced ran O7 at each slot of the run and
then O9. -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator] {T : Finset Validator}

/-- **O10 (thesis Theorem 12).** Under production and post-`R`
synchrony, a recurring run of `c` correct-led slots decides
every slot below it, on any view caught up to the horizon — with the
run placed past both the target and `R` by fairness. Note the horizon:
the run's last slot needs rounds up to its `slotRound + 1` only. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hspan : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn T c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v := by
  obtain ⟨b, hb, hRb, h⟩ :=
    Timed.decidedBelow_of_fairRun (Properties.voteSupport (OdontocetiProperties.odontocetiRule
      (Validator := Validator) (BlockId := BlockId) (Payload := Payload)))
      (Timed.voteSupport_ofCoverage _) OdontocetiProperties.voteSupport_commits
      (OdontocetiProperties.descends hc hspan) (T := T)
      ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩ fair R k
  refine ⟨b, hb, hRb, fun U N V hpop hs hN hcov i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hcov hN i hi
  exact ⟨v, hv.2.1⟩

/-- **O10 at `T := Correct`.** -/
theorem all_decided_below_of_fairRun_correct {c : ℕ} (hc : 0 < c)
    (hspan : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn (Correct : Finset Validator) c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r, R ≤ r → r ≤ N → Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl card_correct hspan fair R k

end Odontoceti


namespace OdontocetiProperties

/-! ## The headlines -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

theorem safety : Properties.Safe (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

theorem liveness : Properties.Support.Lives (Properties.voteSupport (odontocetiRule
    (Validator := Validator) (BlockId := BlockId) (Payload := Payload)))
    (coreReliability Validator) :=
  Properties.Support.liveness voteSupport_commits commitsCandidate selfParent noEquiv

end OdontocetiProperties

end LeanDag
