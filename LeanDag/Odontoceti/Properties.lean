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
import LeanDag.Odontoceti.Liveness
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# Odontoceti conforms to the target properties

`docs/target-properties.md` §11.2. Odontoceti's own content is a
shorter wavelength — `decisionRound k = slotRound k + 1`, no
certificate round — and `ThickLink`, the indirect test counting
supporters inside the anchor's cone; both need their own band
transport, and the minimality premise on `indirectCommit` needs
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
are there. Here is the band and what it gives, plus the two liveness
properties needing the bounded relation. Odontoceti shares the core's
block vocabulary, so the core's band lemmas apply once the carriers are
identified; its own content is the direct rule counting supporters at
`slotRound k + 1` and the indirect test `ThickLink`, needing their own
transport. -/

section Band

variable {U U' : BlockUniverse Validator BlockId Payload} {lo hi g g' : ℕ}

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
    AnchoredRule.holdsAtLeast_votesFor_band h hV (by omega) (by omega)
      (by simp only [Odontoceti.odontocetiAnchored_wave] at hhi; omega) hc
  skip_band := fun h hkk hlk hlo hhi hV hs =>
    le_trans hs (Finset.card_le_card (AnchoredRule.slotBlamesIn_band h hkk hlk hlo.le
      (by simp only [Odontoceti.odontocetiAnchored_wave] at hhi; omega) hV))
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi _ _
    simp only [Odontoceti.odontocetiAnchored_wave] at hhi
    show Odontoceti.ThickLink U' A L (S'.slotRound k') ↔ Odontoceti.ThickLink U A L (S.slotRound k)
    unfold Odontoceti.ThickLink coneLink
    rw [AnchoredRule.coneSupporters_band h hA hAlo hAhi (n := S.slotRound k + 1) (by omega) (by omega)
      (by omega)]
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi _ _ hL ht
    simp only [Odontoceti.odontocetiAnchored_wave] at hhi
    change Odontoceti.ThickLink U' A L (S'.slotRound k') at ht
    unfold Odontoceti.ThickLink coneLink at ht
    rw [AnchoredRule.coneSupporters_band_novel h hA hAlo hAhi (n := S.slotRound k + 1)
      (by omega) (by omega) (by omega) hL, Finset.card_empty] at ht
    have := thickLink_threshold_pos (Validator := Validator)
    omega

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
it. -/

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
