import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import LeanDag.Nemo.Carrier
import LeanDag.Nemo.Liveness
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Derived.Bounded
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# Nemo conforms to the target properties

`docs/archive/porting-plan.md` step 1. `Nemo/Carrier.lean` has the carrier and
the three properties that are one Nemo theorem apiece; here is
`Banded`, the one induction the rule owes, and the liveness pair on top
of it. Nemo is the cheapest of the four rules — three constructors, no
direct skip, a wave of two, rules reading one round above the slot —
and needs only the generic band helpers of `Properties/Band.lean`.
-/

namespace LeanDag

namespace NemoProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Band

variable {U U' : Nemo.Universe Validator BlockId Payload} {lo hi g g' : ℕ}

/-- **The anchor certifies what it certified.** Both directions: a
certificate inside an old anchor's history is old, by `reaches_old`, and
an old one stays inside it, by `reaches_of`. -/
theorem certifiedIn_band (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Nemo.CertifiedIn U' A L r' ↔ Nemo.CertifiedIn U A L r := by
  have hA' : A ∈ U'.ids := AnchoredRule.band_mem h hA hAlo hAhi
  constructor
  · rintro ⟨p, hp, hpr, hpL⟩
    have hpre : ReachesFrom U'.block A p := (mem_history_iff hA').mp hp
    obtain ⟨hpU, hpreU, hpeq⟩ :=
      AgreeBand.reaches_old h hA hAlo hAhi hpre (by
        show lo ≤ (U'.block p).round + g'; omega)
    have hpeq' : (U.block p).round + g = (U'.block p).round + g' := hpeq
    refine ⟨p, (mem_history_iff hA).mpr hpreU, by omega, ?_⟩
    rwa [AnchoredRule.band_refs h hpU (by omega) (by omega)] at hpL
  · rintro ⟨p, hp, hpr, hpL⟩
    have hpre : ReachesFrom U.block A p := (mem_history_iff hA).mp hp
    have hpU : p ∈ U.ids := U.causal.mem_ids_of_reaches hA hpre
    have hb := AnchoredRule.band_block h hpU (by omega) (by omega)
    refine ⟨p, (mem_history_iff hA').mpr
      (AgreeBand.reaches_of h hA hAhi hpre (by
        show lo ≤ (U.block p).round + g; omega)), by omega, ?_⟩
    rw [AnchoredRule.band_refs h hpU (by omega) (by omega)]; exact hpL

/-- **A candidate the band did not carry is certified from no old
anchor.** Its certificate would have to lie in the anchor's history,
which is old, and an old block references only old blocks. This is the
premise `indirectSkip` needs. -/
theorem not_certifiedIn_band_novel
    (h : AgreeBand (nemoRule (Payload := Payload)) U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hL : L ∉ U.ids) : ¬ Nemo.CertifiedIn U' A L r' := by
  intro hc
  rw [certifiedIn_band h hA hAlo hAhi hrr hr hhi] at hc
  obtain ⟨p, hp, -, hpL⟩ := hc
  have hpre : ReachesFrom U.block A p := (mem_history_iff hA).mp hp
  exact hL (U.complete p (U.causal.mem_ids_of_reaches hA hpre) L hpL)

end Band

/-- **What Nemo owes the band**: the direct commit and the link carry
across a band covering the slot's wave, and a candidate the band did not
carry is certified from no old anchor. -/
theorem nemoBandLaws : (Nemo.nemoAnchored Validator BlockId Payload).BandLaws where
  commit_band := fun h hkk _ hlo hhi hV _ hc =>
    AnchoredRule.holdsAtLeast_votesFor_band h hV (by omega) (by omega)
      (by simp only [Nemo.nemoAnchored_wave] at hhi; omega) hc
  skip_band := fun _ _ _ _ _ _ h => h.elim
  link_band := fun h hA hAlo hAhi hkk _ hlo hhi _ _ =>
    certifiedIn_band h hA hAlo hAhi hkk hlo (by simp only [Nemo.nemoAnchored_wave] at hhi; omega)
  link_novel := fun h hA hAlo hAhi hkk _ hlo hhi _ _ hL =>
    not_certifiedIn_band_novel h hA hAlo hAhi hkk hlo
      (by simp only [Nemo.nemoAnchored_wave] at hhi; omega) hL

/-- **Nemo is banded**: the relation's band at Nemo's laws. -/
theorem banded : Banded (nemoRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.banded nemoBandLaws

/-! ## The liveness properties

`LeaderCommits` is `Support.leaderCommits` at `voteSupport`, and `Descends` is not among them: it follows from `Indirect` by the generic
induction in `Properties/Derived/Descent.lean` (§11.2b), and what Nemo
supplies for it is the round-structure hypothesis. -/

/-- **Law 3 of `voteSupport`, for Nemo** (`Properties/Support.lean`): a
majority referencing the candidate one round up is its direct commit.
Laws 1 and 2 are the generic ones for the one-round shape. -/
theorem voteSupport_commits (hn : 0 < Fintype.card Validator) :
    (voteSupport (nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))).Commits (nemoReliability Validator hn) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : Nemo.majority Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - (Fintype.card Validator - Nemo.majority Validator)
      ≤ T.card at h2
    have : Nemo.majority Validator ≤ Fintype.card Validator := by unfold Nemo.majority; omega
    omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hdc : Nemo.DirectCommit U L (S.slotRound k) := by
    refine le_trans hcard (Finset.card_le_card ?_)
    intro w hw
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
      (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) w hw
    exact mem_supporters.mpr ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ w hw b hb hbc hbr, hbc⟩
  have hin : Nemo.DirectCommitIn U V L (S.slotRound k) := Nemo.directCommitIn_of_coversUpto hdc hcov
  refine ⟨L, by omega, Nemo.Decided.directCommit ⟨hLmem, hLr, hLc⟩ hin, ?_⟩
  intro S' hround hlead'
  refine Nemo.Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-- **A3 as a property**: the relation's indirect property, with no tie
to break. -/
theorem indirect :
    Indirect (nemoRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (fun sr i j => sr i + (Nemo.nemoAnchored Validator BlockId Payload).wave + 1 ≤ sr j) :=
  AnchoredRule.indirect Nemo.nemoLaws.link_congr fun _ ⟨L, hL, hl⟩ => ⟨L, hL, hl, fun _ _ _ h => h⟩

/-- **And a committed run decides everything below it**, from `Indirect`
with no induction of its own. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : (Nemo.nemoAnchored Validator BlockId Payload).SpansEligible (S := S) c) :
    Descends (nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c :=
  Descends.of_indirect indirect hc
    (fun b i hi => (Nemo.nemoAnchored Validator BlockId Payload).eligible_iff.mp (hspans b i hi))

end NemoProperties

namespace Nemo

/-! ## Liveness, composed

`Timed.decidedBelow_of_fairRun` at Nemo's vote support, under the
majority fault model `nemoReliability`. -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [C : CrashFaults Validator] [S : Slots Validator] {T : Finset Validator}

/-- **Liveness.** Under post-`R` coverage, growth to the horizon, and a
recurring run of `c` reliable-led slots, every slot below the run is
decided, the run placed past both the target and `R` by fairness. The
slot `b` is fixed by the schedule alone, before any universe is named,
so "eventually" means any DAG grown past this schedule-fixed slot;
crashed-leader slots are settled here and only here, via
`indirectSkip`. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ Live Validator)
    (hcard : majority Validator ≤ T.card)
    (hspan : (Nemo.nemoAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v := by
  have hTn := Finset.card_le_univ T
  have hn : 0 < Fintype.card Validator := by unfold majority at hcard; omega
  obtain ⟨b, hb, hRb, h⟩ :=
    Timed.decidedBelow_of_fairRun (Properties.voteSupport (NemoProperties.nemoRule
      (Validator := Validator) (BlockId := BlockId) (Payload := Payload)))
      (Timed.voteSupport_ofCoverage _) (NemoProperties.voteSupport_commits hn)
      (NemoProperties.descends hc hspan) (T := T)
      ⟨Finset.subset_univ _, by
        change Fintype.card Validator - (Fintype.card Validator - majority Validator) ≤ T.card
        omega⟩ fair R s
  refine ⟨b, hb, hRb, fun U N V hpop hs hN hcov i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs (fun r _ h2 => PopulatedOn.mono hT (hpop r h2)) hcov hN i hi
  exact ⟨v, hv.2.1⟩

/-- **Liveness at `T := Live`** — the whole live class, which the tight
committee `n = 2f + 1` requires exactly. -/
theorem all_decided_below_of_fairRun_live {c : ℕ} (hc : 0 < c)
    (hspan : (Nemo.nemoAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn (Live Validator) c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r ≤ N, Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl majority_le_card_live hspan fair R s

end Nemo


namespace NemoProperties

/-! ## The headlines

Nemo's model has no self-parent clause, so it shows progress and not
inclusion. -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

theorem safety : Properties.Safe (nemoRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

theorem progress (hn : 0 < Fintype.card Validator) :
    Properties.Support.Progresses (Properties.voteSupport (nemoRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload))) (nemoReliability Validator hn) :=
  Properties.Support.progress (voteSupport_commits hn)

end NemoProperties

end LeanDag
