import Mathlib.Order.Interval.Finset.Nat
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import Mathlib.Data.Finset.Lattice.Fold
import LeanDag.Hybrid.Carrier
import LeanDag.Hybrid.Liveness
import LeanDag.Mysticeti.Properties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Derived.Bounded
import LeanDag.Properties.Arcs.Headline
/-!
# Hybrid conforms to the target properties

`docs/archive/porting-plan.md` step 2: `Banded` and the liveness pair, alongside
the three one-theorem properties in `Carrier.lean`. Hybrid's skip needed
the same slot-level repair as the core's and Odontoceti's
(`Hybrid/Decision.lean`); the band helpers are the core's, reached
through `toCore` since the carrier's universe is a subtype.
-/

namespace LeanDag

namespace HybridProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

section Band

variable {k : ℕ}
variable {U U' : BlockUniverse Validator BlockId Payload}
variable {lo hi g g' : ℕ}

end Band

/-- **What Hybrid owes the band**, at a positive threshold: its direct
commit, its slot-level skip and the thick link carry across a band
covering the slot's wave, and a candidate the band did not carry is
thick-linked from no old anchor. -/
theorem hybridBandLaws {kt : ℕ} (hpos : 0 < kt) :
    (Hybrid.hybridAnchored Validator BlockId Payload kt).BandLaws where
  commit_band := fun h hkk _ hlo hhi hV _ hc =>
    AnchoredRule.holdsAtLeast_votesFor_band h hV (by omega) (by omega)
      (by simp only [Hybrid.hybridAnchored_wave] at hhi; omega) hc
  skip_band := fun h hkk hlk hlo hhi hV hs =>
    le_trans hs (Finset.card_le_card (AnchoredRule.slotBlamesIn_band h hkk hlk hlo.le
      (by simp only [Hybrid.hybridAnchored_wave] at hhi; omega) hV))
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi _ _
    simp only [Hybrid.hybridAnchored_wave] at hhi
    show Hybrid.ThickLink kt U' A L (S'.slotRound k') ↔ Hybrid.ThickLink kt U A L (S.slotRound k)
    unfold Hybrid.ThickLink coneLink
    rw [AnchoredRule.coneSupporters_band h hA hAlo hAhi (n := S.slotRound k + 1) (by omega) (by omega)
      (by omega)]
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi _ _ hL ht
    simp only [Hybrid.hybridAnchored_wave] at hhi
    change Hybrid.ThickLink kt U' A L (S'.slotRound k') at ht
    unfold Hybrid.ThickLink coneLink at ht
    rw [AnchoredRule.coneSupporters_band_novel h hA hAlo hAhi (n := S.slotRound k + 1)
      (by omega) (by omega) (by omega) hL, Finset.card_empty] at ht
    omega

/-- **Hybrid is banded**, at a positive threshold: the relation's band
under `HonestNoEquiv`. -/
theorem banded {kt : ℕ} (hpos : 0 < kt) :
    Banded (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) :=
  AnchoredRule.bandedOn (hybridBandLaws hpos)

/-! ## The two liveness properties, and the skip -/

/-- **Hybrid skips an unsupported slot from a hybrid quorum.** The
liveness half of the slot-level repair: a set meeting the hybrid quorum
whose voting-round blocks reference no candidate skips the slot, with
no anchor and no synchrony needed — confirming the repaired rule is
still reachable, not merely tightened. -/
theorem skipsUnsupported (kt : ℕ) :
    SkipsUnsupported (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) (fun T => Hybrid.q Validator ≤ T.card) := by
  intro S U V T k hq hpres huns
  refine Hybrid.Decided.directSkip (S := S) (le_trans hq (Finset.card_le_card ?_))
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
  have hcU : c ∈ U.val.ids := V.subset_ids hcV
  refine Finset.mem_image.mpr ⟨c, ?_, hcc⟩
  rw [Finset.mem_inter, slotBlamers, Finset.mem_filter]
  exact ⟨⟨mem_blocksAt.mpr ⟨hcU, hcr⟩,
    fun j hj hjL => huns c hcV (by rw [hcc]; exact hv) hcr j hjL hj⟩, hcV⟩

/-- **Law 3 of `voteSupport`, for Hybrid** (`Properties/Support.lean`):
the hybrid quorum referencing the candidate one round up is its direct
commit. -/
theorem voteSupport_commits (kt : ℕ) :
    (voteSupport (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt)).Commits (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : Hybrid.q Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    rw [hybrid_f] at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hdc : Hybrid.DirectCommit U.val L (S.slotRound k) := by
    refine le_trans hcard (Finset.card_le_card ?_)
    intro w hw
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
      (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) w hw
    exact mem_supporters.mpr ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ w hw b hb hbc hbr, hbc⟩
  have hin : Hybrid.DirectCommitIn U.val V L (S.slotRound k) :=
    Hybrid.directCommitIn_of_coversUpto hdc hcov
  refine ⟨L, by omega, Hybrid.Decided.directCommit ⟨hLmem, hLr, hLc⟩ hin, ?_⟩
  intro S' hround hlead'
  refine Hybrid.Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-- **H-A3 as a property**: the relation's indirect property, committing
the least thick-linked candidate. -/
theorem indirect (kt : ℕ) :
    Indirect (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) kt)
      (fun sr i j =>
        sr i + (Hybrid.hybridAnchored Validator BlockId Payload kt).wave + 1 ≤ sr j) :=
  AnchoredRule.indirectOn ((Hybrid.hybridAnchored Validator BlockId Payload kt).linkCongr_of_round
    (fun _ U A L r => Hybrid.ThickLink kt U A L r) fun _ _ _ _ _ _ => rfl)
    fun hi h => Hybrid.exists_least hi h

/-- **And a committed run decides everything below it.** -/
theorem descends {kt : ℕ} {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : (Hybrid.hybridAnchored Validator BlockId Payload kt).SpansEligible (S := S) c) :
    Descends (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) S c :=
  Descends.of_indirect (indirect kt) hc
    (fun b i hi => (Hybrid.hybridAnchored Validator BlockId Payload kt).eligible_iff.mp
      (hspans b i hi))

/-! ## The headlines -/

theorem safety {kt : ℕ} (hpos : 0 < kt) (hk : Hybrid.Admissible Validator kt) :
    Properties.Safe (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) :=
  Properties.safety (banded hpos) (agree hk) (commitsCandidate kt)

theorem liveness (kt : ℕ) : Properties.Support.Lives (Properties.voteSupport (hybridRule
    (Validator := Validator) (BlockId := BlockId) (Payload := Payload) kt))
    (coreReliability Validator) :=
  Properties.Support.liveness (voteSupport_commits kt) (commitsCandidate kt) (selfParent kt)
    (noEquiv kt)

end HybridProperties

end LeanDag
