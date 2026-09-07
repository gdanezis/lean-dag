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

`docs/porting-plan.md` step 2. `Hybrid/Carrier.lean` has the carrier at
each threshold and the three properties that are one Hybrid theorem
apiece; here is `Banded` and the liveness pair.

**The band forced a repair before it could be proved.** Hybrid's skip
quantified over the candidates a slot happens to have, which a mechanism
adding one defeats; `DirectSkipSlotIn` replaced it, as it replaced the
core's and Odontoceti's. That is recorded where it happened, in
`Hybrid/Decision.lean`.

**The universe is the core's**, so the band helpers are the core's too,
reached through `toCore` — the carrier's universe is a subtype of the
core's, and `AgreeBand` at the subtype is `AgreeBand` at the underlying
universe by its three fields.
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

/-- **Supporters survive the band.** -/
theorem supportersIn_band (h : AgreeBand (Hybrid.hybridAnchored Validator BlockId Payload k).toDagRule U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g →
      (U.block b).round + g ≤ hi → b ∈ V'.ids)
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
theorem directCommitIn_band (h : AgreeBand (Hybrid.hybridAnchored Validator BlockId Payload k).toDagRule U U' lo hi g g')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    {r r' : ℕ} (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g →
      (U.block b).round + g ≤ hi → b ∈ V'.ids)
    {L : BlockId} (hc : Hybrid.DirectCommitIn U V L r) :
    Hybrid.DirectCommitIn U' V' L r' :=
  le_trans hc (Finset.card_le_card (supportersIn_band h hrr hr hhi hV))

/-- **The anchor's cone of supporters is the cone it was.** -/
theorem coneSupports_band (h : AgreeBand (Hybrid.hybridAnchored Validator BlockId Payload k).toDagRule U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Hybrid.coneSupports U' A L r' = Hybrid.coneSupports U A L r := by
  have hset : (blocksAt U' (r' + 1)).filter
        (fun q => L ∈ (U'.block q).refs ∧ q ∈ history U' A)
      = (blocksAt U (r + 1)).filter
        (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A) := by
    have hA' : A ∈ U'.ids := AnchoredRule.band_mem h hA hAlo hAhi
    ext q
    simp only [Finset.mem_filter, mem_blocksAt]
    constructor
    · rintro ⟨⟨hqU', hqr'⟩, hqL, hqh⟩
      have hqre : ReachesFrom U'.block A q := (mem_history_iff (U := U') hA').mp hqh
      obtain ⟨hqU, hqreU, hqeq⟩ :=
        AgreeBand.reaches_old h hA hAlo hAhi hqre
          (by show lo ≤ (U'.block q).round + g'; omega)
      have hqeq' : (U.block q).round + g = (U'.block q).round + g' := hqeq
      refine ⟨⟨hqU, by omega⟩, ?_, (mem_history_iff (U := U) hA).mpr hqreU⟩
      rwa [AnchoredRule.band_refs h hqU (by omega) (by omega)] at hqL
    · rintro ⟨⟨hqU, hqr⟩, hqL, hqh⟩
      have hqre : ReachesFrom U.block A q := (mem_history_iff (U := U) hA).mp hqh
      refine ⟨?_, ?_, ?_⟩
      · exact mem_blocksAt.mp (AnchoredRule.blocksAt_band h
          (by omega) (by omega) (by omega) (mem_blocksAt.mpr ⟨hqU, hqr⟩))
      · rw [AnchoredRule.band_refs h hqU (by omega) (by omega)]; exact hqL
      · exact (mem_history_iff (U := U') hA').mpr
          (AgreeBand.reaches_of h hA hAhi hqre
            (by show lo ≤ (U.block q).round + g; omega))
  unfold Hybrid.coneSupports
  rw [hset]
  refine AnchoredRule.creatorsOf_band h ?_
  intro b hb
  obtain ⟨hbA, -⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.ids := (mem_blocksAt.mp hbA).1
  have hbr : (U.block b).round = r + 1 := (mem_blocksAt.mp hbA).2
  exact ⟨hbU, by omega, by omega⟩

/-- **So the indirect test reads the same.** -/
theorem thickLink_band (h : AgreeBand (Hybrid.hybridAnchored Validator BlockId Payload k).toDagRule U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi) :
    Hybrid.ThickLink k U' A L r' ↔ Hybrid.ThickLink k U A L r := by
  unfold Hybrid.ThickLink
  rw [coneSupports_band h hA hAlo hAhi hrr hr hhi]

/-- **A candidate the band did not carry passes the indirect test from
no old anchor.** Its supporters would sit in the anchor's cone, which is
old, and an old block references only old blocks — so the cone supports
nothing, and an admissible threshold is positive. -/
theorem not_thickLink_band_novel
    (h : AgreeBand (Hybrid.hybridAnchored Validator BlockId Payload k).toDagRule U U' lo hi g g')
    {A L : BlockId} {r r' : ℕ} (hA : A ∈ U.ids)
    (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hrr : r + g = r' + g') (hr : lo ≤ r + g) (hhi : r + 1 + g ≤ hi)
    (hL : L ∉ U.ids) (hpos : 0 < k) : ¬ Hybrid.ThickLink k U' A L r' := by
  intro ht
  rw [thickLink_band h hA hAlo hAhi hrr hr hhi] at ht
  unfold Hybrid.ThickLink Hybrid.coneSupports at ht
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

/-- **What Hybrid owes the band**, at a positive threshold: its direct
commit, its slot-level skip and the thick link carry across a band
covering the slot's wave, and a candidate the band did not carry is
thick-linked from no old anchor. -/
theorem hybridBandLaws {kt : ℕ} (hpos : 0 < kt) :
    (Hybrid.hybridAnchored Validator BlockId Payload kt).BandLaws where
  commit_band := fun h hkk _ hlo hhi hV _ hc =>
    directCommitIn_band h hkk (by omega)
      (by simp only [Hybrid.hybridAnchored_wave] at hhi; omega) hV hc
  skip_band := fun h hkk hlk hlo hhi hV hs =>
    le_trans hs (Finset.card_le_card (AnchoredRule.slotBlamesIn_band h hkk hlk hlo
      (by simp only [Hybrid.hybridAnchored_wave] at hhi; omega) hV))
  link_band := fun h hA hAlo hAhi hkk _ hlo hhi _ _ =>
    thickLink_band h hA hAlo hAhi hkk hlo
      (by simp only [Hybrid.hybridAnchored_wave] at hhi; omega)
  link_novel := fun h hA hAlo hAhi hkk _ hlo hhi _ _ hL =>
    not_thickLink_band_novel h hA hAlo hAhi hkk hlo
      (by simp only [Hybrid.hybridAnchored_wave] at hhi; omega) hL hpos

/-- **Hybrid is banded**, at a positive threshold: the relation's band
under `HonestNoEquiv`. -/
theorem banded {kt : ℕ} (hpos : 0 < kt) :
    Banded (hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) :=
  AnchoredRule.bandedOn (hybridBandLaws hpos)

/-! ## The two liveness properties, and the skip -/

/-- **Hybrid skips an unsupported slot from a hybrid quorum.**

The liveness half of the repair, and the reason to believe it was a
repair rather than a tightening: making the skip a count of blockers
made it strictly harder to satisfy, and a rule no quorum can trigger
would be sound and useless. This says the repaired rule is still
reachable — a set meeting the hybrid quorum whose voting-round blocks
reference no candidate skips the slot, with no anchor and no synchrony.

The blamer set is the core's shape, so the containment argument is the
core's; only the threshold differs. -/
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
  AnchoredRule.indirectOn Hybrid.linkCongr fun hi h => Hybrid.exists_least hi h

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
