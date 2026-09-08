import LeanDag.Common.Anchored.Bounded
import LeanDag.Properties.Sustain
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Optional.Skip
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Properties.Support
import LeanDag.Properties.Derived.Bounded
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Band
import LeanDag.Properties.Deliver
import LeanDag.Properties.Derived.FromBand
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import LeanDag.Mysticeti.Liveness
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# The core rule as a carrier, and what it makes of a sustaining mechanism

The core protocol is a single file, `Mysticeti.lean`, rather than a
directory, so its properties-arc material lives here: `mysticetiRule`,
the core rule as a `Properties.DagRule`, stated independently of any
mechanism; and what a sustaining mechanism gives the core's liveness —
`Sustains` transports the certificate layer
(`certifiesAt_of_sustains`), so any mechanism that sustains preserves
the reactive discipline's commit on the transformed DAG, with no pacing
structure carried across.
-/

namespace LeanDag

/-! Schedule congruence of the candidate and the slot-level skip is in
`Anchored.lean` (`isLeaderBlock_congr`) and `Mysticeti.lean`
(`blameSkip_congr`). -/

namespace MysticetiProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [Faults Validator]

/-- **The core rule as a carrier.** -/
def mysticetiRule : DagRule Validator BlockId Payload :=
  (coreAnchored Validator BlockId Payload).toDagRule

variable {U U' : BlockUniverse Validator BlockId Payload} {G R₀ : ℕ}

/-- The carrier's production predicate is the core's, on the nose: both
are `PopulatedFrom` over the same block assignment and the same ids.
They differed by the order of two conjuncts until `LiveReachable` needed
them interchangeable in five files at once. -/
theorem populatedOn_ofCore {T : Finset Validator} {r : ℕ}
    (h : LeanDag.PopulatedOn U T r) : Properties.PopulatedOn mysticetiRule U T r := h

theorem populatedOn_toCore {T : Finset Validator} {r : ℕ}
    (h : Properties.PopulatedOn mysticetiRule U T r) : LeanDag.PopulatedOn U T r := h

/-- The carrier's synchrony predicate is the core's, on the nose. -/
theorem synchronisedOn_eq {T : Finset Validator} {r : ℕ} :
    Timed.SynchronisedOn mysticetiRule U T r ↔ LeanDag.SynchronisedOn U T r :=
  Iff.rfl

/-- The votes an old decision-round block counts are the votes it
counted: its references are unchanged, and so are theirs. -/
theorem votesIn_of_sustains (h : Sustains mysticetiRule U U' G R₀) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : R₀ + 1 < (U.block C).round) :
    votesIn U' C L = votesIn U C L := by
  unfold votesIn carriedVotes
  have hrefs : (U'.block C).refs = (U.block C).refs :=
    h.refs C hC (by change R₀ < (U.block C).round; omega)
  rw [hrefs]
  refine Finset.filter_congr fun q hq => ?_
  have hqU : q ∈ U.ids := U.complete C hC q hq
  have hqr := U.round_of_mem_refs hC hq
  have : (U'.block q).refs = (U.block q).refs :=
    h.refs q hqU (by change R₀ < (U.block q).round; omega)
  unfold IsVote; rw [this]

/-- **The core's certificate predicate transports.** -/
theorem certifies_of_sustains (h : Sustains mysticetiRule U U' G R₀) {C L : BlockId}
    (hC : C ∈ U.ids) (hCr : R₀ + 1 < (U.block C).round) :
    Certifies U' C L ↔ Certifies U C L := by
  unfold Certifies CarriesVotes
  rw [show carriedVotes U' (IsVote U') C L = carriedVotes U (IsVote U) C L from
    votesIn_of_sustains h hC hCr]
  have : creatorsOf U'.block (carriedVotes U (IsVote U) C L) =
      creatorsOf U.block (carriedVotes U (IsVote U) C L) := by
    refine Finset.image_congr fun q hq => ?_
    have hqref := (mem_carriedVotes.mp hq).1
    have hqU : q ∈ U.ids := U.complete C hC q hqref
    have hqr := U.round_of_mem_refs hC hqref
    exact h.creator q hqU (by change R₀ ≤ (U.block q).round; omega)
  rw [this]

/-- **Certification at a slot survives a sustaining mechanism**, above
its settling round. -/
theorem certifiesAt_of_sustains (h : Sustains mysticetiRule U U' G R₀)
    {T : Finset Validator} {r : ℕ} {L : BlockId} (hr : R₀ ≤ r) (hG : G ≤ r)
    (hc : CertifiesAt U T r L) : CertifiesAt U' T (r - G) L := by
  intro v hv c hc' hcc hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc' (by change R₀ ≤ (U'.block c).round + G; omega)
  have hround' : (U'.block c).round + G = (U.block c).round := hround
  have hUr : (U.block c).round = r + 2 := by omega
  have hcreator : (U'.block c).creator = (U.block c).creator :=
    h.creator c hcU (by change R₀ ≤ (U.block c).round; omega)
  have hcc' : (U.block c).creator = v := by rw [← hcreator]; exact hcc
  exact (certifies_of_sustains h hcU (by omega)).mpr (hc v hv c hcU hcc' hUr)

/-- **The reactive commit survives any sustaining mechanism.** The
hypotheses are exactly what `Reactive/Mysticeti.directCommit` establishes
on the original DAG — certification by `cert_or_wait`, and production —
and the conclusion is the commit on the transformed one. -/
theorem directCommit_of_sustains (h : Sustains mysticetiRule U U' G R₀)
    {T : Finset Validator} {r : ℕ} {L : BlockId} (hr : R₀ ≤ r) (hG : G ≤ r)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommit U' L (r - G) :=
  directCommit_of_certifiesAt hcard
    (by
      have := h.populatedOn_of (T := T) (r := r + 2) (by omega) (by omega)
        (populatedOn_ofCore hpop)
      have e : r + 2 - G = r - G + 2 := by omega
      rw [e] at this
      exact populatedOn_toCore this)
    (certifiesAt_of_sustains h hr hG hc)

/-! ## Persistence

The core persists unconditionally: `Decided.directSkip` takes
`DirectSkipSlotIn`, a count of blockers at the slot rather than at a
candidate, so a skip is never vacuous on a candidate an extension adds
later. -/

/-- **The core's universes are quorate**, at the core's fault model:
validity's counting clause read at the carrier. This is what chain
quality reads (`Properties/Arcs/Quality.lean`), and it is one line
because `ValidWrt` already says it. -/
theorem quorate : Quorate (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun U => BlockUniverse.quorateOn U

/-- **P3′ at the carrier**: every non-genesis block references its
author's previous block. -/
theorem selfParent : SelfParent (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  fun U b hb hr => (U.valid b hb).self_parent hr

/-- **One block per correct author per round**, from the universe's
non-equivocation clause. -/
theorem noEquiv : NoEquiv (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.no_equivocation b hb c hc hbc heq hr

/-- Two quorums share a correct validator, so a quorum is not empty. -/
theorem quorumCard_pos : 0 < quorumCard Validator := by
  have := (inferInstance : Faults Validator).card_validators; omega

section PersistProof

variable {U U' : BlockUniverse Validator BlockId Payload}

theorem ext_block (he : Extends mysticetiRule U U') {b : BlockId} (hb : b ∈ U.ids) :
    U'.block b = U.block b := he.block b hb

theorem ext_mem (he : Extends mysticetiRule U U') {b : BlockId} (hb : b ∈ U.ids) :
    b ∈ U'.ids := he.subset b hb

/-- An old block votes for nothing the extension added. -/
theorem not_mem_refs_novel (he : Extends mysticetiRule U U') {b L : BlockId}
    (hb : b ∈ U.ids) (hL : L ∉ U.ids) : L ∉ (U'.block b).refs := by
  rw [ext_block he hb]; exact fun hin => hL (U.complete b hb L hin)

theorem blocksAt_subset (he : Extends mysticetiRule U U') (r : ℕ) :
    blocksAt U r ⊆ blocksAt U' r := by
  intro b hb
  rw [mem_blocksAt] at hb ⊢
  exact ⟨ext_mem he hb.1, by rw [ext_block he hb.1]; exact hb.2⟩

theorem creatorsOf_old (he : Extends mysticetiRule U U') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids) : creatorsOf U'.block s = creatorsOf U.block s :=
  Finset.image_congr fun i hi => by rw [ext_block he (hs i hi)]

theorem isLeaderBlock_mono [S : Slots Validator] (he : Extends mysticetiRule U U') {k : ℕ} {L : BlockId}
    (h : IsLeaderBlock U k L) : IsLeaderBlock U' k L := by
  obtain ⟨hm, hr, hc⟩ := h
  exact ⟨ext_mem he hm, by rw [ext_block he hm]; exact hr, by rw [ext_block he hm]; exact hc⟩

theorem isLeaderBlock_old [S : Slots Validator] (he : Extends mysticetiRule U U') {k : ℕ} {L : BlockId}
    (hL : L ∈ U.ids) (h : IsLeaderBlock U' k L) : IsLeaderBlock U k L := by
  obtain ⟨_, hr, hc⟩ := h
  rw [ext_block he hL] at hr hc
  exact ⟨hL, hr, hc⟩

/-- The votes an old certificate counts are the votes it counted. -/
theorem votesIn_old (he : Extends mysticetiRule U U') {C L : BlockId} (hC : C ∈ U.ids) :
    votesIn U' C L = votesIn U C L := by
  unfold votesIn carriedVotes
  rw [ext_block he hC]
  refine Finset.filter_congr fun q hq => ?_
  unfold IsVote; rw [ext_block he (U.complete C hC q hq)]

theorem certifies_old (he : Extends mysticetiRule U U') {C L : BlockId} (hC : C ∈ U.ids) :
    Certifies U' C L ↔ Certifies U C L := by
  unfold Certifies CarriesVotes
  rw [show carriedVotes U' (IsVote U') C L = carriedVotes U (IsVote U) C L from votesIn_old he hC,
    creatorsOf_old he]
  intro q hq
  exact U.complete C hC q (mem_carriedVotes.mp hq).1

theorem mem_certificates_old (he : Extends mysticetiRule U U') {C L : BlockId} {r : ℕ}
    (hC : C ∈ U.ids) : C ∈ certificates U' L r ↔ C ∈ certificates U L r := by
  simp only [mem_certificatesAt]
  have hb := ext_block he hC
  have hce := certifies_old he hC (L := L)
  constructor
  · rintro ⟨-, hr, hcert⟩; exact ⟨hC, by rw [← hb]; exact hr, hce.mp hcert⟩
  · rintro ⟨-, hr, hcert⟩; exact ⟨ext_mem he hC, by rw [hb]; exact hr, hce.mpr hcert⟩

/-! ### The direct rules -/

theorem directCommitIn_mono (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ}
    (h : DirectCommitIn U V L r) : DirectCommitIn U' V' L r := by
  refine le_trans h (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCV, hvC⟩ := mem_heldAuthors.mp hv
  have hCU : C ∈ U.ids := (mem_certificatesAt.mp hC).1
  refine mem_heldAuthors.mpr ⟨C, (mem_certificates_old he hCU).mpr hC, hV hCV, ?_⟩
  rw [ext_block he hCU]; exact hvC

/-- **An old candidate blamed before is blamed still.** -/
theorem directSkipIn_mono (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ}
    (h : DirectSkipIn U V L r) : DirectSkipIn U' V' L r := by
  refine le_trans h (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqV, hvq⟩ := mem_heldAuthors.mp hv
  obtain ⟨hqU, hqr, hqn⟩ := mem_omissionsOf.mp hq
  refine mem_heldAuthors.mpr ⟨q, mem_omissionsOf.mpr ⟨ext_mem he hqU, ?_, ?_⟩, hV hqV, ?_⟩
  · rw [ext_block he hqU]; exact hqr
  · rw [ext_block he hqU]; exact hqn
  · rw [ext_block he hqU]; exact hvq

/-- **A new candidate is blamed by every old block in view** — and the
grade supplies a quorum of them. This is the one place the condition is
consumed. -/
theorem directSkipIn_novel (he : Extends mysticetiRule U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hV : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ} (hL : L ∉ U.ids)
    (hq : quorumCard Validator ≤ (creatorsOf U.block ((blocksAt U (r + 1)) ∩ V.ids)).card) :
    DirectSkipIn U' V' L r := by
  unfold DirectSkipIn
  refine le_trans hq (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq', hvq⟩ := Finset.mem_image.mp hv
  obtain ⟨hqA, hqV⟩ := Finset.mem_inter.mp hq'
  have hqU : q ∈ U.ids := (mem_blocksAt.mp hqA).1
  refine Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨blocksAt_subset he _ hqA, not_mem_refs_novel he hqU hL⟩, hV hqV⟩, ?_⟩
  rw [ext_block he hqU]; exact hvq

/-! ### The rung test -/

theorem certifiedIn_old (he : Extends mysticetiRule U U') {A L : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) : CertifiedIn U' A L r ↔ CertifiedIn U A L r := by
  unfold CertifiedIn
  constructor
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hreU, hCU⟩ := Extends.reaches_old he hA hre
    exact ⟨C, (mem_certificates_old he hCU).mp hC, hreU⟩
  · rintro ⟨C, hC, hre⟩
    have hCU : C ∈ U.ids := (mem_blocksAt.mp (Finset.mem_filter.mp hC).1).1
    exact ⟨C, (mem_certificates_old he hCU).mpr hC,
      (Extends.reaches_iff he hA).mpr hre⟩

/-- **A new candidate is certified by nothing an old anchor can see.** -/
theorem not_certifiedIn_novel (he : Extends mysticetiRule U U') {A L : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) (hL : L ∉ U.ids) : ¬ CertifiedIn U' A L r := by
  rintro ⟨C, hC, hre⟩
  obtain ⟨-, hCU⟩ := Extends.reaches_old he hA hre
  have hcert : Certifies U' C L := (mem_certificatesAt.mp hC).2.2
  unfold Certifies CarriesVotes at hcert
  have hempty : votesIn U' C L = ∅ := by
    rw [votesIn_old he hCU, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqref, hqv⟩ := mem_carriedVotes.mp hq
    exact hL (U.complete q (U.complete C hCU q hqref) L hqv)
  rw [show carriedVotes U' (IsVote U') C L = ∅ from hempty] at hcert
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty, Nat.le_zero] at hcert
  exact absurd hcert (Nat.pos_iff_ne_zero.mp quorumCard_pos)

/-! ### The band, and the helpers it needs

The same lemmas as above, with the extension replaced by agreement on
a range of rounds; one-directional, since `U'` may hold blocks `U`
does not. -/

section Band

variable {lo hi g g' : ℕ}

/-! The band's field projections, layer and creator transports and
candidate transport are `Anchored/Band.lean`'s, at `mysticetiRule`. -/

variable {S S' : Slots Validator}

end Band

/-! ### Persistence -/

/-- **What the core owes the band**: its direct commit, its slot-level
skip and the certificate in the anchor's cone carry across a band
covering the slot's wave, and a candidate the band did not carry is
certified from no old anchor. -/
theorem coreBandLaws : (coreAnchored Validator BlockId Payload).BandLaws where
  commit_band := fun h hkk _ hlo hhi hV _ hc =>
    AnchoredRule.holdsAtLeast_certificatesAt_band h hV (by omega) (by omega)
      (by simp only [coreAnchored_wave] at hhi; omega)
      (AnchoredRule.isVote_band_at h (by omega) (by simp only [coreAnchored_wave] at hhi; omega)) hc
  skip_band := fun h hkk hlk hlo hhi hV hs =>
    le_trans hs (Finset.card_le_card (AnchoredRule.slotBlamesIn_band h hkk hlk hlo.le
      (by simp only [coreAnchored_wave] at hhi; omega) hV))
  link_band := fun h hA hAlo hAhi hkk _ hlo hhi _ _ =>
    AnchoredRule.linkedVia_certificatesAt_band h hA hAlo hAhi (by omega) (by omega)
      (by simp only [coreAnchored_wave] at hhi; omega)
      (AnchoredRule.isVote_band_at h (by omega) (by simp only [coreAnchored_wave] at hhi; omega))
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi _ _ hL
    simp only [coreAnchored_wave] at hhi
    exact AnchoredRule.not_linkedVia_certificatesAt_band_novel h hA hAlo hAhi
      (n := S.slotRound k + 2) (by omega) (by omega) (by omega)
      (AnchoredRule.not_isVote_band_novel h hL) quorumCard_pos

/-- **The core reads a band.** -/
theorem banded : Banded
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.banded coreBandLaws

/-- The carrier's coverage predicate is the core's, on the nose. -/
theorem coversUpto_eq {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {N : ℕ} :
    Properties.CoversUpto mysticetiRule V N ↔ V.CoversUpto N := Iff.rfl

/-- **A commit names the slot's candidate.** `isLeaderBlock_of_decided`
under the property's name — one of seven such lemmas across the
protocols, and the reason `Properties/Candidate.lean` exists. -/
theorem commitsCandidate : CommitsCandidate
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.commitsCandidate

/-- **A direct commit is a verdict**, at the core's own direct-commit
predicate: `Decided.directCommit` under the property's name. -/
theorem commitsDirect : CommitsDirect
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {U} V L r => DirectCommitIn U V L r) :=
  fun S _ _ _ _ hc hd => Decided.directCommit (S := S) hc hd

/-- **The core persists unconditionally**, as an evidence-backed rule
must — now a corollary of the band rather than an induction of its own.
The grade `Quorate` that stood here before was not a property of the
protocol but the missing half of its skip rule. -/
theorem persist : Persist
    (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Persist.of_banded banded

end PersistProof

/-! ## Skippability, at a correct quorum

If every `T`-block at the voting round references none of a slot's
candidates, each is a blamer for every candidate at once, so a correct
quorum skips an unsupported slot. Hydrozoan needs a higher threshold,
which is the price of the unconditional
persistence the core had to be repaired to reach. -/

section Skip

variable {U : BlockUniverse Validator BlockId Payload} [S : Slots Validator]

/-- Every member of `T` blames the slot: its voting-round block is in
view and references no candidate, which is what `Unsupported` says. -/
theorem subset_blamers {V : View Validator BlockId Payload U} {T : Finset Validator} {k : ℕ}
    (hpres : PresentAt mysticetiRule V T (S.slotRound k + 1))
    (huns : Unsupported mysticetiRule S U V T k) :
    T ⊆ creatorsOf U.block (slotBlamers U k ∩ V.ids) := by
  intro v hv
  obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
  have hcU : c ∈ U.ids := V.subset_ids hcV
  refine Finset.mem_image.mpr ⟨c, ?_, hcc⟩
  rw [Finset.mem_inter, slotBlamers, Finset.mem_filter]
  exact ⟨⟨mem_blocksAt.mpr ⟨hcU, hcr⟩,
    fun j hj hjL => huns c hcV (by rw [hcc]; exact hv) hcr j hjL hj⟩, hcV⟩

/-- **The core skips an unsupported slot from a correct quorum.** -/
theorem skipsUnsupported :
    SkipsUnsupported (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun T => quorumCard Validator ≤ T.card) :=
  fun S U V T k hq hpres huns =>
    Decided.directSkip (le_trans hq (Finset.card_le_card (subset_blamers (S := S) hpres huns)))

/-- **L5 from the properties.** A slot whose leader produced nothing at
all is skipped, on any view holding a quorum of the round above:
`Unsupported` is vacuous with no candidate to support. -/
theorem decided_none_of_leader_absent_of_properties [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hhalt : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k)
    (hq : quorumCard Validator ≤
      (creatorsOf U.block (blocksAt U (S.slotRound k + 1) ∩ V.ids)).card) :
    Decided U V k none := by
  classical
  set T := creatorsOf U.block (blocksAt U (S.slotRound k + 1) ∩ V.ids) with hT
  have hpres : Properties.PresentAt (mysticetiRule (Payload := Payload)) V T
      (S.slotRound k + 1) := by
    intro v hv
    rw [hT, creatorsOf, Finset.mem_image] at hv
    obtain ⟨c, hc, hcv⟩ := hv
    rw [Finset.mem_inter, mem_blocksAt] at hc
    exact ⟨c, hc.2, hcv, hc.1.2⟩
  have huns : Properties.Unsupported (mysticetiRule (Payload := Payload)) S U V T k := by
    intro c _ _ _ L hL _
    exact hhalt L hL.1 hL.2.1 hL.2.2
  exact skipsUnsupported S U V T k hq hpres huns

end Skip

end MysticetiProperties

/-! ## The core's bounded decision relation

`DecidedWithin` is `Anchored/Bounded.lean`'s at the core: `Decided`
with every slot the derivation mentions strictly below a bound `B`.
`decidedBelow_of_decidedWithin` carries it into the mechanism's
`Properties.DecidedBelow`. -/

section BoundedRelation

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- **The bounded decision relation**, at the core. -/
abbrev DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop :=
  (coreAnchored Validator BlockId Payload).DecidedWithin (S := S) U V B

namespace DecidedWithin
export AnchoredRule.DecidedWithin (directCommit directSkip indirectCommit indirectSkip)
end DecidedWithin

end BoundedRelation

/-! ## Conformance to the schedule family

`Agree` for safety; `LeaderCommits` under the timed precondition
`coreLive`, and `Descends` under `SpansEligible`, for liveness. -/

namespace MysticetiProperties

open Properties

section Bounded

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **M6 as a property.** -/
theorem agree :
    Agree (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.agree coreLaws

/-- **The timed core's liveness precondition**, over a slot window: a
quorum synchronised and populating from some round to a horizon, the
view caught up to it, and every slot two rounds under it. Reads no
leader, so it holds under every schedule with the same rounds. -/
def coreLive (S : Slots Validator) {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧
    ∃ R₀ N, SynchronisedOn U T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) ∧ V.CoversUpto N ∧
      ∀ k, k < K → S.slotRound k + 2 ≤ N

/-- The precondition, from the global hypotheses: what every staged
statement of the core assembles. -/
theorem coreLive_of {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {T : Finset Validator} {lo K R₀ N : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R₀)
    (hRW : R₀ ≤ S.slotRound lo) (hpop : ∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r)
    (hcov : V.CoversUpto N) (hN : ∀ k, k < K → S.slotRound k + 2 ≤ N) :
    coreLive S V T lo K :=
  ⟨hcard, R₀, N, hs, hRW, hpop, hcov, hN⟩

/-! ## One precondition for two execution models

`coreLive` asks for coverage and `reactiveLive` asks for a reactive
execution past GST, and the two are incomparable, a reactive builder's
`SynchronisedOn` being false by design. `certLive` is what both
deliver — the reliable set certifies the slot's leader block —
`LeaderCommits` is proved once against it, and each execution model
contributes its own bridge: coverage through
`certifiesAt_of_synchronisedOn`, the reactive discipline through
`ReactiveM.certifies`. -/

/-- **The core's precondition, in what its commit rule counts.** A
quorum, a horizon the view is caught up to with every slot two rounds
under it, production at the propose and certificate rounds, and `T`
certifying every candidate of every `T`-led slot in the window. -/
def certLive (S : Slots Validator) {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧
    ∃ N, V.CoversUpto N ∧ (∀ k, k < K → S.slotRound k + 2 ≤ N) ∧
      ∀ k, lo ≤ k → k < K → S.leader k ∈ T →
        PopulatedOn U T (S.slotRound k) ∧ PopulatedOn U T (S.slotRound k + 2) ∧
          ∀ L, IsLeaderBlock (S := S) U k L → CertifiesAt U T (S.slotRound k) L

/-- **A reliably-led slot commits, from the certificates alone.** The
one `LeaderCommits` proof the core needs; every execution model reaches
it through its own bridge. -/
theorem leaderCommits_cert :
    LeaderCommits (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => certLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hcard, N, hcov, hN, hslot⟩ := hlive
  obtain ⟨hpop0, hpop2, hcert⟩ := hslot k hlo hK hlead
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop0 (S.leader k) hlead
  have hL : IsLeaderBlock (S := S) U k L := ⟨hLmem, hLr, hLc⟩
  have hdc : DirectCommit U L (S.slotRound k) :=
    directCommit_of_certifiesAt hcard hpop2 (hcert L hL)
  have hin : DirectCommitIn U V L (S.slotRound k) :=
    directCommitIn_of_coversUpto hdc (hcov.mono (hN k hK))
  refine ⟨L, by omega, Decided.directCommit hL hin, ?_⟩
  intro S' hround hlead'
  refine Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-- **Coverage is one bridge.** Full reference coverage certifies every
candidate of every reliably-led slot, which is
`certifiesAt_of_synchronisedOn` at each slot of the window. -/
theorem certLive_of_coreLive {S : Slots Validator}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {T : Finset Validator} {lo K : ℕ} (h : coreLive S (U := U) V T lo K) :
    certLive S (U := U) V T lo K := by
  obtain ⟨hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := h
  refine ⟨hcard, N, hcov, hN, ?_⟩
  intro k hlo hK _
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk := hN k hK
  refine ⟨hpop _ hRk (by omega), hpop _ (by omega) (by omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩
  exact certifiesAt_of_synchronisedOn hcard hs hRk (hpop _ (by omega) (by omega))
    hLmem hLr (by rw [hLc]; assumption)

/-- **The timed theorem, as a corollary.** Its statement is unchanged;
its proof is now the bridge composed with the one `LeaderCommits`. -/
theorem leaderCommits :
    LeaderCommits (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => coreLive S (U := U) V T lo K) :=
  fun S _ V T lo K hlive => leaderCommits_cert S V T lo K (certLive_of_coreLive hlive)

/-! ## The core's support shape

`Properties/Support.lean`, at what the core's commit counts:
certificates two rounds above the candidate, whose parents' votes for
the candidate form a quorum. The three laws are `certifies_of_sustains`,
`certifies_of_synchronisedOn` and `leaderCommits_cert`, each unpacked. -/

/-- **The core's support**: wavelength two, certification the rule's own. -/
def coreSupport : Support (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  wave := 2
  Certifies := fun U c L => Certifies U c L

/-- **Law 1.** A certifier two rounds above the settling round reads
references strictly above it, which `RebasedAbove` preserves. -/
theorem coreSupport_local :
    Support.Local (R := mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) coreSupport := by
  intro U U' G R₀ h c L hc hcr _ _
  exact certifies_of_sustains h hc (by change R₀ + 2 ≤ (U.block c).round at hcr; omega)

/-- **Law 2.** Coverage toward the candidate over two layers: every
quorum block one round up references it, and every quorum block two
rounds up references each of those, so the certifier's voting parents
are the whole quorum. -/
theorem coreSupport_ofCoverage :
    Timed.OfCoverage (R := mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) coreSupport (coreReliability Validator) := by
  intro U T hq r L hpop hct hL hLr hLc c hc hcc hcr
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  have hcr' : (BlockRecord.block U c).round = r + 2 := hcr
  have hcc' : (BlockRecord.block U c).creator ∈ T := hcc
  have hLr' : (BlockRecord.block U L).round = r := hLr
  have hLc' : (BlockRecord.block U L).creator ∈ T := hLc
  change quorumCard Validator ≤ (creatorsOf U.block (votesIn U c L)).card
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq', hqc, hqr⟩ := hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega) v hv
  have hqc' : (BlockRecord.block U q).creator = v := hqc
  have hqr' : (BlockRecord.block U q).round = r + 1 := hqr
  have hqT : (BlockRecord.block U q).creator ∈ T := by rw [hqc']; exact hv
  have hvote : L ∈ (BlockRecord.block U q).refs :=
    hct r le_rfl (by change r < r + 2; omega) q hq' hqT hqr' L hL hLc' hLr'
      Relation.ReflTransGen.refl
  have hpar : q ∈ (BlockRecord.block U c).refs :=
    hct (r + 1) (by omega) (by change r + 1 < r + 2; omega) c hc hcc'
      (by change (BlockRecord.block U c).round = r + 1 + 1; rw [hcr']) q hq' hqT hqr'
      (Relation.ReflTransGen.single hvote)
  rw [mem_creatorsOf]
  exact ⟨q, Finset.mem_filter.mpr ⟨hpar, hvote⟩, hqc'⟩

/-- **Law 3**, as a corollary of `leaderCommits_cert`: the support's
precondition at one slot is `certLive` at that slot, and `certLive`
asks less — any quorum by count, not one inside the correct set — so
the direct proof is the one that stays and this is derived. -/
theorem coreSupport_commits :
    Support.Commits (R := mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) coreSupport (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  refine leaderCommits_cert S V T k (k + 1) ⟨hcard, S.slotRound k + 2, hcov, ?_, ?_⟩ k le_rfl
    (Nat.lt_succ_self k) hlead
  · intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    omega
  · intro j hlo hj _
    have hjk : j = k := by omega
    rw [hjk]
    exact ⟨hpop _ le_rfl (by change S.slotRound k ≤ S.slotRound k + 2; omega),
      hpop _ (by omega) (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega),
      fun L hL => hcert L hL⟩

/-- **A3 as a property**: the relation's indirect property at the core,
with no tie to break, read at the three-round eligibility. -/
theorem indirect :
    Indirect (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (fun sr i j => sr i + 3 ≤ sr j) :=
  (AnchoredRule.indirect coreLaws.link_congr fun hi h => exists_least hi h).congr
    (fun _ _ _ => by simp only [coreAnchored_wave] <;> omega)

/-- **L4's capstone form, from the properties.** The shape every
consumer of direct liveness uses — synchrony from `R`, production to a
horizon `N`, a `T`-led slot two rounds under it — reached from
`LeaderCommits` and `CommitsCandidate` at the single-slot window,
rather than from `decided_of_leader_of_populated`. This is the same
bridge `Timed.Good` is for Barnacle
(`docs/target-properties.md` §11.2b), and it is the reason the
capstones do not need their own route into the protocol. -/
theorem decided_of_leader_of_populated_of_properties [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {R N k : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R)
    (hR : R ≤ S.slotRound k) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  have hwin : ∀ j, j < k + 1 → S.slotRound j + 2 ≤ N := by
    intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    omega
  have hlive : coreLive S (U := U) (View.full U) T k (k + 1) :=
    ⟨hcard, R, N, hs, hR, hpop, View.coversUpto_full U N, hwin⟩
  obtain ⟨L, hL⟩ :=
    leaderCommits S (U := U) (View.full U) T k (k + 1) hlive k le_rfl
      (Nat.lt_succ_self k) hlead
  exact ⟨L, commitsCandidate S U (View.full U) k L hL.2.1, hL.2.1⟩

/-- **L6, from the properties.** Commits recur under a fair schedule:
some slot past `k` and past round `R` is led by a member of `T`, and
every DAG grown past it commits it. -/
theorem commits_recur_on_of_properties [S : Slots Validator] {T : Finset Validator}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧ CommitsAt BlockId Payload T R k' := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨k', hk', hlead⟩ := fair (max k k₀)
  have hRk' : R ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hk'))
  refine ⟨k', le_trans (le_max_left _ _) hk', hRk', ?_⟩
  intro U N hpop hs hN
  exact decided_of_leader_of_populated_of_properties (S := S) hcard hs hRk' hpop hN hlead

/-! The core's bounded relation lands in the derived one by the
relation's `decidedBelow_of_decidedWithin` at `coreLaws`. -/

/-- **The descent as a property**, under the spanning hypothesis on the
round structure: `Descends.of_indirect` at `Eligible` read as the round
inequality the property is stated with. -/
theorem descends {S : Slots Validator} {c : ℕ} (hc : 0 < c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible (S := S) c) :
    Descends (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) S c :=
  Descends.of_indirect indirect hc (fun b i hi => by
    have := (coreAnchored Validator BlockId Payload).eligible_iff.mp (hspans b i hi)
    simp only [coreAnchored_wave] at this; omega)

end Bounded

end MysticetiProperties

/-! ## L10 — the ledger does not stall

`FairRunOn T c` gives `c` consecutive `T`-led slots arbitrarily far
out, and `SpansEligible c` says the run reaches far enough for every
slot below it to anchor on its last member; `Timed.decidedBelow_of_fairRun`
at the core's support settles everything below. The run is named by the
schedule alone, before any DAG is mentioned, so the horizon cannot cap
how far fairness may reach: `c = 1` under three-round spacing, `c = 3`
under pipelining, where round-robin over `3f+1` supplies three
consecutive correct leaders for every `f ≥ 1`. -/

section Ledger

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator] {T : Finset Validator}

/-- **L10.** For every slot `k` there is a `b ≥ k` such that every slot
below `b` is decided, in any sufficiently grown synchronous DAG: the
ledger advances rather than merely committing, unlike L6. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hspan : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn T c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨b, hb, hRb, h⟩ :=
    Timed.decidedBelow_of_fairRun (MysticetiProperties.coreSupport (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload))
      MysticetiProperties.coreSupport_ofCoverage MysticetiProperties.coreSupport_commits
      (MysticetiProperties.descends hc hspan) (T := T)
      ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩ fair R k
  refine ⟨b, hb, hRb, fun U N hpop hs hN i hi => ?_⟩
  obtain ⟨v, hv⟩ := h (View.full U) N (MysticetiProperties.synchronisedOn_eq.mpr hs)
    (fun r h1 h2 => MysticetiProperties.populatedOn_ofCore (hpop r h1 h2))
    (MysticetiProperties.coversUpto_eq.mpr (View.coversUpto_full U N)) hN i hi
  exact ⟨v, hv.2.1⟩

/-- **L10 at `T := Correct`.** -/
theorem all_decided_below_of_fairRun_correct {c : ℕ} (hc : 0 < c)
    (hspan : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn (Correct : Finset Validator) c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl card_correct hspan fair R k

end Ledger

namespace MysticetiProperties

/-! ## The headlines -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Safety**, across any stack of mechanisms, for the core and for its
reactive execution alike. -/
theorem safety : Properties.Safe (mysticetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

/-- **Liveness**, at the core's support: certification is the only
antecedent, so the timed and the reactive execution share it. -/
theorem liveness : Properties.Support.Lives (coreSupport (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload)) (coreReliability Validator) :=
  Properties.Support.liveness coreSupport_commits commitsCandidate selfParent noEquiv

end MysticetiProperties

end LeanDag
