import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.OptimalHydrozoan.Helpers.SlotAgreement
/-!
# Optimal-Hydrozoan's rules read a band of rounds

Not part of the audit surface. What `Properties.Banded` needs of this
protocol, on top of Hydrozoan's band file: Optimal shares Hydrozoan's
blocks, votes, LeanDag.Hydrozoan.certificates and slotBlames, so `Hydrozoan/Helpers/Banded.lean`
carries the whole direct layer and rung 1 unchanged, and what is left is
the fast path — fast evidence, the no-evidence quorum, and the anchored
evidence rung.

**Every new rule is a count over one block's refs**, which is what
makes them transportable. `IsFastEvidence U k C L` reads `C`'s refs
and the votes they cast, so a band two rounds above the floor fixes it
exactly, for *every* candidate whatever — old ones because references
are unchanged, and ones the band added because an old block's refs
reference only old blocks, so a new candidate collects no votes at all.

**That is what saves the skip.** `IsNoFastEvidence` quantifies over the
slot's candidates and denies evidence for each, and a band may add a
candidate — the shape §3.2 recorded as a defect in the core and §3.12 in
Odontoceti. Here the added candidate has an empty vote count and both
`tPlain` and `tEquiv` are at least one, so no old block is evidence for
it and the quorum survives. The same argument disposes of the two
negative clauses of the graded rungs.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan
open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [O : OptimalFaults Replica]
variable [S : LeanDag.Slots Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {lo hi g g' : ℕ}
variable {R : AnchoredRule Replica BlockId Unit LeanDag.Hydrozoan.ValidWrt
  (LeanDag.Hydrozoan.NonByzantine : Finset Replica)}

/-! ## The votes a decision-round block references -/

/-- **A block's refs vote the same way in both universes**, for every
candidate whatever. Two rounds of slack, as for a certificate: the count
reads the refs' own refs. -/
theorem votesFor_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {C : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) (L : BlockId) :
    votesFor U' C L = votesFor U C L := by
  unfold votesFor
  rw [voteBlocks_bnd h hC h1 h2, AnchoredRule.creatorsOf_band h]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  have := (U.valid C hC).predecessor b hbp
  exact ⟨U.complete C hC b hbp, by omega, by omega⟩

/-- **And a candidate the band added collects none.** An old block's
refs are old and reference only old blocks. -/
theorem votesFor_eq_empty_of_novel (h : AgreeBand R.toDagRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) (hL : L ∉ U.ids) :
    votesFor U' C L = ∅ := by
  rw [votesFor_bnd h hC h1 h2]
  have hempty : LeanDag.Hydrozoan.voteBlocks U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    exact hL (U.complete b (U.complete C hC b hbp) L hbv)
  unfold votesFor
  rw [hempty]
  simp [LeanDag.creatorsOf]

/-- **Witnessing an equivocation is the same event.** Both directions: a
witness on the larger side is voted for by an old parent, so it is a
candidate the band already had. -/
theorem witnessesEquivocation_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (hk1 : lo ≤ S.slotRound k + g) (hk2 : S.slotRound k + g ≤ hi)
    {C : BlockId} (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    WitnessesEquivocation (S := S') U' k' C ↔ WitnessesEquivocation (S := S) U k C := by
  have hpar : (U'.block C).refs = (U.block C).refs := AnchoredRule.band_refs h hC (by omega) h2
  have hold : ∀ j ∈ (U.block C).refs,
      j ∈ U.ids ∧ (U.block j).round + 1 = (U.block C).round :=
    fun j hj => ⟨U.complete C hC j hj, (U.valid C hC).predecessor j hj⟩
  constructor
  · rintro ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    rw [hpar] at hj₁ hj₂
    obtain ⟨hj₁U, hj₁r⟩ := hold j₁ hj₁
    obtain ⟨hj₂U, hj₂r⟩ := hold j₂ hj₂
    have hv₁U : LeanDag.Hydrozoan.IsVote U j₁ L₁ := (isVote_bnd h hj₁U (by omega) (by omega)).mp hv₁
    have hv₂U : LeanDag.Hydrozoan.IsVote U j₂ L₂ := (isVote_bnd h hj₂U (by omega) (by omega)).mp hv₂
    exact ⟨L₁, L₂,
      AnchoredRule.isLeaderBlock_band_old h hkk hlead hk1 hk2 (U.complete j₁ hj₁U L₁ hv₁U) hL₁,
      AnchoredRule.isLeaderBlock_band_old h hkk hlead hk1 hk2 (U.complete j₂ hj₂U L₂ hv₂U) hL₂,
      hne, ⟨j₁, hj₁, hv₁U⟩, ⟨j₂, hj₂, hv₂U⟩⟩
  · rintro ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    obtain ⟨hj₁U, hj₁r⟩ := hold j₁ hj₁
    obtain ⟨hj₂U, hj₂r⟩ := hold j₂ hj₂
    exact ⟨L₁, L₂, AnchoredRule.isLeaderBlock_band h hkk hlead hk1 hk2 hL₁,
      AnchoredRule.isLeaderBlock_band h hkk hlead hk1 hk2 hL₂, hne,
      ⟨j₁, by rw [hpar]; exact hj₁, (isVote_bnd h hj₁U (by omega) (by omega)).mpr hv₁⟩,
      ⟨j₂, by rw [hpar]; exact hj₂,
        (isVote_bnd h hj₂U (by omega) (by omega)).mpr hv₂⟩⟩

/-- **Fast evidence is the same evidence.** The counts are equal, the
equivocation test is the same test, and the rival clause survives the
band's new candidates because they collect no votes and `t_equiv` is at
least one. -/
theorem isFastEvidence_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (hk1 : lo ≤ S.slotRound k + g) (hk2 : S.slotRound k + g ≤ hi)
    {C : BlockId} (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) (L : BlockId) :
    IsFastEvidence (S := S') U' k' C L ↔ IsFastEvidence (S := S) U k C L := by
  have htE : 1 ≤ tEquiv Replica := by
    unfold tEquiv pOpt; omega
  have hwit := witnessesEquivocation_bnd h hkk hlead hk1 hk2 hC h1 h2
  unfold IsFastEvidence
  constructor
  · rintro ⟨hp, he⟩
    refine ⟨fun hnw => ?_, fun hw => ?_⟩
    · rw [← votesFor_bnd h hC h1 h2]
      exact hp (fun hx => hnw (hwit.mp hx))
    · obtain ⟨hc, hriv⟩ := he (hwit.mpr hw)
      refine ⟨by rw [← votesFor_bnd h hC h1 h2]; exact hc, fun L' hL' hne => ?_⟩
      rw [← votesFor_bnd h hC h1 h2]
      exact hriv L' (AnchoredRule.isLeaderBlock_band h hkk hlead hk1 hk2 hL') hne
  · rintro ⟨hp, he⟩
    refine ⟨fun hnw => ?_, fun hw => ?_⟩
    · rw [votesFor_bnd h hC h1 h2]
      exact hp (fun hx => hnw (hwit.mpr hx))
    · obtain ⟨hc, hriv⟩ := he (hwit.mp hw)
      refine ⟨by rw [votesFor_bnd h hC h1 h2]; exact hc, fun L' hL' hne => ?_⟩
      by_cases hLo : L' ∈ U.ids
      · rw [votesFor_bnd h hC h1 h2]
        exact hriv L' (AnchoredRule.isLeaderBlock_band_old h hkk hlead hk1 hk2 hLo hL') hne
      · rw [votesFor_eq_empty_of_novel h hC h1 h2 hLo]
        simp only [Finset.card_empty]
        omega

/-- **A block that was evidence for no candidate still is.** The old
candidates by the equivalence above, and a candidate the band added
because it collects no votes and both thresholds are at least one. -/
theorem isNoFastEvidence_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (hk1 : lo ≤ S.slotRound k + g) (hk2 : S.slotRound k + g ≤ hi)
    {C : BlockId} (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi)
    (hne : IsNoFastEvidence (S := S) U k C) : IsNoFastEvidence (S := S') U' k' C := by
  intro L hL hfe
  by_cases hLo : L ∈ U.ids
  · exact hne L (AnchoredRule.isLeaderBlock_band_old h hkk hlead hk1 hk2 hLo hL)
      ((isFastEvidence_bnd h hkk hlead hk1 hk2 hC h1 h2 L).mp hfe)
  · have hempty := votesFor_eq_empty_of_novel h hC h1 h2 hLo
    obtain ⟨hp, hq⟩ := hfe
    by_cases hw : WitnessesEquivocation (S := S') U' k' C
    · have htE : 1 ≤ tEquiv Replica := by unfold tEquiv pOpt; omega
      have := (hq hw).1
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega
    · have htP := tPlain_pos (Replica := Replica)
      have := hp hw
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega

/-! ## The direct rules of the fast path -/

/-- The fast commit is Hydrozoan's vote count at a lower threshold, so
Hydrozoan's containment carries it. -/
theorem fastCommitOptInView_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo ≤ n + g)
    (h2 : n + 1 + g ≤ hi) (hc : FastCommitOptInView U V L n) :
    FastCommitOptInView U' V' L n' :=
  le_trans hc (Finset.card_le_card
    (supportersInView_bnd h hv (n := n + 1) (n' := n' + 1) (by omega) (by omega) (by omega)))

/-- **The no-evidence quorum is carried across.** Each block of it stays
at the decision round, stays in view, and stays evidence for no
candidate — the last by `isNoFastEvidence_bnd`, which is where a
candidate the band added is disposed of. -/
theorem noEvidenceQuorumInView_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    (hq : NoEvidenceQuorumInView (S := S) U V k) :
    NoEvidenceQuorumInView (S := S') U' V' k' := by
  have hdr : LeanDag.Hydrozoan.decisionRound (S := S) Replica k = S.slotRound k + 2 := rfl
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := hq
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = S.slotRound k + 2 := by
    intro b hb
    obtain ⟨hbA, -, -⟩ := hs b hb
    exact ⟨(Finset.mem_filter.mp hbA).1, (Finset.mem_filter.mp hbA).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbV, hbn⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    exact ⟨blocksAt_bnd h (n := LeanDag.Hydrozoan.decisionRound (S := S) Replica k)
        (n' := LeanDag.Hydrozoan.decisionRound (S := S') Replica k')
        (by omega) (by omega) (by omega) hbA,
      hv b hbV (by omega) (by omega),
      isNoFastEvidence_bnd h hkk hlead h1 (by omega) hbU (by omega) (by omega) hbn⟩
  · rw [AnchoredRule.creatorsOf_band h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

/-- **And so is the direct skip.** Blames by Hydrozoan's containment, the
no-evidence half by the one above. -/
theorem skippedLeaderOptInView_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    (hs : SkippedLeaderOptInView (S := S) U V k) :
    SkippedLeaderOptInView (S := S') U' V' k' :=
  ⟨le_trans hs.1 (Finset.card_le_card
      (blamesInView_bnd h hv hkk hlead h1 (by omega))),
    noEvidenceQuorumInView_bnd h hv hkk hlead h1 h2 hs.2⟩

/-! ## The anchored evidence rung

Three parts, as for Hydrozoan's two anchored tests: forward, back for a
candidate the band already had, and — the clause a one-directional band
forces — that a candidate the band did not carry passes the test on
neither side, because the anchor's cone never leaves the blocks the band
had and an old block's refs vote only for old blocks. -/

theorem evidenceLinked_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    {A L : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    (he : EvidenceLinked (S := S) U A L k) : EvidenceLinked (S := S') U' A L k' := by
  have hdr : LeanDag.Hydrozoan.decisionRound (S := S) Replica k = S.slotRound k + 2 := rfl
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := he
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = S.slotRound k + 2 := by
    intro b hb
    obtain ⟨hbA, -, -⟩ := hs b hb
    exact ⟨(Finset.mem_filter.mp hbA).1, (Finset.mem_filter.mp hbA).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (R.toDagRule.block U b).round = (U.block b).round := rfl
    exact ⟨blocksAt_bnd h (n := LeanDag.Hydrozoan.decisionRound (S := S) Replica k)
        (n' := LeanDag.Hydrozoan.decisionRound (S := S') Replica k')
        (by omega) (by omega) (by omega) hbA,
      (isFastEvidence_bnd h hkk hlead h1 (by omega) hbU (by omega) (by omega) L).mpr hbe,
      AgreeBand.reaches_of h hA hAhi hbre (by omega)⟩
  · rw [AnchoredRule.creatorsOf_band h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem evidenceLinked_bnd_old (h : AgreeBand R.toDagRule U U' lo hi g g')
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    {A L : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi)
    (he : EvidenceLinked (S := S') U' A L k') : EvidenceLinked (S := S) U A L k := by
  have hdr : LeanDag.Hydrozoan.decisionRound (S := S) Replica k = S.slotRound k + 2 := rfl
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  obtain ⟨s, hs, hcard⟩ := he
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = S.slotRound k + 2 := by
    intro b hb
    obtain ⟨hbA, -, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = S'.slotRound k' + 2 := (Finset.mem_filter.mp hbA).2
    have hlink : (R.toDagRule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    have hbe : (U.block b).round + g = (U'.block b).round + g' := hbeq
    exact ⟨hbU, by omega⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (R.toDagRule.block U' b).round = (U'.block b).round := rfl
    have hbr'' : (U'.block b).round = S'.slotRound k' + 2 := (Finset.mem_filter.mp hbA).2
    obtain ⟨-, hbreU, -⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    exact ⟨Finset.mem_filter.mpr ⟨hbU, by omega⟩,
      (isFastEvidence_bnd h hkk hlead h1 (by omega) hbU (by omega) (by omega) L).mp hbe,
      hbreU⟩
  · rw [← AnchoredRule.creatorsOf_band h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem not_evidenceLinked_bnd_novel (h : AgreeBand R.toDagRule U U' lo hi g g')
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 2 + g ≤ hi)
    {A L : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ EvidenceLinked (S := S') U' A L k' := by
  have hdr' : LeanDag.Hydrozoan.decisionRound (S := S') Replica k' = S'.slotRound k' + 2 := rfl
  have htE : 1 ≤ tEquiv Replica := by unfold tEquiv pOpt; omega
  have htP := tPlain_pos (Replica := Replica)
  rintro ⟨s, hs, hcard⟩
  have hsempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbA, hbe, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = S'.slotRound k' + 2 := (Finset.mem_filter.mp hbA).2
    have hlink : (R.toDagRule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    have hbe' : (U.block b).round + g = (U'.block b).round + g' := hbeq
    have hbr : (U.block b).round = S.slotRound k + 2 := by omega
    have hempty := votesFor_eq_empty_of_novel h hbU (by omega) (by omega) hL
    obtain ⟨hp, hq⟩ := hbe
    by_cases hw : WitnessesEquivocation (S := S') U' k' b
    · have := (hq hw).1
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega
    · have := hp hw
      rw [hempty] at this
      simp only [Finset.card_empty] at this
      omega
  rw [hsempty] at hcard
  simp only [LeanDag.creatorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcard
  have : 0 < LeanDag.Hydrozoan.qCert Replica := by
    unfold LeanDag.Hydrozoan.qCert; omega
  omega

/-! ## The band laws

What the relation's band induction asks of the rules: each direct
predicate and each rung carries across the band, and a candidate the
band did not carry is linked from no old anchor. Hydrozoan's direct
layer and rung `0` are read from `Hydrozoan/Helpers/Banded.lean`
unchanged; the fast path and the evidence rung are this file's. -/

omit S in
theorem optimalBandLaws : (optimalAnchored Replica BlockId).BandLaws where
  commit_band := by
    intro S S' U U' lo hi g g' V V' k k' L h hkk hlk hlo hhi hV _ hc
    simp only [optimalAnchored_wave] at hhi
    rcases hc with hc | hc
    · exact Or.inl (fastCommitOptInView_bnd h (fun b hb h1 h2 => hV b hb (by omega) (by omega))
        (n := S.slotRound k) (n' := S'.slotRound k') (by omega) (by omega) (by omega) hc)
    · exact Or.inr (le_trans hc (Finset.card_le_card
        (certifiersInView_bnd h (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k) (n' := S'.slotRound k') (by omega) (by omega) (by omega))))
  skip_band := by
    intro S S' U U' lo hi g g' V V' k k' h hkk hlk hlo hhi hV hs
    simp only [optimalAnchored_wave] at hhi
    exact skippedLeaderOptInView_bnd h (fun b hb h1 h2 => hV b hb (by omega) (by omega))
      hkk hlk (by omega) (by omega) hs
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk hlk hlo hhi hi _
    simp only [optimalAnchored_wave] at hhi
    rcases i with _ | _ | i
    · exact ⟨fun h' => certifiedIn_bnd_old h hA hAlo hAhi hkk (by omega) (by omega) h',
        fun h' => certifiedIn_bnd h hA hAlo hAhi hkk (by omega) (by omega) h'⟩
    · exact ⟨fun h' => evidenceLinked_bnd_old h hkk hlk (by omega) (by omega) hA hAlo hAhi h',
        fun h' => evidenceLinked_bnd h hkk hlk (by omega) (by omega) hA hAlo hAhi h'⟩
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk hlk hlo hhi hi _ hLo
    simp only [optimalAnchored_wave] at hhi
    rcases i with _ | _ | i
    · exact not_certifiedIn_bnd_novel h hA hAlo hAhi hkk (by omega) (by omega) hLo
    · exact not_evidenceLinked_bnd_novel h hkk hlk (by omega) (by omega) hA hAlo hAhi hLo
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)

end OptimalHydrozoan

end LeanDag
