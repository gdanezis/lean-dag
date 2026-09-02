import LeanDag.Integration.Hydrozoan.Transport
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Integration.Hydrozoan.ChopDecided

/-!
# P8 — the decision relation across the fill

`docs/hydrozoan-integration.md` §5.1. The fill adds one block per gap
round for the recovering replica; this file carries Hydrozoan's rules
across it and then the derivation.

**Why the in-view rules are exact rather than merely monotone.**
`SafeSkip`'s `liftView` keeps the *same* identifier set — a view of `U`
is a view of the extension unchanged, holding no filled block. So every
rule a view reads counts the same blocks either side, and the transfers
are equalities. What can grow is what the *universe* offers: fresh
candidates, and fresh votes for them.

**Why Hydrozoan's skip needs no quorum hypothesis where the core's
does.** The core's `decided_fill` carries `hq`, consumed at one point:
its `directSkip` premise is stated per candidate, so a filled candidate
is a new `L` for which the skip must be re-justified, and that needs a
quorum of view-held blocks not referencing it. Hydrozoan's premise is a
single count at the slot — `qFast ≤ blamesInView` — which the fill
leaves untouched, since a blame is a voting-round block none of whose
parents is a candidate, and no old block references a fresh identifier.
The asymmetry is `docs/hydrozoan-integration.md` §5.1's finding, read
in the direction that favours Hydrozoan.

**What the fill can add, and why it does not disturb the rungs.** An
old anchor reaches only old blocks (`reaches_fill_old`), so both rung
tests read the same material from it; and a fresh candidate is
certified and weak-linked by nothing an old anchor can see, which is
`not_certifiedIn_fresh` and its `WeakLinked` counterpart below.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {hsp : SelfParenting U} {sk : SkipMsg (toCore U hsp)}
  {V : LeanDag.Hydrozoan.View U}

/-! ## The extension, in Hydrozoan's terms -/

theorem skipFillHZ_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (skipFillHZ U hsp sk).block b = U.block b := by
  show (⟨(sk.skipFill.block b).round, (sk.skipFill.block b).creator,
    (sk.skipFill.block b).refs⟩ : LeanDag.Hydrozoan.Block Replica BlockId) = U.block b
  rw [sk.skipFill_block_old hb]
  rfl

@[simp] theorem roundHZ_fill_old {b : BlockId} (hb : b ∈ U.ids) :
    ((skipFillHZ U hsp sk).block b).round = (U.block b).round := by
  rw [skipFillHZ_block_old hb]

@[simp] theorem authorHZ_fill_old {b : BlockId} (hb : b ∈ U.ids) :
    ((skipFillHZ U hsp sk).block b).author = (U.block b).author := by
  rw [skipFillHZ_block_old hb]

@[simp] theorem parentsHZ_fill_old {b : BlockId} (hb : b ∈ U.ids) :
    ((skipFillHZ U hsp sk).block b).parents = (U.block b).parents := by
  rw [skipFillHZ_block_old hb]

/-- Above the fill an old block's vote is its vote. -/
theorem isVoteHZ_fill_old {b L : BlockId} (hb : b ∈ U.ids) :
    LeanDag.Hydrozoan.IsVote (skipFillHZ U hsp sk) b L
      ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
  rw [parentsHZ_fill_old hb]

/-- Author sets read identically on any set of old blocks. -/
theorem authorsOfHZ_fill {s : Finset BlockId} (hs : s ⊆ U.ids) :
    LeanDag.Hydrozoan.authorsOf (skipFillHZ U hsp sk).block s
      = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun b hb => authorHZ_fill_old (hs hb)

theorem ids_subset_skipFillHZ : U.ids ⊆ (skipFillHZ U hsp sk).ids :=
  sk.ids_subset_skipFill

@[simp] theorem liftViewHZ_ids_eq :
    (liftViewHZ U hsp sk V).ids = V.ids := rfl

/-! ## Candidacy -/

theorem isLeaderBlockHZ_fill [S : LeanDag.Hydrozoan.Slots Replica] {k : ℕ} {L : BlockId}
    (h : LeanDag.Hydrozoan.IsLeaderBlock U k L) :
    LeanDag.Hydrozoan.IsLeaderBlock (skipFillHZ U hsp sk) k L :=
  ⟨ids_subset_skipFillHZ h.1, by rw [roundHZ_fill_old h.1]; exact h.2.1,
    by rw [authorHZ_fill_old h.1]; exact h.2.2⟩

/-- An old candidate of the extension is an old candidate. -/
theorem isLeaderBlockHZ_fill_old [S : LeanDag.Hydrozoan.Slots Replica] {k : ℕ} {L : BlockId}
    (hL : L ∈ U.ids) (h : LeanDag.Hydrozoan.IsLeaderBlock (skipFillHZ U hsp sk) k L) :
    LeanDag.Hydrozoan.IsLeaderBlock U k L := by
  refine ⟨hL, ?_, ?_⟩
  · have := h.2.1; rwa [roundHZ_fill_old hL] at this
  · have := h.2.2; rwa [authorHZ_fill_old hL] at this

/-! ## The rules a view reads are exact

The lifted view holds no filled block, so each of these counts the same
set of old blocks either side. -/

theorem supportersInView_fill (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.supportersInView (skipFillHZ U hsp sk)
        (liftViewHZ U hsp sk V) L r
      = LeanDag.Hydrozoan.supportersInView U V L r := by
  unfold LeanDag.Hydrozoan.supportersInView
  have hset : ((LeanDag.Hydrozoan.blocksAt (skipFillHZ U hsp sk) r).filter
        fun b => LeanDag.Hydrozoan.IsVote (skipFillHZ U hsp sk) b L)
        ∩ (liftViewHZ U hsp sk V).ids
      = ((LeanDag.Hydrozoan.blocksAt U r).filter
        fun b => LeanDag.Hydrozoan.IsVote U b L) ∩ V.ids := by
    ext b
    simp only [Finset.mem_inter, Finset.mem_filter, LeanDag.Hydrozoan.blocksAt,
      liftViewHZ_ids_eq]
    constructor
    · rintro ⟨⟨⟨_, hbr⟩, hv⟩, hV⟩
      have hbo := V.subset_ids hV
      rw [roundHZ_fill_old hbo] at hbr
      exact ⟨⟨⟨hbo, hbr⟩, (isVoteHZ_fill_old hbo).mp hv⟩, hV⟩
    · rintro ⟨⟨⟨hbo, hbr⟩, hv⟩, hV⟩
      exact ⟨⟨⟨ids_subset_skipFillHZ hbo, by rw [roundHZ_fill_old hbo]; exact hbr⟩,
        (isVoteHZ_fill_old hbo).mpr hv⟩, hV⟩
  rw [hset]
  exact authorsOfHZ_fill fun b hb => V.subset_ids (Finset.mem_inter.mp hb).2

theorem fastCommitInView_fill (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.FastCommitInView (skipFillHZ U hsp sk)
        (liftViewHZ U hsp sk V) L r
      ↔ LeanDag.Hydrozoan.FastCommitInView U V L r := by
  unfold LeanDag.Hydrozoan.FastCommitInView
  rw [supportersInView_fill (V := V)]

/-- Certification reads identically on an old block: its parents are
unchanged, and so are their votes. -/
theorem isCertificateHZ_fill_old {C L : BlockId} (hC : C ∈ U.ids) :
    LeanDag.Hydrozoan.IsCertificate (skipFillHZ U hsp sk) C L
      ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  have hvb : LeanDag.Hydrozoan.voteBlocks (skipFillHZ U hsp sk) C L
      = LeanDag.Hydrozoan.voteBlocks U C L := by
    unfold LeanDag.Hydrozoan.voteBlocks
    rw [parentsHZ_fill_old hC]
    exact Finset.filter_congr fun b hb => isVoteHZ_fill_old (U.complete C hC b hb)
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [hvb, authorsOfHZ_fill (s := LeanDag.Hydrozoan.voteBlocks U C L)
    (fun b hb => U.complete C hC b (Finset.mem_filter.mp hb).1)]

theorem certifiersInView_fill (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.certifiersInView (skipFillHZ U hsp sk)
        (liftViewHZ U hsp sk V) L r
      = LeanDag.Hydrozoan.certifiersInView U V L r := by
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
  have hset : LeanDag.Hydrozoan.certificates (skipFillHZ U hsp sk) L r
        ∩ (liftViewHZ U hsp sk V).ids
      = LeanDag.Hydrozoan.certificates U L r ∩ V.ids := by
    ext C
    simp only [Finset.mem_inter, LeanDag.Hydrozoan.certificates,
      LeanDag.Hydrozoan.blocksAt, Finset.mem_filter, liftViewHZ_ids_eq]
    constructor
    · rintro ⟨⟨⟨_, hCr⟩, hc⟩, hV⟩
      have hCo := V.subset_ids hV
      rw [roundHZ_fill_old hCo] at hCr
      exact ⟨⟨⟨hCo, hCr⟩, (isCertificateHZ_fill_old hCo).mp hc⟩, hV⟩
    · rintro ⟨⟨⟨hCo, hCr⟩, hc⟩, hV⟩
      exact ⟨⟨⟨ids_subset_skipFillHZ hCo, by rw [roundHZ_fill_old hCo]; exact hCr⟩,
        (isCertificateHZ_fill_old hCo).mpr hc⟩, hV⟩
  rw [hset]
  exact authorsOfHZ_fill fun C hC => V.subset_ids (Finset.mem_inter.mp hC).2

theorem slowCommitInView_fill (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.SlowCommitInView (skipFillHZ U hsp sk)
        (liftViewHZ U hsp sk V) L r
      ↔ LeanDag.Hydrozoan.SlowCommitInView U V L r := by
  unfold LeanDag.Hydrozoan.SlowCommitInView
  rw [certifiersInView_fill (V := V)]

/-! ## The skip, and why it costs no hypothesis

`blamesInView` is a single count at the slot, and the lifted view holds
only old blocks whose parents are old. A filled candidate is fresh, and
no old block references a fresh identifier, so the blame condition reads
the same either side. Nothing is re-justified against a new candidate,
which is the whole of what the core's `hq` is for. -/

section Skip

variable [S : LeanDag.Hydrozoan.Slots Replica]

theorem blamesInView_fill (k : ℕ) :
    LeanDag.Hydrozoan.blamesInView (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k
      = LeanDag.Hydrozoan.blamesInView U V k := by
  unfold LeanDag.Hydrozoan.blamesInView
  have hset : ((LeanDag.Hydrozoan.blocksAt (skipFillHZ U hsp sk)
        (LeanDag.Hydrozoan.votingRound Replica k)).filter fun b =>
        ∀ j ∈ ((skipFillHZ U hsp sk).block b).parents,
          ¬ LeanDag.Hydrozoan.IsLeaderBlock (skipFillHZ U hsp sk) k j)
        ∩ (liftViewHZ U hsp sk V).ids
      = ((LeanDag.Hydrozoan.blocksAt U (LeanDag.Hydrozoan.votingRound Replica k)).filter
        fun b => ∀ j ∈ (U.block b).parents, ¬ LeanDag.Hydrozoan.IsLeaderBlock U k j)
        ∩ V.ids := by
    ext b
    simp only [Finset.mem_inter, Finset.mem_filter, LeanDag.Hydrozoan.blocksAt,
      liftViewHZ_ids_eq]
    constructor
    · rintro ⟨⟨⟨_, hbr⟩, hbl⟩, hV⟩
      have hbo := V.subset_ids hV
      rw [roundHZ_fill_old hbo] at hbr
      refine ⟨⟨⟨hbo, hbr⟩, fun j hj hL => ?_⟩, hV⟩
      exact hbl j (by rw [parentsHZ_fill_old hbo]; exact hj) (isLeaderBlockHZ_fill hL)
    · rintro ⟨⟨⟨hbo, hbr⟩, hbl⟩, hV⟩
      refine ⟨⟨⟨ids_subset_skipFillHZ hbo, by rw [roundHZ_fill_old hbo]; exact hbr⟩,
        fun j hj hL => ?_⟩, hV⟩
      rw [parentsHZ_fill_old hbo] at hj
      exact hbl j hj (isLeaderBlockHZ_fill_old (U.complete b hbo j hj) hL)
  rw [hset]
  exact authorsOfHZ_fill fun b hb => V.subset_ids (Finset.mem_inter.mp hb).2

/-- **The skip survives the fill, with no quorum hypothesis.** -/
theorem skippedLeaderInView_fill (k : ℕ) :
    LeanDag.Hydrozoan.SkippedLeaderInView (skipFillHZ U hsp sk)
        (liftViewHZ U hsp sk V) k
      ↔ LeanDag.Hydrozoan.SkippedLeaderInView U V k := by
  unfold LeanDag.Hydrozoan.SkippedLeaderInView
  rw [blamesInView_fill (V := V)]

end Skip

/-! ## Reachability, and the two rung tests

An old anchor reaches only old blocks, which is `SafeSkip`'s
`reaches_fill_old` read through the transport — Hydrozoan's `Reaches`
and the core's are one relation. So both rungs read the same material
from an old anchor, and a fresh candidate is reached by neither. -/

theorem reachesHZ_fill_old {A B : BlockId} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.Reaches (skipFillHZ U hsp sk) A B
      ↔ B ∈ U.ids ∧ LeanDag.Hydrozoan.Reaches U A B :=
  sk.reaches_fill_old hA

/-- An old block never references a fresh identifier. -/
theorem not_isVote_fresh {b L : BlockId} (hb : b ∈ U.ids) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.IsVote U b L :=
  fun hv => hL (U.complete b hb L hv)

theorem certifiedInHZ_fill {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.CertifiedIn (skipFillHZ U hsp sk) A L r
      ↔ LeanDag.Hydrozoan.CertifiedIn U A L r := by
  unfold LeanDag.Hydrozoan.CertifiedIn
  constructor
  · rintro ⟨C, hC, hreach⟩
    obtain ⟨hCo, hreach'⟩ := (reachesHZ_fill_old hA).mp hreach
    refine ⟨C, ?_, hreach'⟩
    simp only [LeanDag.Hydrozoan.certificates, LeanDag.Hydrozoan.blocksAt,
      Finset.mem_filter] at hC ⊢
    exact ⟨⟨hCo, by rw [← roundHZ_fill_old hCo]; exact hC.1.2⟩,
      (isCertificateHZ_fill_old hCo).mp hC.2⟩
  · rintro ⟨C, hC, hreach⟩
    simp only [LeanDag.Hydrozoan.certificates, LeanDag.Hydrozoan.blocksAt,
      Finset.mem_filter] at hC
    refine ⟨C, ?_, (reachesHZ_fill_old hA).mpr ⟨hC.1.1, hreach⟩⟩
    simp only [LeanDag.Hydrozoan.certificates, LeanDag.Hydrozoan.blocksAt,
      Finset.mem_filter]
    exact ⟨⟨ids_subset_skipFillHZ hC.1.1, by rw [roundHZ_fill_old hC.1.1]; exact hC.1.2⟩,
      (isCertificateHZ_fill_old hC.1.1).mpr hC.2⟩

theorem weakLinkedHZ_fill {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) :
    LeanDag.Hydrozoan.WeakLinked (skipFillHZ U hsp sk) A L r
      ↔ LeanDag.Hydrozoan.WeakLinked U A L r := by
  unfold LeanDag.Hydrozoan.WeakLinked
  constructor
  · rintro ⟨s, hs, hcard⟩
    have hsub : s ⊆ U.ids := fun b hb => ((reachesHZ_fill_old hA).mp (hs b hb).2.2).1
    refine ⟨s, fun b hb => ?_, by rwa [authorsOfHZ_fill hsub] at hcard⟩
    obtain ⟨hbAt, hbv, hbr⟩ := hs b hb
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hbAt
    rw [roundHZ_fill_old (hsub hb)] at hbAt
    refine ⟨?_, (isVoteHZ_fill_old (hsub hb)).mp hbv, ((reachesHZ_fill_old hA).mp hbr).2⟩
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
    exact ⟨hsub hb, hbAt.2⟩
  · rintro ⟨s, hs, hcard⟩
    have hsub : s ⊆ U.ids := by
      intro b hb
      have h := (hs b hb).1
      simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at h
      exact h.1
    refine ⟨s, fun b hb => ?_, by rw [authorsOfHZ_fill hsub]; exact hcard⟩
    obtain ⟨hbAt, hbv, hbr⟩ := hs b hb
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hbAt
    refine ⟨?_, (isVoteHZ_fill_old hbAt.1).mpr hbv,
      (reachesHZ_fill_old hA).mpr ⟨hbAt.1, hbr⟩⟩
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
    exact ⟨ids_subset_skipFillHZ hbAt.1, by rw [roundHZ_fill_old hbAt.1]; exact hbAt.2⟩

/-! ## A fresh candidate is reached by neither rung

Votes for a fresh identifier can come only from fresh blocks, and an
old anchor reaches none. So both rung tests are false for a filled
candidate, which is what lets the graded rungs' negative premises
survive the fill even though the fill adds candidates. -/

theorem not_certifiedInHZ_fresh {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids)
    (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.CertifiedIn (skipFillHZ U hsp sk) A L r := by
  rintro ⟨C, hC, hreach⟩
  obtain ⟨hCo, _⟩ := (reachesHZ_fill_old hA).mp hreach
  simp only [LeanDag.Hydrozoan.certificates, Finset.mem_filter] at hC
  have hcert := (isCertificateHZ_fill_old hCo).mp hC.2
  have hempty : LeanDag.Hydrozoan.voteBlocks U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    exact not_isVote_fresh (U.complete C hCo b hbp) hL hbv
  unfold LeanDag.Hydrozoan.IsCertificate at hcert
  rw [hempty] at hcert
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty,
    Finset.card_empty, Nat.le_zero] at hcert
  exact absurd hcert (by unfold LeanDag.Hydrozoan.qCert; omega)

theorem not_weakLinkedHZ_fresh {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids)
    (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.WeakLinked (skipFillHZ U hsp sk) A L r := by
  rintro ⟨s, hs, hcard⟩
  have hempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨_, hbv, hbr⟩ := hs b hb
    have hbo := ((reachesHZ_fill_old hA).mp hbr).1
    exact not_isVote_fresh hbo hL ((isVoteHZ_fill_old hbo).mp hbv)
  rw [hempty] at hcard
  simp only [LeanDag.Hydrozoan.authorsOf, Finset.image_empty,
    Finset.card_empty, Nat.le_zero] at hcard
  exact absurd hcard (by unfold LeanDag.Hydrozoan.qWeak; omega)

/-! ## P8 — the verdicts survive the fill

One direction only, which is all the fill admits: it adds blocks, so it
can create verdicts the original did not have. What it cannot do is
disturb one already reached. -/

section Induction

variable [LinearOrder BlockId] [S : LeanDag.Hydrozoan.Slots Replica]

/-- **Verdict invariance across the fill.** Every verdict a view
reached in `U` re-derives, for the lifted view, in the extension — and
unlike the core's `decided_fill` this needs **no quorum hypothesis**,
because Hydrozoan's skip is a count at the slot rather than a condition
per candidate. -/
theorem decided_fillHZ {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k v := by
  induction h with
  | @directFast k L hL hc =>
      exact LeanDag.Hydrozoan.Decided.directFast (isLeaderBlockHZ_fill hL)
        ((fastCommitInView_fill (V := V) L _).mpr hc)
  | @directSlow k L hL hc =>
      exact LeanDag.Hydrozoan.Decided.directSlow (isLeaderBlockHZ_fill hL)
        ((slowCommitInView_fill (V := V) L _).mpr hc)
  | @directSkip k hskip =>
      exact LeanDag.Hydrozoan.Decided.directSkip
        ((skippedLeaderInView_fill (V := V) k).mpr hskip)
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      exact LeanDag.Hydrozoan.Decided.indirectCert hkj helig ihj ihmid
        (isLeaderBlockHZ_fill hL) ((certifiedInHZ_fill hA).mpr hcert)
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak hkj helig ihj ihmid ?_
        (isLeaderBlockHZ_fill hL) ((weakLinkedHZ_fill hA).mpr hweak) ?_
      · intro L' hL' hc
        by_cases hL'o : L' ∈ U.ids
        · exact hnocert L' (isLeaderBlockHZ_fill_old hL'o hL')
            ((certifiedInHZ_fill hA).mp hc)
        · exact not_certifiedInHZ_fresh hA hL'o hc
      · intro L' hL' hw
        by_cases hL'o : L' ∈ U.ids
        · exact hmin L' (isLeaderBlockHZ_fill_old hL'o hL') ((weakLinkedHZ_fill hA).mp hw)
        · exact absurd hw (not_weakLinkedHZ_fresh hA hL'o)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip hkj helig ihj ihmid ?_ ?_
      · intro L' hL' hc
        by_cases hL'o : L' ∈ U.ids
        · exact hnocert L' (isLeaderBlockHZ_fill_old hL'o hL')
            ((certifiedInHZ_fill hA).mp hc)
        · exact not_certifiedInHZ_fresh hA hL'o hc
      · intro L' hL' hw
        by_cases hL'o : L' ∈ U.ids
        · exact hnoweak L' (isLeaderBlockHZ_fill_old hL'o hL') ((weakLinkedHZ_fill hA).mp hw)
        · exact absurd hw (not_weakLinkedHZ_fresh hA hL'o)

/-- **Cross-fill agreement.** A verdict reached before the recovery and
one reached after it agree, which is `integration.md` SS5 for
Hydrozoan's rule. -/
theorem decided_fill_agreeHZ {k : ℕ} {v w : Option BlockId}
    {W : LeanDag.Hydrozoan.View (skipFillHZ U hsp sk)}
    (hV : LeanDag.Hydrozoan.Decided U V k v)
    (hW : LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) W k w) :
    v = w :=
  LeanDag.Hydrozoan.SlotAgreement.holds Replica BlockId (skipFillHZ U hsp sk)
    (liftViewHZ U hsp sk V) W k v w (decided_fillHZ hV) hW

end Induction

end Hydrozoan

end Integration

end LeanDag
