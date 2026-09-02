import LeanDag.Integration.Hydrozoan.Transport
import LeanDag.GC.ChopDecided
import LeanDag.Integration.ScheduleShape
import LeanDag.Hydrozoan.SlotAgreement.Proof

/-!
# P7 — the decision relation across the cut, foundations

`docs/hydrozoan-integration.md` §5. This file carries what the
constructor induction of `decided_chop_hz` stands on: the truncated
universe read as Hydrozoan's, the truncated view, the induced
schedule, and the rules transported.

**What the bridge already supplies.** `chopHZ U hsp G` is
`ofCore (chop (toCore U hsp) G)`, so the truncation *is* the core's,
read back — its identifiers and blocks are `chop`'s, and every lemma
`GC/Chop.lean` proves about those applies here through the
identification. What has to be redone is the rule layer, which is
Hydrozoan's and which no bridge reaches (§9).

**The schedule is the core's too.** `Slots.chop` moves `slotRound` and
`leader` together, so re-indexing by a base slot needs no new
arithmetic; `ofCoreSlots` reads the result back. This is the
coordinated re-indexing §4.1 contrasts with Barnacle's quantification
over arbitrary schedules.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {hsp : SelfParenting U} {G : ℕ}

/-! ## The truncated universe, in Hydrozoan's terms -/

@[simp] theorem chopHZ_round (i : BlockId) :
    ((chopHZ U hsp G).block i).round = (U.block i).round - G :=
  chopBlock_round (U := toCore U hsp)

@[simp] theorem chopHZ_author (i : BlockId) :
    ((chopHZ U hsp G).block i).author = (U.block i).author :=
  chopBlock_creator (U := toCore U hsp)

theorem mem_chopHZ_ids {i : BlockId} :
    i ∈ (chopHZ U hsp G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round := by
  rw [chopHZ_ids, Finset.mem_filter]

/-- Above the cut the parents are untouched. -/
theorem chopHZ_parents_of_lt {i : BlockId} (h : G < (U.block i).round) :
    ((chopHZ U hsp G).block i).parents = (U.block i).parents :=
  chopBlock_refs_of_lt (U := toCore U hsp) h

/-- At the cut the block becomes a genesis. -/
theorem chopHZ_parents_of_le {i : BlockId} (h : (U.block i).round ≤ G) :
    ((chopHZ U hsp G).block i).parents = ∅ :=
  chopBlock_refs_of_le (U := toCore U hsp) h

/-! ## The truncated view -/

/-- A replica's view, truncated at the horizon: keep what clears the
cut. Closure survives, a retained block's parents sitting one round
below it and so at or above the cut — except at the base layer, where
they are gone. -/
def View.chopHZ (V : LeanDag.Hydrozoan.View U) (hsp : SelfParenting U) (G : ℕ) :
    LeanDag.Hydrozoan.View (chopHZ U hsp G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chopHZ_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with hlt | hge
    · rw [chopHZ_parents_of_lt hlt] at hj
      have hround := (U.valid i (V.subset_ids hi.1)).predecessor j hj
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj, by omega⟩
    · rw [chopHZ_parents_of_le hge] at hj
      exact absurd hj (Finset.notMem_empty j)

@[simp] theorem View.chopHZ_ids (V : LeanDag.Hydrozoan.View U)
    (hsp : SelfParenting U) (G : ℕ) :
    (View.chopHZ V hsp G).ids = V.ids.filter fun i => G ≤ (U.block i).round := rfl

/-! ## The induced schedule -/

section Schedule

variable [S : LeanDag.Hydrozoan.Slots Replica] {d : ℕ}

/-- The schedule re-indexed from the base slot `d` and rebased by the
cut — the core's `Slots.chop`, read back through `ofCoreSlots`, so its
monotonicity, unboundedness and keying proofs are reused entire. -/
@[reducible]
def slotsChopHZ (hd : G ≤ S.slotRound d) : LeanDag.Hydrozoan.Slots Replica :=
  ofCoreSlots (LeanDag.Slots.chop (toCoreSlots) G d hd)

omit [Fintype Replica] [DecidableEq Replica] F [Fact (HybridCommittee Replica)] in
@[simp] theorem slotsChopHZ_slotRound (hd : G ≤ S.slotRound d) (k : ℕ) :
    (slotsChopHZ hd).slotRound k = S.slotRound (d + k) - G := rfl

omit [Fintype Replica] [DecidableEq Replica] F [Fact (HybridCommittee Replica)] in
@[simp] theorem slotsChopHZ_leader (hd : G ≤ S.slotRound d) (k : ℕ) :
    (slotsChopHZ hd).leader k = S.leader (d + k) := rfl

omit [Fintype Replica] [DecidableEq Replica] F [Fact (HybridCommittee Replica)] in
/-- Every slot from the base slot on clears the horizon. -/
theorem horizon_le_slotRoundHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    G ≤ S.slotRound (d + k) :=
  hd.trans (S.mono (Nat.le_add_right d k))

/-! ## The rules that read only rounds and authors -/

/-- Candidacy is re-indexed: a block is slot `k`'s candidate in the
truncation exactly when it is slot `d + k`'s in the original. -/
theorem isLeaderBlockHZ_chop (hd : G ≤ S.slotRound d) {k : ℕ} {L : BlockId} :
    @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ (slotsChopHZ hd) (chopHZ U hsp G) k L
      ↔ LeanDag.Hydrozoan.IsLeaderBlock U (d + k) L := by
  have hG := horizon_le_slotRoundHZ (S := S) hd k
  simp only [LeanDag.Hydrozoan.IsLeaderBlock, mem_chopHZ_ids, chopHZ_round,
    chopHZ_author, slotsChopHZ_slotRound, slotsChopHZ_leader]
  constructor
  · rintro ⟨⟨hL, _⟩, hround, hauthor⟩
    exact ⟨hL, by omega, hauthor⟩
  · rintro ⟨hL, hround, hauthor⟩
    exact ⟨⟨hL, by omega⟩, by omega, hauthor⟩

omit [Fintype Replica] [DecidableEq Replica] F [Fact (HybridCommittee Replica)] in
/-- Anchor eligibility is re-indexed, both slots moving together. -/
theorem eligibleAsAnchorHZ_chop (hd : G ≤ S.slotRound d) {k j : ℕ} :
    @LeanDag.Hydrozoan.EligibleAsAnchor Replica (slotsChopHZ hd) k j
      ↔ LeanDag.Hydrozoan.EligibleAsAnchor Replica (d + k) (d + j) := by
  have hk := horizon_le_slotRoundHZ (S := S) hd k
  have hj := horizon_le_slotRoundHZ (S := S) hd j
  show S.slotRound (d + k) - G + 2 < S.slotRound (d + j) - G
    ↔ S.slotRound (d + k) + 2 < S.slotRound (d + j)
  omega

/-! ## The schedule's fairness and shape survive the cut

`integration.md` I3, transported. These are functions of a `Slots`
instance and nothing else, so the coercion of `Schedule.lean` carries
them: the Hydrozoan predicates and the core's are the same
propositions, and `slotsChopHZ` is the core's `Slots.chop` read back.
A replica reasoning inside a truncation therefore has a schedule that
is fair and spanning in its own right, which is what liveness below the
cut consumes. -/

omit [Fintype Replica] [DecidableEq Replica] F [Fact (HybridCommittee Replica)] in
/-- Run fairness survives the cut, the search shifted past the base
slot. Proved directly rather than through the core's `fairRunOn_chop`,
which is stated over a `Faults` instance: schedule fairness should not
depend on a committee condition, and here it does not. -/
theorem fairRunOn_slotsChopHZ (hd : G ≤ S.slotRound d) {T : Finset Replica} {c : ℕ}
    (h : LeanDag.Hydrozoan.EventualDecision.FairRunOn Replica T c) :
    @LeanDag.Hydrozoan.EventualDecision.FairRunOn Replica (slotsChopHZ hd) T c := by
  intro k
  obtain ⟨m, hm, hrun⟩ := h (d + k)
  refine ⟨m - d, by omega, fun i hi => ?_⟩
  show S.leader (d + (m - d + i)) ∈ T
  have hshift : d + (m - d + i) = m + i := by omega
  rw [hshift]
  exact hrun i hi

omit [Fintype Replica] [DecidableEq Replica] F [Fact (HybridCommittee Replica)] in
/-- And the runway a committed run needs, by the same re-indexing that
carries anchor eligibility. -/
theorem spansEligible_slotsChopHZ (hd : G ≤ S.slotRound d) {c : ℕ}
    (h : LeanDag.Hydrozoan.IndirectLiveness.SpansEligible Replica c) :
    @LeanDag.Hydrozoan.IndirectLiveness.SpansEligible Replica (slotsChopHZ hd) c := by
  intro b i hi
  refine (eligibleAsAnchorHZ_chop hd).mpr ?_
  have horig := h (d + b) (d + i) (by omega)
  have heq : d + b + c - 1 = d + (b + c - 1) := by omega
  rwa [heq] at horig

end Schedule

/-! ## The counting rules, transported

Every rule of `Model/DirectRules.lean` counts authors of blocks at a
fixed round, filtered by a condition on parents. Three facts carry all
of them: author sets are untouched, rounds shift by the cut, and above
the cut parents are untouched. -/

section Rules

variable {V : LeanDag.Hydrozoan.View U}

@[simp] theorem authorsOf_chopHZ (s : Finset BlockId) :
    LeanDag.Hydrozoan.authorsOf (chopHZ U hsp G).block s
      = LeanDag.Hydrozoan.authorsOf U.block s :=
  Finset.image_congr fun i _ => chopHZ_author i

/-- The rounds shift by the cut, at every round including the new base
layer: `G ≤ round` and `round − G = r` together pin `round = G + r`. -/
theorem blocksAt_chopHZ (r : ℕ) :
    LeanDag.Hydrozoan.blocksAt (chopHZ U hsp G) r
      = LeanDag.Hydrozoan.blocksAt U (G + r) := by
  ext i
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter, mem_chopHZ_ids, chopHZ_round]
  constructor
  · rintro ⟨⟨hi, hge⟩, hr⟩; exact ⟨hi, by omega⟩
  · rintro ⟨hi, hr⟩; exact ⟨⟨hi, by omega⟩, by omega⟩

/-- Above the cut a vote is a vote: the parents are the same set. -/
theorem isVote_chopHZ {b L : BlockId} (h : G < (U.block b).round) :
    LeanDag.Hydrozoan.IsVote (chopHZ U hsp G) b L
      ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
  rw [chopHZ_parents_of_lt h]

/-- A block above the cut is held by the truncated view exactly when
the original view holds it. -/
theorem mem_viewChopHZ {b : BlockId} (h : G ≤ (U.block b).round) :
    b ∈ (View.chopHZ V hsp G).ids ↔ b ∈ V.ids := by
  rw [View.chopHZ_ids, Finset.mem_filter]
  exact ⟨fun hb => hb.1, fun hb => ⟨hb, h⟩⟩

/-- Supporters at a round above the new base layer are the originals,
at the shifted round. -/
theorem supportersInView_chopHZ (L : BlockId) (r : ℕ) (hr : 0 < r) :
    LeanDag.Hydrozoan.supportersInView (chopHZ U hsp G) (View.chopHZ V hsp G) L r
      = LeanDag.Hydrozoan.supportersInView U V L (G + r) := by
  unfold LeanDag.Hydrozoan.supportersInView
  rw [authorsOf_chopHZ]
  congr 1
  rw [blocksAt_chopHZ]
  ext b
  simp only [Finset.mem_inter, Finset.mem_filter, LeanDag.Hydrozoan.blocksAt]
  constructor
  · rintro ⟨⟨⟨hb, hbr⟩, hv⟩, hV⟩
    exact ⟨⟨⟨hb, hbr⟩, (isVote_chopHZ (by omega)).mp hv⟩,
      (mem_viewChopHZ (V := V) (by omega)).mp hV⟩
  · rintro ⟨⟨⟨hb, hbr⟩, hv⟩, hV⟩
    exact ⟨⟨⟨hb, hbr⟩, (isVote_chopHZ (by omega)).mpr hv⟩,
      (mem_viewChopHZ (V := V) (by omega)).mpr hV⟩

/-- Two rounds above the cut a block's votes are the originals: its own
parents are untouched, and so are theirs. -/
theorem voteBlocks_chopHZ {C L : BlockId} (hC : C ∈ U.ids)
    (h : G + 1 < (U.block C).round) :
    LeanDag.Hydrozoan.voteBlocks (chopHZ U hsp G) C L
      = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [chopHZ_parents_of_lt (by omega)]
  refine Finset.filter_congr fun b hb => ?_
  have hbr := (U.valid C hC).predecessor b hb
  exact isVote_chopHZ (by omega)

/-- The truncation only ever drops parents, never adds them. -/
theorem chopHZ_parents_subset (i : BlockId) :
    ((chopHZ U hsp G).block i).parents ⊆ (U.block i).parents := by
  rcases Nat.lt_or_ge G (U.block i).round with h | h
  · rw [chopHZ_parents_of_lt h]
  · rw [chopHZ_parents_of_le h]; exact Finset.empty_subset _

/-- Certification is a count over a block's votes, so it transports
where the votes do. -/
theorem isCertificate_chopHZ {C L : BlockId} (hC : C ∈ U.ids)
    (h : G + 1 < (U.block C).round) :
    LeanDag.Hydrozoan.IsCertificate (chopHZ U hsp G) C L
      ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [voteBlocks_chopHZ hC h, authorsOf_chopHZ]

theorem certificates_chopHZ (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.certificates (chopHZ U hsp G) L r
      = LeanDag.Hydrozoan.certificates U L (G + r) := by
  unfold LeanDag.Hydrozoan.certificates
  have : G + (r + 2) = G + r + 2 := by omega
  rw [blocksAt_chopHZ, this]
  refine Finset.filter_congr fun C hC => ?_
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hC
  exact isCertificate_chopHZ hC.1 (by omega)

theorem certifiersInView_chopHZ (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.certifiersInView (chopHZ U hsp G) (View.chopHZ V hsp G) L r
      = LeanDag.Hydrozoan.certifiersInView U V L (G + r) := by
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
  rw [authorsOf_chopHZ, certificates_chopHZ]
  congr 1
  ext b
  simp only [Finset.mem_inter, LeanDag.Hydrozoan.certificates,
    LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨hb, hbr⟩, hc⟩, hV⟩
    exact ⟨⟨⟨hb, hbr⟩, hc⟩, (mem_viewChopHZ (V := V) (by omega)).mp hV⟩
  · rintro ⟨⟨⟨hb, hbr⟩, hc⟩, hV⟩
    exact ⟨⟨⟨hb, hbr⟩, hc⟩, (mem_viewChopHZ (V := V) (by omega)).mpr hV⟩

/-! ## The two direct commit rules -/

theorem fastCommitInView_chopHZ (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.FastCommitInView (chopHZ U hsp G) (View.chopHZ V hsp G) L r
      ↔ LeanDag.Hydrozoan.FastCommitInView U V L (G + r) := by
  unfold LeanDag.Hydrozoan.FastCommitInView
  have : G + (r + 1) = G + r + 1 := by omega
  rw [supportersInView_chopHZ (V := V) L (r + 1) (by omega), this]

theorem slowCommitInView_chopHZ (L : BlockId) (r : ℕ) :
    LeanDag.Hydrozoan.SlowCommitInView (chopHZ U hsp G) (View.chopHZ V hsp G) L r
      ↔ LeanDag.Hydrozoan.SlowCommitInView U V L (G + r) := by
  unfold LeanDag.Hydrozoan.SlowCommitInView
  rw [certifiersInView_chopHZ (V := V) L r]

/-! ## Reachability across the cut

Hydrozoan's `Reaches` is the core's `ReachesFrom` on the adapted lookup
— the two relations are one term — so `Causality.lean` applies. Going
down is unconditional, since truncation only drops parents; coming back
needs the target above the cut, which forces every block on the path
above it too, rounds decreasing by one per step. -/

theorem reaches_of_reaches_chopHZ {A B : BlockId}
    (h : LeanDag.Hydrozoan.Reaches (chopHZ U hsp G) A B) :
    LeanDag.Hydrozoan.Reaches U A B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chopHZ_parents_subset _ hstep)

theorem reaches_chopHZ_of_reaches {A B : BlockId} (hA : A ∈ U.ids)
    (h : LeanDag.Hydrozoan.Reaches U A B) :
    G < (U.block B).round → LeanDag.Hydrozoan.Reaches (chopHZ U hsp G) A B := by
  induction h with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hAb hstep ih =>
      intro hc
      have hbmem : b ∈ U.ids :=
        (LeanDag.Barnacle.Hydrozoan.causalStructure U).mem_ids_of_reaches hA hAb
      have hbr := (U.valid b hbmem).predecessor c hstep
      refine (ih (by omega)).tail ?_
      show c ∈ ((chopHZ U hsp G).block b).parents
      rw [chopHZ_parents_of_lt (by omega)]
      exact hstep

theorem reaches_chopHZ {A B : BlockId} (hA : A ∈ U.ids)
    (hB : G < (U.block B).round) :
    LeanDag.Hydrozoan.Reaches (chopHZ U hsp G) A B
      ↔ LeanDag.Hydrozoan.Reaches U A B :=
  ⟨reaches_of_reaches_chopHZ, fun h => reaches_chopHZ_of_reaches hA h hB⟩

end Rules


/-! ## The slot-level rules, and the two rung tests

These read the schedule as well as the DAG, so they are stated at the
re-indexed schedule of `slotsChopHZ`. -/

section SlotRules

variable [S : LeanDag.Hydrozoan.Slots Replica] {d : ℕ}
variable {V : LeanDag.Hydrozoan.View U}

theorem blamesInView_chopHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    LeanDag.Hydrozoan.blamesInView (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k
      = LeanDag.Hydrozoan.blamesInView U V (d + k) := by
  have hG := horizon_le_slotRoundHZ (S := S) hd k
  unfold LeanDag.Hydrozoan.blamesInView
  rw [authorsOf_chopHZ]
  congr 1
  have hvr : LeanDag.Hydrozoan.votingRound Replica (S := slotsChopHZ hd) k
      = S.slotRound (d + k) - G + 1 := rfl
  rw [hvr, blocksAt_chopHZ]
  have hsum : G + (S.slotRound (d + k) - G + 1)
      = LeanDag.Hydrozoan.votingRound Replica (d + k) := by
    unfold LeanDag.Hydrozoan.votingRound; omega
  rw [hsum]
  ext b
  simp only [Finset.mem_inter, Finset.mem_filter, LeanDag.Hydrozoan.blocksAt,
    LeanDag.Hydrozoan.votingRound] at *
  constructor
  · rintro ⟨⟨⟨hb, hbr⟩, hblame⟩, hV⟩
    refine ⟨⟨⟨hb, hbr⟩, ?_⟩, (mem_viewChopHZ (V := V) (by omega)).mp hV⟩
    intro j hj hL
    exact hblame j (by rw [chopHZ_parents_of_lt (by omega)]; exact hj)
      ((isLeaderBlockHZ_chop (hsp := hsp) hd).mpr hL)
  · rintro ⟨⟨⟨hb, hbr⟩, hblame⟩, hV⟩
    refine ⟨⟨⟨hb, hbr⟩, ?_⟩, (mem_viewChopHZ (V := V) (by omega)).mpr hV⟩
    intro j hj hL
    rw [chopHZ_parents_of_lt (U := U) (hsp := hsp) (by omega)] at hj
    exact hblame j hj ((isLeaderBlockHZ_chop (hsp := hsp) hd).mp hL)

theorem skippedLeaderInView_chopHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    LeanDag.Hydrozoan.SkippedLeaderInView (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k
      ↔ LeanDag.Hydrozoan.SkippedLeaderInView U V (d + k) := by
  unfold LeanDag.Hydrozoan.SkippedLeaderInView
  rw [blamesInView_chopHZ (V := V) hd k]

/-- Rung 1's test: the certificate and the anchor both sit above the
cut, so both the certificate set and the reachability transport. -/
theorem certifiedIn_chopHZ (hd : G ≤ S.slotRound d) {A L : BlockId}
    (hA : A ∈ U.ids) (k : ℕ) :
    LeanDag.Hydrozoan.CertifiedIn (chopHZ U hsp G) A L
        ((slotsChopHZ hd).slotRound k)
      ↔ LeanDag.Hydrozoan.CertifiedIn U A L (S.slotRound (d + k)) := by
  have hG := horizon_le_slotRoundHZ (S := S) hd k
  unfold LeanDag.Hydrozoan.CertifiedIn
  have hr : G + (slotsChopHZ hd).slotRound k = S.slotRound (d + k) := by
    show G + (S.slotRound (d + k) - G) = S.slotRound (d + k); omega
  rw [certificates_chopHZ, hr]
  constructor
  · rintro ⟨C, hC, hreach⟩
    exact ⟨C, hC, reaches_of_reaches_chopHZ hreach⟩
  · rintro ⟨C, hC, hreach⟩
    refine ⟨C, hC, reaches_chopHZ_of_reaches hA hreach ?_⟩
    simp only [LeanDag.Hydrozoan.certificates, LeanDag.Hydrozoan.blocksAt,
      Finset.mem_filter] at hC
    omega

/-- Rung 2's test: the witness set is the same set of blocks, each a
voting-round block above the cut. -/
theorem weakLinked_chopHZ (hd : G ≤ S.slotRound d) {A L : BlockId}
    (hA : A ∈ U.ids) (k : ℕ) :
    LeanDag.Hydrozoan.WeakLinked (chopHZ U hsp G) A L
        ((slotsChopHZ hd).slotRound k)
      ↔ LeanDag.Hydrozoan.WeakLinked U A L (S.slotRound (d + k)) := by
  have hG := horizon_le_slotRoundHZ (S := S) hd k
  have hr : G + ((slotsChopHZ hd).slotRound k + 1) = S.slotRound (d + k) + 1 := by
    show G + (S.slotRound (d + k) - G + 1) = S.slotRound (d + k) + 1; omega
  unfold LeanDag.Hydrozoan.WeakLinked
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s, fun b hb => ?_, by rwa [authorsOf_chopHZ] at hcard⟩
    obtain ⟨hbAt, hbv, hbr⟩ := hs b hb
    rw [blocksAt_chopHZ, hr] at hbAt
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hbAt
    exact ⟨by simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]; exact hbAt,
      (isVote_chopHZ (by omega)).mp hbv, reaches_of_reaches_chopHZ hbr⟩
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s, fun b hb => ?_, by rw [authorsOf_chopHZ]; exact hcard⟩
    obtain ⟨hbAt, hbv, hbr⟩ := hs b hb
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter] at hbAt
    refine ⟨?_, (isVote_chopHZ (by omega)).mpr hbv,
      reaches_chopHZ_of_reaches hA hbr (by omega)⟩
    rw [blocksAt_chopHZ, hr]
    simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter]
    exact hbAt

end SlotRules


/-! ## P7 — the decision relation survives the cut

The two directions, by structural induction on the derivation. Every
premise is discharged by a transfer of §"the rules transported"; what
the induction itself does is re-index slots by the base slot `d` and
match the derivation trees constructor for constructor.

The three graded rungs carry negative premises — no candidate has an
anchor-linked certificate, no candidate clears the weak quorum — and
those transport because every rule transfer above is a
**biconditional**, not a one-way implication. That is what retires the
risk `docs/hydrozoan-integration.md` §5 records for this step. -/

section Anchor

variable [LinearOrder BlockId]

/-- A commit verdict is about a candidate of its slot, so the anchor of
an indirect derivation is a block of the universe. Stated over an
arbitrary universe and schedule, since the induction below needs it at
the truncation's. -/
theorem isLeaderBlock_of_decidedHZ
    {W : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {SS : LeanDag.Hydrozoan.Slots Replica}
    {V : LeanDag.Hydrozoan.View W} {k : ℕ} {L : BlockId}
    (h : LeanDag.Hydrozoan.Decided (S := SS) W V k (some L)) :
    LeanDag.Hydrozoan.IsLeaderBlock (S := SS) W k L := by
  cases h with
  | directFast hL _ => exact hL
  | directSlow hL _ => exact hL
  | indirectCert _ _ _ _ hL _ => exact hL
  | indirectWeak _ _ _ _ _ hL _ _ => exact hL

end Anchor

section Induction

variable [LinearOrder BlockId] [S : LeanDag.Hydrozoan.Slots Replica] {d : ℕ}

/-- The cut and the re-indexing cancel above the base slot. -/
theorem chopRound_add (hd : G ≤ S.slotRound d) (k : ℕ) :
    G + (slotsChopHZ hd).slotRound k = S.slotRound (d + k) := by
  have := horizon_le_slotRoundHZ (S := S) hd k
  show G + (S.slotRound (d + k) - G) = S.slotRound (d + k)
  omega

/-- Forward: a verdict reached on the truncation is the original
verdict, at the re-indexed slot. -/
theorem decided_of_decided_chopHZ (hd : G ≤ S.slotRound d)
    {V : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
      (View.chopHZ V hsp G) k v) :
    LeanDag.Hydrozoan.Decided U V (d + k) v := by
  induction h with
  | @directFast k L hL hc =>
      have hGk := horizon_le_slotRoundHZ (S := S) hd k
      refine LeanDag.Hydrozoan.Decided.directFast ((isLeaderBlockHZ_chop hd).mp hL) ?_
      have h2 := (fastCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mp hc
      rwa [chopRound_add hd k] at h2
  | @directSlow k L hL hc =>
      have hGk := horizon_le_slotRoundHZ (S := S) hd k
      refine LeanDag.Hydrozoan.Decided.directSlow ((isLeaderBlockHZ_chop hd).mp hL) ?_
      have h2 := (slowCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mp hc
      rwa [chopRound_add hd k] at h2
  | @directSkip k hskip =>
      exact LeanDag.Hydrozoan.Decided.directSkip
        ((skippedLeaderInView_chopHZ (V := V) hd k).mp hskip)
  | @indirectCert k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      have hGk := horizon_le_slotRoundHZ (S := S) hd k
      have hA : A ∈ U.ids :=
        (mem_chopHZ_ids.mp (isLeaderBlock_of_decidedHZ hanchor).1).1
      refine LeanDag.Hydrozoan.Decided.indirectCert (by omega)
        ((eligibleAsAnchorHZ_chop hd).mp helig) ihj ?_
        ((isLeaderBlockHZ_chop hd).mp hL) ?_
      · intro i h1 h2 he
        obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
        exact ihmid i' (by omega) (by omega) ((eligibleAsAnchorHZ_chop hd).mpr he)
      · exact (certifiedIn_chopHZ hd hA k).mp hcert
  | @indirectWeak k j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      have hGk := horizon_le_slotRoundHZ (S := S) hd k
      have hA : A ∈ U.ids :=
        (mem_chopHZ_ids.mp (isLeaderBlock_of_decidedHZ hanchor).1).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak (by omega)
        ((eligibleAsAnchorHZ_chop hd).mp helig) ihj ?_ ?_
        ((isLeaderBlockHZ_chop hd).mp hL) ((weakLinked_chopHZ hd hA k).mp hweak) ?_
      · intro i h1 h2 he
        obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
        exact ihmid i' (by omega) (by omega) ((eligibleAsAnchorHZ_chop hd).mpr he)
      · intro L' hL' hcert
        exact hnocert L' ((isLeaderBlockHZ_chop hd).mpr hL')
          ((certifiedIn_chopHZ hd hA k).mpr hcert)
      · intro L' hL' hw
        exact hmin L' ((isLeaderBlockHZ_chop hd).mpr hL')
          ((weakLinked_chopHZ hd hA k).mpr hw)
  | @indirectSkip k j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      have hGk := horizon_le_slotRoundHZ (S := S) hd k
      have hA : A ∈ U.ids :=
        (mem_chopHZ_ids.mp (isLeaderBlock_of_decidedHZ hanchor).1).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip (by omega)
        ((eligibleAsAnchorHZ_chop hd).mp helig) ihj ?_ ?_ ?_
      · intro i h1 h2 he
        obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
        exact ihmid i' (by omega) (by omega) ((eligibleAsAnchorHZ_chop hd).mpr he)
      · intro L' hL' hcert
        exact hnocert L' ((isLeaderBlockHZ_chop hd).mpr hL')
          ((certifiedIn_chopHZ hd hA k).mpr hcert)
      · intro L' hL' hw
        exact hnoweak L' ((isLeaderBlockHZ_chop hd).mpr hL')
          ((weakLinked_chopHZ hd hA k).mpr hw)

/-- Backward: the original verdict is reached on the truncation.
Generalised over the slot, with the re-indexing threaded as an
equation, so that the induction can move through anchors — an anchor of
slot `d + k` is not itself `d + k`. -/
theorem decided_chopHZ_of_decided (hd : G ≤ S.slotRound d)
    {V : LeanDag.Hydrozoan.View U} {n : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V n v) :
    ∀ k, n = d + k →
      LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k v := by
  induction h with
  | @directFast n L hL hc =>
      rintro k rfl
      refine LeanDag.Hydrozoan.Decided.directFast (S := slotsChopHZ hd) ((isLeaderBlockHZ_chop hd).mpr hL) ?_
      refine (fastCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mpr ?_
      rwa [chopRound_add hd k]
  | @directSlow n L hL hc =>
      rintro k rfl
      refine LeanDag.Hydrozoan.Decided.directSlow (S := slotsChopHZ hd) ((isLeaderBlockHZ_chop hd).mpr hL) ?_
      refine (slowCommitInView_chopHZ (V := V) L ((slotsChopHZ hd).slotRound k)).mpr ?_
      rwa [chopRound_add hd k]
  | @directSkip n hskip =>
      rintro k rfl
      exact LeanDag.Hydrozoan.Decided.directSkip (S := slotsChopHZ hd)
        ((skippedLeaderInView_chopHZ (V := V) hd k).mpr hskip)
  | @indirectCert n j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectCert (S := slotsChopHZ hd) (by omega)
        ((eligibleAsAnchorHZ_chop hd).mpr helig) (ihj j' rfl) ?_
        ((isLeaderBlockHZ_chop hd).mpr hL) ((certifiedIn_chopHZ hd hA k).mpr hcert)
      intro i' h1 h2 he
      exact ihmid (d + i') (by omega) (by omega)
        ((eligibleAsAnchorHZ_chop hd).mp he) i' rfl
  | @indirectWeak n j A L hkj helig hanchor hmid hnocert hL hweak hmin ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := slotsChopHZ hd) (by omega)
        ((eligibleAsAnchorHZ_chop hd).mpr helig) (ihj j' rfl) ?_ ?_
        ((isLeaderBlockHZ_chop hd).mpr hL)
        ((weakLinked_chopHZ hd hA k).mpr hweak) ?_
      · intro i' h1 h2 he
        exact ihmid (d + i') (by omega) (by omega)
          ((eligibleAsAnchorHZ_chop hd).mp he) i' rfl
      · intro L' hL' hcert
        exact hnocert L' ((isLeaderBlockHZ_chop hd).mp hL')
          ((certifiedIn_chopHZ hd hA k).mp hcert)
      · intro L' hL' hw
        exact hmin L' ((isLeaderBlockHZ_chop hd).mp hL')
          ((weakLinked_chopHZ hd hA k).mp hw)
  | @indirectSkip n j A hkj helig hanchor hmid hnocert hnoweak ihj ihmid =>
      rintro k rfl
      obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
      have hA : A ∈ U.ids := (isLeaderBlock_of_decidedHZ hanchor).1
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := slotsChopHZ hd) (by omega)
        ((eligibleAsAnchorHZ_chop hd).mpr helig) (ihj j' rfl) ?_ ?_ ?_
      · intro i' h1 h2 he
        exact ihmid (d + i') (by omega) (by omega)
          ((eligibleAsAnchorHZ_chop hd).mp he) i' rfl
      · intro L' hL' hcert
        exact hnocert L' ((isLeaderBlockHZ_chop hd).mp hL')
          ((certifiedIn_chopHZ hd hA k).mp hcert)
      · intro L' hL' hw
        exact hnoweak L' ((isLeaderBlockHZ_chop hd).mp hL')
          ((weakLinked_chopHZ hd hA k).mp hw)

/-- **P7 — the decision relation survives the cut.** A replica that has
pruned below the horizon reaches exactly the verdicts it would have
reached with its whole history, at the re-indexed slot. The base-slot
premise `G ≤ S.slotRound d` is the only condition: no synchrony, no
fairness, no liveness. -/
theorem decided_chopHZ (hd : G ≤ S.slotRound d)
    {V : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId} :
    LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k v
      ↔ LeanDag.Hydrozoan.Decided U V (d + k) v :=
  ⟨decided_of_decided_chopHZ hd, fun h => decided_chopHZ_of_decided hd h k rfl⟩

/-- **Cross-cut agreement.** A replica that has pruned below the horizon
and one that has not cannot disagree about a slot. The pruned replica's
view `W` is an *arbitrary* view of the truncation, not a truncated
full-history view — a joiner's view is never of the latter form, since
lifted to `U` it would not be downward closed, its base layer having
lost its parents. The proof plays HZ3 inside the truncation and moves
across the cut by `decided_chopHZ_of_decided`. -/
theorem decided_agree_chopHZ (hd : G ≤ S.slotRound d)
    {V : LeanDag.Hydrozoan.View U} {W : LeanDag.Hydrozoan.View (chopHZ U hsp G)}
    {k : ℕ} {v w : Option BlockId}
    (hV : LeanDag.Hydrozoan.Decided U V (d + k) v)
    (hW : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G) W k w) :
    v = w :=
  (@LeanDag.Hydrozoan.SlotAgreement.holds Replica BlockId _ _ _ _ _ (slotsChopHZ hd)
    (chopHZ U hsp G) W (View.chopHZ V hsp G) k w v hW
    (decided_chopHZ_of_decided hd hV k rfl)).symm

end Induction

end Hydrozoan

end Integration

end LeanDag
