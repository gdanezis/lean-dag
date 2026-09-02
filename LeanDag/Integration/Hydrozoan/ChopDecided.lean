import LeanDag.Integration.Hydrozoan.Transport
import LeanDag.GC.ChopDecided

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
  [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)]
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

omit [Fintype Replica] [DecidableEq Replica] F [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)] in
@[simp] theorem slotsChopHZ_slotRound (hd : G ≤ S.slotRound d) (k : ℕ) :
    (slotsChopHZ hd).slotRound k = S.slotRound (d + k) - G := rfl

omit [Fintype Replica] [DecidableEq Replica] F [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)] in
@[simp] theorem slotsChopHZ_leader (hd : G ≤ S.slotRound d) (k : ℕ) :
    (slotsChopHZ hd).leader k = S.leader (d + k) := rfl

omit [Fintype Replica] [DecidableEq Replica] F [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)] in
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

omit [Fintype Replica] [DecidableEq Replica] F [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)] in
/-- Anchor eligibility is re-indexed, both slots moving together. -/
theorem eligibleAsAnchorHZ_chop (hd : G ≤ S.slotRound d) {k j : ℕ} :
    @LeanDag.Hydrozoan.EligibleAsAnchor Replica (slotsChopHZ hd) k j
      ↔ LeanDag.Hydrozoan.EligibleAsAnchor Replica (d + k) (d + j) := by
  have hk := horizon_le_slotRoundHZ (S := S) hd k
  have hj := horizon_le_slotRoundHZ (S := S) hd j
  show S.slotRound (d + k) - G + 2 < S.slotRound (d + j) - G
    ↔ S.slotRound (d + k) + 2 < S.slotRound (d + j)
  omega

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

end Hydrozoan

end Integration

end LeanDag
