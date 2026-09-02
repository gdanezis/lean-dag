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

end Hydrozoan

end Integration

end LeanDag
