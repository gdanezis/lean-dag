import LeanDagTest.Integration.HydrozoanTransport
import LeanDag.Integration.Hydrozoan.ChopDecided

/-!
# Verdicts across the cut — witnesses

P7 on the low-fault four-replica universe `U7`
(`LeanDagTest/Hydrozoan/DirectLiveness.lean`): three rounds, replicas
`{0, 2, 3}` producing at each, replica `1` crashed after genesis, slot
`k` at round `k` led by `k % 4`.

Slot `1` is led by the crashed replica, so it has no candidate at all,
and every round-`2` block blames it vacuously — three blames against
`qFast = 3`. It is therefore directly skipped, which is the verdict the
truncation must preserve.

Cutting at `G = 1` from base slot `d = 1`, slot `1` of the original is
slot `0` of the truncation, and `decided_chopHZ` carries the skip both
ways. The `decide` calls settle the rule on data; the transport is the
theorem.
-/

namespace LeanDagTest

namespace Integration

open LeanDag LeanDag.Integration.Hydrozoan

/-- The full view of the low-fault universe. -/
abbrev V7 : LeanDag.Hydrozoan.View LeanDagTest.Hydrozoan.U7 :=
  LeanDag.Hydrozoan.View.full LeanDagTest.Hydrozoan.U7

/-! ## Slot 1 has no candidate, and is skipped -/

example : ∀ L, ¬ LeanDag.Hydrozoan.IsLeaderBlock LeanDagTest.Hydrozoan.U7 1 L := by decide

/-- Three blames at the voting round, against `qFast = 3`. -/
theorem skipped_slot_one :
    LeanDag.Hydrozoan.SkippedLeaderInView LeanDagTest.Hydrozoan.U7 V7 1 := by decide

theorem decided_slot_one :
    LeanDag.Hydrozoan.Decided LeanDagTest.Hydrozoan.U7 V7 1 none :=
  LeanDag.Hydrozoan.Decided.directSkip skipped_slot_one

/-! ## The cut, and the verdict across it

Base slot `d = 1` sits at round `1`, so a horizon at `G = 1` clears it
and the premise `G ≤ slotRound d` holds. Slot `1` of the original is
slot `0` of the truncation. -/

theorem hd1 : (1 : ℕ) ≤ LeanDag.Hydrozoan.Slots.slotRound (Fin 4) 1 := by decide

/-- The truncation keeps the six blocks at rounds `1` and `2`. -/
example : (chopHZ LeanDagTest.Hydrozoan.U7 selfParenting_U7 1).ids
    = {3, 4, 5, 6, 7, 8} := by decide

/-- **The skip survives the cut**, at the re-indexed slot. -/
example : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd1)
    (chopHZ LeanDagTest.Hydrozoan.U7 selfParenting_U7 1)
    (View.chopHZ V7 selfParenting_U7 1) 0 none :=
  (decided_chopHZ (V := V7) hd1).mpr decided_slot_one

/-- And back the other way: a verdict reached on the truncation is the
original verdict. -/
example (v : Option (Fin 9))
    (h : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd1)
      (chopHZ LeanDagTest.Hydrozoan.U7 selfParenting_U7 1)
      (View.chopHZ V7 selfParenting_U7 1) 0 v) :
    LeanDag.Hydrozoan.Decided LeanDagTest.Hydrozoan.U7 V7 1 v :=
  (decided_chopHZ (V := V7) hd1).mp h

/-! ## Cross-cut agreement

A replica that has pruned and one that has not cannot disagree, and the
pruned replica's view is an arbitrary view of the truncation rather
than a truncated full-history view. -/

example (W : LeanDag.Hydrozoan.View
      (chopHZ LeanDagTest.Hydrozoan.U7 selfParenting_U7 1))
    (w : Option (Fin 9))
    (hW : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd1)
      (chopHZ LeanDagTest.Hydrozoan.U7 selfParenting_U7 1) W 0 w) :
    none = w :=
  decided_agree_chopHZ hd1 decided_slot_one hW

end Integration

end LeanDagTest
