import LeanDagTest.Integration.HydrozoanUniverse
import LeanDag.Integration.Hydrozoan.Stack

/-!
# The fill and the stack — witnesses

P8 and P9 on a universe built for them. The witness universes of the
Hydrozoan arc cannot host a `SkipMsg`: `U7`'s crashed replica authors
nothing at all, so there is no anchor to fill from, and the
seven-replica universe fails `SelfParenting`. This one is a
three-round DAG over four replicas in which replica `1` authors its
genesis block and then stops — a crash with an anchor.

Identifiers are `ℕ` rather than a `Fin`, which is what `SkipMsg.hidx`
forces: `idx (fresh k) = k` at every `k`, so `fresh` is injective on all
of `ℕ` and cannot land in a finite type. The existing Safe Skip
witnesses make the same choice.

What the configuration exercises:

* **a commit and a skip before the recovery** — slot `0` fast-commits
  its candidate at exactly `qFast = 3`, and slot `1`, led by the
  crashed replica, has no candidate and is skipped by three vacuous
  blames;
* **the fill gives slot `1` a candidate** — the filled block at round
  `1` is authored by replica `1`, which is slot `1`'s leader, so the
  slot goes from having no candidate to having one;
* **and the skip survives anyway** — which is
  `docs/hydrozoan-integration.md` §5.1's finding on data. The core
  needs a quorum hypothesis at exactly this point, because its skip is
  stated per candidate and the new candidate demands a fresh
  justification. Hydrozoan's is a count at the slot, and no old block
  references a fresh identifier, so the count does not move.
-/

namespace LeanDagTest

namespace Integration

open LeanDag LeanDag.Integration.Hydrozoan
open LeanDagTest.Hydrozoan (fourReplicas)

/-- Ten blocks over four replicas: genesis for all four, then rounds
`1` and `2` authored by `{0, 2, 3}` alone. Replica `1` crashes after
its genesis block, which is the anchor a `SkipMsg` needs. -/
def lkf : ℕ → LeanDag.Hydrozoan.Block (Fin 4) ℕ := fun i =>
  if h : i < 4 then { round := 0, author := ⟨i, h⟩, parents := ∅ }
  else if i < 7 then
    { round := 1
      author := if i = 4 then 0 else if i = 5 then 2 else 3
      parents := {0, 2, 3} }
  else if i < 10 then
    { round := 2
      author := if i = 7 then 0 else if i = 8 then 2 else 3
      parents := {4, 5, 6} }
  else { round := 0, author := 0, parents := ∅ }

/-- The universe: a crash with an anchor. -/
def Ucr : LeanDag.Hydrozoan.BlockUniverse (Fin 4) ℕ where
  ids := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  block := lkf
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- Every non-genesis block references its own author's block below. -/
theorem selfParenting_Ucr : SelfParenting Ucr := by decide

/-- The full view. -/
abbrev Vcr : LeanDag.Hydrozoan.View Ucr := LeanDag.Hydrozoan.View.full Ucr

/-! ## Before the recovery: a commit and a skip -/

example : LeanDag.Hydrozoan.IsLeaderBlock Ucr 0 0 := by decide

/-- Slot `0` fast-commits at exactly the quorum: three supporters
against `qFast = 3`. -/
theorem committed_slot_zero : LeanDag.Hydrozoan.Decided Ucr Vcr 0 (some 0) :=
  LeanDag.Hydrozoan.Decided.directFast (by decide) (by decide)

/-- Slot `1` is led by the crashed replica and has no candidate.
Quantified over the identifiers the universe holds — candidacy requires
membership, so that is the whole of it, and it keeps the statement
decidable over `ℕ` ids. -/
example : ∀ L ∈ Ucr.ids, ¬ LeanDag.Hydrozoan.IsLeaderBlock Ucr 1 L := by decide

/-- So it is skipped, by three vacuous blames. -/
theorem skipped_slot_one_cr : LeanDag.Hydrozoan.Decided Ucr Vcr 1 none :=
  LeanDag.Hydrozoan.Decided.directSkip (by decide)

/-! ## The recovery message -/

/-- Replica `1` rejoins from its genesis block, on replica `0`'s line,
filling rounds `1` and `2`. -/
def skcr : SkipMsg (toCore Ucr selfParenting_Ucr) where
  v1 := 1
  B1 := 1
  v2 := 0
  r := 2
  line k := if k = 0 then 0 else if k = 1 then 4 else 7
  fresh k := 10 + k
  idx b := b - 10
  hB1uniq := by decide
  hv12 := by decide
  hB1 := by decide
  hB1c := by decide
  hline_mem := by
    intro k _ hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  hline_creator := by
    intro k _ hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  hline_round := by
    intro k _ hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  hline_chain := by
    intro k hk1 hk2
    have hr0 : ((toCore Ucr selfParenting_Ucr).block 1).round = 0 := rfl
    rw [hr0] at hk1
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl <;> decide
  hfresh_new := by
    intro k
    show (10 + k) ∉ Ucr.ids
    simp only [Ucr, Finset.mem_insert, Finset.mem_singleton]
    omega
  hidx := by intro k; omega
  hgap := by decide

/-! ## After the recovery

The filled block at round `1` is authored by replica `1`, which leads
slot `1`, so the slot acquires a candidate it did not have. -/

example : LeanDag.Hydrozoan.IsLeaderBlock (skipFillHZ Ucr selfParenting_Ucr skcr) 1
    (skcr.fresh 1) := by decide

/-- **The skip survives the fill**, though the slot now has a candidate
— and with no quorum hypothesis, which is §5.1's finding. -/
example : LeanDag.Hydrozoan.Decided (skipFillHZ Ucr selfParenting_Ucr skcr)
    (liftViewHZ Ucr selfParenting_Ucr skcr Vcr) 1 none :=
  decided_fillHZ skipped_slot_one_cr

/-- And the commit survives it. -/
example : LeanDag.Hydrozoan.Decided (skipFillHZ Ucr selfParenting_Ucr skcr)
    (liftViewHZ Ucr selfParenting_Ucr skcr Vcr) 0 (some 0) :=
  decided_fillHZ committed_slot_zero

/-! ## The stack: recovered, then pruned

Cutting at `G = 1` from base slot `d = 1`, slot `1` of the original is
slot `0` of the stack. -/

theorem hdcr : (1 : ℕ) ≤ LeanDag.Hydrozoan.Slots.slotRound (Fin 4) 1 := by decide

/-- **The skip survives the whole stack.** -/
example : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hdcr)
    (stackHZ Ucr selfParenting_Ucr skcr 1)
    (stackView Ucr selfParenting_Ucr skcr 1 Vcr) 0 none :=
  decided_stackHZ hdcr skipped_slot_one_cr

/-- **And nobody can disagree with the recovered, pruned replica** —
over an arbitrary view of the stack. -/
example (W : LeanDag.Hydrozoan.View (stackHZ Ucr selfParenting_Ucr skcr 1))
    (w : Option ℕ)
    (hW : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hdcr)
      (stackHZ Ucr selfParenting_Ucr skcr 1) W 0 w) :
    none = w :=
  agree_stackHZ hdcr skipped_slot_one_cr hW

end Integration

end LeanDagTest
