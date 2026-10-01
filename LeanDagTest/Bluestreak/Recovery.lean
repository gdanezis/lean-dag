import LeanDag.Bluestreak.Record
import Mathlib.Tactic.FinCases

/-!
# Bluestreak recovering from a crash, in one message

Four validators, `f = 1`, the Byzantine `0`, one leader per round,
`leader k = k mod 4`, ids `4·round + creator`. Validator `3` crashes
after round `1`: `Ucr` holds rounds `0` to `4` without its blocks at
rounds `2` to `4`, so round `3`, which it leads, has no candidate. The
round-`3` blocks claim the round-`1` leader and the round-`4` blocks the
round-`2` leader.

Its recovery message is `rcGap`: `v1 = 3`, `B1 = 7`, the target round
`3`, and fresh ids `100 + k`. The chain fill adds `102` and `103`,
ordinary and claiming nothing. The discipline survives it, slot `2`
stays committed, and slot `3`, whose candidate is now the untagged
`103`, stays skipped.
-/

namespace LeanDagTest

open LeanDag LeanDag.Bluestreak

namespace Recovery

instance rcFaults : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

instance rcSlots : Slots (Fin 4) := Slots.identity fun k => ⟨k % 4, Nat.mod_lt _ (by omega)⟩

/-- A block from its round, creator, references and claim, tagged a
leader block when its creator leads its round. -/
def rcBlock (r v : ℕ) (hv : v < 4) (refs : Finset ℕ) (c : Option ℕ) :
    Block (Fin 4) ℕ (Bool × Option ℕ) :=
  { round := r, creator := ⟨v, hv⟩, refs := refs, payload := (decide (v = r % 4), c) }

def rcBlk : ℕ → Block (Fin 4) ℕ (Bool × Option ℕ)
  | 0 => rcBlock 0 0 (by omega) ∅ none | 1 => rcBlock 0 1 (by omega) ∅ none
  | 2 => rcBlock 0 2 (by omega) ∅ none | 3 => rcBlock 0 3 (by omega) ∅ none
  | 4 => rcBlock 1 0 (by omega) {0} none | 5 => rcBlock 1 1 (by omega) {0, 1, 2, 3} none
  | 6 => rcBlock 1 2 (by omega) {2, 0} none | 7 => rcBlock 1 3 (by omega) {3, 0} none
  | 8 => rcBlock 2 0 (by omega) {4, 5} none | 9 => rcBlock 2 1 (by omega) {5} none
  | 10 => rcBlock 2 2 (by omega) {4, 5, 6, 7} none
  | 12 => rcBlock 3 0 (by omega) {8, 10} (some 5) | 13 => rcBlock 3 1 (by omega) {9, 10} (some 5)
  | 14 => rcBlock 3 2 (by omega) {10} (some 5)
  | 16 => rcBlock 4 0 (by omega) {12, 13, 14} none
  | 17 => rcBlock 4 1 (by omega) {13} (some 10) | 18 => rcBlock 4 2 (by omega) {14} (some 10)
  | _ => rcBlock 0 0 (by omega) ∅ none

def rcIds : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18}

/-- The universe before recovery: `3` silent from round `2`. -/
def Ucr : Universe (Fin 4) ℕ (Bool × Option ℕ) where
  ids := rcIds
  block := rcBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem Ucr_disciplined : Disciplined Ucr := Disciplined.of_decide (by decide)

theorem lt_of_mem_rcIds {b : ℕ} (h : b ∈ rcIds) : b < 19 := by
  revert b; decide

/-- **The recovery message**: `3`, its last block `7`, the target round
`3`, and fresh ids above the universe's. -/
def rcGap : GapData Ucr.ids Ucr.block where
  v1 := 3
  B1 := 7
  r := 3
  fresh k := 100 + k
  idx b := b - 100
  hB1 := by decide
  hB1c := rfl
  hfresh_new k h := by have := lt_of_mem_rcIds h; omega
  hidx k := by omega
  hgap := by decide

/-- An ordinary payload with no claim. -/
theorem rc_leader : Format.leader (BlockId := ℕ) ((false, none) : Bool × Option ℕ) = false := rfl

/-- **The universe after recovery.** -/
def Ufill : Universe (Fin 4) ℕ (Bool × Option ℕ) := chainFill rcGap rc_leader

/-- The filled blocks: `102` references `B1`, `103` references `102`,
both by `3` and untagged. -/
example : (Ufill.block 102).refs = {7} ∧ (Ufill.block 103).refs = {102} ∧
    (Ufill.block 103).round = 3 ∧ (Ufill.block 103).creator = 3 ∧ ¬ Tagged Ufill 103 := by
  decide

/-- **The discipline survives the recovery** (BS19 at the witness). -/
theorem Ufill_disciplined : Disciplined Ufill :=
  disciplined_chainFill rcGap rc_leader Ucr_disciplined rfl

/-- Slot `2` is committed before the recovery: three claims at round
`4`, the leader `16`'s carried by its votes. -/
theorem Ucr_slot2 : Decided Ucr (View.full Ucr) 2 (some 10) :=
  Decided.directCommit (by decide) (by decide)

/-- Slot `3` is skipped before the recovery: it has no candidate. -/
theorem Ucr_slot3 : Decided Ucr (View.full Ucr) 3 none :=
  Decided.directSkip (by decide)

/-- **And after it**: slot `2` is committed, and slot `3`, whose
candidate is now the filled `103`, is skipped — no round-`4` block
references it. -/
theorem Ufill_slot2 : Decided Ufill (View.full Ufill) 2 (some 10) :=
  Decided.directCommit (by decide) (by decide)

theorem Ufill_slot3 : Decided Ufill (View.full Ufill) 3 none :=
  Decided.directSkip (by decide)

example : leaderBlocksAt (S := rcSlots) Ufill 3 = {103} := by decide

/-- **The fill cell at the witness**: the carrier's fill, and every verdict
of the crashed universe carried across it by `decided_fill`. -/
example {k : ℕ} {v : Option ℕ} (h : Decided Ucr (View.full Ucr) k v) :
    (BluestreakProperties.bluestreakRule (Validator := Fin 4) (BlockId := ℕ)
      (Payload := Bool × Option ℕ)).Decided rcSlots
      (BluestreakProperties.onRecord.liftView
        (hI := disciplined_chainFill rcGap rc_leader Ucr_disciplined rfl)
        (U := ⟨Ucr, Ucr_disciplined⟩) (View.full Ucr)) k v :=
  BluestreakProperties.onRecord.decided_fill BluestreakProperties.banded h

/-- **The prompt skip at the witness**: on the full view of the
carrier's fill, the quorum `{0, 1, 2}` is present at round `4`, so
slot `3`, which the recovering `3` leads inside its gap, is skipped. -/
example : (BluestreakProperties.bluestreakRule (Validator := Fin 4) (BlockId := ℕ)
    (Payload := Bool × Option ℕ)).Decided rcSlots
    (U := BluestreakProperties.fill ⟨Ucr, Ucr_disciplined⟩ rcGap rc_leader rfl)
    (View.full (BluestreakProperties.fill ⟨Ucr, Ucr_disciplined⟩ rcGap rc_leader rfl).val) 3
    none := by
  refine BluestreakProperties.decided_none_fresh (S := rcSlots) (U := ⟨Ucr, Ucr_disciplined⟩)
    (k := 3) (T := {0, 1, 2}) rcGap rc_leader rfl ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · rfl
  · show 1 < 3; omega
  · show 3 ≤ 3; omega
  intro v hv
  fin_cases hv
  · exact ⟨16, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩

end Recovery

end LeanDagTest
