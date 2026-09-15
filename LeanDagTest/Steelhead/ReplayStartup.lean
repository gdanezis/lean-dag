import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Replay.Proof
import Mathlib.Order.Interval.Finset.Nat
/-!
# Steelhead witnesses: the replay on a startup window

Theorem 3 of the paper assumes that the update rule maps a window in which no synchronous slot
commits to period `1`, and Algorithm 2 is meant to be that rule (`steelhead.md` §7, findings 3
and 4). One universe, `rs36`: nine rounds `0..8` of the committee of the other witnesses, in
which round `m`'s blocks by validators `m mod 4` and `(m + 3) mod 4` reference every block of
round `m − 1` while the other two omit the block of validator `m mod 4`, the known leader
`(r + 1) mod 4` of round `r = m − 1`; so every synchronous slot has two votes and two blames,
neither a quorum. At interval `8`, candidates `[1, 2, 4]`, current period `4`, the waves `3` and
`5`, the canary `7` and the first anchor at round `4` (block `16`):

* the window is rounds `1` to `4`, one asynchronous round and no synchronous commit or
  certificate; the synchronous slots are neither committed nor skipped in the full universe;
* every candidate period scores `6`: the window is too short to resolve any slot, so every
  outcome pays the window's top;
* **Algorithm 2 keeps period `4`**, at hysteresis `0` as at the deployment's `1/10`, and so does
  not map the window to period `1`.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead LeanDag.Steelhead.Replay

set_option maxRecDepth 8192

/-- Block `4m + v` is validator `v`'s round-`m` block; validators `m mod 4` and `(m + 3) mod 4`
reference all of round `m − 1`, the other two omit validator `m mod 4`'s block. -/
def rs36Blk (i : Fin 36) : Block (Fin 4) (Fin 36) Unit where
  round := i.val / 4
  creator := ⟨i.val % 4, by omega⟩
  refs := Finset.univ.filter fun q => q.val / 4 + 1 = i.val / 4 ∧
    (i.val % 4 = (i.val / 4) % 4 ∨ i.val % 4 = ((i.val / 4) + 3) % 4 ∨
      q.val % 4 ≠ (i.val / 4) % 4)
  payload := ()

/-- **`rs36`**: nine rounds, every synchronous slot at two votes and two blames. -/
def rs36 : BlockUniverse (Fin 4) (Fin 36) Unit where
  ids := Finset.univ
  block := rs36Blk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The waves `3` and `5`, the canary `7`, and the known leader `(r + 1) mod 4`. -/
def rsConfig : Config (Fin 4) := ⟨3, 5, 7, fun r => ⟨(r + 1) % 4, by omega⟩⟩

/-- **The startup window**: the causal history of the first anchor, block `16` at round `4`,
over the last eight rounds. -/
def rsWindow : Evidence (Fin 4) := ofAnchor rs36 16 8

/-- The window is rounds `1` to `4`, one of them asynchronous under period `4`. -/
theorem rsWindow_bounds : rsWindow.bottom = 1 ∧ rsWindow.top = 4 ∧
    ((rounds rsWindow).filter fun r => r % 4 == 0).length = 1 := by decide +kernel

/-- No synchronous slot of the window commits, and none is certified. -/
theorem rsWindow_no_sync_commit : ∀ r ∈ Finset.Icc 1 3,
    ¬ rsWindow.commits r 3 (rsConfig.known r) ∧ ¬ rsWindow.certified r 3 (rsConfig.known r) := by
  decide +kernel

/-- **The synchronous slots are undecided in the full universe**: neither directly skipped nor,
for any block of the leader, directly committed, at every round whose wave the universe holds. -/
theorem rs36_sync_undecided : ∀ r ∈ Finset.Icc 1 6, r % 4 ≠ 0 →
    ¬ MahiMahi.DirectSkipIn rs36 (View.full rs36) 3 (rsConfig.known r) r ∧
    ∀ L : Fin 36, IsLeaderBlock (S := chainSlots rsConfig.known) rs36 r L →
      ¬ MahiMahi.DirectCommitIn rs36 (View.full rs36) 3 L r := by decide +kernel

/-- No synchronous candidate has a certificate, so no anchor commits it either. -/
theorem rs36_no_sync_certificate : ∀ r ∈ Finset.Icc 1 6, r % 4 ≠ 0 →
    ∀ L : Fin 36, IsLeaderBlock (S := chainSlots rsConfig.known) rs36 r L →
      MahiMahi.certificates rs36 3 L r = ∅ := by decide +kernel

/-- **Every candidate period scores `6`** on the window. -/
theorem rsWindow_tied_scores : ∀ k ∈ ([1, 2, 4] : List ℕ), score rsWindow rsConfig k = 6 := by
  decide +kernel

/-- **Algorithm 2 keeps period `4`** at the anchor, at hysteresis `0` and at `1/10`. -/
theorem rs36_keeps_four :
    anchorUpdate rs36 8 rsConfig [1, 2, 4] 0 0 16 4 = 4 ∧
      anchorUpdate rs36 8 rsConfig [1, 2, 4] (1 / 10) 0 16 4 = 4 := by decide +kernel

#print axioms rs36
#print axioms rs36_sync_undecided
#print axioms rs36_keeps_four

end LeanDagTest
