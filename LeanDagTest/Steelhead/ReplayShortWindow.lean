import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Replay.Proof
import Mathlib.Order.Interval.Finset.Nat
/-!
# Steelhead witnesses: a complete window too short for a wave

The adaptive section bounds the interval by `I ≥ 2 · maxPeriod`, so that every window holds two
asynchronous slots. At `I = 4` and `maxPeriod = 2` the bound holds, yet the asynchronous wave is
`5`: no window of four rounds ever holds the decision round of one of its asynchronous slots, so
the replay resolves none of them, at any period (`steelhead.md` §7). One universe, `rw44`:
eleven rounds `0..10` shaped as `rs36` is, every synchronous slot at two votes and two blames.
With candidates `[1, 2]`, the waves `3` and `5`, the canary `7` and the known leader
`(r + 1) mod 4`:

* the startup window of the anchor at round `2` (block `9`) keeps period `2`;
* the window of the anchor at round `6` (block `25`) is complete: rounds `3` to `6`, two of them
  asynchronous under period `2`, and no wave of `5` fits;
* no synchronous slot of that window commits, and the slots at rounds `3` and `5` are neither
  committed nor skipped in the full universe;
* both candidates score `6`, so **Algorithm 2 keeps period `2` at every hysteresis `ε ≥ 0`**,
  although no synchronous slot committed.

The bound the replay needs is `I ≥ max(2 · maxPeriod, w_a)`.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead LeanDag.Steelhead.Replay

set_option maxRecDepth 8192

/-- Block `4m + v` is validator `v`'s round-`m` block, referencing as in `rs36`. -/
def rw44Blk (i : Fin 44) : Block (Fin 4) (Fin 44) Unit where
  round := i.val / 4
  creator := ⟨i.val % 4, by omega⟩
  refs := Finset.univ.filter fun q => q.val / 4 + 1 = i.val / 4 ∧
    (i.val % 4 = (i.val / 4) % 4 ∨ i.val % 4 = ((i.val / 4) + 3) % 4 ∨
      q.val % 4 ≠ (i.val / 4) % 4)
  payload := ()

/-- **`rw44`**: eleven rounds, every synchronous slot at two votes and two blames. -/
def rw44 : BlockUniverse (Fin 4) (Fin 44) Unit where
  ids := Finset.univ
  block := rw44Blk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The waves `3` and `5`, the canary `7`, and the known leader `(r + 1) mod 4`. -/
def rwConfig : Config (Fin 4) := ⟨3, 5, 7, fun r => ⟨(r + 1) % 4, by omega⟩⟩

/-- **The complete window**: the causal history of the anchor at round `6`, block `25`, over
four rounds. -/
def rwWindow : Evidence (Fin 4) := ofAnchor rw44 25 4

/-- The startup window, of the anchor at round `2`, keeps period `2`. -/
theorem rw44_startup_keeps_two : anchorUpdate rw44 4 rwConfig [1, 2] (1 / 10) 0 9 ∅ 2 = 2 := by
  decide +kernel

/-- The complete window is rounds `3` to `6`, two of them asynchronous under period `2`. -/
theorem rwWindow_bounds : rwWindow.bottom = 3 ∧ rwWindow.top = 6 ∧
    ((rounds rwWindow).filter fun r => r % 2 == 0).length = 2 := by decide +kernel

/-- No wave of `5` fits in the window: every round's decision round lies past the top. -/
theorem rwWindow_no_wave_fits : ∀ r ∈ rounds rwWindow, rwWindow.top < r + 5 - 1 := by
  decide +kernel

/-- No synchronous slot of the window commits. -/
theorem rwWindow_no_sync_commit : ∀ r ∈ Finset.Icc 3 6,
    ¬ rwWindow.commits r 3 (rwConfig.known r) := by decide +kernel

/-- The synchronous slots at rounds `3` and `5` are undecided in the full universe, whose rounds
hold their whole waves. -/
theorem rw44_sync_undecided : ∀ r ∈ ({3, 5} : Finset ℕ),
    ¬ MahiMahi.DirectSkipIn rw44 (View.full rw44) 3 (rwConfig.known r) r ∧
    ∀ L : Fin 44, IsLeaderBlock (S := chainSlots rwConfig.known) rw44 r L →
      ¬ MahiMahi.DirectCommitIn rw44 (View.full rw44) 3 L r := by decide +kernel

/-- **Both candidates score `6`** on the complete window. -/
theorem rwWindow_scores : score rwWindow rwConfig 1 = 6 ∧ score rwWindow rwConfig 2 = 6 := by
  decide +kernel

/-- **Algorithm 2 keeps period `2` at every hysteresis**: the best candidate scores what the
current period scores, and no `ε ≥ 0` makes `6 < (1 − ε) · 6`. -/
theorem rw44_keeps_two (epsilon : ℚ) (he : 0 ≤ epsilon) :
    anchorUpdate rw44 4 rwConfig [1, 2] epsilon 1 25 ∅ 2 = 2 := by
  change select [1, 2] (score rwWindow rwConfig) 2 epsilon = 2
  have hmem := best_mem [1, 2] (score rwWindow rwConfig) 2 (by simp)
  have hbest : score rwWindow rwConfig (best [1, 2] (score rwWindow rwConfig) 2) = 6 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> rw [h]
    · exact rwWindow_scores.1
    · exact rwWindow_scores.2
  dsimp only [select]
  split
  · rename_i h
    rw [hbest, rwWindow_scores.2] at h
    linarith
  · rfl

#print axioms rw44
#print axioms rw44_sync_undecided
#print axioms rw44_keeps_two

end LeanDagTest
