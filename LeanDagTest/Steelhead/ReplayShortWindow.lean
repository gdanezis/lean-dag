import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Replay.Proof
import Mathlib.Order.Interval.Finset.Nat
/-!
# Steelhead witnesses: a complete window too short for a wave

The adaptive section bounds the interval by `I ≥ 2 · maxPeriod`, so that every window holds two
asynchronous slots. The window is the anchor's causal history at the rounds `round A − I` and
above, `I + 1` rounds, so it holds the decision round of an asynchronous slot of period `k'` only
when `I ≥ k' + w_a − 2`; at `I = 4`, `maxPeriod = 2` and `w_a = 5` the paper's bound holds and
this one does not, and whether the window resolves anything then turns on where the anchor falls
(`steelhead.md` §7). One universe, `rw44`: eleven rounds `0..10` shaped as `rs36` is, every
synchronous slot at two votes and two blames. With candidates `[1, 2]`, the waves `3` and `5`,
the canary `7` and the known leader `(r + 1) mod 4`:

* the startup window of the anchor at round `2` (block `9`) keeps period `2`;
* the window of the anchor at round `7` (block `28`) is complete: rounds `3` to `7`, two of them
  asynchronous under period `2`, and neither holds its own decision round;
* one round lower, at the anchor of round `6` (block `25`), the window does hold the decision
  round of its asynchronous slot at round `2`: the same parameters resolve a slot at one anchor
  and none at the next;
* no synchronous slot of the complete window commits, and the slots at rounds `3` and `5` are
  neither committed nor skipped in the full universe;
* both candidates score `10`, so **Algorithm 2 keeps period `2` at every hysteresis `ε ≥ 0`**,
  although no synchronous slot committed.

The bound the replay needs is `I ≥ max(2 · maxPeriod, maxPeriod + w_a − 2)`.
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
def rwConfig : Config (Fin 4) := ⟨3, 5, some 7, fun r => ⟨(r + 1) % 4, by omega⟩⟩

/-- **The complete window**: the causal history of the anchor at round `7`, block `28`, at the
rounds `7 − 4` and above. -/
def rwWindow : Evidence (Fin 4) := ofAnchor rw44 28 4

/-- The startup window, of the anchor at round `2`, keeps period `2`. -/
theorem rw44_startup_keeps_two : anchorUpdate rw44 4 rwConfig [1, 2] (1 / 10) 9 2 = 2 := by
  decide +kernel

/-- The complete window is rounds `3` to `7`, two of them asynchronous under period `2`. -/
theorem rwWindow_bounds : rwWindow.bottom = 3 ∧ rwWindow.top = 7 ∧
    ((rounds rwWindow).filter fun r => r % 2 == 0).length = 2 := by decide +kernel

/-- No wave of `5` fits above an asynchronous slot of the window: both lie too high for the
window to hold their decision rounds. -/
theorem rwWindow_no_wave_fits : ∀ r ∈ rounds rwWindow, r % 2 = 0 → rwWindow.top < r + 5 - 1 := by
  decide +kernel

/-- **One round lower the same parameters do resolve a slot**: the window of the anchor at round
`6` is rounds `2` to `6` and holds the decision round of its asynchronous slot at round `2`. So
`I ≥ 2 · maxPeriod` leaves the outcome to the anchor's round. -/
theorem rw44_lower_anchor_fits : (ofAnchor rw44 25 4).bottom = 2 ∧ (ofAnchor rw44 25 4).top = 6 ∧
    2 + 5 - 1 ≤ (ofAnchor rw44 25 4).top := by decide +kernel

/-- No synchronous slot of the window commits. -/
theorem rwWindow_no_sync_commit : ∀ r ∈ Finset.Icc 3 7,
    ¬ rwWindow.commits r 3 (rwConfig.known r) := by decide +kernel

/-- The synchronous slots at rounds `3` and `5` are undecided in the full universe, whose rounds
hold their whole waves. -/
theorem rw44_sync_undecided : ∀ r ∈ ({3, 5} : Finset ℕ),
    ¬ MahiMahi.DirectSkipIn rw44 (View.full rw44) 3 (rwConfig.known r) r ∧
    ∀ L : Fin 44, IsLeaderBlock (S := chainSlots rwConfig.known) rw44 r L →
      ¬ MahiMahi.DirectCommitIn rw44 (View.full rw44) 3 L r := by decide +kernel

/-- **Both candidates score `10`** on the complete window: every round pays the window's top. -/
theorem rwWindow_scores : score rwWindow rwConfig 1 = 10 ∧ score rwWindow rwConfig 2 = 10 := by
  decide +kernel

/-- **Algorithm 2 keeps period `2` at every hysteresis**: the best candidate scores what the
current period scores, and no `ε ≥ 0` makes `10 < (1 − ε) · 10`. -/
theorem rw44_keeps_two (epsilon : ℚ) (he : 0 ≤ epsilon) :
    anchorUpdate rw44 4 rwConfig [1, 2] epsilon 28 2 = 2 := by
  change select [1, 2] (score rwWindow rwConfig) 2 epsilon = 2
  have hmem := best_mem [1, 2] (score rwWindow rwConfig) 2 (by simp)
  have hbest : score rwWindow rwConfig (best [1, 2] (score rwWindow rwConfig) 2) = 10 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> rw [h]
    · exact rwWindow_scores.1
    · exact rwWindow_scores.2
  dsimp only [select]
  rw [if_pos (by simp)]
  split
  · rename_i h
    rw [hbest, rwWindow_scores.2] at h
    linarith
  · rfl

#print axioms rw44
#print axioms rw44_sync_undecided
#print axioms rw44_keeps_two

end LeanDagTest
