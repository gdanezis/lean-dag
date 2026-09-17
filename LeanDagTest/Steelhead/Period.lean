import LeanDagTest.Steelhead.Model
import LeanDag.Steelhead.Model.Period
import LeanDag.Steelhead.Model.Coin
import LeanDag.Steelhead.Helpers.Period
/-!
# Steelhead witnesses: the period and the coin on data

The definitions of `Model/Period.lean` and `Model/Coin.lean` exercised
before anything is proved from them (`steelhead.md` §5).

* **the interval boundaries**, which `intervalOf`'s docstring asserts and
  no theorem pins: rounds `j·I + 1` to `(j + 1)·I` form interval `j`, and
  the arithmetic leaves round `0` in interval `0` beside them, where the
  scan never reads it;
* **the adaptive wavelength** at a concrete period sequence, reading each
  round's wavelength from its own interval's period;
* **a two-interval period derivation** on the universe of `Model.lean`:
  interval `0` runs at the initial period with the agreed output at slot
  `1`, its anchor is the chain commit at round `1`, the first round the
  scan reads, and interval `1` runs at that anchor's update, over whose
  history the agreed output advances;
* **the committed set the coin measures**, on the same universe.

`commitProb` and `noCommitProb` are `noncomputable` measures, so they are
witnessed through `goodAt`, the set the uniform draw reads.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

attribute [local instance] shSlots

set_option maxRecDepth 4096

/-! ## The interval of a round

At `I = 4`: interval `0` is rounds `1` to `4`, interval `1` rounds `5` to
`8`, and the arithmetic puts round `0` in interval `0`, which no scan
reads: `IntervalAnchor` and `NoAnchor` ask for rounds `1` and above. -/

example : intervalOf 4 0 = 0 := by decide
example : intervalOf 4 1 = 0 := by decide
example : intervalOf 4 4 = 0 := by decide
example : intervalOf 4 5 = 1 := by decide
example : intervalOf 4 8 = 1 := by decide
example : intervalOf 4 9 = 2 := by decide

/-! ## The adaptive wavelength

A period sequence that runs interval `0` at period `4` and every later
interval at period `1`. Rounds `1` to `4` then read `periodic 3 5 4` and
rounds `5` onward `periodic 3 5 1`, which is the constant `5`. -/

/-- Interval `0` at period `4`, the rest at period `1`. -/
def shPer : ℕ → ℕ := fun j => if j = 0 then 4 else 1

example : adaptiveWave 3 5 4 shPer 1 = 3 := by decide
example : adaptiveWave 3 5 4 shPer 4 = 5 := by decide
example : adaptiveWave 3 5 4 shPer 5 = 5 := by decide
example : adaptiveWave 3 5 4 shPer 6 = 5 := by decide

/-! ## The period sequence on data

Round `1`, the first round the scan reads, chain-commits block `7`
(`sh8_chain1`), so it is interval `0`'s anchor whatever the period in
force. The scan then advances the agreed output over the anchor's causal
history and hands interval `1` the update rule's answer, here the doubled
period; the failover cannot fire at an anchor of round `1`, which lies
below every last commit plus `I`. -/

/-- An update rule: double the period at every interval. -/
def shDouble : UpdateRule (Fin 32) := fun _ k => 2 * k

/-- Round `1` chain-commits validator `3`'s block `7`: the coin names `3` there, and the whole of
round `5` certifies the block. -/
theorem sh8_chain1 : ChainDecided 5 shCoin sh8 (View.full sh8) 1 (some 7) :=
  AnchoredRule.Decided.directCommit (S := chainSlots shCoin) (by decide) (by decide)

/-- Interval `0`'s anchor is the chain commit at round `1`: it lies in the
interval, and no scanned round of the interval sits below it. -/
theorem sh8_anchor1 : IntervalAnchor 4 5 shCoin sh8 (View.full sh8) 0 1 7 where
  pos := le_rfl
  mem := by decide
  commit := sh8_chain1
  below := fun _ h1 _ h => absurd (lt_of_le_of_lt h1 h) (lt_irrefl _)

/-- Every wavelength of `w4` is at least two rounds, which the agreed output's advance asks. -/
theorem w4_ge_two (r : ℕ) : 2 ≤ w4 r := by
  unfold w4 periodic
  split <;> omega

/-- Interval `1` runs at the update of interval `0`'s anchor: starting at
period `4`, it runs at `8`, wherever the agreed output stops. -/
theorem sh8_period1 : ∃ next' last',
    PeriodAt 4 5 shCoin shDouble 4 sh8 (View.full sh8) w4 1 ⟨8, next', last'⟩ := by
  obtain ⟨next', last', hadv⟩ :=
    AgreedAdvance.exists (U := sh8) (w := w4) w4_ge_two (A := 7) (by decide) 1 0
  exact ⟨next', last', PeriodAt.anchor PeriodAt.zero sh8_anchor1 hadv⟩

/-! ## The window, and the agreed output on data

The window of an anchor is its causal history at the rounds `round A − I` and above, round `0`
excluded: `I + 1` rounds once the anchor is high enough, and fewer at the start of the run. At
`I = 8` the window of block `28`, a round-`7` block reaching the whole of rounds `0` to `6`,
starts at round `1`.

The agreed output is read on the same history: slots `0` and `1` are committed in it, so an
advance from slot `1` over that anchor passes slot `1` and carries its leader's round. -/

example : windowBottom sh8 28 8 = 1 := by decide
example : windowBottom sh8 28 4 = 3 := by decide
example : windowBottom sh8 2 4 = 1 := by decide

/-- Slots `0` and `1` are committed in the history of block `28`, a round-`7` block that reaches
the whole of rounds `4` and `3`. -/
theorem sh8_slot0_in_history :
    Steelhead.Decided (S := shSlots) w4 sh8 (sh8.historyView 28 (by decide)) 0 (some 1) :=
  Decided.directCommit (by decide) (by decide)

theorem sh8_slot1_in_history :
    Steelhead.Decided (S := shSlots) w4 sh8 (sh8.historyView 28 (by decide)) 1 (some 6) :=
  Decided.directCommit (by decide) (by decide)

/-- An advance from slot `1` over that anchor passes it: the new cursor is undecided in the
history and slot `1` is not, and the last commit is at or above slot `1`'s round. -/
theorem sh8_advance28 {next' last' : ℕ}
    (h : AgreedAdvance sh8 w4 28 (by decide) 1 next' 0 last') : 2 ≤ next' ∧ 1 ≤ last' := by
  have hnext : 2 ≤ next' := by
    rcases Nat.lt_or_ge next' 2 with hlt | hge
    · obtain rfl : next' = 1 := by have := h.le; omega
      exact absurd sh8_slot1_in_history (h.stuck _)
    · exact hge
  exact ⟨hnext, by simpa using h.last_le 1 6 le_rfl (by omega) sh8_slot1_in_history⟩

/-! ## The adaptive schedule, and the coins of blocks

`adaptiveSlots` names the coin at the rounds `shPer` makes asynchronous and the known schedule
elsewhere: round `1` sits in interval `0` at period `4`, so its leader is the known one; round `4`
is asynchronous there, and from round `5` on every round is, at period `1`. `coinOfBlocks` reads a
block map back at the rounds of its blocks: at `I = 4`, `K = 2` and `j₀ = 0`, block `0` opens
interval `2` at rounds `9` and `10`, block `1` interval `3` at rounds `13` and `14`. -/

/-- A known schedule: validator `0` everywhere. -/
def shKnown : ℕ → Fin 4 := fun _ => 0

example : (adaptiveSlots shCoin shKnown 4 shPer).leader 1 = shKnown 1 := by decide
example : (adaptiveSlots shCoin shKnown 4 shPer).leader 4 = shCoin 4 := by decide
example : (adaptiveSlots shCoin shKnown 4 shPer).leader 7 = shCoin 7 := by decide
example : (adaptiveSlots shCoin shKnown 4 shPer).slotRound 7 = 7 := rfl

/-- Two blocks of two coins: block `0` names validators `1` and `2`, block `1` validators `3`
and `0`. -/
def shBlocks : Fin 2 → Fin 2 → Fin 4 := ![![1, 2], ![3, 0]]

example : blockRound 4 0 0 0 = 9 := by decide
example : blockRound 4 0 1 1 = 14 := by decide
example : coinOfBlocks 4 0 shBlocks 0 9 = 1 := by decide
example : coinOfBlocks 4 0 shBlocks 0 10 = 2 := by decide
example : coinOfBlocks 4 0 shBlocks 0 14 = 0 := by decide
-- Round `11` lies in no block, so the map draws the default.
example : coinOfBlocks 4 0 shBlocks 3 11 = 3 := by decide

/-! ## The set the coin measures

`commitProb` is the uniform measure of `goodAt`, the validators whose
round-`0` block the DAG directly commits at wave `5`. Validator `2`
authored block `2`, which round `4` certifies. -/

example : (2 : Fin 4) ∈ MahiMahi.goodAt sh8 5 0 := by decide

/-! ## Axioms -/

#print axioms sh8_period1

end LeanDagTest
