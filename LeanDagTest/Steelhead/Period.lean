import LeanDagTest.Steelhead.Model
import LeanDag.Steelhead.Model.Period
import LeanDag.Steelhead.Model.Coin
/-!
# Steelhead witnesses: the period and the coin on data

The definitions of `Model/Period.lean` and `Model/Coin.lean` exercised
before anything is proved from them (`steelhead.md` §5).

* **the interval boundaries**, which `intervalOf`'s docstring asserts and
  no theorem pins: rounds `j·I + 1` to `(j + 1)·I` form interval `j`, and
  round `0` falls in interval `0` beside them;
* **the adaptive wavelength** at a concrete period sequence, reading each
  round's wavelength from its own interval's period;
* **a two-interval period derivation** on the universe of `Model.lean`:
  interval `0` runs at the initial period, its anchor is the chain commit
  at round `0`, and interval `1` runs at that anchor's update;
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
`8`, and round `0` sits in interval `0`. -/

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

`sh8_chain0` (`Model.lean`) is a chain commit at round `0`, which is
asynchronous under every period and the lowest round of interval `0`, so
it is that interval's anchor whatever the period in force. Any update
rule then fixes interval `1`'s period; this one doubles it. -/

/-- An update rule: double the period at every interval. -/
def shDouble : UpdateRule (Fin 32) := fun _ _ k => 2 * k

/-- Interval `0`'s anchor is the chain commit at round `0`: it lies in the
interval, is asynchronous, and no asynchronous round of the interval sits
below it. -/
theorem sh8_anchor0 (k : ℕ) :
    IntervalAnchor 4 5 shCoin sh8 (View.full sh8) 0 k 0 2 where
  mem := by decide
  async := by simp [IsAsync]
  commit := sh8_chain0
  below := fun _ _ _ h => absurd h (Nat.not_lt_zero _)

/-- Interval `1` runs at the update of interval `0`'s anchor: starting at
period `4`, it runs at `8`. -/
theorem sh8_period1 :
    PeriodAt 4 5 shCoin shDouble 4 sh8 (View.full sh8) 1 8 :=
  PeriodAt.anchor PeriodAt.zero (sh8_anchor0 4)

/-! ## The failover on data

`ResetsOnNoOutput` asks the update rule to answer `1` at an anchor whose history shows no output
of the interval. The constant rule `1` satisfies it outright. Its premise is not vacuous: block
`28`, at round `7`, reaches the round-`4` certificates of block `1`, so slot `0` is committed in
its history with nothing undecided below it, and the clause asks nothing of the update at that
anchor. -/

/-- The update rule that always answers `1`. -/
def shOne : UpdateRule (Fin 32) := fun _ _ _ => 1

example : ResetsOnNoOutput sh8 w4 4 shOne := fun _ _ _ _ _ => rfl

/-- Slot `0` is committed in the history of block `28`, a round-`7` block that reaches the whole
of round `4`. -/
theorem sh8_slot0_in_history :
    Steelhead.Decided (S := shSlots) w4 sh8 (sh8.historyView 28 (by decide)) 0 (some 1) :=
  Decided.directCommit (by decide) (by decide)

/-- So the failover's premise fails at that anchor: the committed slot `0` has no slot below it. -/
example : ¬ (∀ (s : ℕ) (L : Fin 32), intervalOf 4 (shSlots.slotRound s) = 0 →
    Steelhead.Decided (S := shSlots) w4 sh8 (sh8.historyView 28 (by decide)) s (some L) →
    ∃ s', s' < s ∧
      ∀ v, ¬ Steelhead.Decided (S := shSlots) w4 sh8 (sh8.historyView 28 (by decide)) s' v) :=
  fun h => by
    obtain ⟨s', hs', -⟩ := h 0 1 (by decide) sh8_slot0_in_history
    exact Nat.not_lt_zero _ hs'

/-! ## The adaptive schedule, and the coins of blocks

`adaptiveSlots` names the coin at the rounds `shPer` makes asynchronous and the known schedule
elsewhere: round `1` sits in interval `0` at period `4`, so its leader is the known one; round `4`
is asynchronous there, and from round `5` on every round is, at period `1`. `coinOfBlocks` reads a
block map back at the rounds of its blocks: at `I = 4`, `K = 2` and `j₀ = 0`, block `0` opens
interval `1` at rounds `5` and `6`, block `1` interval `2` at rounds `9` and `10`. -/

/-- A known schedule: validator `0` everywhere. -/
def shKnown : ℕ → Fin 4 := fun _ => 0

example : (adaptiveSlots shCoin shKnown 4 shPer).leader 1 = shKnown 1 := by decide
example : (adaptiveSlots shCoin shKnown 4 shPer).leader 4 = shCoin 4 := by decide
example : (adaptiveSlots shCoin shKnown 4 shPer).leader 7 = shCoin 7 := by decide
example : (adaptiveSlots shCoin shKnown 4 shPer).slotRound 7 = 7 := rfl

/-- Two blocks of two coins: block `0` names validators `1` and `2`, block `1` validators `3`
and `0`. -/
def shBlocks : Fin 2 → Fin 2 → Fin 4 := ![![1, 2], ![3, 0]]

example : blockRound 4 0 0 0 = 5 := by decide
example : blockRound 4 0 1 1 = 10 := by decide
example : coinOfBlocks 4 0 shBlocks 0 5 = 1 := by decide
example : coinOfBlocks 4 0 shBlocks 0 6 = 2 := by decide
example : coinOfBlocks 4 0 shBlocks 0 10 = 0 := by decide
-- Round `7` lies in no block, so the map draws the default.
example : coinOfBlocks 4 0 shBlocks 3 7 = 3 := by decide

/-! ## The set the coin measures

`commitProb` is the uniform measure of `goodAt`, the validators whose
round-`0` block the DAG directly commits at wave `5`. Validator `2`
authored block `2`, which round `4` certifies. -/

example : (2 : Fin 4) ∈ MahiMahi.goodAt sh8 5 0 := by decide

/-! ## Axioms -/

#print axioms sh8_period1

end LeanDagTest
