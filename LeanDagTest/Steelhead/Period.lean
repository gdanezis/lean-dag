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

/-! ## The set the coin measures

`commitProb` is the uniform measure of `goodAt`, the validators whose
round-`0` block the DAG directly commits at wave `5`. Validator `2`
authored block `2`, which round `4` certifies. -/

example : (2 : Fin 4) ∈ MahiMahi.goodAt sh8 5 0 := by decide

/-! ## Axioms -/

#print axioms sh8_period1

end LeanDagTest
