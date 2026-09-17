import LeanDagTest.Steelhead.Model
import LeanDag.Steelhead.Coin.Proof
/-!
# Steelhead witness: the good sets an adaptive adversary answers with

SH11f bounds the probability that every block of a set holds a bad coin when the good set of a
block's rounds is fixed by the blocks below it, which is what `NonAnticipating` asks of a
strategy. The bound is the one a fixed family gets, so the claim is worth exactly what its
hypothesis admits: this file exhibits a family that does read an earlier block's coin, checks
both hypotheses on data, and reads off the bound SH11f gives it.

Two blocks of one round each over the committee of the other witnesses. Block `0`'s good set is
`{1, 2}`; block `1`'s is `{1, 2}` if block `0`'s coin fell on validator `0` and `{2, 3}`
otherwise. Both hold two validators, so the bound applies at `c = 2`, and the second block's set
is not the first's: no fixed family agrees with this one.
-/

namespace LeanDagTest

namespace SteelheadAdaptiveCoin

open LeanDag LeanDag.Steelhead
open scoped ENNReal

/-- The good sets of two one-round blocks, the second reading the first block's coin. -/
def acGood : (Fin 2 → Fin 1 → Fin 4) → Fin 2 → Fin 1 → Finset (Fin 4) :=
  fun g j _ => if j = 0 then {1, 2} else if g 0 0 = 0 then {1, 2} else {2, 3}

/-- The family reads only the coins of the blocks below its own, SH11f's first hypothesis. -/
theorem ac_nonAnticipating : ∀ g g' (j : Fin 2), (∀ j' : Fin 2, j' < j → g j' = g' j') →
    ∀ i, acGood g j i = acGood g' j i := by
  decide

/-- Every good set holds two validators, SH11f's second hypothesis at `c = 2`. -/
theorem ac_card : ∀ g j i, 2 ≤ (acGood g j i).card := by decide

-- The family is genuinely adaptive: the second block's good set moves with the first's draw.
example : acGood (fun _ _ => 0) 1 0 ≠ acGood (fun _ _ => 1) 1 0 := by decide

/-- **The bound SH11f gives this family**: both blocks hold a bad coin with probability at most
`((4 − 2) / 4)²`, which is the fixed family's bound, although the second block's good set is the
adversary's own answer to the first block's draw. -/
theorem ac_bound :
    (PMF.uniformOfFintype (Fin 2 → Fin 1 → Fin 4)).toOuterMeasure
        {g | ∀ j ∈ (Finset.univ : Finset (Fin 2)), ∃ i, g j i ∉ acGood g j i} ≤
      ((((Fintype.card (Fin 4) ^ 1 - 2 ^ 1 : ℕ) : ℝ≥0∞) / (Fintype.card (Fin 4) : ℝ≥0∞) ^ 1) ^
        (Finset.univ : Finset (Fin 2)).card) :=
  (Coin.holds (Fin 4) (Fin 32) Unit sh8 3 5 8 1).2.2.2.2.2.2.1 2 2 Finset.univ acGood
    ac_nonAnticipating ac_card

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms ac_nonAnticipating
#print axioms ac_bound

end SteelheadAdaptiveCoin

end LeanDagTest
