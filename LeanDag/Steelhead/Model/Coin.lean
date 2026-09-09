import LeanDag.Steelhead.Model.Chain
import LeanDag.MahiMahi.Model.Good
import Mathlib.Probability.Distributions.Uniform
/-!
# Steelhead — the coin

The coin of an asynchronous round, modelled as a distribution rather
than by its effect (`steelhead.md` §4): uniform over the validators,
and independent across rounds, which is the uniform distribution over
the leader maps of `m` rounds. Events are read through
`PMF.toOuterMeasure`, so no measurable structure on the validators is
assumed. The chain slot of round `r` commits directly exactly when the
coin lands in `goodAt U wa r`, the validators whose round-`r` block the
DAG directly commits; the two quantities below are the probabilities
the counting lemma bounds in `Coin/Statement.lean`.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The fault model has at least one validator, which a uniform coin needs. Scoped to the arc: it
is a fact about `Faults` rather than a Steelhead notion, and a global instance would install it
library-wide from here. -/
scoped instance nonempty_of_faults : Nonempty Validator :=
  Fintype.card_pos_iff.mp (by have := F.card_validators; omega)

/-- **The probability that the coin of round `r` names a committed leader**: the measure of
`goodAt U wa r` under the uniform coin. -/
noncomputable def commitProb (U : BlockUniverse Validator BlockId Payload) (wa r : ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype Validator).toOuterMeasure ↑(MahiMahi.goodAt U wa r)

/-- **The probability that no coin of the `m` rounds from `r₀` names a committed leader**, the
coins independent: the measure, under the uniform distribution over the leader maps, of the maps
that miss every round's committed set. -/
noncomputable def noCommitProb (U : BlockUniverse Validator BlockId Payload) (wa r₀ m : ℕ) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
    {coins | ∀ i : Fin m, coins i ∉ MahiMahi.goodAt U wa (r₀ + i)}

end Steelhead

end LeanDag
