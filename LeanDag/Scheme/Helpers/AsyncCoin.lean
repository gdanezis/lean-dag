import LeanDag.Scheme.Helpers.Async
import LeanDag.Steelhead.Helpers.Coin
import LeanDag.Scheme.Model.NoFaults
/-!
# The asynchronous rows: the coin

A uniform coin, independent across rounds, read as Steelhead reads it
(`Steelhead/Model/Coin.lean`): it lands in a set with the set's density,
`m` independent coins all miss sets of at least `c` validators with
probability at most `((n − c)/n)^m`, which tends to zero. Steelhead's
counts ask its fault model only for a validator, so `noFaults` is supplied
inside the proofs here and appears in no statement.
-/

namespace LeanDag

namespace Scheme

open Filter Topology
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Nonempty Validator]

/-- **The coin lands in a set of at least `c` validators with probability at
least `c / n`.** -/
theorem floor_le_coin {G : Finset Validator} {c : ℕ} (hc : c ≤ G.card) :
    (c : ℝ≥0∞) / Fintype.card Validator ≤ (PMF.uniformOfFintype Validator).toOuterMeasure ↑G := by
  rw [Steelhead.uniform_prob_mem]
  exact ENNReal.div_le_div_right (by exact_mod_cast hc) _

/-- **`m` independent coins all miss sets of at least `c` validators** with
probability at most `((n − c)/n)^m`. -/
theorem noHit_le {m c : ℕ} (G : Fin m → Finset Validator) (hc : ∀ i, c ≤ (G i).card) :
    (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure {g | ∀ i, g i ∉ G i} ≤
      (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m := by
  letI : Faults Validator := noFaults
  exact Steelhead.no_hit_prob_le G hc

/-- **That bound tends to zero** at a positive floor. -/
theorem noHit_tendsto_zero {c : ℕ} (hc : 0 < c) (hcn : c ≤ Fintype.card Validator) :
    Tendsto (fun m : ℕ => (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) /
      Fintype.card Validator) ^ m) atTop (𝓝 0) :=
  Steelhead.no_hit_prob_tendsto_zero hc hcn

end Scheme

end LeanDag
