import LeanDag.Barnacle.Model.Chains
import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Bounded anchor chains from random assignments — statement

An assignment algorithm draws the heads of the rounds in blocks of `L`
rounds, the blocks independent, each with law `μ` (`blockHead`). If, for
every set `T` missing at most `slack` validators, a block opens with `w`
heads from `T` except with probability at most `ε`, then every
configuration with those heads has bounded anchor chains up to `Nmax`
(`Config.BoundedChainsUpto`, gap `2·M·L`), except with probability at most
`2ⁿ · J · ε^M`, over `J` windows of `M` blocks covering the horizon
(`RandomChains`). The adversary fixes the faults before the draw; the
union over the sets `T` makes the bound hold for every split at once.

A fresh uniformly random ordering of the validators for every block of `n`
rounds is such an algorithm, with `ε = 1 − (n − slack)^(w) / n^(w)`
(`ShuffleChains`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Chains

open MeasureTheory
open scoped ENNReal

/-- **Random assignments have bounded anchor chains up to a horizon.** -/
def RandomChains : Prop :=
  ∀ (Validator : Type) [Fintype Validator] [DecidableEq Validator] [MeasurableSpace Validator]
    [MeasurableSingletonClass Validator] (L w J M slack fb : ℕ) (dflt : Validator)
    (μ : Measure (Fin L → Validator)) [IsProbabilityMeasure μ] (ε : ℝ≥0∞),
    0 < w → w ≤ L →
    (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack → μ (PrefixIn T w)ᶜ ≤ ε) →
    ∀ Nmax : ℕ, Nmax ≤ J * (M * L) →
      (Measure.pi fun _ : Fin (J * M) => μ)
          {g | ¬ ∀ C : Config Validator, (∀ ρ, C.head ρ = blockHead dflt g ρ) →
            C.BoundedChainsUpto slack fb w (2 * (M * L)) Nmax} ≤
        2 ^ Fintype.card Validator * (J * ε ^ M)

/-- **A random ordering of the validators, drawn afresh for every block of
`n` rounds, has bounded anchor chains up to a horizon**: each block opens
with `w` heads outside the at most `slack` faulty validators with
probability at least `(n − slack)^(w) / n^(w)` (falling factorials), which is
positive once `w ≤ n − slack`. -/
def ShuffleChains : Prop :=
  ∀ (Validator : Type) [Fintype Validator] [DecidableEq Validator] [MeasurableSpace Validator]
    [MeasurableSingletonClass Validator] (w J M slack fb : ℕ) (dflt : Validator),
    0 < w → w ≤ Fintype.card Validator →
    ∀ Nmax : ℕ, Nmax ≤ J * (M * Fintype.card Validator) →
      (Measure.pi fun _ : Fin (J * M) => (shuffle Validator).toMeasure)
          {g | ¬ ∀ C : Config Validator, (∀ ρ, C.head ρ = blockHead dflt g ρ) →
            C.BoundedChainsUpto slack fb w (2 * (M * Fintype.card Validator)) Nmax} ≤
        2 ^ Fintype.card Validator * (J * (1 -
          ((Fintype.card Validator - slack).descFactorial w : ℝ≥0∞) /
            (Fintype.card Validator).descFactorial w) ^ M)

/-- Random assignments and bounded anchor chains. -/
def Statement : Prop := RandomChains ∧ ShuffleChains

end Chains

end Barnacle

end LeanDag
