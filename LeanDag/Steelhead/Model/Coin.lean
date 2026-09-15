import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Good
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
/-!
# Steelhead — the coin

The coin of an asynchronous round, modelled as a distribution rather
than by its effect (`steelhead.md` §4): uniform over the validators,
and independent across rounds, which is the uniform distribution over
the leader maps of `m` rounds. Events on finitely many rounds are read
through `PMF.toOuterMeasure`, so no measurable structure on the
validators is assumed; the coin as a process over every round
(`coinMeasure`) is the infinite product of the uniform distribution, on
whatever discrete measurable structure the validators carry. The chain
slot of round `r` commits directly exactly when the coin lands in
`goodAt U wa r`, the validators whose round-`r` block the DAG directly
commits; the quantities below are the probabilities the counting lemma
bounds in `Coin/Statement.lean`: of one good coin, of `m` bad ones in a
row, and of a slot of the adaptive output staying undecided over the
coins of `M` blocks of `K` rounds, one block opening each interval from
the second after the slot's, the first whose anchor's window lies wholly
above the slot.

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

/-- **Round `i` of block `j`**: block `j` opens interval `j₀ + 2 + j`, so its round `i` is the
`(i + 1)`-th round of that interval. The blocks start two intervals past `j₀` so that the window
of an anchor in any of them lies wholly above interval `j₀`. -/
def blockRound (I j₀ j i : ℕ) : ℕ := (j₀ + 2 + j) * I + 1 + i

/-- **The coins of `M` blocks of `K` rounds**, block `j` opening interval `j₀ + 2 + j`, read as a
coin map: round `i` of block `j` draws `g j i`, and every other round draws `d`, which no event
below reads. At `K ≤ I` the blocks are disjoint and the map reads them back exactly. -/
def coinOfBlocks {M K : ℕ} (I j₀ : ℕ) (g : Fin M → Fin K → Validator) (d : Validator) :
    ℕ → Validator :=
  fun r =>
    if h : (j₀ + 2) * I + 1 ≤ r ∧ (r - ((j₀ + 2) * I + 1)) / I < M ∧
        (r - ((j₀ + 2) * I + 1)) % I < K then
      g ⟨(r - ((j₀ + 2) * I + 1)) / I, h.2.1⟩ ⟨(r - ((j₀ + 2) * I + 1)) % I, h.2.2⟩
    else d

/-- **The horizon the blocks need**: the decision round of the last block's `wa`-th round. -/
def blocksHorizon (I wa j₀ M : ℕ) : ℕ := MahiMahi.decisionRoundAt wa ((j₀ + 1 + M) * I + wa)

/-- **The probability that slot `s` stays undecided**, over the uniform independent coins of `M`
blocks of `K` rounds opening the intervals from the second after the slot's: the measure of the
coin maps under which some view holding the horizon, at some period sequence that matches every
period the view derives and at which the update rule fails over, either has not derived the period
of the slot's interval or leaves `s` undecided at the adaptive wavelength and schedule. A sequence
matching what the view derives is arbitrary where the scan has stalled, so a slot that counts as
decided is decided under every such completion, from derived periods alone, and a scan that never
reaches the slot's interval counts as a failure. The coins outside the blocks draw `d`. -/
noncomputable def undecidedProb (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ)
    (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator) (s M : ℕ) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
    {g | ¬ ∀ (V : View Validator BlockId Payload U) (per : ℕ → ℕ),
      ResetsOnNoOutput (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per) U
        (adaptiveWave ws wa I per) I upd →
      V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
      (∀ j k, PeriodAt I wa (coinOfBlocks I (intervalOf I s) g d) upd k₀ U V j k → per j = k) →
      PeriodAt I wa (coinOfBlocks I (intervalOf I s) g d) upd k₀ U V (intervalOf I s)
        (per (intervalOf I s)) ∧
      ∃ v, Decided (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per)
        (adaptiveWave ws wa I per) U V s v}

/-- **The coin as a process**: an independent uniform draw at every round, the infinite product
of the uniform distribution over the validators on the measurable structure they carry. The
measure the almost-sure claim (SH15c) reads its events through; on finitely many rounds it agrees
with the uniform distribution over the leader maps of those rounds. -/
noncomputable def coinMeasure (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [MeasurableSpace Validator] : MeasureTheory.Measure (ℕ → Validator) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Validator).toMeasure

end Steelhead

end LeanDag
