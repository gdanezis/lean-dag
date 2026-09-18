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
row, of a slot below `M` consecutive blocks of `wa` coins staying
undecided at period one, and of a slot of the adaptive output staying
undecided over the coins of `M` blocks of `K` rounds, one block opening
each interval from the second after the slot's, the first whose anchor's
window lies wholly above the slot.

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

/-- **The probability that every coin of the `m` rounds from `r₀` names a committed leader**, the
coins independent: the measure, under the uniform distribution over the leader maps, of the maps
that hit every round's committed set. The run of consecutive commits a wave asks for. -/
noncomputable def runProb (U : BlockUniverse Validator BlockId Payload) (wa r₀ m : ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
    {coins | ∀ i : Fin m, coins i ∈ MahiMahi.goodAt U wa (r₀ + i)}

/-- **The probability that no coin of the `m` rounds from `r₀` names a committed leader**, the
coins independent: the measure, under the uniform distribution over the leader maps, of the maps
that miss every round's committed set. -/
noncomputable def noCommitProb (U : BlockUniverse Validator BlockId Payload) (wa r₀ m : ℕ) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
    {coins | ∀ i : Fin m, coins i ∉ MahiMahi.goodAt U wa (r₀ + i)}

/-- **The coins of `K` rounds read as a coin map**: round `r` below `K` draws `g r`, every round
at or above `K` the fixed `d`, which no event below reads. -/
def coinOfRounds {K : ℕ} (g : Fin K → Validator) (d : Validator) : ℕ → Validator :=
  fun r => if h : r < K then g ⟨r, h⟩ else d

/-- **The coins of `M` blocks of `K` rounds from round `b`**, read as a coin map: round
`b + j·K + i` draws `g j i`, and every round outside the blocks draws `d`, which no event below
reads. The consecutive blocks over which the search's tail is measured (SH11h). -/
def coinOfBlocksFrom {M K : ℕ} (b : ℕ) (g : Fin M → Fin K → Validator) (d : Validator) :
    ℕ → Validator :=
  fun r =>
    if h : b ≤ r ∧ (r - b) / K < M ∧ (r - b) % K < K then
      g ⟨(r - b) / K, h.2.1⟩ ⟨(r - b) % K, h.2.2⟩
    else d

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

/-- **The coins of `M` blocks of `K` rounds**, read from a coin map: the inverse of
`coinOfBlocks` on the blocks' own rounds. -/
def blockCoins (I j₀ M K : ℕ) (coin : ℕ → Validator) : Fin M → Fin K → Validator :=
  fun j i => coin (blockRound I j₀ j i)

/-- **The horizon the blocks need**: the decision round of the last block's `wa`-th round. -/
def blocksHorizon (I wa j₀ M : ℕ) : ℕ := MahiMahi.decisionRoundAt wa ((j₀ + 1 + M) * I + wa)

/-- **A period sequence matches what a view derives**: at every interval the view derives a state
for, reading its agreed output on the schedule the sequence names, whose kinds are the
sequence's own, the sequence's period is the state's. Arbitrary where the scan has stalled. -/
def Matches (I K wa : ℕ) [NeZero K] (coin known : ℕ → Validator) (upd : UpdateRule BlockId)
    (k₀ ws : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) : Prop :=
  ∀ j st, PeriodAt (S := adaptiveSlots coin known I per) I K wa coin upd k₀ U V
    (wavelength ws wa) j st → per j = st.period

/-- **A view settles a slot at a matching sequence**: it derives the state of the slot's interval,
and decides the slot on the sequence's schedule. -/
def Settles (I K wa : ℕ) [NeZero K] (coin known : ℕ → Validator) (upd : UpdateRule BlockId)
    (k₀ ws : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s : ℕ) : Prop :=
  (∃ st, PeriodAt (S := adaptiveSlots coin known I per) I K wa coin upd k₀ U V
    (wavelength ws wa) (intervalOf I s) st) ∧
  ∃ v, Decided (S := adaptiveSlots coin known I per) (wavelength ws wa) U V s v

/-- **The probability that slot `s` stays undecided**, over the uniform independent coins of `M`
blocks of `K` rounds opening the intervals from the second after the slot's: the measure of the
coin maps under which some view holding the horizon, at some period sequence matching what it
derives, either has not derived the state of the slot's interval or leaves `s` undecided at that
sequence's wavelength and schedule. A sequence matching what the view derives is arbitrary where
the scan has stalled, so a slot that counts as decided is decided under every such completion,
from derived periods alone, and a scan that never reaches the slot's interval counts as a failure.
The coins outside the blocks draw `d`. -/
noncomputable def undecidedProb (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ)
    [NeZero K] (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator)
    (s M : ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
    {g | ¬ ∀ (V : View Validator BlockId Payload U) (per : ℕ → ℕ),
      V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
      Matches I K wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws U V per →
      Settles I K wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws U V per s}

/-- **A non-anticipating strategy, with the floor `G`**: a record built from the coins of `M`
blocks of `K` rounds, and at every round of a block a set of candidates the record commits
directly, fixed by the coins drawn before that round, those of the blocks below and of the
block's own earlier rounds. The adversary may shape the whole DAG from the draws already
revealed, and may commit more candidates once a round's coin is out, as Byzantine certifiers
that learn it from the honest shares can; what it may not do is take a candidate out of the
floor after the draw. The claims below read the floor's size and nothing else of the record, so
what "the adversary does not see the coin before it is used" means on a DAG is a floor of the
counting lemma's size that the coin cannot shrink. -/
def NonAnticipating {M K : ℕ}
    (σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload)
    (G : (Fin M → Fin K → Validator) → Fin M → Fin K → Finset Validator) (wa I j₀ : ℕ) : Prop :=
  (∀ g (j : Fin M) (i : Fin K), G g j i ⊆ MahiMahi.goodAt (σ g) wa (blockRound I j₀ j i)) ∧
    ∀ g g' (j : Fin M) (i : Fin K), (∀ j' : Fin M, j' < j → g j' = g' j') →
      (∀ i' : Fin K, i' < i → g j i' = g' j i') → G g j i = G g' j i

/-- **The probability that slot `s` stays undecided against a strategy**: `undecidedProb` with
the record the adversary builds from the coins in place of a fixed one. The event reads the
strategy's own record at each block map, so the blocks' committed sets move with the draw. -/
noncomputable def undecidedProbAgainst {M K : ℕ} [NeZero K]
    (σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload) (ws wa I : ℕ)
    (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator) (s : ℕ) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
    {g | ¬ ∀ (V : View Validator BlockId Payload (σ g)) (per : ℕ → ℕ),
      V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
      Matches I K wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws (σ g) V per →
      Settles I K wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws (σ g) V per s}

/-- **The coin as a process**: an independent uniform draw at every round, the infinite product
of the uniform distribution over the validators on the measurable structure they carry. The
measure the almost-sure claim (SH15c) reads its events through; on finitely many rounds it agrees
with the uniform distribution over the leader maps of those rounds. -/
noncomputable def coinMeasure (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [MeasurableSpace Validator] : MeasureTheory.Measure (ℕ → Validator) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Validator).toMeasure

end Steelhead

end LeanDag
