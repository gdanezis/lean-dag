import LeanDag.Steelhead.Model.Coin
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The coin — statement

The probability half of liveness under asynchrony (`steelhead.md` §4),
the paper's Theorem 3 read through a uniform coin. Seven claims:

* **SH11a, the commit probability** — on a wave a quorum has populated,
  the coin of round `r` names a directly committed leader with
  probability at least `(n − f − |byzantine|) / n`, hence at least
  `1/3`: MM2 at `wa ≥ 5` under a uniform draw;
* **SH11e, the commit probability at wave four**: at `wa ≥ 4` MM2
  promises one committed correct candidate, so the coin names a
  committed leader with probability at least `1/n`, the paper's
  wavelength-four trade-off;
* **SH11b, a good coin commits the chain slot** — in every view caught
  up to the decision round;
* **SH11c, the tail** — over `m` consecutive populated waves with
  independent coins, no round's coin names a directly committed leader
  with probability at most `((f + |byzantine|) / n)^m`;
* **SH11d, the tail vanishes** — that bound tends to zero, since
  `f + |byzantine| ≤ 2f < n`;
* **SH15a, the output is live but for a vanishing probability** —
  Theorem 3's "with probability `1`", in the form a finite record
  admits: over the uniform independent coins of `M` blocks of `K` rounds,
  one opening each interval from the second after a slot's, some view
  holding the horizon, at a period sequence matching what it derives and
  at which the update rule fails over, has not derived the period of the
  slot's interval or leaves the slot undecided, with probability at most
  `2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)`. Two good blocks in different
  halves settle every chain verdict up to the later one, so the periods
  are derived that far, and decide the slot (SH14c); each half holds no
  good block with the probability the counting lemma bounds block by
  block. A scan that never reaches the slot's interval counts as a
  failure, and a slot counts as decided only under every completion of
  the derived periods;
* **SH15b, that tail vanishes** — the bound tends to zero as the number
  of blocks grows, since `n − f − b ≥ 1`.

The blocks' coins are drawn after the record is fixed, as SH11c's are:
the adversary that shapes the DAG does not see them, which is the coin's
unpredictability. What SH15a leaves to the network is what SH14c asks of
it, that the waves of the blocks be populated.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

open Filter Topology
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH11a, the commit probability.** -/
def CommitProbability (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- five rounds, a quorum, and the wave populated where MM2 reads it
    5 ≤ wa → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 3) → PopulatedOn U T (MahiMahi.decisionRoundAt wa r) →
    -- then the coin names a committed leader with probability at least (n − f − b) / n ...
    ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      commitProb U wa r ∧
    -- ... and so at least 1/3
    (3 : ℝ≥0∞)⁻¹ ≤ commitProb U wa r

/-- **SH11e, the commit probability at wave four.** -/
def CommitProbabilityFour (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- four rounds, a quorum, and the wave populated where MM2's weaker form reads it
    4 ≤ wa → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 2) → PopulatedOn U T (MahiMahi.decisionRoundAt wa r) →
    -- then the coin names a committed leader with probability at least 1 / n
    (Fintype.card Validator : ℝ≥0∞)⁻¹ ≤ commitProb U wa r

/-- **SH11b, a good coin commits the chain slot.** -/
def CommitOfCoin (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (r : ℕ),
    -- the coin of round r names a committed leader
    coin r ∈ MahiMahi.goodAt U wa r →
    -- and the view holds the decision round
    V.CoversUpto (MahiMahi.decisionRoundAt wa r) →
    -- then the chain slot of round r commits its candidate in that view
    ∃ L, IsLeaderBlock (S := chainSlots coin) U r L ∧ ChainDecided wa coin U V r (some L)

/-- **SH11c, the tail.** -/
def NoCommitTail (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r₀ m : ℕ),
    5 ≤ wa → quorumCard Validator ≤ T.card →
    -- each of the m waves from r₀ is populated where MM2 reads it
    (∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) →
    -- then no chain slot of those rounds commits with probability at most ((f + b) / n)^m
    noCommitProb U wa r₀ m ≤
      (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m

/-- **SH11d, the tail vanishes.** -/
def TailVanishes : Prop :=
  Tendsto (fun m : ℕ => (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m)
    atTop (𝓝 0)

/-- **The chance that a block of `K` coins holds a bad one**: `(n^K − (n − f − b)^K) / n^K`, the
bound SH15 states its tail in. -/
noncomputable def badBlockBound (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] (K : ℕ) : ℝ≥0∞ :=
  ((Fintype.card Validator ^ K - (Fintype.card Validator - F.f - F.byzantine.card) ^ K : ℕ) :
    ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K

/-- **SH15a, the output is live but for a vanishing probability.** -/
def UndecidedTail (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) : Prop :=
  ∀ (T : Finset Validator) (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (d : Validator) (s M : ℕ),
    -- the waves, a quorum, a period bound a run of wa fits in, blocks of K rounds that fit in an
    -- interval
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → wa ≤ K → K ≤ I → quorumCard Validator ≤ T.card →
    -- the periods stay in [1, K]
    1 ≤ k₀ → k₀ ≤ K → (∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K) →
    -- the waves of the M blocks are populated where MM2 reads them
    (∀ (j : Fin M) (i : Fin K), PopulatedOn U T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) →
    -- then the slot stays undecided with probability at most twice the chance that each of M/2
    -- blocks holds a bad coin
    undecidedProb U ws wa I K upd k₀ known d s M ≤ 2 * badBlockBound Validator K ^ (M / 2)

/-- **SH15b, the tail vanishes.** -/
def UndecidedTailVanishes (K : ℕ) : Prop :=
  Tendsto (fun M : ℕ => 2 * badBlockBound Validator K ^ (M / 2)) atTop (𝓝 0)

/-- The coin, over every fault configuration, block universe, asynchronous wave, interval and
period bound the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ),
    CommitProbability U wa ∧ CommitProbabilityFour U wa ∧ CommitOfCoin U wa ∧
      NoCommitTail U wa ∧ TailVanishes (Validator := Validator) ∧
      UndecidedTail U ws wa I K ∧ UndecidedTailVanishes (Validator := Validator) K

end Coin

end Steelhead

end LeanDag
