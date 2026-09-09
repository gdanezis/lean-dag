import LeanDag.Steelhead.Model.Coin
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The coin — statement

The probability half of liveness under asynchrony (`steelhead.md` §4),
the paper's Theorem 3 (i) read through a uniform coin. Four claims:

* **SH11a, the commit probability** — on a wave a quorum has populated,
  the coin of round `r` names a directly committed leader with
  probability at least `(n − f − |byzantine|) / n`, hence at least
  `1/3`: MM2 at `wa ≥ 5` under a uniform draw;
* **SH11b, a good coin commits the chain slot** — in every view caught
  up to the decision round;
* **SH11c, the tail** — over `m` consecutive populated waves with
  independent coins, no round's coin names a directly committed leader
  with probability at most `((f + |byzantine|) / n)^m`;
* **SH11d, the tail vanishes** — that bound tends to zero, since
  `f + |byzantine| ≤ 2f < n`.

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

/-- The coin, over every fault configuration, block universe and asynchronous wave the model
admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (wa : ℕ),
    CommitProbability U wa ∧ CommitOfCoin U wa ∧ NoCommitTail U wa ∧
      TailVanishes (Validator := Validator)

end Coin

end Steelhead

end LeanDag
