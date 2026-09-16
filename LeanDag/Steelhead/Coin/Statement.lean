import LeanDag.Steelhead.Model.Coin
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The coin — statement

The probability half of liveness under asynchrony (`steelhead.md` §4),
the paper's Theorem 3 read through a uniform coin, and the per-hop
clause of its Theorem 2. Thirteen claims:

* **SH11a, the commit probability** — on a wave a quorum has populated,
  the coin of round `r` names a directly committed leader with
  probability at least `(n − f − |byzantine|) / n`, hence at least
  `1/3`: MM2 at `wa ≥ 5` under a uniform draw;
* **SH11e, the commit probability at wave four**: at `wa ≥ 4` MM2
  promises one committed correct candidate, so the coin names a
  committed leader with probability at least `1/n`, the paper's
  wavelength-four trade-off;
* **SH11g, the run probability** — the positive form the paper's
  Theorem 3 (ii) states: over `m` consecutive populated waves with
  independent coins, every round's coin names a directly committed
  leader with probability at least `((n − f − b) / n)^m`, which at
  `m = wa` is the run a window is asked to hold. The complementary
  bound is SH11c, and neither implies the other: SH11c bounds the
  chance that no round commits;
* **SH11b, a good coin commits the chain slot** — in every view caught
  up to the decision round;
* **SH11c, the tail** — over `m` consecutive populated waves with
  independent coins, no round's coin names a directly committed leader
  with probability at most `((f + |byzantine|) / n)^m`;
* **SH11d, the tail vanishes** — that bound tends to zero, since
  `f + |byzantine| ≤ 2f < n`;
* **SH11f, the adaptive block bound** — the same bound for good sets
  that read the coins already drawn: if the good set of a block's rounds
  is fixed by the blocks below it and holds at least `c` validators,
  then every block of a set holds a bad coin with probability at most
  `((n^K − c^K) / n^K)` to the size of that set, as for a fixed family.
  The count peels the last block, whose good set the earlier ones fix,
  so the argument is a count over a finite type with no conditioning to
  state;
* **SH15a, the output is live but for a vanishing probability** —
  Theorem 3's "with probability `1`", in the form a finite record
  admits: over the uniform independent coins of `M` blocks of `K` rounds,
  one opening each interval from the second after a slot's at round one
  or above, under any update rule, some view holding the horizon, at a
  period sequence matching what it derives, has not derived the state of
  the slot's interval or leaves the slot undecided,
  with probability at most `2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)`.
  Two good blocks in different halves settle every chain verdict up to
  the later one, so the states are derived that far, and decide the slot
  (SH14c); each half holds no good block with the probability the
  counting lemma bounds block by block. A scan that never reaches the
  slot's interval counts as a failure, and a slot counts as decided only
  under every completion of the derived periods;
* **SH15d, the tail against an adaptive adversary** — SH15a where the
  record is the adversary's own answer to the coins already drawn
  (`NonAnticipating`, `undecidedProbAgainst`): at every block map the
  event reads the record that map produced, and the bound is unchanged,
  by SH11f. What the adversary may not do is read a block's own coins
  before fixing the committed set of that block's rounds;
* **SH15b, that tail vanishes** — the bound tends to zero as the number
  of blocks grows, since `n − f − b ≥ 1`;
* **SH15c, the slot is decided almost surely** — Theorem 3's "with
  probability `1`" itself, over a sequence of finite records, the `m`-th
  holding the waves of `m` blocks, and the coin drawn as a process
  (`coinMeasure`, the infinite product of the uniform distribution): for
  almost every coin some record settles the slot in every view holding
  its horizon, in SH15a's sense (`Matches`, `Settles`). The coins under which no record decides
  it lie, for every `m`, among those under which the `m`-th leaves it
  undecided, a set of measure at most SH15a's bound, which vanishes
  (SH15b); so they are null. The records are any sequence, the prefixes
  of one execution among them, since the argument reads each on its own;
* **SH11h, the floor chain's landings under the coin** — Theorem 2's
  per-hop clause, "each hop of that search onto a Byzantine-led slot
  having probability at most `b/n` under the coin", as one event over
  the whole chain: at period one, against a strategy that answers only
  the draws already made, the first `h` landings are all led from
  outside their round's committed set with probability at most
  `((n − c) / n)^h`. A landing is led from outside only if the coin at
  the floor it hopped from was, since a committed candidate's slot is
  never skipped and the search would have stopped there; those floors
  climb, and each is fixed with its good set by the coins drawn below
  it, so the count peels one floor at a time. The landings themselves
  are not a filtration: whether a slot is skipped is settled by its own
  wave, which is why the strategy must fix the skips of a slot before
  the coin of the round above its wave is drawn;
* **SH15e, almost surely against an adaptive adversary** — SH15c where
  the `m`-th record is a strategy's own answer to the coins of its `m`
  blocks: for almost every coin some strategy's record settles the slot,
  by SH15d at each `m`.

The blocks' coins are drawn after the record is fixed, as SH11c's are,
and the records of SH15c before the process: the adversary that shapes
the DAG does not see them, which is the coin's unpredictability. SH11f
and SH15d weaken that to what the argument needs, an adversary that
answers the draws already made. What
SH15a leaves to the network is what SH14c asks of it, that the waves of
the blocks be populated.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

open Filter Topology MeasureTheory
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

/-- **SH11g, the run probability.** -/
def RunProbability (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r₀ m : ℕ),
    -- five rounds, a quorum, and each of the m waves from r₀ populated where MM2 reads it
    5 ≤ wa → quorumCard Validator ≤ T.card →
    (∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) →
    -- then every one of those rounds names a committed leader with probability at least
    -- ((n − f − b) / n)^m, which at m = wa is the run the paper asks a window for
    ((((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) /
      Fintype.card Validator) ^ m) ≤ runProb U wa r₀ m

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
    -- the slot lies at round one or above
    1 ≤ s →
    -- the waves of the M blocks are populated where MM2 reads them
    (∀ (j : Fin M) (i : Fin K), PopulatedOn U T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) →
    -- then the slot stays undecided with probability at most twice the chance that each of M/2
    -- blocks holds a bad coin
    undecidedProb U ws wa I K upd k₀ known d s M ≤ 2 * badBlockBound Validator K ^ (M / 2)

/-- **SH11h, the floor chain's landings under the coin.** Theorem 2's per-hop clause. -/
def BadChainBound (wa K : ℕ) : Prop :=
  ∀ (w : ℕ → ℕ) (c k₀ h : ℕ) (d : Validator)
    (σ : (Fin K → Validator) → BlockUniverse Validator BlockId Payload)
    (V : ∀ g, View Validator BlockId Payload (σ g)),
    -- period one, where every slot is the coin's, at a wave the chain rule reads
    (∀ r, w r = wa) → 3 ≤ wa →
    -- the strategy answers only the draws already made
    NonAnticipatingChain σ V w wa d →
    -- every view holds the decision rounds the chain reads, so a committed candidate's slot is
    -- decided there and the search never skips it
    (∀ g r, V g |>.CoversUpto (MahiMahi.decisionRoundAt wa r)) →
    -- every round's committed set holds at least c candidates, as MM2 gives on a populated wave
    (∀ g r, c ≤ (MahiMahi.goodAt (σ g) wa r).card) →
    -- the chain's landings are landings, not the fallback of `floorLanding`
    (∀ g i, i < h → ¬ Decided (S := chainSlots (coinOfRounds g d)) w (σ g) (V g)
      (chainLandings σ V w d k₀ g (i + 1)) none) →
    -- the chain stays inside the rounds the coins cover
    (∀ g i, i ≤ h → chainLandings σ V w d k₀ g i + wa < K) →
    -- then every one of the first h landings is led from outside its round's committed set with
    -- probability at most ((n − c) / n)^h, the paper's b/n a hop
    badChainProb σ V w wa d k₀ h ≤
      (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ h

/-- **SH11f, the adaptive block bound.** -/
def AdaptiveBlockBound (K : ℕ) : Prop :=
  ∀ (M c : ℕ) (H : Finset (Fin M))
    (G : (Fin M → Fin K → Validator) → Fin M → Fin K → Finset Validator),
    -- the good sets read only the coins of the blocks below their own ...
    (∀ g g' (j : Fin M), (∀ j' : Fin M, j' < j → g j' = g' j') → ∀ i, G g j i = G g' j i) →
    -- ... and each holds at least c validators
    (∀ g j i, c ≤ (G g j i).card) →
    -- then every block of H holds a bad coin with at most the fixed family's probability
    (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        {g | ∀ j ∈ H, ∃ i, g j i ∉ G g j i} ≤
      ((((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) /
        (Fintype.card Validator : ℝ≥0∞) ^ K) ^ H.card)

/-- **SH15d, the tail against an adaptive adversary.** -/
def UndecidedTailAgainst (ws wa I K : ℕ) : Prop :=
  ∀ (T : Finset Validator) (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (d : Validator) (s M : ℕ)
    (σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload),
    -- the waves, a quorum, a period bound a run of wa fits in, blocks of K rounds that fit in an
    -- interval, and a slot at round one or above
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → wa ≤ K → K ≤ I → quorumCard Validator ≤ T.card → 1 ≤ s →
    -- the adversary builds its record from the coins of the blocks below each block ...
    NonAnticipating σ wa I (intervalOf I s) →
    -- ... and every record it builds has the M blocks' waves populated where MM2 reads them
    (∀ (g : Fin M → Fin K → Validator) (j : Fin M) (i : Fin K),
      PopulatedOn (σ g) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (σ g) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) →
    -- then the slot stays undecided with the probability SH15a gives against a fixed record
    undecidedProbAgainst σ ws wa I upd k₀ known d s ≤ 2 * badBlockBound Validator K ^ (M / 2)

/-- **SH15b, the tail vanishes.** -/
def UndecidedTailVanishes (K : ℕ) : Prop :=
  Tendsto (fun M : ℕ => 2 * badBlockBound Validator K ^ (M / 2)) atTop (𝓝 0)

/-- **SH15c, the slot is decided almost surely.** -/
def DecidedAlmostSurely (ws wa I K : ℕ) : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (s : ℕ),
    -- the waves, a quorum, a period bound a run of wa fits in, blocks of K rounds that fit in an
    -- interval
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → wa ≤ K → K ≤ I → quorumCard Validator ≤ T.card →
    -- the slot lies at round one or above
    1 ≤ s →
    -- record m holds the waves of m blocks, populated where MM2 reads them
    (∀ (m : ℕ) (j : Fin m) (i : Fin K),
      PopulatedOn (U m) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (U m) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) →
    -- then for almost every coin some record decides s in every view holding its horizon, at
    -- every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) m) →
        Matches I wa coin known (upd m) k₀ ws (U m) V per →
        Settles I wa coin known (upd m) k₀ ws (U m) V per s

/-- **SH15e, almost surely against an adaptive adversary.** -/
def DecidedAlmostSurelyAgainst (ws wa I K : ℕ) : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (σ : ∀ m : ℕ, (Fin m → Fin K → Validator) → BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (s : ℕ),
    -- the waves, a quorum, a period bound a run of wa fits in, blocks of K rounds that fit in an
    -- interval, and a slot at round one or above
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → wa ≤ K → K ≤ I → quorumCard Validator ≤ T.card → 1 ≤ s →
    -- every strategy of the sequence answers the draws already made ...
    (∀ m, NonAnticipating (σ m) wa I (intervalOf I s)) →
    -- ... and every record it builds holds the m blocks' waves populated where MM2 reads them
    (∀ (m : ℕ) (g : Fin m → Fin K → Validator) (j : Fin m) (i : Fin K),
      PopulatedOn (σ m g) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (σ m g) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) →
    -- then for almost every coin some strategy's own record decides s in every view holding its
    -- horizon, at every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (σ m (blockCoins I (intervalOf I s) m K coin)))
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) m) →
        Matches I wa coin known (upd m) k₀ ws (σ m (blockCoins I (intervalOf I s) m K coin))
          V per →
        Settles I wa coin known (upd m) k₀ ws (σ m (blockCoins I (intervalOf I s) m K coin))
          V per s

/-- The coin, over every fault configuration, block universe, asynchronous wave, interval and
period bound the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ),
    CommitProbability U wa ∧ CommitProbabilityFour U wa ∧ RunProbability U wa ∧
      CommitOfCoin U wa ∧
      NoCommitTail U wa ∧ TailVanishes (Validator := Validator) ∧
      AdaptiveBlockBound (Validator := Validator) K ∧
      UndecidedTail U ws wa I K ∧
      UndecidedTailAgainst (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      UndecidedTailVanishes (Validator := Validator) K ∧
      DecidedAlmostSurely (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      DecidedAlmostSurelyAgainst (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      BadChainBound (Validator := Validator) (BlockId := BlockId) (Payload := Payload) wa K

end Coin

end Steelhead

end LeanDag
