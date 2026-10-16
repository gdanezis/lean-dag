import LeanDag.Scheme.Model.Async
import LeanDag.Common.Anchored
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
/-!
# The asynchronous rows — statement

`docs/scheme.md` §11. The scheme's asynchronous rows add buffer rounds
between the proposal and the vote, and elect the leader by a coin opened
at the decision round. On a record whose blocks reference `q` distinct
authors one round down and whose validators outside `honest`, at most
`f`, may equivocate, at every row and vote:

* **the count, with no network hypothesis**: at `2q ≥ n + f + 1` a common
  core (`CommonCore`); a safe honest block is good (`SafeGood`); with
  one buffer round an honest good validator (`GoodNonempty`) and the
  double count over the buffer round (`GoodCount`); with two, `q − f`
  honest good validators (`GoodCard`); and several leaders include a good
  one once they outnumber the rest (`MultiLeader`);
* **liveness under the coin clause**: a good leader's slot commits
  (`GoodCommits`), every window commits (`CommitsWithin`), and every slot
  below a run is decided (`AllDecidedBelow`);
* **the coin**: a uniform coin names a good leader with probability at
  least the count over `n` (`CoinCommit`), and over `m` independent coins
  misses every time with probability at most `((n − c)/n)^m`, which
  vanishes (`CoinTail`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Async

open Filter Topology
open scoped ENNReal

/-- **The common core**: at `2q ≥ n + f + 1`, a block at round `r + 2`
gives an honest round-`r` block in the history of every block from round
`r + 2` up. -/
def CommonCore : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (c₀ : BlockId),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q →
    c₀ ∈ U.ids → (U.block c₀).round = r + 2 →
    ∃ b ∈ U.ids, (U.block b).round = r ∧ (U.block b).creator ∈ honest ∧
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b

/-- **A safe honest block is good**: one every vote-round block reaches is
committed, when a population of the decision round meets the commit
threshold, and the certificate threshold is at most `q` where votes are
certified a round later. -/
def SafeGood : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (L : BlockId)
    (T : Finset Validator),
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    PopulatedOn U T (r + (p.waveLength - 1)) → p.commitThreshold ≤ T.card →
    L ∈ U.ids → (U.block L).round = r → (U.block L).creator ∈ honest →
    (∀ b ∈ U.ids, (U.block b).round = r + p.voteOffset → Reaches U b L) →
    (U.block L).creator ∈ goodAt p σ U r

/-- **One buffer round: an honest good validator**, at `2q ≥ n + f + 1`,
given a population of round `r + 2` and of the decision round. -/
def GoodNonempty : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q →
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    2 ≤ p.voteOffset → T.Nonempty → PopulatedOn U T (r + 2) →
    PopulatedOn U T (r + (p.waveLength - 1)) → p.commitThreshold ≤ T.card →
    (goodAt p σ U r ∩ honest).Nonempty

/-- **Two buffer rounds: `q − f` honest good validators**, at
`2q ≥ n + f + 1`, given a population of round `r + 3` and of the decision
round. -/
def GoodCard : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q →
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    3 ≤ p.voteOffset → T.Nonempty → PopulatedOn U T (r + 3) →
    PopulatedOn U T (r + (p.waveLength - 1)) → p.commitThreshold ≤ T.card →
    q ≤ (goodAt p σ U r ∩ honest).card + f

/-- **One buffer round: the double count.** With an honest population `T`
of the buffer round and the decision round, at least `n − q` strong,
`|T|·(q − f) + G·(n − q) ≤ G·|T| + |honest|·(n − q)`, `G` the honest good
validators. -/
def GoodCount : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f →
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    2 ≤ p.voteOffset → T ⊆ honest → PopulatedOn U T (r + 1) →
    PopulatedOn U T (r + (p.waveLength - 1)) → p.commitThreshold ≤ T.card →
    Fintype.card Validator - q ≤ T.card →
    T.card * (q - f) + (goodAt p σ U r ∩ honest).card * (Fintype.card Validator - q) ≤
      (goodAt p σ U r ∩ honest).card * T.card + honest.card * (Fintype.card Validator - q)

/-- **Several leaders**: leaders of round `r` more than `n` less the honest
good validators include a good one. -/
def MultiLeader : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (M : Finset Validator),
    (∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v) →
    Fintype.card Validator < M.card + (goodAt p σ U r ∩ honest).card →
    ∃ k, S.slotRound k = r ∧ S.leader k ∈ good p σ U k

/-- **A good leader's slot commits** on every view holding its decision
round. -/
def GoodCommits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (k : ℕ),
    S.leader k ∈ good p σ U k → V.CoversUpto (S.slotRound k + (p.waveLength - 1)) →
    ∃ L, IsLeaderBlock U k L ∧ (schemeAnchored p σ).Decided U V k (some L)

/-- **Every window commits** under the single-hit clause, on every view
holding the rounds up to the horizon. -/
def CommitsWithin : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (c N : ℕ),
    UnpredictableWithin p σ U c N → V.CoversUpto N →
    ∀ k, (schemeAnchored p σ).decisionRound (k + c) ≤ N →
      ∃ k', k ≤ k' ∧ k' < k + c ∧ ∃ L, IsLeaderBlock U k' L ∧
        (schemeAnchored p σ).Decided U V k' (some L)

/-- **Every slot below a run is decided** under the run clause, when a run
of `d` slots spans eligibility, on every view holding the rounds up to the
horizon. -/
def AllDecidedBelow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator) (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    [S : Slots Validator] (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (c d N : ℕ),
    0 < d → (schemeAnchored p σ).SpansEligible (S := S) d →
    UnpredictableRunWithin p σ U c d N → V.CoversUpto N →
    ∀ k, (schemeAnchored p σ).decisionRound (k + c + d - 1) ≤ N →
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, (schemeAnchored p σ).Decided U V i v

/-- **The coin names a good leader** with probability at least `1/n` at one
buffer round and `(q − f)/n` at two, under the hypotheses of the counts. -/
def CoinCommit : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q →
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    T.Nonempty → PopulatedOn U T (r + (p.waveLength - 1)) → p.commitThreshold ≤ T.card →
    (2 ≤ p.voteOffset → PopulatedOn U T (r + 2) →
      (1 : ℝ≥0∞) / Fintype.card Validator ≤
        (PMF.uniformOfFintype Validator).toOuterMeasure ↑(goodAt p σ U r)) ∧
    (3 ≤ p.voteOffset → PopulatedOn U T (r + 3) →
      ((q - f : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
        (PMF.uniformOfFintype Validator).toOuterMeasure ↑(goodAt p σ U r))

/-- **The tail**: `m` independent coins over rounds whose good sets hold at
least `c` validators all miss with probability at most `((n − c)/n)^m`,
which vanishes at a positive floor. -/
def CoinTail : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    (honest : Finset Validator) (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r₀ c : ℕ),
    (∀ m : ℕ, (∀ i : Fin m, c ≤ (goodAt p σ U (r₀ + i)).card) →
      (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
          {g | ∀ i : Fin m, g i ∉ goodAt p σ U (r₀ + i)} ≤
        (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m) ∧
    (0 < c → c ≤ Fintype.card Validator →
      Tendsto (fun m : ℕ => (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) /
        Fintype.card Validator) ^ m) atTop (𝓝 0))

/-- The asynchronous rows' claims. -/
def Statement : Prop :=
  CommonCore ∧ SafeGood ∧ GoodNonempty ∧ GoodCard ∧ GoodCount ∧ MultiLeader ∧ GoodCommits ∧
    CommitsWithin ∧ AllDecidedBelow ∧ CoinCommit ∧ CoinTail

end Async

end Scheme

end LeanDag
