import LeanDag.Scheme.Model.Async
import LeanDag.Scheme.Model.AsyncPace
import Mathlib.Data.Prod.Lex
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
  core (`CommonCore`); with one buffer round a safe validator, an honest
  one whose block every vote-round block reaches (`SafeNonempty`), and the
  double count over the buffer round (`SafeCount`); with two, `q − f` safe
  validators (`SafeCard`); several leaders include a safe one once they
  outnumber the rest (`MultiLeader`); a safe validator is good once the
  decision round is populated (`SafeGood`); and further buffer rounds add
  nothing (`BufferTight`): at every `f < q ≤ n` and every vote offset, an
  execution under eventual delivery has exactly `q − f` safe validators;
* **liveness under the coin clause**: a good leader's slot commits
  (`GoodCommits`), every window commits (`CommitsWithin`), and every slot
  below a run is decided (`AllDecidedBelow`);
* **the coin**: a uniform coin names a safe leader with probability at
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

/-- **A safe validator is good**: every decision-round block certifies its
block, when the certificate threshold is at most `q` where votes are
certified a round later, so a population of the decision round meeting the
commit threshold commits it. -/
def SafeGood : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    PopulatedOn U T (r + (p.waveLength - 1)) → p.commitThreshold ≤ T.card →
    safeAt p U r ⊆ goodAt p σ U r

/-- **One buffer round: a safe validator**, at `2q ≥ n + f + 1`, given a
population of round `r + 2`. -/
def SafeNonempty : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q →
    2 ≤ p.voteOffset → T.Nonempty → PopulatedOn U T (r + 2) →
    (safeAt p U r).Nonempty

/-- **Two buffer rounds: `q − f` safe validators**, at `2q ≥ n + f + 1`,
given a population of round `r + 3`. -/
def SafeCard : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q →
    3 ≤ p.voteOffset → T.Nonempty → PopulatedOn U T (r + 3) →
    q ≤ (safeAt p U r).card + f

/-- **One buffer round: the double count.** With an honest population `T`
of the buffer round, at least `n − q` strong,
`|T|·(q − f) + G·(n − q) ≤ G·|T| + |honest|·(n − q)`, `G` the size of the
safe set. -/
def SafeCount : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → 2 ≤ p.voteOffset → T ⊆ honest → PopulatedOn U T (r + 1) →
    Fintype.card Validator - q ≤ T.card →
    T.card * (q - f) + (safeAt p U r).card * (Fintype.card Validator - q) ≤
      (safeAt p U r).card * T.card + honest.card * (Fintype.card Validator - q)

/-- **Several leaders**: leaders of round `r` more than `n` less the safe
set include a safe one. -/
def MultiLeader : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator) (p : Params) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (M : Finset Validator),
    (∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v) →
    Fintype.card Validator < M.card + (safeAt p U r).card →
    ∃ k, S.slotRound k = r ∧ S.leader k ∈ safe p U k

/-- **Buffer rounds past two add nothing**: at every `f < q ≤ n` and every
vote offset within the horizon, a record on `n` validators, `f` of them
Byzantine, whose blocks reference `q` distinct authors, the author's
previous block among them, and in which every validator builds every round,
has exactly `q − f` safe validators at round `0`. It is produced under
asynchronous pacing at `q` by validators that reference, at each round,
every block of the round below they hold when they build. -/
def BufferTight : Prop :=
  ∀ (n f q N : ℕ) (p : Params), f < q → q ≤ n → 1 ≤ p.voteOffset → p.voteOffset ≤ N →
    ∃ (honest : Finset (Fin n))
      (U : BlockRecord (Fin n) (Lex (ℕ × Fin n)) Unit
        (ValidAt q (Clause.distinct.and Clause.selfParent)) honest)
      (ap : AsyncPace q U honest N),
      honestᶜ.card = f ∧ (∀ r ≤ N, PopulatedOn U Finset.univ r) ∧
      (∀ b ∈ U.ids, (U.block b).refs =
        (ap.holds (U.block b).creator (U.block b).round).filter
          fun j => (U.block j).round + 1 = (U.block b).round) ∧
      (safeAt p U 0).card = q - f

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

/-- **The coin names a safe leader** with probability at least `1/n` at one
buffer round and `(q − f)/n` at two, under the hypotheses of the counts. -/
def CoinCommit : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) (T : Finset Validator),
    honestᶜ.card ≤ f → Fintype.card Validator + f + 1 ≤ 2 * q → T.Nonempty →
    (2 ≤ p.voteOffset → PopulatedOn U T (r + 2) →
      (1 : ℝ≥0∞) / Fintype.card Validator ≤
        (PMF.uniformOfFintype Validator).toOuterMeasure ↑(safeAt p U r)) ∧
    (3 ≤ p.voteOffset → PopulatedOn U T (r + 3) →
      ((q - f : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
        (PMF.uniformOfFintype Validator).toOuterMeasure ↑(safeAt p U r))

/-- **The tail**: `m` independent coins over rounds whose safe sets hold at
least `c` validators all miss with probability at most `((n − c)/n)^m`,
which vanishes at a positive floor. -/
def CoinTail : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (U : BlockRecord Validator BlockId Payload P honest) (r₀ c : ℕ),
    (∀ m : ℕ, (∀ i : Fin m, c ≤ (safeAt p U (r₀ + i)).card) →
      (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
          {g | ∀ i : Fin m, g i ∉ safeAt p U (r₀ + i)} ≤
        (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m) ∧
    (0 < c → c ≤ Fintype.card Validator →
      Tendsto (fun m : ℕ => (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) /
        Fintype.card Validator) ^ m) atTop (𝓝 0))

/-- The asynchronous rows' claims. -/
def Statement : Prop :=
  CommonCore ∧ SafeGood ∧ SafeNonempty ∧ SafeCard ∧ SafeCount ∧ MultiLeader ∧ BufferTight ∧
    GoodCommits ∧
    CommitsWithin ∧ AllDecidedBelow ∧ CoinCommit ∧ CoinTail

end Async

end Scheme

end LeanDag
