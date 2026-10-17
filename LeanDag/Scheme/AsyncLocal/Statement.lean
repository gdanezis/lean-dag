import LeanDag.Scheme.Model.AsyncPace
import LeanDag.Scheme.Model.Async
/-!
# The asynchronous rows on a validator's own view — statement

`docs/scheme.md` §11.1. Under asynchronous pacing at a quorum `qp`
(`AsyncPace`: eventual delivery among the reliable validators, no time
bound) with the reliable set `T` at least `qp` strong, at every row and
vote:

* **delivery**: every reliable block of the record is held by every
  reliable validator from some time on (`Delivered`);
* **production**: every round below the horizon has a block by every
  reliable validator (`Populated`);
* **a safe leader's slot commits** on every reliable validator's own view
  from some time on, when the reliable set meets the commit threshold
  (`SafeCommits`);
* **every window commits**, and **every slot below a run is decided**, on
  every reliable validator's own view from some time on, under the clauses
  over safe leaders (`CommitsWithin`, `AllDecidedBelow`);
* **every timed run is an asynchronous one** (`OfPaceCore`): the pacing
  trunk of the timed disciplines, with a progress rule at `qp`, gives
  asynchronous pacing.

The coin names a safe leader with the probabilities of
`Scheme/Async/Statement.lean` (`Scheme.Async.CoinCommit`,
`Scheme.Async.CoinTail`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace AsyncLocal

/-- **Every reliable block is held by every reliable validator** from some
time on. -/
def Delivered : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N),
    ∃ t, ∀ t', t ≤ t' → ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ ap.holds v t'

/-- **Production**: every round below the horizon has a block by every
reliable validator, when the reliable set is `qp` strong. -/
def Populated : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ),
    AsyncPace qp U T N → qp ≤ T.card → ∀ n ≤ N, PopulatedOn U T n

/-- **A safe leader's slot commits on every reliable validator's own view**,
from some time on. -/
def SafeCommits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (k : ℕ),
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    p.commitThreshold ≤ T.card → qp ≤ T.card →
    S.slotRound k + (p.waveLength - 1) ≤ N → S.leader k ∈ safe p U k →
    ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ T),
      ∃ L, IsLeaderBlock U k L ∧ (schemeAnchored p σ).Decided U (ap.viewAt hv t') k (some L)

/-- **Every window commits on every reliable validator's own view** under
the single-hit clause over safe leaders, from some time on. -/
def CommitsWithin : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (c : ℕ),
    2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    p.commitThreshold ≤ T.card → qp ≤ T.card → SafeWithin p σ U c N →
    ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ T), ∀ k,
      (schemeAnchored p σ).decisionRound (k + c) ≤ N →
      ∃ k', k ≤ k' ∧ k' < k + c ∧ ∃ L, IsLeaderBlock U k' L ∧
        (schemeAnchored p σ).Decided U (ap.viewAt hv t') k' (some L)

/-- **Every slot below a run is decided on every reliable validator's own
view** under the run clause over safe leaders, when a run of `d` slots
spans eligibility, from some time on. -/
def AllDecidedBelow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (c d : ℕ),
    0 < d → 2 ≤ p.waveLength →
    (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) →
    p.commitThreshold ≤ T.card → qp ≤ T.card →
    (schemeAnchored p σ).SpansEligible (S := S) d → SafeRunWithin p σ U c d N →
    ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ T), ∀ k,
      (schemeAnchored p σ).decisionRound (k + c + d - 1) ≤ N →
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ w, (schemeAnchored p σ).Decided U (ap.viewAt hv t') i w

/-- **Every timed run is an asynchronous one**: the pacing trunk, with a
progress rule at `qp`, gives asynchronous pacing at `qp`. -/
def OfPaceCore : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    (honest : Finset Validator) (U : BlockRecord Validator BlockId Payload P honest)
    (T : Finset Validator) (N qp : ℕ) (pc : PaceCore U T N),
    (∀ v ∈ T, ∀ n < N, ∀ t, qp ≤ (authorsIn U (pc.holds v t) n).card → n < pc.top v) →
    Nonempty (AsyncPace qp U T N)

/-- The asynchronous rows on a validator's own view. -/
def Statement : Prop :=
  Delivered ∧ Populated ∧ SafeCommits ∧ CommitsWithin ∧ AllDecidedBelow ∧ OfPaceCore

end AsyncLocal

end Scheme

end LeanDag
