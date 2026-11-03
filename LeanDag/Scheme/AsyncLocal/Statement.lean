import LeanDag.Scheme.Model.AsyncPace
import LeanDag.Scheme.Model.Async
import Mathlib.Probability.Distributions.Uniform
/-!
# The asynchronous rows on a validator's own view — statement

`docs/scheme.md` §11.1. Under asynchronous pacing at a quorum `qp`
(`AsyncPace`: eventual delivery among the reliable validators, no time
bound) with the reliable set `T` at least `qp` strong, at every row and
vote:

* **the coin's leader eventually commits** (`CoinLive`): at a row ready
  for the count, with `qp = q`, a uniform coin names a leader whose slot
  commits on every reliable validator's own view from some time on, with
  probability at least `1/n` at one buffer round and `(q − f)/n` at two or
  more;

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

The coin's bounds are those of `Scheme/Async/Statement.lean`
(`Scheme.Async.CoinCommit`, `Scheme.Async.CoinTail`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace AsyncLocal

open scoped ENNReal

/-- **The coin's leader eventually commits on every reliable validator's
own view**, with probability at least `1/n` at one buffer round and
`(q − f)/n` at two or more, at a row ready for the count, under
asynchronous pacing at `q` with a reliable set at least `q` strong. The
coin's outcome `v` is the schedule `elect v`, in which `v` leads slot `k`
at round `r`. -/
def CoinLive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ)
    (ap : AsyncPace q U T N) (elect : Validator → Slots Validator) (b r k : ℕ),
    honestᶜ.card ≤ f → p.AsyncReady (Fintype.card Validator) f q b → q ≤ T.card →
    (∀ v, (elect v).leader k = v ∧ (elect v).slotRound k = r) →
    r + (p.waveLength - 1) ≤ N →
    (1 ≤ b → (1 : ℝ≥0∞) / Fintype.card Validator ≤
      (PMF.uniformOfFintype Validator).toOuterMeasure
        {v | ap.EventuallyCommits (S := elect v) p σ k}) ∧
    (2 ≤ b → ((q - f : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      (PMF.uniformOfFintype Validator).toOuterMeasure
        {v | ap.EventuallyCommits (S := elect v) p σ k})

/-- **Every reliable block is held by every reliable validator** from some
time on. -/
def Delivered : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N),
    ap.Eventually fun V => ∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ V.ids

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
    p.CertFits q → p.commitThreshold ≤ T.card → qp ≤ T.card →
    S.slotRound k + (p.waveLength - 1) ≤ N → S.leader k ∈ safe p U k →
    ap.EventuallyCommits p σ k

/-- **Every window commits on every reliable validator's own view** under
the single-hit clause over safe leaders, from some time on. -/
def CommitsWithin : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (c : ℕ),
    p.CertFits q → p.commitThreshold ≤ T.card → qp ≤ T.card → SafeWithin p σ U c N →
    ap.Eventually fun V => WindowsCommit p σ U V c N

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
    0 < d → p.CertFits q → p.commitThreshold ≤ T.card → qp ≤ T.card →
    (schemeAnchored p σ).SpansEligible (S := S) d → SafeRunWithin p σ U c d N →
    ap.Eventually fun V => PrefixDecided p σ U V c d N

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
  CoinLive ∧ Delivered ∧ Populated ∧ SafeCommits ∧ CommitsWithin ∧ AllDecidedBelow ∧ OfPaceCore

end AsyncLocal

end Scheme

end LeanDag
