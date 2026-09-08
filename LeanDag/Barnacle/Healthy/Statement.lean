import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Model.Window
import Mathlib.Order.Interval.Finset.Nat

/-!
# BN12 — a healthy window is read as healthy

Safety and liveness are unconditional in the leader count, and that
leaves one thing unsaid: nothing so far stops the measurement reading
every scoring slot as unhealthy and the AIMD rule driving the count to
one for ever, safe and live but inert. `WindowHealthy` says what a
healthy window is — every slot of every scoring round directly
committed on the anchor's history — and BN12 says such a window reaches
the `expected` count, since the scoring rounds `waveLength ≤ d ≤
interval` are exactly `expected` divided by the count.

**What this does not claim**: that a good DAG *makes* the window
healthy. That needs the anchor's history to carry the good validators'
blocks below it, a property of the base protocol rather than of the
mechanism, and is the natural next result.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Healthy

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A healthy window**: every slot of every scoring round of the window
is directly committed on the anchor's causal history. -/
def WindowHealthy (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ P.maxLeaders) : Prop :=
  ∀ d, R.waveLength ≤ d → d ≤ P.interval → ∀ l, l < m →
    R.SlotDirect (Sched getLeader hk m hm hmax) U (R.historyView U A hA)
      (m * ((R.block U A).round - d) + l)

/-- **BN12a, a healthy window reaches the expected count.** -/
def Counted (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U) (m : ℕ) (hm : 0 < m)
    (hmax : m ≤ P.maxLeaders),
    R.waveLength ≤ P.interval → P.interval ≤ (R.block U A).round →
    WindowHealthy R P getLeader hk U A hA m hm hmax →
    expected R P m ≤ observed R P getLeader hk U A m hm hmax

/-- **BN12b, and the rule then increases.** At a threshold of at most
one — the paper's `num / den ≤ 1` — a healthy window raises the count
by one, capped at `maxLeaders`, and resets the back-off. -/
def Raises (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U) (m : ℕ) (hm : 0 < m)
    (hmax : m ≤ P.maxLeaders) (backoff : ℕ) (V : R.View U),
    P.num ≤ P.den → R.waveLength ≤ P.interval → P.interval ≤ (R.block U A).round →
    WindowHealthy R P getLeader hk U A hA m hm hmax →
    Aimd.rule R P getLeader hk m backoff U V A = (min (m + 1) P.maxLeaders, 0)

/-- **BN12c, the count counts verdicts.** Every slot the window counts is
a slot the protocol committed — `Properties.CommitsDirect`, without
which a rule whose direct predicate holds of everything would pass this
count vacuously. -/
def Sound (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U) (m : ℕ) (hm : 0 < m)
    (hmax : m ≤ P.maxLeaders),
    WindowHealthy R P getLeader hk U A hA m hm hmax →
    ∀ d, R.waveLength ≤ d → d ≤ P.interval → ∀ l, l < m →
      ∃ L, R.Decided (Sched getLeader hk m hm hmax) (R.historyView U A hA)
        (m * ((R.block U A).round - d) + l) (some L)

/-- The count of a healthy window, and the step it produces. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders),
    Properties.CommitsDirect R.toDagRule (fun {_} V => R.DirectCommitIn V) →
    Counted R P getLeader hk ∧ Raises R P getLeader hk ∧ Sound R P getLeader hk

end Healthy

end Barnacle

end LeanDag
