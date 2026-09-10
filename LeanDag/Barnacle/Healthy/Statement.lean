import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Aimd.Rule
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
C.interval` are exactly the rounds `expected` counts the slots of.

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
def WindowHealthy (R : BaseRule Validator BlockId Payload) (C : Config Validator)
    (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U) : Prop :=
  ∀ d, R.waveLength ≤ d → d ≤ C.interval → ∀ i, i < C.slotsAt ((R.block U A).round - d) →
    R.SlotDirect C.sched U (R.historyView U A hA) (C.index ((R.block U A).round - d) i)

/-- **BN12a, a healthy window reaches the expected count.** -/
def Counted (R : BaseRule Validator BlockId Payload) : Prop :=
  ∀ (C : Config Validator) (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U),
    R.waveLength ≤ C.interval → C.interval ≤ (R.block U A).round →
    WindowHealthy R C U A hA →
    expected R C (R.block U A).round ≤ observed R C U A

/-- **BN12b, and the rule then increases.** At a threshold of at most
one — the paper's `num / den ≤ 1` — a healthy window raises the count
by one, capped at `maxLeaders`, and resets the back-off. -/
def Raises (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders) : Prop :=
  ∀ (C : Config Validator) (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U)
    (backoff : ℕ) (V : R.View U),
    P.num ≤ P.den → R.waveLength ≤ C.interval → C.interval ≤ (R.block U A).round →
    WindowHealthy R C U A hA →
    Aimd.rule R P lead hl C backoff U V A =
      (Config.uniform lead hl (Aimd.count P (C.slotsAt (R.block U A).round) backoff true)
        (Aimd.count_pos P _ _ _) (Aimd.count_le P _ _ _) C.interval, 0)

/-- **BN12c, the count counts verdicts.** Every slot the window counts is
a slot the protocol committed — `Properties.CommitsDirect`, without
which a rule whose direct predicate holds of everything would pass this
count vacuously. -/
def Sound (R : BaseRule Validator BlockId Payload) : Prop :=
  ∀ (C : Config Validator) (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U),
    WindowHealthy R C U A hA →
    ∀ d, R.waveLength ≤ d → d ≤ C.interval →
      ∀ i, i < C.slotsAt ((R.block U A).round - d) →
        ∃ L, R.Decided C.sched (R.historyView U A hA)
          (C.index ((R.block U A).round - d) i) (some L)

/-- The count of a healthy window, and the step it produces. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders),
    Properties.CommitsDirect R.toDagRule (fun {_} V => R.DirectCommitIn V) →
    Counted R ∧ Raises R P lead hl ∧ Sound R

end Healthy

end Barnacle

end LeanDag
