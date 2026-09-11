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

**BN12d** is the complement: below one wave the measurement is empty and
the test passes unconditionally, so `waveLength ≤ interval` is what a
deployment owes the loop.

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
    (Aimd.rule R P lead hl C backoff U V A).1.slotsAt =
        (fun _ => Aimd.count P (C.slotsAt (R.block U A).round) backoff true) ∧
      (Aimd.rule R P lead hl C backoff U V A).1.lead = lead ∧
      (Aimd.rule R P lead hl C backoff U V A).1.interval = C.interval ∧
      (Aimd.rule R P lead hl C backoff U V A).2 = 0

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

/-- **BN12d, and below one wave there is nothing to measure.** A
configuration whose interval is shorter than the rule's wave has no
window round old enough to have been decided, so `expected` is zero at
every anchor and the health test passes whatever the DAG did: the rule
raises the count and resets the back-off, always. The loop is open, and
a deployment that wants it closed must choose `waveLength ≤ interval` —
which is the hypothesis BN12a carries. -/
def Vacuous (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders) : Prop :=
  ∀ C : Config Validator, C.interval < R.waveLength →
    (∀ r, expected R C r = 0) ∧
    ∀ (U : R.Universe) (V : R.View U) (A : BlockId) (backoff : ℕ),
      (Aimd.rule R P lead hl C backoff U V A).1.slotsAt =
          (fun _ => Aimd.count P (C.slotsAt (R.block U A).round) backoff true) ∧
        (Aimd.rule R P lead hl C backoff U V A).2 = 0

/-- The count of a healthy window, the step it produces, and the
interval below which there is no measurement. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders),
    Properties.CommitsDirect R.toDagRule (fun {_} V => R.DirectCommitIn V) →
    Counted R ∧ Raises R P lead hl ∧ Sound R ∧ Vacuous R P lead hl

end Healthy

end Barnacle

end LeanDag
