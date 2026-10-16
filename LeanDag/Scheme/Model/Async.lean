import LeanDag.Scheme.Model.Rule
/-!
# The asynchronous rows: the good set and the coin clause

`docs/scheme.md` §11. An asynchronous row elects a wave's leader by a
coin opened at the decision round. The model has no adversary and no
time, so the coin enters, as in the Mahi-Mahi and Async BlueBottle arcs,
through its observable consequence on the schedule and the record:

* `goodAt p σ U r`: the validators whose round-`r` block the record's
  certificates commit: `commit` authors of decision-round blocks certify
  it; `good` the same at a slot's round;
* `Params.AsyncReady`: the arithmetic a row meets for the count at `b`
  buffer rounds;
* `UnpredictableWithin`: in every window of `c` slots whose decision
  rounds lie below the horizon `N`, the schedule names a good leader;
  `UnpredictableRunWithin`, a run of `d` good leaders.

Definitions only; the claims are `Scheme/Async/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

/-- **Ready for the asynchronous count**, at `b` buffer rounds: two quorums
of `q` overlap past `f` (the common core), the vote round is `b + 1` above
the proposal, certificates fit in `q` where votes are certified a round
later, and the commit threshold is within `q`. -/
def Params.AsyncReady (p : Params) (n f q b : ℕ) : Prop :=
  n + f + 1 ≤ 2 * q ∧ p.voteOffset = b + 1 ∧ 2 ≤ p.waveLength ∧
    (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q) ∧ p.commitThreshold ≤ q

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest)

/-- **The good set at round `r`**: the validators whose round-`r` block the
record's certificates commit, `commit` authors of decision-round blocks
certifying it. -/
def goodAt (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) : Finset Validator :=
  Finset.univ.filter (fun v => ∃ L ∈ U.ids, (U.block L).round = r ∧ (U.block L).creator = v ∧
    p.commitThreshold ≤ (creatorsOf U.block (certsAt p σ U L r)).card)

variable [S : Slots Validator]

/-- The good set at slot `k`'s round. -/
def good (U : BlockRecord Validator BlockId Payload P honest) (k : ℕ) : Finset Validator :=
  goodAt p σ U (S.slotRound k)

/-- **The single-hit clause**: in every window of `c` slots whose decision
rounds lie below the horizon `N`, the schedule names a good leader. -/
def UnpredictableWithin (U : BlockRecord Validator BlockId Payload P honest) (c N : ℕ) : Prop :=
  ∀ k, (schemeAnchored p σ).decisionRound (k + c) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good p σ U k'

/-- **The run clause**: in every window of `c` slots below the horizon, a
run of `d` consecutive slots led by good leaders. -/
def UnpredictableRunWithin (U : BlockRecord Validator BlockId Payload P honest) (c d N : ℕ) :
    Prop :=
  ∀ k, (schemeAnchored p σ).decisionRound (k + c + d - 1) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ good p σ U (k' + i)

end Scheme

end LeanDag
