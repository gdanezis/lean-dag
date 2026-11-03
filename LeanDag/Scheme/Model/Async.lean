import LeanDag.Scheme.Model.Rule
/-!
# The asynchronous rows: the safe set and the coin clause

`docs/scheme.md` §11. An asynchronous row elects a wave's leader by a
coin opened at the decision round. The model has no adversary and no
time, so the coin enters, as in the Mahi-Mahi and Async BlueBottle arcs,
through its observable consequence on the schedule and the record:

* `safeAt p U r`: the honest validators whose round-`r` block every
  vote-round block reaches; `safe` the same at a slot's round. The paper
  calls these blocks the core;
* `Params.AsyncReady`: the arithmetic a row meets for the count at `b`
  buffer rounds;
* `SafeWithin`: in every window of `c` slots whose decision rounds lie
  below the horizon `N`, the schedule names a safe leader;
  `SafeRunWithin`, a run of `d` safe leaders.

Definitions only; the claims are `Scheme/Async/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

/-- **Ready for the asynchronous count**, at `b` buffer rounds: two quorums
of `q` overlap past `f` (the common core), the vote round is `b + 1` above
the proposal, a certificate fits the wave and `q`, and the commit threshold
is within `q`. -/
def Params.AsyncReady (p : Params) (n f q b : ℕ) : Prop :=
  n + f + 1 ≤ 2 * q ∧ p.voteOffset = b + 1 ∧ p.CertFits q ∧ p.commitThreshold ≤ q

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest)

section Safe

variable [P.Mechanised]

/-- **The safe set at round `r`**: the honest validators whose round-`r`
block lies in the history of every vote-round block. -/
def safeAt (U : BlockRecord Validator BlockId Payload P honest) (r : ℕ) : Finset Validator :=
  honest.filter (fun v => ∃ L ∈ U.ids, (U.block L).round = r ∧ (U.block L).creator = v ∧
    ∀ b ∈ U.ids, (U.block b).round = r + p.voteOffset → L ∈ history U b)

variable [S : Slots Validator]

/-- The safe set at slot `k`'s round. -/
def safe (U : BlockRecord Validator BlockId Payload P honest) (k : ℕ) : Finset Validator :=
  safeAt p U (S.slotRound k)

/-- **The single-hit clause over safe leaders**: in every window of `c`
slots whose decision rounds lie below the horizon `N`, the schedule names a
safe leader. -/
def SafeWithin (U : BlockRecord Validator BlockId Payload P honest) (c N : ℕ) : Prop :=
  ∀ k, (schemeAnchored p σ).decisionRound (k + c) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ safe p U k'

/-- **The run clause over safe leaders**: in every window of `c` slots
below the horizon, a run of `d` consecutive slots led by safe leaders. -/
def SafeRunWithin (U : BlockRecord Validator BlockId Payload P honest) (c d N : ℕ) : Prop :=
  ∀ k, (schemeAnchored p σ).decisionRound (k + c + d - 1) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ safe p U (k' + i)

end Safe

end Scheme

end LeanDag
