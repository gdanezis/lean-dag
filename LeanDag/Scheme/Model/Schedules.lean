import LeanDag.Scheme.Model.Local
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Barnacle.Model.Schedule
import LeanDag.Timed.Silent
import LeanDag.Scheme.Model.Reactive
/-!
# The decider as a Barnacle live rule

`schemeLive p σ rel` is the decider at `p` and `σ` read by Barnacle's runs
(`LeanDag/Barnacle/`), with the DAG good from a round at the reliability
`rel` (`Timed.Good`). HammerHead's runs are Barnacle's at
`Boundary.atThreshold` and read the same rule.

`p.Scheduled n slack` is what Barnacle's round-robin liveness asks of a
row on `n` validators of which at most `slack` are unreliable.

`schemeLiveSilent p σ rel fb` is the same rule with the DAG good when, in
addition, the validators outside a synchronised quorum are silent or among
`fb` others (`Timed.SilentGood`). `p.SkipScheduled n slack fb` is what
round-robin liveness asks there, on one slot per round.

`schemeLiveReactive p σ rel` is the same rule with the DAG good under a
schedule `S` when a quorum of `rel` runs it responsively under `S`
(`reactiveGood`): past GST, its timeout clearing `2Δ + proc`, its
validators waiting for `S`'s leaders up to the horizon. A responsive
validator waits only for the leaders it knows, so this goodness, unlike
the timed ones, reads the schedule.

Definitions only; the theorems are `Scheme/Schedules/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

/-- **The decider as a live rule**, at reliability `rel`. -/
def schemeLive (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) : Barnacle.LiveRule Validator BlockId Payload :=
  Barnacle.liveOfAnchored (schemeAnchored p σ) (fun _ => rfl) rel

/-- **The row fits round-robin scheduling** on `n` validators, at most
`slack` unreliable: `n − slack` meets the certificate and commit
thresholds, and `waveLength · slack + 1 ≤ n`. -/
def Params.Scheduled (p : Params) (n slack : ℕ) : Prop :=
  p.certThreshold ≤ n - slack ∧ p.commitThreshold ≤ n - slack ∧ p.waveLength * slack + 1 ≤ n

/-- **The decider as a live rule whose crashed validators are silent**, at
reliability `rel` with at most `fb` validators neither synchronised nor
silent. -/
def schemeLiveSilent (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (fb : ℕ) : Barnacle.LiveRule Validator BlockId Payload :=
  { Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl) with
    Good := fun _ => Timed.SilentGood (schemeAnchored p σ).toDagRule rel fb }

/-- **The row fits round-robin scheduling on one slot per round with silent
crashes**, on `n` validators with at most `slack` unreliable and `fb`
neither reliable nor silent: `n − slack` meets the certificate, commit and
skip thresholds, the vote round is one above the proposal, and
`(waveLength − 1)·fb + slack + 1 ≤ n`. -/
def Params.SkipScheduled (p : Params) (n slack fb : ℕ) : Prop :=
  p.certThreshold ≤ n - slack ∧ p.commitThreshold ≤ n - slack ∧ p.skipThreshold ≤ n - slack ∧
    p.voteOffset = 1 ∧ (p.waveLength - 1) * fb + slack + 1 ≤ n

/-- **The heads of `C` are a permutation of round-robin.** -/
def PermRR {n : ℕ} (hn : 0 < n) (C : Barnacle.Config (Fin n)) : Prop :=
  ∃ π : Equiv.Perm (Fin n), C.head = fun ρ => π (Barnacle.roundRobin n hn ρ)

/-- **One slot per round, its heads a permutation of round-robin.** -/
def SinglePermRR {n : ℕ} (hn : 0 < n) (C : Barnacle.Config (Fin n)) : Prop :=
  (∀ r, C.slotsAt r = 1) ∧ PermRR hn C

attribute [local instance] noFaults in
/-- **Good under `S`, responsively**: a quorum `T` of `rel` of honest
validators runs the family responsively under `S` past GST at `Rnd`, the
timeout clearing `2Δ + proc` from `Rnd`, and waits for `S`'s leaders up to
`N`. -/
def reactiveGood [Nonempty Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator)
    (S : Slots Validator) (U : BlockRecord Validator BlockId Payload P honest) (Rnd N : ℕ) :
    Prop :=
  ∃ T : Finset Validator, rel.IsQuorum T ∧ T ⊆ honest ∧
    ∃ (N' : ℕ) (rs : SchemeReactive (S := S) (Fintype.card Validator - rel.slack) p σ U T N'),
      rs.gst ≤ Rnd ∧ (∀ n, Rnd ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) ∧ N ≤ rs.waits

/-- **The decider as a live rule, run responsively**, at reliability
`rel`. -/
def schemeLiveReactive [Nonempty Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator) :
    Barnacle.LiveRule Validator BlockId Payload :=
  { Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl) with
    Good := fun S U Rnd N => reactiveGood p σ rel S U Rnd N }

end Scheme

end LeanDag
