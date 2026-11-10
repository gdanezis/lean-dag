import LeanDag.Scheme.Model.Local
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Barnacle.Model.Schedule
/-!
# The decider as a Barnacle live rule

`schemeLive p σ rel` is the decider at `p` and `σ` read by Barnacle's runs
(`LeanDag/Barnacle/`), with the DAG good from a round at the reliability
`rel` (`Timed.Good`). HammerHead's runs are Barnacle's at
`Boundary.atThreshold` and read the same rule.

`p.Scheduled n slack` is what Barnacle's round-robin liveness asks of a
row on `n` validators of which at most `slack` are unreliable.

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

/-- **The heads of `C` are a permutation of round-robin.** -/
def PermRR {n : ℕ} (hn : 0 < n) (C : Barnacle.Config (Fin n)) : Prop :=
  ∃ π : Equiv.Perm (Fin n), C.head = fun ρ => π (Barnacle.roundRobin n hn ρ)

end Scheme

end LeanDag
