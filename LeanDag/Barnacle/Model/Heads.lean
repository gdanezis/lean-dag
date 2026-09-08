import LeanDag.Properties.Commit
import LeanDag.Barnacle.Model.Live
/-!
# Barnacle: the descent laws and runs of heads

What a base protocol owes for liveness under multiple leaders per round
(`barnacle.md` §8). The development's own run-of-consecutive-slots route
has no instance under the paper's rotation at several leaders and few
validators, so the argument instead runs on *heads*, first slots of
consecutive rounds. `LiveRule.Descent` packages the two facts this
needs — A4's direct-commit clause and A3's indirect rule — and
`HeadsRun` is the schedule clause a run of heads satisfies; round-robin
meets it by pigeonhole (`Heads/Statement.lean`).

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **The descent laws** of a live rule: `Properties.Descent` at the
rule's own gap and goodness predicate, with `slack` the number of
validators the good set may miss. -/
abbrev LiveRule.Descent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop :=
  Properties.Descent R.toBaseRule.toDagRule R.Good R.waveLength slack

/-- **A run of heads**: from every round `r`, within `c₀` rounds, `g`
consecutive rounds whose heads — first slots, led by `getLeader` of the
round — are led by members of `T`. -/
def HeadsRun (getLeader : ℕ → Validator) (T : Finset Validator) (g c₀ : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ρ + g ≤ r + c₀ ∧ ∀ i, i < g → getLeader (ρ + i) ∈ T

end Barnacle

end LeanDag
