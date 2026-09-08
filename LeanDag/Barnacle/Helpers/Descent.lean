import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Timed.Coverage
/-!
# The descent laws, from a support

Not part of the audit surface. `LiveRule.Descent` for any live rule with
a `Support` whose `OfCoverage` and `Commits` hold at a fault model, an
`Indirect` property at the rule's eligibility, and good DAGs that are
`Timed.Good` — the generic theorem read at the rule's own gap.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A Barnacle rule's eligibility**: an anchor a full wave above the slot. -/
def LiveRule.elig (R : LiveRule Validator BlockId Payload) : (ℕ → ℕ) → ℕ → ℕ → Prop :=
  fun sr i j => sr i + R.waveLength ≤ sr j

/-- **The descent laws, from a support**, at the fault model's slack:
`Timed.descent_of_support` at a live rule's own gap and goodness. -/
theorem descent_of_support (R : LiveRule Validator BlockId Payload)
    (sp : Properties.Support R.toBaseRule.toDagRule) {rel : Reliability Validator}
    (hcov : Timed.OfCoverage sp rel) (hlc : sp.Commits rel)
    (hind : Properties.Indirect R.toBaseRule.toDagRule R.elig)
    (hwave : sp.wave ≤ R.waveLength)
    (hgood : ∀ U Rnd N, R.Good U Rnd N → Timed.Good R.toBaseRule.toDagRule rel U Rnd N) :
    R.Descent rel.slack :=
  Timed.descent_of_support _ R.Good R.waveLength sp hcov hlc hind hwave hgood

end Barnacle

end LeanDag
