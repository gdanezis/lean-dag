import LeanDag.Properties.Carrier
import LeanDag.Common.Density
/-!
# What a rule owes about its own validity

`docs/target-properties.md` §11.4. Optional, like the rest of
`Properties/Optional/`: chain quality (`Arcs/Quality.lean`) rests on
density, which rests on one clause of block validity — a non-genesis
block references a quorum of distinct authors one round below — and
`Quorate` names that clause as a `Prop` rather than a carrier field, on
the precedent of `Causal`. A rule that shows the six composes with
every other mechanism regardless; chain quality is a guarantee a
deployment may or may not want to quote, and every rule here discharges
`Quorate` in a line.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A rule's universes are quorate.** Every non-genesis block
references blocks by at least `n − slack` distinct authors — the
counting clause of validity, which is what density counts against.

The fault model comes in as a `Reliability`: which validators the count
is about, how many may be outside them, and that those are a minority.
Six fault classes are in play across the development and each supplies
one in a line, which is why neither this property nor `LeanDag.Density`
names any of them. -/
def Quorate (R : DagRule Validator BlockId Payload) (rel : Reliability Validator) : Prop :=
  ∀ U : R.Universe, QuorateOn (R.block U) (R.ids U) rel

end Properties

end LeanDag
