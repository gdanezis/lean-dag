import LeanDagTest.OptimalHydrozoan.Universe
import LeanDag.Barnacle.OptimalHydrozoan.Proof
import LeanDag.Barnacle.OptimalHydrozoanLive.Proof
/-!
# Barnacle over Optimal-Hydrozoan — the witnesses

The sixth instantiation, on the sixteen-block universe of
`LeanDagTest/OptimalHydrozoan/Universe.lean` where the Byzantine leader
equivocates and a decision-round block has watched it.

The point of interest is the carrier. `OptUniverse` cannot be the interface's `Universe`, that type being indexed by a schedule, and the carrier is the same clause stated over a `(round, leader)` pair (`docs/hydrozoan-integration.md` §3). These two `decide` calls
say the replacement separates exactly the universes the arc's own rule
does: `UX`, which the arc exhibits as an `OptUniverse`, satisfies it,
and `UbadX`, which the arc exhibits as a `BlockUniverse` that **no**
`OptUniverse` extends, does not.

So the schedule-free form is neither vacuous nor stronger in effect
than the rule it replaces, on the data the Optimal arc built to test
that rule.
-/

namespace LeanDagTest

namespace Barnacle

open LeanDag LeanDag.Barnacle

/-- The universe the arc exhibits fails the exclusion clause at one block,
so it is no Optimal universe; `OX` is. -/
example : ¬ Clause.leaderExcluded LeanDagTest.OptimalHydrozoan.UbadX.block
    (LeanDagTest.OptimalHydrozoan.UbadX.block 15) := by decide

/-- The laws hold at this configuration; applying them end to end is
what would fail were a hypothesis silently strengthened. -/
theorem lawsX : LeanDag.Barnacle.BaseRule.Laws
    (LeanDag.Barnacle.optimalHydrozoan (Replica := Fin 4) (BlockId := Fin 16)) :=
  LeanDag.Barnacle.OptimalHydrozoan.holds (Fin 4) (Fin 16)

end Barnacle

end LeanDagTest
