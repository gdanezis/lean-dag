import LeanDagTest.OptimalHydrozoan.Universe
import LeanDag.Barnacle.OptimalHydrozoan.Proof
import LeanDag.Barnacle.OptimalHydrozoanLive.Proof

/-!
# Barnacle over Optimal-Hydrozoan — the witnesses

The sixth instantiation, on the sixteen-block universe of
`LeanDagTest/OptimalHydrozoan/Universe.lean` where the Byzantine leader
equivocates and a decision-round block has watched it.

The point of interest is the carrier. `docs/hydrozoan-integration.md`
§4.1 could not use `OptUniverse` as the interface's `Universe`, that
type being indexed by a schedule, and the replacement is the same
clause stated over a `(round, leader)` pair. These two `decide` calls
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

/-- The universe the Optimal arc exhibits as an `OptUniverse` obeys the
schedule-free rule. -/
theorem leaderExcluded_UX :
    OptimalHydrozoan.LeaderExcludedAll LeanDagTest.OptimalHydrozoan.UX := by decide

/-- And the one no `OptUniverse` extends does not. -/
example : ¬ OptimalHydrozoan.LeaderExcludedAll LeanDagTest.OptimalHydrozoan.UbadX := by
  decide

/-- The carrier, at the witness universe. -/
abbrev CX : {U : LeanDag.Hydrozoan.BlockUniverse (Fin 4) (Fin 16) //
    OptimalHydrozoan.LeaderExcludedAll U} :=
  ⟨LeanDagTest.OptimalHydrozoan.UX, leaderExcluded_UX⟩

/-- The laws hold at this configuration; applying them end to end is
what would fail were a hypothesis silently strengthened. -/
theorem lawsX : LeanDag.Barnacle.BaseRule.Laws
    (LeanDag.Barnacle.optimalHydrozoan (Replica := Fin 4) (BlockId := Fin 16)) :=
  LeanDag.Barnacle.OptimalHydrozoan.holds (Fin 4) (Fin 16)

end Barnacle

end LeanDagTest
