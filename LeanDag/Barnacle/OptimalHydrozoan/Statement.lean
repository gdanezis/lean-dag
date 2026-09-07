import LeanDag.Barnacle.Model.Anchored
import LeanDag.OptimalHydrozoan.Carrier
/-!
# Barnacle over Optimal-Hydrozoan — statement

The theory-only variant of Hydrozoan (`docs/optimal-hydrozoan.md`) as a
base rule with its laws. The universes are the records satisfying
`LeaderExcludedAll`, Optimal's exclusion clause stated without a
schedule, since the clause names one and the universe is fixed before
it. Identifiers need no order — the evidence rung has no tie-break — and
the fast path is Optimal's, at `qFastOpt`. Statements only; the proofs
live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]

/-- **Optimal-Hydrozoan as a base rule**: its anchored rule over the
Hydrozoan records obeying the exclusion rule. -/
def optimalHydrozoan [LeanDag.OptimalHydrozoan.OptimalFaults Replica] :
    BaseRule Replica BlockId Unit :=
  ofAnchoredOn (LeanDag.OptimalHydrozoan.optimalAnchored Replica BlockId)
    LeanDag.OptimalHydrozoan.LeaderExcludedAll

namespace OptimalHydrozoan

/-- **Optimal-Hydrozoan satisfies the laws**; agreement is OH3. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica],
    BaseRule.Laws (optimalHydrozoan (Replica := Replica) (BlockId := BlockId))

/-- The laws of the base rule. -/
def Statement : Prop := Laws

end OptimalHydrozoan

end Barnacle

end LeanDag
