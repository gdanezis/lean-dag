import LeanDag.Barnacle.Model.Anchored
import LeanDag.OptimalHydrozoan.Carrier
/-!
# Barnacle over Optimal-Hydrozoan — statement

The theory-only variant of Hydrozoan (`docs/optimal-hydrozoan.md`) as a
base rule with its laws. The universes are Optimal's own records, read
through their projection to Hydrozoan's. Identifiers need no order — the evidence rung has no tie-break — and
the fast path is Optimal's, at `qFastOpt`. Statements only; the proofs
live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]

/-- **Optimal-Hydrozoan as a base rule**: its anchored rule over its
records. -/
def optimalHydrozoan [LeanDag.OptimalHydrozoan.OptimalFaults Replica] :
    BaseRule Replica BlockId Unit :=
  ofAnchoredVia (LeanDag.OptimalHydrozoan.optimalAnchored Replica BlockId)
    LeanDag.OptimalHydrozoan.OptUniverse.toBlockRecord

namespace OptimalHydrozoan

/-- **Optimal-Hydrozoan satisfies the laws**; agreement is OH3. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica],
    BaseRule.Laws (optimalHydrozoan (Replica := Replica) (BlockId := BlockId))

end OptimalHydrozoan

end Barnacle

end LeanDag
