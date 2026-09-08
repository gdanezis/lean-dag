import LeanDag.Barnacle.Model.Anchored
import LeanDag.Hydrozoan.Helpers.Carrier
/-!
# Barnacle over Hydrozoan — statement

The dual-path commit rule under hybrid faults (`docs/hydrozoan.md`) as a
base rule with its laws; the live rule is `Barnacle/HydrozoanLive/`. The
carrier is Hydrozoan's own record, which needs neither the committee
condition `c ≤ k` nor the self-parent clause here. The wave length is
three, not the fast path's two, because it is also the anchor gap of the
descent laws' indirect rule, which at two would ask for a conclusion no
Hydrozoan derivation gives; the direct predicate is the disjunction of
the two routes, and neither branch may be dropped (`docs/hydrozoan.md`
§0, §11). Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [LinearOrder BlockId]

/-- **Hydrozoan as a base rule**: its anchored rule, over its own record. -/
def hydrozoan [LeanDag.Hydrozoan.Faults Replica] : BaseRule Replica BlockId Unit :=
  ofAnchored (LeanDag.Hydrozoan.hydrozoanAnchored Replica BlockId)

namespace Hydrozoan

/-- **Hydrozoan satisfies the laws**; agreement is HZ3. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica],
    BaseRule.Laws (hydrozoan (Replica := Replica) (BlockId := BlockId))

end Hydrozoan

end Barnacle

end LeanDag
