import LeanDag.Barnacle.Model.Anchored
import LeanDag.OptimalHydrozoan.Carrier
/-!
# Barnacle over Optimal-Hydrozoan — statement

The theory-only variant of Hydrozoan (`docs/optimal-hydrozoan.md`) as a
base rule, so that the adaptive leader count runs over it too. The
mirror of `Barnacle/Hydrozoan/`, with three differences.

* **The carrier bears the exclusion rule.** Optimal-Hydrozoan's
  universe carries a validity clause Hydrozoan's does not — a block
  that has watched the leader equivocate must not reference it — and
  that clause names the schedule, which the universe is fixed before.
  The rule is therefore `ofAnchoredOn` at `LeaderExcludedAll`, the same
  clause stated over a `(round, leader)` pair rather than a slot
  (`docs/hydrozoan-integration.md` §3).
* **No order on identifiers.** Optimal's evidence rung needs no
  tie-break (`optimal-hydrozoan.md` §7), so `DecidableEq` suffices
  where Hydrozoan's instantiation takes a `LinearOrder`.
* **The fast threshold is Optimal's.** The direct predicate is
  `FastCommitOptInView ∨ SlowCommitInView` — the fast path at
  `qFastOpt = n − pOpt`, the slow path unchanged from Hydrozoan.

Wave length is three for the same reason as Hydrozoan's
(`Barnacle/Hydrozoan/Statement.lean`): it is also the anchor gap of the
descent laws.
Statements only; the proofs live in `Proof.lean`.
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

/-- **Optimal-Hydrozoan satisfies the laws.** Agreement is OH3, which
like HZ3 is already quantified over every universe and every schedule. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica],
    BaseRule.Laws (optimalHydrozoan (Replica := Replica) (BlockId := BlockId))

/-- The laws of the base rule. -/
def Statement : Prop := Laws

end OptimalHydrozoan

end Barnacle

end LeanDag
