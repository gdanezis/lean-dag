import LeanDag.Barnacle.Helpers.OptimalHydrozoan
import LeanDag.Barnacle.Hydrozoan.Statement
import LeanDag.Hydrozoan.Model.Liveness

/-!
# Barnacle over Optimal-Hydrozoan — statement

The theory-only variant of Hydrozoan (`docs/optimal-hydrozoan.md`) as a
base rule, so that the adaptive leader count runs over it too. The
mirror of `Barnacle/Hydrozoan/`, with three differences.

* **The carrier bears the exclusion rule.** Optimal-Hydrozoan's
  universe carries a validity clause Hydrozoan's does not — a block
  that has watched the leader equivocate must not reference it — and
  that clause names the schedule, which `BaseRule.Universe` is fixed
  before. The carrier is therefore the subtype satisfying
  `LeaderExcludedAll`, the same clause stated over a `(round, leader)`
  pair rather than a slot, from which `optUniverseOf` builds an
  `OptUniverse` at whatever schedule the interface hands
  (`docs/hydrozoan-integration.md` §4.1).
* **No order on identifiers.** Optimal's evidence rung needs no
  tie-break (`optimal-hydrozoan.md` §7), so `DecidableEq` suffices
  where Hydrozoan's instantiation takes a `LinearOrder`.
* **The fast threshold is Optimal's.** `DirectCommitIn` is
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

/-- **Optimal-Hydrozoan as a base rule.** The universe is the subtype
of Hydrozoan universes obeying the exclusion rule; wave length three;
the direct commit predicate is Optimal's fast path or Hydrozoan's
slow one. -/
def optimalHydrozoan [LeanDag.OptimalHydrozoan.OptimalFaults Replica] :
    BaseRule Replica BlockId Unit where
  Universe := {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId //
    OptimalHydrozoan.LeaderExcludedAll U}
  View := fun U => LeanDag.Hydrozoan.View U.val
  block := fun U => Hydrozoan.adaptBlk U.val
  ids := fun U => U.val.ids
  viewIds := fun V => V.ids
  full := fun U => LeanDag.Hydrozoan.View.full U.val
  historyView := fun U A hA => Hydrozoan.historyView U.val A hA
  waveLength := 3
  DirectCommitIn := fun {U} V L r =>
    LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L r
      ∨ LeanDag.Hydrozoan.SlowCommitInView U.val V L r
  decDirect := fun _ _ _ => inferInstance
  Decided := fun S {U} V k v =>
    letI := slotsOf S
    LeanDag.OptimalHydrozoan.DecidedOpt
      (OptimalHydrozoan.optUniverseOf U.val U.property) V k v

namespace OptimalHydrozoan

/-- **Optimal-Hydrozoan satisfies the laws.** Agreement is OH3, which
like HZ3 is already quantified over every universe and every schedule;
the rest are read off the `View` structure and the `DecidedOpt`
constructors. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica],
    BaseRule.Laws (optimalHydrozoan (Replica := Replica) (BlockId := BlockId))

/-- The laws of the base rule. -/
def Statement : Prop := Laws

end OptimalHydrozoan

end Barnacle

end LeanDag
