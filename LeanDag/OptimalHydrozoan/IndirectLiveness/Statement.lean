import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.Hydrozoan.IndirectLiveness.Statement
/-!
# Optimal-Hydrozoan: indirect liveness — the graded rule is total

Hydrozoan's `IndirectLiveness` read over `DecidedOpt`: `AnchoredTotality`
says a nearest eligible committed anchor always returns a verdict — the
evidence rung fires on any candidate clearing it, uniqueness being slot
agreement's business, not totality's — and `DecidedBelowRun` says a
long-enough committed run decides everything below it.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace IndirectLiveness

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- Indirect liveness of Optimal-Hydrozoan, over every fault
configuration, schedule, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    (optimalAnchored Replica BlockId).Total U.toBlockRecord ∧
      (optimalAnchored Replica BlockId).DecidedBelowRun U.toBlockRecord

end IndirectLiveness

end OptimalHydrozoan

end LeanDag
