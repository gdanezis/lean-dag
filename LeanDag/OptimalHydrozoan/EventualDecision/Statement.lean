import LeanDag.OptimalHydrozoan.IndirectLiveness.Statement
import LeanDag.Hydrozoan.EventualDecision.Statement
import LeanDag.Hydrozoan.Model.Liveness
/-!
# Optimal-Hydrozoan: eventual decision — the ledger does not stall

Hydrozoan's `EventualDecision` read over `DecidedOpt`: `FairRunOn` and
`RunsRecur` are Hydrozoan's, reused verbatim, since fairness is
schedule-only; only `RunDecidesBelow` is re-stated. `ledgerProgress` in
`Proof.lean` composes them, as in Hydrozoan.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace EventualDecision

open LeanDag.Hydrozoan.EventualDecision (RunsRecur)

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- **A committed-to-be run decides everything below it.** Direct
liveness commits each of the `c` run slots through the unchanged slow
path, and the indirect descent settles every slot below. -/
def RunDecidesBelow (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R b c : ℕ),
    T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) →     -- a set of correct replicas ...
    q Replica ≤ T.card →                 -- ... of at least a DAG quorum,
    SynchronisedOn U.toBlockRecord T R →  -- internally synchronised from R,
    0 < c →                              -- a nonempty run of slots ...
    (optimalAnchored Replica BlockId).SpansEligible c →  -- ... every run's end anchoring all below,
    R ≤ S.slotRound b →                  -- lying at or after R,
    (∀ i, i < c → S.leader (b + i) ∈ T) →  -- every run slot T-led,
    (∀ r, S.slotRound b ≤ r →            -- and T fills every round from
      r ≤ S.slotRound (b + c - 1) + 2 →  -- the run's propose round to its
      PopulatedOn U.toBlockRecord T r) →  -- last decision round:
    ∀ V : LeanDag.Hydrozoan.View U.toBlockRecord,        -- then, on any view caught up
      V.CoversUpto (S.slotRound (b + c - 1) + 2) →  -- ... to that round:
    ∀ i, i < b → ∃ v, DecidedOpt U V i v  -- all below decided.

/-- Eventual decision, together with Hydrozoan's schedule-only fairness
claim. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica],
    (∀ U : OptUniverse Replica BlockId, RunDecidesBelow U) ∧
      RunsRecur Replica

end EventualDecision

end OptimalHydrozoan

end LeanDag
