import LeanDag.Hydrozoan.IndirectLiveness.Statement
import LeanDag.Hydrozoan.Model.Liveness
/-!
# Statement: eventual decision — the ledger does not stall

The liveness headline, composing direct liveness (commits a
synchronised, populated, correct-led wave) with indirect liveness
(settles everything below a committed run). `RunDecidesBelow` takes the
run's location as a hypothesis; `RunsRecur` is the schedule-only claim
that fairness places one past any point. `ledgerProgress` in
`Proof.lean` composes them.
-/

namespace LeanDag

namespace Hydrozoan
namespace EventualDecision

section Schedule

variable (Replica : Type*) [S : Slots Replica]

/-- **Fairness places a run wherever needed**: past any slot `k` and any
round `R`, some run of `c` consecutive `T`-led slots begins. Pure
schedule arithmetic. -/
def RunsRecur : Prop :=
  ∀ (T : Finset Replica) (c k R : ℕ),
    FairRunOn T c →                      -- given a fair schedule:
    ∃ b, k ≤ b ∧                         -- a run location past k ...
      R ≤ S.slotRound b ∧                -- ... at or after round R ...
      ∀ i, i < c → S.leader (b + i) ∈ T  -- ... with every slot T-led.

end Schedule

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- **A committed-to-be run decides everything below it.** The workhorse
with the run location `b` explicit: direct liveness commits each of the
`c` run slots, and the indirect descent settles every slot below. -/
def RunDecidesBelow (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R b c : ℕ),
    T ⊆ (Correct : Finset Replica) →     -- a set of correct replicas ...
    q Replica ≤ T.card →                 -- ... of at least a DAG quorum,
    SynchronisedOn U T R →               -- internally synchronised from R,
    0 < c →                              -- a nonempty run of slots ...
    (hydrozoanAnchored Replica BlockId).SpansEligible c →  -- ... every run's end anchoring all below,
    R ≤ S.slotRound b →                  -- lying at or after R,
    (∀ i, i < c → S.leader (b + i) ∈ T) →  -- every run slot T-led,
    (∀ r, S.slotRound b ≤ r →            -- and T fills every round from
      r ≤ S.slotRound (b + c - 1) + 2 →  -- the run's propose round to its
      PopulatedOn U T r) →               -- last decision round:
    ∀ V : View U,                        -- then, on any view caught up
      V.CoversUpto (S.slotRound (b + c - 1) + 2) →  -- ... to that round:
    ∀ i, i < b → ∃ v, Decided U V i v    -- all below decided.

/-- Eventual decision, over every fault configuration, schedule,
tie-break order, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica],
    (∀ U : BlockUniverse Replica BlockId, RunDecidesBelow U) ∧
      RunsRecur Replica

end EventualDecision
end Hydrozoan

end LeanDag
