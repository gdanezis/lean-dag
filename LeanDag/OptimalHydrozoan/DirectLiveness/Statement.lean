import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.Hydrozoan.Model.Liveness
/-!
# Optimal-Hydrozoan: direct liveness — statement

`CommitLiveness` is Hydrozoan's slow path, unchanged, harvested as
`DecidedOpt`. `SkipLiveness` is the arc's addition: a candidate-less
slot is directly skipped by the guaranteed quorum alone, with no
fault-count or synchrony hypothesis — a liveness claim where Hydrozoan's
same skip is only opportunistic. It is restricted to candidate-less
slots deliberately: with a candidate present, Byzantine votes can make
every correct decision-round block fast evidence (FinWhale's attack), so
such a slot resolves indirectly instead. `FastLatency` stays outside
`Statement`, as in Hydrozoan: a performance characterization at `pOpt`.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace DirectLiveness

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- **Commit liveness** (Hydrozoan's, harvested as `DecidedOpt`): a
quorum-sized correct set, populated through the wave and synchronised
from `R`, slow-commits its correct leader, on any view caught up to the
decision round. The fast path may also fire in the same universe; this
is the route the guaranteed quorum always reaches. -/
def CommitLiveness (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ),      -- for any set T, round R, slot k:
    T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) →     -- T holds only correct replicas ...
    q Replica ≤ T.card →                 -- ... and is at least a DAG quorum,
    SynchronisedOn U.toBlockRecord T R →  -- T is internally synchronised from R,
    R ≤ S.slotRound k →                  -- the wave lies at or after R,
    PopulatedOn U.toBlockRecord T (S.slotRound k) →      -- T fills the propose round ...
    PopulatedOn U.toBlockRecord T (S.slotRound k + 1) →  -- ... the voting round ...
    PopulatedOn U.toBlockRecord T (S.slotRound k + 2) →  -- ... and the decision round,
    S.leader k ∈ T →                     -- and the slot's leader is in T:
    ∀ V : LeanDag.Hydrozoan.View U.toBlockRecord,        -- then, on any view caught up
      V.CoversUpto (S.slotRound k + 2) → -- ... to the decision round:
    ∃ L, IsLeaderBlock U.toBlockRecord k L ∧           -- a candidate exists,
      SlowCommit U.toBlockRecord L (S.slotRound k) ∧   -- the slow threshold is met,
      DecidedOpt U V k (some L)          -- and its verdict is committed

/-- **Skip liveness** (the arc's addition): a candidate-less slot is
directly skipped by any quorum-sized correct set filling its voting and
decision rounds, on any view caught up to the decision round. No
synchrony or fault-count hypothesis: slotBlames and no-evidence
reference nothing. -/
def SkipLiveness (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (k : ℕ),        -- for any set T and slot k:
    T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) →     -- T holds only correct replicas ...
    q Replica ≤ T.card →                 -- ... and is at least a DAG quorum,
    PopulatedOn U.toBlockRecord T (S.slotRound k + 1) →  -- T fills the voting round ...
    PopulatedOn U.toBlockRecord T (S.slotRound k + 2) →  -- ... and the decision round,
    (∀ L, ¬ IsLeaderBlock U.toBlockRecord k L) →         -- and no candidate exists:
    ∀ V : LeanDag.Hydrozoan.View U.toBlockRecord,        -- then, on any view caught up
      V.CoversUpto (S.slotRound k + 2) → -- ... to the decision round:
    SkippedLeaderOpt U.toBlockRecord k ∧  -- the slot skips directly,
      DecidedOpt U V k none              -- and the verdict is output

/-- Direct liveness of Optimal-Hydrozoan, over every fault configuration,
schedule, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    CommitLiveness U ∧ SkipLiveness U

/-- **Performance, not liveness — deliberately outside `Statement`.**
When the actual faults fit `pOpt`, a synchronised, populated wave with a
correct leader fires the fast path in two rounds — needing all of
`Correct`, not just a quorum-sized `T`. -/
def FastLatency (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (R k : ℕ),                           -- for any round R and slot k:
    (O.byzantine ∪ O.crashed).card ≤ pOpt Replica →  -- ACTUAL faults fit pOpt,
    Synchronised U.toBlockRecord R →   -- all correct synchronised from R,
    R ≤ S.slotRound k →                  -- the wave lies at or after R,
    Populated U.toBlockRecord (S.slotRound k) →        -- correct fill the propose round ...
    Populated U.toBlockRecord (S.slotRound k + 1) →    -- ... and the voting round,
    S.leader k ∈ (LeanDag.Hydrozoan.Correct : Finset Replica) →            -- and the leader is correct:
    ∃ L, IsLeaderBlock U.toBlockRecord k L ∧           -- then a candidate exists ...
      FastCommitOpt U.toBlockRecord L (S.slotRound k)  -- ... and it fast-commits

end DirectLiveness

end OptimalHydrozoan

end LeanDag
