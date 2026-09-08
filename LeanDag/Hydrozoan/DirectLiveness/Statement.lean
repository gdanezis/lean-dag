import LeanDag.Hydrozoan.Model.Liveness
import LeanDag.Hydrozoan.Model.Decided
/-!
# Direct-commit liveness — statement

`CommitLiveness`: a synchronised, populated wave with a correct leader
slow-commits, on any view caught up to the decision round. The
guaranteed path is the slow one — `q = n − f − c` voters are certain,
and `q < q_fast` in general, but `q_cert ≤ q ≤ q_slow` keeps the slow
path reachable. The opportunistic pair (`FastLatency`, `SkipLatency`)
stays outside `Statement`: performance characterizations, not liveness.
-/

namespace LeanDag

namespace Hydrozoan

namespace DirectLiveness

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- **Commit liveness**: a quorum-sized correct set, populated through
the wave and synchronised from `R`, slow-commits its correct leader on
any view caught up to the decision round. The fast path may also fire
in the same universe; this is the route the guaranteed quorum always
reaches. -/
def CommitLiveness (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ),      -- for any set T, round R, slot k:
    T ⊆ (Correct : Finset Replica) →     -- T holds only correct replicas ...
    q Replica ≤ T.card →                 -- ... and is at least a DAG quorum,
    SynchronisedOn U T R →               -- T is internally synchronised from R,
    R ≤ S.slotRound k →                  -- the wave lies at or after R,
    PopulatedOn U T (S.slotRound k) →    -- T fills the propose round ...
    PopulatedOn U T (S.slotRound k + 1) →  -- ... the voting round ...
    PopulatedOn U T (S.slotRound k + 2) →  -- ... and the decision round,
    S.leader k ∈ T →                     -- and the slot's leader is in T:
    ∀ V : View U,                        -- then, on any view caught up
      V.CoversUpto (S.slotRound k + 2) → -- ... to the decision round:
    ∃ L, IsLeaderBlock U k L ∧           -- a candidate exists,
      SlowCommit U L (S.slotRound k) ∧   -- the slow threshold is met,
      Decided U V k (some L)             -- and its verdict is committed

/-- Direct-commit liveness over every fault configuration, schedule,
tie-break order, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica] (U : BlockUniverse Replica BlockId),
    CommitLiveness U

/-- **Performance, not liveness — deliberately outside `Statement`.**
When the actual faults fit `p`, a synchronised, populated wave with a
correct leader fires the fast path in two rounds — needing all of
`Correct`, not just a quorum-sized `T`. -/
def FastLatency (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (R k : ℕ),                           -- for any round R and slot k:
    (F.byzantine ∪ F.crashed).card ≤ p Replica →  -- ACTUAL faults fit p,
    Synchronised U R →                   -- all correct synchronised from R,
    R ≤ S.slotRound k →                  -- the wave lies at or after R,
    Populated U (S.slotRound k) →        -- correct fill the propose round ...
    Populated U (S.slotRound k + 1) →    -- ... and the voting round,
    S.leader k ∈ (Correct : Finset Replica) →  -- and the leader is correct:
    ∃ L, IsLeaderBlock U k L ∧           -- then a candidate exists ...
      FastCommit U L (S.slotRound k)     -- ... and it fast-commits (2 rounds)

/-- **Performance, not liveness — the skip half of the opportunistic
pair.** With at most `p` actual faults, a candidate-less slot is
skipped directly at the voting round; beyond `p` it is opportunistic
rather than guaranteed, and resolves indirectly instead. -/
def SkipLatency (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (k : ℕ),                             -- for any slot k:
    (F.byzantine ∪ F.crashed).card ≤ p Replica →  -- ACTUAL faults fit p,
    Populated U (S.slotRound k + 1) →    -- correct fill the voting round,
    (∀ L, ¬ IsLeaderBlock U k L) →       -- and no candidate exists:
    SkippedLeader U k                    -- then the slot skips directly

end DirectLiveness

end Hydrozoan

end LeanDag
