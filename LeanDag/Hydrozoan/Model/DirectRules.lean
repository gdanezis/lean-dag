import LeanDag.Hydrozoan.Model.View
import LeanDag.Common.Leader
import LeanDag.Common.Rules
/-!
# Direct decision rules

Votes, certificates, and the three direct rules — `FastCommittedLeader`,
`SlowCommittedLeader`, `SkippedLeader` — as predicates over the block
universe and their view-relative variants, each a cardinality comparison
counting creators, never raw blocks, against the thresholds of
`Model/Faults.lean`. The counting vocabulary is the record's
(`Common/Support.lean`, `Common/Leader.lean`); what is Hydrozoan's is the
certificate and the thresholds.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- The round at which slot `k`'s slow path is settled (the paper's
`DecisionRound`): its certificates live here. Its voting round is the
shared `votingRound`, one above the proposal. -/
abbrev decisionRound (Replica : Type*) [S : Slots Replica] (k : ℕ) : ℕ := S.slotRound k + 2

/-! A vote is the record's `IsVote`, direct reference rather than the
paper's depth-first traversal; the two coincide at wave length 3, argued
in prose and not in Lean. `distinct_creators` gives at most one vote per
creator per slot. -/

/-- The refs of `C` that vote for `L` — the inner set of the paper's
`IsCertificate`: the record's carried votes. -/
abbrev voteBlocks (U : BlockUniverse Replica BlockId) (C L : BlockId) : Finset BlockId :=
  carriedVotes U (IsVote U) C L

/-- `C` certifies `L` (the paper's `IsCertificate`): `C`'s votes for `L`
come from `q_cert` distinct creators — the record's certificate at `q_cert`. -/
abbrev IsCertificate (U : BlockUniverse Replica BlockId) (C L : BlockId) : Prop :=
  CarriesVotes U (IsVote U) (qCert Replica) C L

/-- `L` is fast-committed (the paper's `FastCommittedLeader`): `q_fast`
votes at the voting round, `r` its propose round. Two message delays. -/
def FastCommit (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qFast Replica ≤ (supporters U L (r + 1)).card

/-- The decision-round blocks certifying `L`, `r` its propose round. -/
abbrev certificates (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  certificatesAt U (IsVote U) (qCert Replica) L (r + 2)

/-- The replicas whose decision-round block certifies `L` — the
slow-path counterpart of `supporters`. -/
def certifiers (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Finset Replica :=
  creatorsOf U.block (certificates U L r)

/-- `L` is slow-committed (the paper's `SlowCommittedLeader`): `q_slow`
certificates at the decision round. Three message delays. -/
def SlowCommit (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qSlow Replica ≤ (certifiers U L r).card

section Skip

variable [S : Slots Replica]

/-- Slot `k` is skipped (the paper's `SkippedLeader`): `q_fast` slotBlames
at the voting round. Opportunistic — safe whenever it fires, but not
guaranteed to fire. -/
def SkippedLeader (U : BlockUniverse Replica BlockId) (k : ℕ) : Prop :=
  qFast Replica ≤ (slotBlames U k).card

end Skip

section ViewRules

/-- Fast commit, as judged from a single view: the view holds votes for
`L` at the voting round from `q_fast` replicas. -/
abbrev FastCommitInView (U : BlockUniverse Replica BlockId) (V : View U)
    (L : BlockId) (r : ℕ) : Prop :=
  supportCommit (qFast Replica) U V L r

/-- Slow commit, as judged from a single view: the view holds
certificates for `L` from `q_slow` replicas. -/
abbrev SlowCommitInView (U : BlockUniverse Replica BlockId) (V : View U)
    (L : BlockId) (r : ℕ) : Prop :=
  certCommit IsVote (qSlow Replica) (qCert Replica) 2 U V L r

variable [S : Slots Replica]

/-- Skip, as judged from a single view. -/
abbrev SkippedLeaderInView (U : BlockUniverse Replica BlockId) (V : View U)
    (k : ℕ) : Prop :=
  blameSkip (qFast Replica) U V k

end ViewRules

end Hydrozoan

end LeanDag
