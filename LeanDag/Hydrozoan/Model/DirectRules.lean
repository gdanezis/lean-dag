import LeanDag.Hydrozoan.Model.View
import LeanDag.Common.Leader
/-!
# Direct decision rules

Trusted core: votes, certificates, and the three direct rules of
`sections/algorithms.tex` — `FastCommittedLeader`, `SlowCommittedLeader`,
`SkippedLeader` — as predicates over the block universe, plus their
view-relative variants (the rules a replica actually runs on its local
DAG, differing from the universe versions by exactly `∩ V.ids`).

Every rule is a cardinality comparison **counting creators**, never raw
blocks — the pseudocode's "count creators, as replicas may equivocate" —
against the audited thresholds of `Model/Faults.lean`. Universe-level
rules are primary (the safety arithmetic happens there); a view can only
under-report them, never exceed them.

The commit rules are round-parameterized: `r` is the slot's propose
round, and callers pass `S.slotRound k` (the paper's wave `w` maps to
`r = ProposeRound(w)`). Only the skip rule is slot-parameterized,
because slotBlames target the leader slot, not a specific block.

The counting vocabulary — `blocksAt`, `supporters`, `supportersIn`,
`slotBlames`, `slotBlamesIn`, `votingRound` — is the record's
(`Common/Support.lean`, `Common/Leader.lean`); what is Hydrozoan's is the
certificate and the thresholds. The predicates used inside
`Finset.filter` (`IsVote`, `IsCertificate`) are `@[reducible]` so their
decidability is inferable; the top-level rules get explicit `Decidable`
instances in `Helpers/`.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- The round at which slot `k`'s slow path is settled (the paper's
`DecisionRound`): its certificates live here. Its voting round is the
shared `votingRound`, one above the proposal. -/
abbrev decisionRound (Replica : Type*) [S : Slots Replica] (k : ℕ) : ℕ := S.slotRound k + 2

/-- `b` votes for `L` (the paper's `IsVote`): `L` is among `b`'s refs.

Recall `ValidWrt.distinct_creators`: a well-formed block never references
two blocks by the same creator, so `b` votes for at most one copy of any
leader — even an equivocating one.

**Fidelity gap**: the paper defines a vote by deterministic depth-first
traversal — `L` is the first block by its creator encountered in `b`'s
causal history. The model uses the direct reference instead. At wave
length 3 the two coincide for the blocks the rules inspect — a leader
copy can only appear among a voter's direct references — and one vote
per creator per slot follows from `distinct_creators` plus universe-level
non-equivocation; the DFS ≡ direct-reference equivalence is argued in
prose, not in Lean. Definitionally this is `RefStep`, kept under the
protocol's name. -/
@[reducible]
def IsVote (U : BlockUniverse Replica BlockId) (b L : BlockId) : Prop :=
  L ∈ (U.block b).refs

/-- The refs of `C` that vote for `L` — the inner set of the paper's
`IsCertificate`. -/
def voteBlocks (U : BlockUniverse Replica BlockId) (C L : BlockId) :
    Finset BlockId :=
  (U.block C).refs.filter fun b => IsVote U b L

/-- `C` certifies `L` (the paper's `IsCertificate`): `C`'s votes for `L`
come from `q_cert` distinct creators. -/
@[reducible]
def IsCertificate (U : BlockUniverse Replica BlockId) (C L : BlockId) : Prop :=
  qCert Replica ≤ (creatorsOf U.block (voteBlocks U C L)).card

/-- `L` is fast-committed (the paper's `FastCommittedLeader`): `q_fast`
votes at the voting round, `r` its propose round. Two message delays. -/
def FastCommit (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qFast Replica ≤ (supporters U L (r + 1)).card

/-- The decision-round blocks certifying `L`, `r` its propose round. -/
def certificates (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 2)).filter fun C => IsCertificate U C L

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
  HoldsAtLeast U V (qFast Replica) (votesFor U L (r + 1))

/-- Slow commit, as judged from a single view: the view holds
certificates for `L` from `q_slow` replicas. -/
abbrev SlowCommitInView (U : BlockUniverse Replica BlockId) (V : View U)
    (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (qSlow Replica) (certificates U L r)

variable [S : Slots Replica]

/-- Skip, as judged from a single view. -/
abbrev SkippedLeaderInView (U : BlockUniverse Replica BlockId) (V : View U)
    (k : ℕ) : Prop :=
  HoldsAtLeast U V (qFast Replica) (slotBlamers U k)

end ViewRules

end Hydrozoan

end LeanDag
