import LeanDag.OptimalHydrozoan.Model.Faults
import LeanDag.OptimalHydrozoan.Model.Universe
import LeanDag.Common.Rules
/-!
# Optimal-Hydrozoan: direct decision rules

Trusted core: the fast commit at the new allowance, per-block *fast
evidence*, and the direct skip (`IsFastEvidence`, `IsNoFastEvidence`,
`SkippedLeader`), as predicates over the block universe and their
view-relative variants. Everything else of the direct layer is
Hydrozoan's, unchanged. Quorums of decision-round blocks are stated
existentially over a witness set, as `WeakLinked` is, since the
property is not decidable on a `Finset.filter`.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]

/-- `L` is fast-committed (the paper's `FastCommittedLeader`, read with the
Optimal allowance): `qFastOpt` votes at the voting round, `r` its propose
round. Two message delays; one vote fewer than Hydrozoan at the same
committee size. -/
def FastCommitOpt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qFastOpt Replica ≤ (supporters U L (r + 1)).card

/-- Fast commit, as judged from a single view. -/
abbrev FastCommitOptInView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V : LeanDag.Hydrozoan.View U) (L : BlockId) (r : ℕ) : Prop :=
  supportCommit (qFastOpt Replica) U V L r

/-- The replicas among `C`'s refs whose block votes for `L` — the set
whose cardinality is the paper's `Votes(b, b_leader)` (Algorithm 3). Also
the inner set of Hydrozoan's `LeanDag.Hydrozoan.IsCertificate`, which is definitionally
`qCert ≤ (votersOf U C L).card`. -/
def votersOf (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (C L : BlockId) :
    Finset Replica :=
  creatorsOf U.block (LeanDag.Hydrozoan.voteBlocks U C L)

section Slots

variable [S : Slots Replica]

/-- `C` is *fast evidence* for `L` in slot `k`: if `C` witnesses no
equivocation in `k`, `tPlain` votes for `L` suffice; if it does, `tEquiv`
votes for `L` and fewer than `tEquiv` for every rival candidate, so a
witnessing block is evidence for at most one candidate. Stated as two
implications, needing no decidability. -/
def IsFastEvidence (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ) (C L : BlockId) :
    Prop :=
  (¬ WitnessesEquivocation U k C →                 -- no equivocation witnessed:
    tPlain Replica ≤ (votersOf U C L).card) ∧      --   t_plain votes for L suffice
  (WitnessesEquivocation U k C →                   -- equivocation witnessed:
    tEquiv Replica ≤ (votersOf U C L).card ∧       --   t_equiv votes for L, and
    ∀ L', IsLeaderBlock U k L' → L' ≠ L →          --   every rival candidate
      (votersOf U C L').card < tEquiv Replica)     --   stays below t_equiv

/-- `C` is fast evidence for no candidate of slot `k` (the paper's
`IsNoFastEvidence(b, w)`). Vacuously true when the slot has no candidate
at all — which is what lets a candidate-less slot be skipped. -/
def IsNoFastEvidence (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ) (C : BlockId) :
    Prop :=
  ∀ L, IsLeaderBlock U k L →                       -- for every candidate of the slot
    ¬ IsFastEvidence U k C L                       -- C is not evidence for it

/-- `qCert` distinct creators of decision-round blocks of slot `k` that are
fast evidence for no candidate — the second half of the paper's
`SkippedLeader`, `noEvidence`. Existential over a witness set of blocks
(see the module docstring). -/
def NoEvidenceQuorum (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ) : Prop :=
  ∃ s : Finset BlockId,                            -- some set of blocks such that
    (∀ b ∈ s,                                      -- every block in it
      b ∈ blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k) ∧   -- sits at slot k's decision round
      IsNoFastEvidence U k b) ∧                    -- and is evidence for no candidate;
    qCert Replica ≤ (creatorsOf U.block s).card     -- and they come from q_cert creators

/-- Slot `k` is skipped (the paper's `SkippedLeader(w)`, Optimal version):
`qCert` slotBlames at the voting round **and** a no-evidence quorum at the
decision round. Hydrozoan's `slotBlames` is reused (a blame is a voting-round
block referencing no candidate); only the threshold changes, from
`qFast` to `qCert`, and the rule is settled one round later. -/
def SkippedLeaderOpt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ) : Prop :=
  qCert Replica ≤ (slotBlames U k).card ∧              -- q_cert slotBlames at the voting round
    NoEvidenceQuorum U k                           -- and q_cert no-evidence decision blocks

/-- The no-evidence quorum a view actually holds. -/
def NoEvidenceQuorumInView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (V : LeanDag.Hydrozoan.View U)
    (k : ℕ) : Prop :=
  ∃ s : Finset BlockId,                            -- some set of blocks such that
    (∀ b ∈ s,                                      -- every block in it
      b ∈ blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k) ∧   -- sits at slot k's decision round,
      b ∈ V.ids ∧                                  -- is held by the view,
      IsNoFastEvidence U k b) ∧                    -- and is evidence for no candidate;
    qCert Replica ≤ (creatorsOf U.block s).card     -- and they come from q_cert creators

/-- Skip, as judged from a single view. -/
def SkippedLeaderOptInView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (V : LeanDag.Hydrozoan.View U)
    (k : ℕ) : Prop :=
  HoldsAtLeast U V (qCert Replica) (slotBlamers U k) ∧  -- q_cert blamers in view
    NoEvidenceQuorumInView U V k                   -- and a no-evidence quorum in view

end Slots

end OptimalHydrozoan

end LeanDag
