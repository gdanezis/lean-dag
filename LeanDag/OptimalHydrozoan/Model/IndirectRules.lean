import LeanDag.OptimalHydrozoan.Model.DirectRules
import LeanDag.Hydrozoan.Model.IndirectRules
/-!
# Optimal-Hydrozoan: the graded indirect rule's second rung

Rung 1 is Hydrozoan's `CertifiedIn`, reused; rung 2 replaces
`WeakLinked`'s anchor-linked votes by `qCert` anchor-linked
decision-round blocks, each fast evidence for the candidate. Stated
existentially over a witness set, as `WeakLinked` is.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- Rung 2's test: `qCert` distinct creators of decision-round blocks of
slot `k`, each fast evidence for `L` and reachable from the anchor
`A`. -/
def EvidenceLinked (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (A L : BlockId) (k : ℕ) :
    Prop :=
  ∃ s : Finset BlockId,                            -- some set of blocks such that
    (∀ b ∈ s,                                      -- every block in it
      b ∈ blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k) ∧   -- sits at slot k's decision round,
      IsFastEvidence U k b L ∧                     -- is fast evidence for L,
      Reaches U A b) ∧                             -- and lies in the anchor's history;
    qCert Replica ≤ (creatorsOf U.block s).card     -- and they come from q_cert creators

end OptimalHydrozoan

end LeanDag
