import LeanDag.OptimalHydrozoan.Model.IndirectRules
import LeanDag.Common.Anchored
/-!
# Optimal-Hydrozoan: the decision relation

Trusted core: the per-slot decision procedure of
`sections/optimal-algorithms.tex` — Hydrozoan's `TryDirectDecide` and
`TryIndirectDecide` with the Optimal `SkippedLeader` and
`DecideFromAnchor` — as the shared anchored relation at Optimal's data.
`DecidedOpt U V k (some L)` says the replica holding view `V` may commit
`L` at slot `k`; `DecidedOpt U V k none` says it may skip the slot;
*undecided* is the absence of any derivation.

As for Hydrozoan's `Decided` (`Hydrozoan/Model/Decided.lean`): the
relation is **order-free between constructors** — any justifiable
verdict is derivable, and the safety theorems prove the routes never
disagree — while inside the indirect rule the strict grading
`certificate → evidence quorum → skip` **is** encoded by the rungs, and
the anchor is the **nearest eligible committed** slot.

Two differences with `Decided`. The rule's laws hold only under leader
exclusion (`LeaderExcluded`), so the universe the relation is read at is
an `OptUniverse` and the safety statements quantify over those; the rule
predicates themselves are applied to `U.toBlockRecord`. And the
evidence rung carries **no tie-break** (decision D3): two candidates
cannot both clear it — two evidence quorums share a non-Byzantine
creator whose unique decision-round block would be evidence for both —
so `argmin digest` of the pseudocode is vacuous; uniqueness is a theorem
of the safety phase, not a premise here. No `LinearOrder BlockId` is
needed, and the rule's tie is empty at both rungs.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

section Rule

variable (Replica BlockId : Type*) [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]

/-- **Optimal-Hydrozoan as an anchored rule**: wave two; the direct
commit is the Optimal fast path or Hydrozoan's slow path in view; the
direct skip is Optimal's; two rungs, the anchor-linked certificate and
then the anchor-linked evidence quorum, neither tie-broken. -/
def optimalAnchored :
    AnchoredRule Replica BlockId Unit LeanDag.Hydrozoan.ValidWrt
      (LeanDag.Hydrozoan.NonByzantine : Finset Replica) where
  wave := 2
  Commit := fun U V L r => FastCommitOptInView U V L r ∨ SlowCommitInView U V L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => SkippedLeaderOptInView (S := S) U V k
  rungs := 2
  Link := fun i U A L S k =>
    match i with
    | 0 => LeanDag.Hydrozoan.CertifiedIn U A L (S.slotRound k)
    | _ => EvidenceLinked (S := S) U A L k
  tie := fun _ _ _ => False

end Rule

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- The verdicts a replica holding view `V` may reach on slot `k`. -/
abbrev DecidedOpt (U : OptUniverse Replica BlockId) (V : LeanDag.Hydrozoan.View U.toBlockRecord) :
    ℕ → Option BlockId → Prop :=
  (optimalAnchored Replica BlockId).Decided (S := S) U.toBlockRecord V

namespace DecidedOpt
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end DecidedOpt

end OptimalHydrozoan

end LeanDag
