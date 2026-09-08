import LeanDag.OptimalHydrozoan.Model.IndirectRules
import LeanDag.Common.Anchored
/-!
# Optimal-Hydrozoan: the decision relation

Hydrozoan's `Decided` at Optimal's data: order-free between
constructors, with the certificate-then-evidence-quorum grading encoded
by the rungs. The rule's laws hold only under leader exclusion, which
every `OptUniverse` supplies, so the relation reads an Optimal universe
through its projection to Hydrozoan's. The evidence rung carries no
tie-break — two candidates cannot both clear it — so no
`LinearOrder BlockId` is needed.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

section Rule

variable (Replica BlockId : Type*) [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]

/-- **Optimal-Hydrozoan as an anchored rule**: wave two, the direct
commit the Optimal fast path or Hydrozoan's slow path, two rungs
(certificate, then evidence quorum), neither tie-broken. -/
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
