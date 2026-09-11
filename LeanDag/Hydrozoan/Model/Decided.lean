import LeanDag.Hydrozoan.Model.IndirectRules
import LeanDag.Common.Anchored
/-!
# The decision relation

The per-slot decision procedure as the shared anchored relation at
Hydrozoan's data: order-free between constructors — any justifiable
verdict is derivable, and safety proves the routes never disagree —
while the graded indirect rule (certificate, then weak quorum, then
skip) is encoded by the rungs. The weak rung tie-breaks by `<
BlockId>`, since equivocating copies may tie at `q_weak`; the
certificate rung needs no tie-break, being unique per slot.
-/

namespace LeanDag

namespace Hydrozoan

section Rule

variable (Replica BlockId : Type*) [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- **Hydrozoan as an anchored rule**: wave two; the direct commit is
the fast path or the slow path in view; the direct skip is `q_fast`
slotBlames in view; two rungs, the anchor-linked certificate and then the
weak quorum, the second tie-broken by the order. -/
def hydrozoanAnchored :
    AnchoredRule Replica BlockId Unit ValidWrt (NonByzantine : Finset Replica) where
  waveAt := fun _ => 2
  Commit := fun U V L r => FastCommitInView U V L r ∨ SlowCommitInView U V L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => SkippedLeaderInView (S := S) U V k
  rungs := 2
  Link := fun i U A L S k =>
    match i with
    | 0 => CertifiedIn U A L (S.slotRound k)
    | _ => WeakLinked U A L (S.slotRound k)
  tie := fun i L' L =>
    match i with
    | 0 => False
    | _ => L' < L

end Rule

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- The verdicts a replica holding view `V` may reach on slot `k`. -/
abbrev Decided (U : BlockUniverse Replica BlockId) (V : View U) : ℕ → Option BlockId → Prop :=
  (hydrozoanAnchored Replica BlockId).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

end Hydrozoan

end LeanDag
