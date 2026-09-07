import LeanDag.Hydrozoan.Model.IndirectRules
import LeanDag.Common.Anchored
/-!
# The decision relation

Trusted core: the per-slot decision procedure of
`sections/algorithms.tex` (`TryDirectDecide` + `TryIndirectDecide` +
`DecideFromAnchor`), as the shared anchored relation at Hydrozoan's
data. `Decided U V k (some L)` says the replica holding view `V` may
commit `L` at slot `k`; `Decided U V k none` says it may skip the slot;
*undecided* is the absence of any derivation.

The relation is **order-free between constructors**: the paper checks
skip before commit and fast before slow operationally, but any
justifiable verdict is derivable here, and the safety theorems prove the
routes never disagree. The direct commit is the disjunction of the two
paths. Within the indirect rule the paper's strict grading
`certificate → weak-quorum → skip` **is** encoded by the relation's
rungs: rung `0` asks for an anchor-linked certificate, rung `1` for
`q_weak` anchor-linked votes and fires only when rung `0` is empty for
every candidate, and the indirect skip only when both are.

The anchor premises follow the paper's `TryIndirectDecide`: the anchor
is the **nearest eligible committed** slot — committed by any route,
with every eligible slot strictly between decided `none` (skipped slots
cannot anchor; a committed one would be the nearer anchor). Eligibility
is wave two: the anchor's propose round lies strictly past the slot's
decision round, `slotRound k + 2`.

The weak rung commits the **least** qualifying candidate
(`[LinearOrder BlockId]`) — the paper's deterministic `argmin digest`
tie-break, since equivocating copies may tie at `q_weak`. Rung `0` needs
no tie-break: certificates are unique per slot (`2·q_cert > n + f`,
proved in the safety phase), which the relation records as an empty
tie.
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
  wave := 2
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
