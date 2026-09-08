import LeanDag.Hydrozoan.Model.DirectRules
import LeanDag.Common.CausalHistory
import LeanDag.Common.History
import LeanDag.Common.Rules
/-!
# The graded indirect rule's ingredients

The two rung tests: rung 1 asks for an anchor-linked certificate, rung 2
for `q_weak` anchor-linked votes. Anchor eligibility is the shared
`EligibleAt` at wave two. `WeakLinked` is stated existentially over a
witness set rather than as a `Finset.filter`, since filtering on
`Reaches` would need deciding reachability; the two forms are equivalent
(`Helpers/IndirectRules.lean`).
-/

namespace LeanDag

namespace Hydrozoan

section RungTests

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- Rung 1's test: a certificate for `L` lies in the anchor's causal
history — the paper's `∃ b : Link(b, b_anchor) ∧ IsCertificate(b, b_leader)`,
with `r` the candidate's propose round. -/
abbrev CertifiedIn (U : BlockUniverse Replica BlockId) (A L : BlockId)
    (r : ℕ) : Prop :=
  certifiedLink IsVote (qCert Replica) 2 U A L r

/-- Rung 2's test: `q_weak` distinct creators of anchor-reachable votes
for `L` at the voting round, stated over a witness set of such blocks
rather than a filter. -/
def WeakLinked (U : BlockUniverse Replica BlockId) (A L : BlockId)
    (r : ℕ) : Prop :=
  ∃ s : Finset BlockId,
    (∀ b ∈ s, b ∈ blocksAt U (r + 1) ∧ IsVote U b L ∧ Reaches U A b) ∧
    qWeak Replica ≤ (creatorsOf U.block s).card

end RungTests

end Hydrozoan

end LeanDag
