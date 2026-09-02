import LeanDag.Hybrid.Faults
import LeanDag.Hydrozoan.Model.Faults

/-!
# B1 — the fault bridge

`docs/hydrozoan-integration.md` §2 and §10.1. Hydrozoan's `(f, c, k)`
model projects onto the hybrid model at `fb := f`, `fc := c`, and
through the hybrid arc's own `HybridFaults.toFaults` onto the core's.
One instance therefore reaches both.

**The committee condition is what the projection consumes.**
`HybridFaults` requires `3·(fb + fc) + 1 ≤ n` and Hydrozoan supplies
`3f + 2c + k + 1 ≤ n`, so the two agree exactly when `c ≤ k`. It is
carried as a `Fact` because an instance takes no explicit hypothesis,
and it is a real restriction: at `n = 8`, `f = 1`, `c = 2`, `k = 0`
Hydrozoan's bound holds and the hybrid one fails. The reason is not
slack in either class — Hydrozoan's uniqueness arguments intersect two
quorums in a **non-Byzantine** replica, needing `n ≥ 3f + 2c + 1`,
where the core's T0 asks for a fully **correct** one and needs
`n ≥ 3f + 3c + 1`.

**The diamond discipline.** With the projection in scope a single
`Replica` carries three fault classes, and `Hydrozoan.q` and
`quorumCard` are both available. They are equal but not definitionally
so — `n − f − c` against `n − (f + c)` is `Nat.sub_sub` — so the three
agreements below are the simp set every transfer cites, and statements
are written in Hydrozoan's spelling.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type*} [Fintype Replica] [DecidableEq Replica]

/-- **Hydrozoan's fault model is the hybrid one**, at `fb := f` and
`fc := c`, whenever the slack does not undershoot the crash bound. The
`Fact` is discharged per configuration; `card_validators` is the only
field that consumes it. -/
instance toHybrid [F : LeanDag.Hydrozoan.Faults Replica]
    [hck : Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)] :
    HybridFaults Replica where
  fb := LeanDag.Hydrozoan.Faults.f Replica
  fc := LeanDag.Hydrozoan.Faults.c Replica
  byzantine := LeanDag.Hydrozoan.Faults.byzantine
  crash := LeanDag.Hydrozoan.Faults.crashed
  disjoint := F.byzantine_disjoint_crashed
  card_byzantine := F.card_byzantine
  card_crash := F.card_crashed
  card_validators := by
    have h := F.card_replicas
    have hck := hck.out
    omega

section Agreements

variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)]

/-- The two quorums coincide: `n − f − c` is `n − (f + c)`. Not
definitional, which is why it is a simp lemma rather than left
implicit. -/
@[simp] theorem quorumCard_eq_q :
    quorumCard Replica = LeanDag.Hydrozoan.q Replica := by
  simp only [LeanDag.Hydrozoan.q, Nat.sub_sub]
  rfl

/-- The correct pools coincide: the derived instance's Byzantine set is
the union, so its complement is Hydrozoan's `Correct`. -/
@[simp] theorem correct_eq :
    (Correct : Finset Replica) = (LeanDag.Hydrozoan.Correct : Finset Replica) := rfl

/-- The never-equivocating pools coincide: the hybrid arc's honest
class is Hydrozoan's `NonByzantine`. -/
@[simp] theorem nonByzantine_eq :
    ((HybridFaults.byzantine : Finset Replica))ᶜ
      = (LeanDag.Hydrozoan.NonByzantine : Finset Replica) := rfl

end Agreements

end Hydrozoan

end Integration

end LeanDag
