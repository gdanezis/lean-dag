import LeanDag.Hybrid.Faults
import LeanDag.Hydrozoan.Model.Faults

/-!
# B1 — the fault bridge

`docs/hydrozoan-integration.md` §2 and §10.1. Hydrozoan's `(f, c, k)`
model projects onto the hybrid model at `fb := f`, `fc := c`, and
through the hybrid arc's own `HybridFaults.toFaults` onto the core's.
One instance therefore reaches both.

**The committee condition is what the projection consumes**, and it is
stated as the bound itself rather than as a restriction on the slack.
`HybridFaults` requires `3·(fb + fc) + 1 ≤ n`; that is `HybridCommittee`
below, carried as a `Fact` because an instance takes no explicit
hypothesis.

The reason it is needed is not slack in either class. Two sets of
`q = n − f − c` authors overlap in at least `n − 2f − 2c`. Hydrozoan's
uniqueness arguments need one member of that overlap outside
`byzantine`, of which there are at most `f`, so they need
`n ≥ 3f + 2c + 1` — which its own committee bound supplies, a crashed
replica not equivocating. The core's T0 concludes a fully **correct**
member, excluding `byzantine ∪ crashed`, and so needs
`n ≥ 3f + 3c + 1`. The gap between those two is exactly what the
projection pays.

`c ≤ k` is a **sufficient** condition and not the right hypothesis:
Hydrozoan's bound `3f + 2c + k + 1 ≤ n` implies the committee bound
when the slack covers the crash bound, but a committee can be large
enough outright with no slack at all — at `n = 20`, `f = 1`, `c = 2`,
`k = 0` both bounds hold and `c ≤ k` fails. So the slack condition is
recorded as `hybridCommittee_of_slack`, a way of discharging the
`Fact` from the parameters alone, and the `Fact` itself asks only for
what is used. The condition is a real restriction either way: at
`n = 8`, `f = 1`, `c = 2`, `k = 0` Hydrozoan's bound holds and the
committee bound fails.

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

/-- **The committee the core's intersection argument needs**: its T0
concludes a fully correct replica from two overlapping quorums, which
takes `n ≥ 3(f + c) + 1` where Hydrozoan's own arguments take only
`n ≥ 3f + 2c + 1`. -/
abbrev HybridCommittee (Replica : Type*) [Fintype Replica] [DecidableEq Replica]
    [LeanDag.Hydrozoan.Faults Replica] : Prop :=
  3 * (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) + 1
    ≤ Fintype.card Replica

/-- **Slack covering the crash bound is enough**, by Hydrozoan's own
committee bound — the convenient way to discharge the `Fact` from the
parameters, though not the weakest way. -/
theorem hybridCommittee_of_slack [F : LeanDag.Hydrozoan.Faults Replica]
    (h : LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica) :
    HybridCommittee Replica := by
  have := F.card_replicas
  omega

/-- **Hydrozoan's fault model is the hybrid one**, at `fb := f` and
`fc := c`, on a committee the core's intersection argument can use. The
`Fact` is discharged per configuration and `card_validators` is the only
field that consumes it — literally, it *is* that field. -/
instance toHybrid [F : LeanDag.Hydrozoan.Faults Replica]
    [hcm : Fact (HybridCommittee Replica)] :
    HybridFaults Replica where
  fb := LeanDag.Hydrozoan.Faults.f Replica
  fc := LeanDag.Hydrozoan.Faults.c Replica
  byzantine := LeanDag.Hydrozoan.Faults.byzantine
  crash := LeanDag.Hydrozoan.Faults.crashed
  disjoint := F.byzantine_disjoint_crashed
  card_byzantine := F.card_byzantine
  card_crash := F.card_crashed
  card_validators := hcm.out

section Agreements

variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (HybridCommittee Replica)]

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
