import LeanDag.Barnacle.OptimalHydrozoan.Statement
import LeanDag.Barnacle.Model.Heads

/-!
# Barnacle over Optimal-Hydrozoan — the live rule, statement

The mirror of `Barnacle/HydrozoanLive/`. `Good` is Optimal's liveness
package, which is Hydrozoan's unchanged: the arc reuses the whole
synchrony rendering (`optimal-hydrozoan.md` §5), so nothing is
re-stated here either.

The descent laws are OH5 and OH6, at slack `f + c` and wave length
three, exactly as Hydrozoan's are HZ5 and HZ6. Round-robin liveness
takes the committee bound `3·(f + c) + 1 ≤ n` directly, for the reason
`Barnacle/HydrozoanLive/Statement.lean` records: it is what
`liveOn_roundRobin` consumes, and stating it as a condition on the
slack would refuse committees large enough outright.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]

/-- **Optimal-Hydrozoan as a live rule**: a DAG is good from `Rnd` to
`N` when a quorum-sized set of correct replicas is synchronised from
`Rnd` and populates every round up to `N`. -/
def optimalHydrozoanLive [LeanDag.OptimalHydrozoan.OptimalFaults Replica] :
    LiveRule Replica BlockId Unit :=
  { optimalHydrozoan with
    Good := fun U Rnd N =>
      ∃ T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica),
        LeanDag.Hydrozoan.q Replica ≤ T.card ∧
        LeanDag.Hydrozoan.SynchronisedOn U.val T Rnd ∧
        ∀ r, Rnd ≤ r → r ≤ N → LeanDag.Hydrozoan.PopulatedOn U.val T r }

namespace OptimalHydrozoanLive

/-- **Optimal-Hydrozoan has the descent laws at slack `f + c`**:
`goodLeaders` is OH5 and `indirect` is OH6. -/
def Descent : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica],
    (optimalHydrozoanLive (Replica := Replica) (BlockId := BlockId)).Descent
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica)

/-- **Optimal-Hydrozoan under round-robin is live at every leader
count**, with gap `n + 2`, on a committee of at least `3·(f + c) + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId : Type) [DecidableEq BlockId]
    [LeanDag.OptimalHydrozoan.OptimalFaults (Fin n)],
    3 * (LeanDag.Hydrozoan.Faults.f (Fin n)
      + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n →
    ∀ (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (optimalHydrozoanLive (Replica := Fin n) (BlockId := BlockId)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 2)

/-- The descent laws, and liveness under round-robin. -/
def Statement : Prop := Descent ∧ RoundRobinLive

end OptimalHydrozoanLive

end Barnacle

end LeanDag
