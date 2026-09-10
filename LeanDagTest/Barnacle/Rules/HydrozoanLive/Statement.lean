import LeanDag.Barnacle.Model.Heads
import LeanDagTest.Barnacle.Rules.Hydrozoan.Statement
/-!
# Barnacle over Hydrozoan — the live rule, statement

Hydrozoan as a live rule at its fault model, its descent laws at slack
`f + c`, and A4 for it under round-robin with gap `n + 2`
(`docs/hydrozoan-integration.md` §3). Round-robin liveness takes the
committee bound `3·(f + c) + 1 ≤ n` as its hypothesis: Hydrozoan's own
bound gives it when `c ≤ k`, which is sufficient but not necessary.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [LinearOrder BlockId]

/-- **Hydrozoan as a live rule**, at its fault model. -/
def hydrozoanLive [LeanDag.Hydrozoan.Faults Replica] : LiveRule Replica BlockId Unit :=
  liveOfAnchored (LeanDag.Hydrozoan.hydrozoanAnchored Replica BlockId)
    (LeanDag.Hydrozoan.hzReliability Replica)

namespace HydrozoanLive

/-- **Hydrozoan has the descent laws at slack `f + c`**, with no committee
condition. -/
def Descent : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica],
    (hydrozoanLive (Replica := Replica) (BlockId := BlockId)).Descent (F.f + F.c)

/-- **Hydrozoan under round-robin is live at every leader count**, with
gap `n + 2`, on a committee of at least `3·(f + c) + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId : Type) [LinearOrder BlockId]
    [F : LeanDag.Hydrozoan.Faults (Fin n)], 3 * (F.f + F.c) + 1 ≤ n →
    ∀ (C : Config (Fin n)) (hC : C.head = roundRobin n hn),
    (hydrozoanLive (Replica := Fin n) (BlockId := BlockId)).LiveOn
      C.sched (n + 2)

/-- The descent laws, and liveness under round-robin. -/
def Statement : Prop := Descent ∧ RoundRobinLive

end HydrozoanLive

end Barnacle

end LeanDag
