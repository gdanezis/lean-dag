import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Hydrozoan.Statement
/-!
# Barnacle over Hydrozoan — the live rule, statement

The liveness half of the fifth instantiation: Hydrozoan as a
`LiveRule`, its descent laws at slack `f + c`, and the paper's A4 for
it under round-robin (`docs/hydrozoan-integration.md` §3); the base
rule and its laws are `Barnacle/Hydrozoan/`.

**A good DAG is `Timed.Good` at Hydrozoan's fault model**: a quorum of
fully-correct replicas, synchronised from `Rnd` and populating every
round to `N` — the three hypotheses HZ5 consumes, bundled. Nothing here
renders synchrony afresh (`docs/hydrozoan.md` §7).

**The slack is `f + c`**, the fully-correct class being what liveness
counts, and `q = n − f − c` supplies it.

**Round-robin liveness is where the committee condition appears.**
`liveOn_roundRobin` needs `waveLength * slack + 1 ≤ n`, here
`3·(f + c) + 1 ≤ n`. Hydrozoan's own committee bound
`3f + 2c + k + 1 ≤ n` gives it when `c ≤ k`, but that is sufficient
rather than necessary, so the bound is the hypothesis and the slack
condition is not. It is a hypothesis of `RoundRobinLive` and of nothing
above it: the laws (P1) and the descent laws below are unconditional.
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

/-- **Hydrozoan has the descent laws at slack `f + c`.** A good DAG's
reliable set misses at most the Byzantine and crashed replicas;
`goodLeaders` is HZ5 and `indirect` is HZ6. No committee condition. -/
def Descent : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica],
    (hydrozoanLive (Replica := Replica) (BlockId := BlockId)).Descent (F.f + F.c)

/-- **Hydrozoan under round-robin is live at every leader count**, with
gap `n + 2`, on a committee of at least `3·(f + c) + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId : Type) [LinearOrder BlockId]
    [F : LeanDag.Hydrozoan.Faults (Fin n)], 3 * (F.f + F.c) + 1 ≤ n →
    ∀ (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (hydrozoanLive (Replica := Fin n) (BlockId := BlockId)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 2)

/-- The descent laws, and liveness under round-robin. -/
def Statement : Prop := Descent ∧ RoundRobinLive

end HydrozoanLive

end Barnacle

end LeanDag
