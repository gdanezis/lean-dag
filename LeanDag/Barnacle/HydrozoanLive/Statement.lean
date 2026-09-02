import LeanDag.Barnacle.Hydrozoan.Statement
import LeanDag.Barnacle.Model.Heads

/-!
# Barnacle over Hydrozoan — the live rule, statement

The liveness half of the fifth instantiation: Hydrozoan as a
`LiveRule`, its descent laws at slack `f + c`, and the paper's A4 for
it under round-robin. P2 of `docs/hydrozoan-integration.md` §13; the
base rule and its laws are P1 (`Barnacle/Hydrozoan/`).

**A good DAG is Hydrozoan's own liveness package.** `Good U Rnd N` is
a quorum-sized set of correct replicas, synchronised from `Rnd` and
populating every round to `N` — the three hypotheses HZ5 consumes,
bundled. Nothing here renders synchrony afresh: the package is
`Model/Liveness.lean`'s, and what it is worth is that arc's business
(`docs/hydrozoan.md` §7).

**The slack is `f + c`**, the fully-correct class being what liveness
counts. The interface asks for a set missing at most `slack` of the
replicas, and `q = n − f − c` supplies it.

**The descent laws are HZ5 and HZ6, unadapted.** `goodLeaders` is
`CommitLiveness`, which already concludes on a view caught up to the
decision round; `indirect` is `AnchoredTotality`, and at wave length
three the interface's `slotRound i + 3 ≤ slotRound j` *is*
`EligibleAsAnchor i j`, since the latter unfolds to
`decisionRound i < slotRound j`.

**Round-robin liveness is where the committee condition appears.**
`liveOn_roundRobin` needs `waveLength * slack + 1 ≤ n`, here
`3·(f + c) + 1 ≤ n` — the same inequality
`docs/hydrozoan-integration.md` §2 derives from the fault projection,
reached here by a route that mentions neither the core's quorum nor its
intersection argument. Hydrozoan's own committee bound
`3f + 2c + k + 1 ≤ n` gives it when `c ≤ k`, but that is sufficient
rather than necessary, so the bound is the hypothesis and the slack
condition is not. It is a hypothesis of `RoundRobinLive` and of nothing
above it: the laws (P1) and the descent laws below are
unconditional.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [LinearOrder BlockId]

/-- **Hydrozoan as a live rule**: a DAG is good from `Rnd` to `N` when
a quorum-sized set of correct replicas is synchronised from `Rnd` and
populates every round up to `N`. -/
def hydrozoanLive [LeanDag.Hydrozoan.Faults Replica] :
    LiveRule Replica BlockId Unit :=
  { hydrozoan with
    Good := fun U Rnd N =>
      ∃ T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica),
        LeanDag.Hydrozoan.q Replica ≤ T.card ∧
        LeanDag.Hydrozoan.SynchronisedOn U T Rnd ∧
        ∀ r, Rnd ≤ r → r ≤ N → LeanDag.Hydrozoan.PopulatedOn U T r }

namespace HydrozoanLive

/-- **Hydrozoan has the descent laws at slack `f + c`.** A good DAG's
reliable set misses at most the Byzantine and crashed replicas;
`goodLeaders` is HZ5 and `indirect` is HZ6. No committee condition. -/
def Descent : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica],
    (hydrozoanLive (Replica := Replica) (BlockId := BlockId)).Descent (F.f + F.c)

/-- **Hydrozoan under round-robin is live at every leader count**, with
gap `n + 2`, on a committee of at least `3·(f + c) + 1`. That bound is
what `liveOn_roundRobin` consumes at wave length three and slack
`f + c`, and it is the hypothesis rather than the sufficient condition
`c ≤ k`, which Hydrozoan's own committee bound would supply but which
excludes committees large enough outright. -/
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
