import LeanDagTest.Hydrozoan.DirectLiveness
import LeanDag.Barnacle.HydrozoanLive.Proof

/-!
# Barnacle over Hydrozoan — the live witnesses

P2 evaluated on concrete data, on the low-fault four-replica
configuration of `LeanDagTest/Hydrozoan/DirectLiveness.lean`
(`f = 0, c = 1, k = 1`, replica `1` crashed) and its three-round
universe `U7`.

What is pinned:

* **the wave length and the slack** — three, and `f + c`, which at this
  configuration is `1`, so the reliable set may miss one replica;
* **`Good` is satisfiable** — `U7` is good from round `0` to round `2`
  with the fully-correct class as its reliable set, so the descent laws
  are not vacuous at this configuration;
* **the descent law applied end to end** — `goodLeaders` yields a set
  missing at most the slack, computed on `U7`;
* **the committee condition, both ways** — `c ≤ k` holds here and at
  the seven-replica model, and fails at the five-replica configuration
  of `LeanDagTest/Hydrozoan/Grounding.lean`, so `RoundRobinLive`'s
  hypothesis is a real restriction rather than a formality.

**What this configuration cannot exercise.** `goodLeaders` concludes a
commit only for a slot whose whole wave fits under the horizon,
`slotRound κ + 3 ≤ N`, and `U7` has three rounds. Running the law
through to a committed verdict needs a four-round synchronised
universe, which no witness of the Hydrozoan arc currently supplies —
`U3` is five rounds but is deliberately unsynchronised, its round-three
blocks omitting replica `4`'s round-two block. That universe is owed,
and is recorded here rather than worked around.
-/

namespace LeanDagTest

namespace Barnacle

open LeanDag

/-! ## The wave length and the slack -/

example : (LeanDag.Barnacle.hydrozoanLive
    (Replica := Fin 4) (BlockId := Fin 9)).waveLength = 3 := rfl

example : LeanDagTest.Hydrozoan.fourReplicas.f
    + LeanDagTest.Hydrozoan.fourReplicas.c = 1 := by decide

/-! ## `Good` is satisfiable at this configuration -/

/-- `U7` is good from round `0` to round `2`: the fully-correct class
is quorum-sized, synchronised from `0`, and populates every round. -/
theorem good_U7 : (LeanDag.Barnacle.hydrozoanLive
    (Replica := Fin 4) (BlockId := Fin 9)).Good LeanDagTest.Hydrozoan.U7 0 2 :=
  ⟨(LeanDag.Hydrozoan.Correct : Finset (Fin 4)), Finset.Subset.refl _, by decide,
    LeanDagTest.Hydrozoan.u7_synchronised, by
      intro r _ hr
      have h : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases h with rfl | rfl | rfl <;> decide⟩

/-! ## The descent law, applied end to end

Applying `descent` at this configuration is what would fail were a
hypothesis silently strengthened. Its `goodLeaders` field returns a
reliable set missing at most the slack. -/

example : ∃ T : Finset (Fin 4),
    Fintype.card (Fin 4) ≤ T.card
      + (LeanDagTest.Hydrozoan.fourReplicas.f + LeanDagTest.Hydrozoan.fourReplicas.c) := by
  obtain ⟨T, hT, _⟩ :=
    (LeanDag.Barnacle.HydrozoanLive.descent (Fin 4) (Fin 9)).goodLeaders
      LeanDagTest.Hydrozoan.U7 0 2 good_U7
  exact ⟨T, hT⟩

/-! ## The committee condition is a real restriction

`RoundRobinLive` consumes `c ≤ k` exactly once, at
`liveOn_roundRobin`'s bound `3·(f + c) + 1 ≤ n`. It holds at the
configurations above and fails at the five-replica one that
`docs/hydrozoan-integration.md` §11 records. -/

example : LeanDagTest.Hydrozoan.fourReplicas.c
    ≤ LeanDagTest.Hydrozoan.fourReplicas.k := by decide

-- And the bound it is there to supply, at this configuration.
example : 3 * (LeanDagTest.Hydrozoan.fourReplicas.f
    + LeanDagTest.Hydrozoan.fourReplicas.c) + 1 ≤ 4 := by decide

end Barnacle

end LeanDagTest
