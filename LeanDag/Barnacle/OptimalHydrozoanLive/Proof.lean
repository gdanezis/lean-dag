import LeanDag.Barnacle.OptimalHydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.OptimalHydrozoan.DirectLiveness.Proof
import LeanDag.OptimalHydrozoan.IndirectLiveness.Proof

/-!
# Barnacle over Optimal-Hydrozoan — the live rule, proof

Unaudited, and the mirror of `Barnacle/HydrozoanLive/Proof.lean`:
`goodLeaders` is OH5, `indirect` is OH6, and round-robin liveness is
`liveOn_roundRobin` at slack `f + c` and wave length three.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoanLive

set_option maxHeartbeats 1000000 in
-- as for the base rule's laws: the carrier is a subtype and
-- `optUniverseOf` is unfolded at each descent obligation
theorem descent : Descent := by
  intro Replica BlockId _ _ _ _
  constructor
  · intro U Rnd N hGood
    obtain ⟨T, hTC, hTq, hsync, hpop⟩ := hGood
    refine ⟨T, ?_, ?_⟩
    · have hcard := LeanDag.Hydrozoan.Faults.card_replicas (Replica := Replica)
      simp only [LeanDag.Hydrozoan.q] at hTq
      omega
    · intro S V κ hcov hRnd hwave hlead
      letI := slotsOf S
      have hw3 : (optimalHydrozoanLive (Replica := Replica)
          (BlockId := BlockId)).waveLength = 3 := rfl
      rw [hw3] at hwave
      have h0 := hpop (S.slotRound κ) hRnd (by omega)
      have h1 := hpop (S.slotRound κ + 1) (by omega) (by omega)
      have h2 := hpop (S.slotRound κ + 2) (by omega) (by omega)
      obtain ⟨L, _, _, hd⟩ :=
        (LeanDag.OptimalHydrozoan.DirectLiveness.holds Replica BlockId
          (OptimalHydrozoan.optUniverseOf U.val U.property)).1
          T Rnd κ hTC hTq hsync hRnd h0 h1 h2 hlead V
          (fun b hb hr => hcov b hb (le_trans hr (show S.slotRound κ + 2 ≤ N by omega)))
      exact ⟨L, hd⟩
  · intro S U V i j A hij hdj hmid
    letI := slotsOf S
    exact (LeanDag.OptimalHydrozoan.IndirectLiveness.holds Replica BlockId
      (OptimalHydrozoan.optUniverseOf U.val U.property)).1 V i j A hij hdj hmid

theorem roundRobinLive : RoundRobinLive := by
  intro n hn BlockId _ _ hb w hk m hm hmax
  have hbound : (optimalHydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength
      * (LeanDag.Hydrozoan.Faults.f (Fin n) + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n := by
    change 3 * (LeanDag.Hydrozoan.Faults.f (Fin n)
      + LeanDag.Hydrozoan.Faults.c (Fin n)) + 1 ≤ n
    exact hb
  have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId) (Nat.succ_pos 2) hbound hk m hm hmax
  have hw3 : (optimalHydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength = 3 := rfl
  rw [hw3] at h
  simpa using h

theorem holds : Statement := ⟨descent, roundRobinLive⟩

end OptimalHydrozoanLive

end Barnacle

end LeanDag
