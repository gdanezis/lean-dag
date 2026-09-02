import LeanDag.Barnacle.HydrozoanLive.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.IndirectLiveness.Proof

/-!
# Barnacle over Hydrozoan — the live rule, proof

Unaudited. `goodLeaders` is HZ5 and `indirect` is HZ6, each applied
without adaptation; round-robin liveness is `liveOn_roundRobin` at
slack `f + c` and wave length three, whose bound `3·(f + c) + 1 ≤ n`
is the committee bound read under `c ≤ k`.
-/

namespace LeanDag

namespace Barnacle

namespace HydrozoanLive

theorem descent : Descent := by
  intro Replica BlockId _ _ _ F
  constructor
  · intro U Rnd N hGood
    obtain ⟨T, hTC, hTq, hsync, hpop⟩ := hGood
    refine ⟨T, ?_, ?_⟩
    · have hcard := F.card_replicas
      simp only [LeanDag.Hydrozoan.q] at hTq
      omega
    · intro S V κ hcov hRnd hwave hlead
      letI := slotsOf S
      -- The wave length is three, and every arithmetic goal below is
      -- stated in the interface's spelling of the slot round; the
      -- Hydrozoan one is definitionally equal but a distinct atom to
      -- `omega`.
      have hw3 : (hydrozoanLive (Replica := Replica)
          (BlockId := BlockId)).waveLength = 3 := rfl
      rw [hw3] at hwave
      have h0 := hpop (S.slotRound κ) hRnd (by omega)
      have h1 := hpop (S.slotRound κ + 1) (by omega) (by omega)
      have h2 := hpop (S.slotRound κ + 2) (by omega) (by omega)
      obtain ⟨L, _, _, hd⟩ :=
        LeanDag.Hydrozoan.DirectLiveness.holds Replica BlockId U T Rnd κ hTC hTq hsync hRnd
          h0 h1 h2 hlead V
          (fun b hb hr => hcov b hb (le_trans hr (show S.slotRound κ + 2 ≤ N by omega)))
      exact ⟨L, hd⟩
  · intro S U V i j A hij hdj hmid
    letI := slotsOf S
    exact (LeanDag.Hydrozoan.IndirectLiveness.holds Replica BlockId U).1 V i j A hij hdj hmid

theorem roundRobinLive : RoundRobinLive := by
  intro n hn BlockId _ F hck w hk m hm hmax
  have hbound : (hydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength * (F.f + F.c) + 1 ≤ n := by
    have hc := F.card_replicas
    rw [Fintype.card_fin] at hc
    change 3 * (F.f + F.c) + 1 ≤ n
    omega
  have h := liveOn_roundRobin hn _ (descent (Fin n) BlockId) (Nat.succ_pos 2) hbound hk m hm hmax
  -- the gap is `n + waveLength - 1`, and the wave length is three
  have hw3 : (hydrozoanLive (Replica := Fin n)
      (BlockId := BlockId)).waveLength = 3 := rfl
  rw [hw3] at h
  simpa using h

theorem holds : Statement := ⟨descent, roundRobinLive⟩

end HydrozoanLive

end Barnacle

end LeanDag
