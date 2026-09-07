import LeanDag.Hydrozoan.EventualDecision.Statement
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.Helpers.IndirectLiveness
/-!
# Helpers: eventual decision

Generated: the two conjuncts of the eventual-decision statement. The
run-commits lemma works at `Type` (it invokes the direct-liveness
headline, which quantifies over `Type`); the schedule lemma is
universe-polymorphic.
-/

namespace LeanDag

namespace Hydrozoan
namespace EventualDecision

theorem runsRecur (Replica : Type*) [S : Slots Replica] : RunsRecur Replica :=
  fun _ _ k R hfair => S.exists_run_past hfair k R

variable {Replica BlockId : Type} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- Direct liveness commits each run slot; the descent settles every slot
below. -/
theorem runDecidesBelow (U : BlockUniverse Replica BlockId) :
    RunDecidesBelow U := by
  intro T R b c hT hcard hsync hc hspan hRb hlead hpop V hcov
  refine AnchoredRule.decided_below_of_run exists_least hc hspan (Led := fun j => S.leader j ∈ T)
    hlead ?_
  intro j h1 h2 hleadj
  have hRj : R ≤ S.slotRound j := le_trans hRb (S.mono h1)
  have hbj : S.slotRound b ≤ S.slotRound j := S.mono h1
  have hjn : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono h2
  obtain ⟨L, -, -, hdec⟩ :=
    DirectLiveness.holds Replica BlockId U T R j hT hcard hsync hRj
      (hpop _ hbj (by omega)) (hpop _ (by omega) (by omega))
      (hpop _ (by omega) (by omega)) hleadj V (hcov.mono (by omega))
  exact ⟨L, hdec⟩

end EventualDecision
end Hydrozoan

end LeanDag
