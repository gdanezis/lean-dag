import LeanDag.OptimalHydrozoan.EventualDecision.Statement
import LeanDag.OptimalHydrozoan.DirectLiveness.Proof
import LeanDag.OptimalHydrozoan.Helpers.IndirectLiveness
import LeanDag.Hydrozoan.EventualDecision.Proof

/-!
# Optimal-Hydrozoan: eventual decision — proof

Generated proof layer; not part of the audit surface. The composition of
`OptimalHydrozoan.DirectLiveness.holds` (each run slot commits) with the descent
`decidedOpt_below_of_committed_run`; `RunsRecur` is Hydrozoan's theorem,
reused. `ledgerProgress` is the composed headline, as in Hydrozoan.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace EventualDecision

open LeanDag.Hydrozoan.IndirectLiveness (SpansEligible)
open LeanDag.Hydrozoan.EventualDecision (FairRunOn RunsRecur)

variable {Replica BlockId : Type} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- The composition: direct liveness commits each run slot, and the
indirect descent settles every slot below the run. -/
theorem runDecidesBelow (U : OptUniverse Replica BlockId) : RunDecidesBelow U := by
  intro T R b c hT hcard hsync hc hspan hRb hlead hpop V hcov i hi
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B, DecidedOpt U V j (some B) := by
    intro j h1 h2
    have hleadj : S.leader j ∈ T := by
      have := hlead (j - b) (by omega)
      rwa [Nat.add_sub_cancel' h1] at this
    have hRj : R ≤ S.slotRound j := le_trans hRb (S.mono h1)
    have hbj : S.slotRound b ≤ S.slotRound j := S.mono h1
    have hjn : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono h2
    obtain ⟨L, -, -, hdec⟩ :=
      (OptimalHydrozoan.DirectLiveness.holds Replica BlockId U).1 T R j hT hcard hsync hRj
        (hpop _ hbj (by omega)) (hpop _ (by omega) (by omega))
        (hpop _ (by omega) (by omega)) hleadj V (hcov.mono (by omega))
    exact ⟨L, hdec⟩
  exact decidedOpt_below_of_committed_run (by omega)
    (fun i' hi' => hspan b i' hi') hrun i hi

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _
  exact ⟨fun U => runDecidesBelow U, Hydrozoan.EventualDecision.runsRecur Replica⟩

/-- **The ledger does not stall** (the composed corollary): under a fair
schedule, past every slot `k` and round `R` there is a bound `b` such
that any Optimal universe in which `T` is synchronised and fills the
run's span has every slot below `b` decided on any view caught up to
the run's last decision round. -/
theorem ledgerProgress :
    ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
      [DecidableEq BlockId] [OptimalFaults Replica] [S : Slots Replica],
    ∀ (T : Finset Replica) (R k c : ℕ),
      T ⊆ (Correct : Finset Replica) → q Replica ≤ T.card →
      0 < c → SpansEligible Replica c →
      FairRunOn Replica T c →
      ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
        ∀ (U : OptUniverse Replica BlockId),
          SynchronisedOn U.toBlockUniverse T R →
          (∀ r, S.slotRound b ≤ r → r ≤ S.slotRound (b + c - 1) + 2 →
            PopulatedOn U.toBlockUniverse T r) →
          ∀ V : View U.toBlockUniverse,
            V.CoversUpto (S.slotRound (b + c - 1) + 2) →
          ∀ i, i < b → ∃ v, DecidedOpt U V i v := by
  intro Replica BlockId _ _ _ _ S T R k c hT hcard hc hspan hfair
  obtain ⟨b, hkb, hRb, hlead⟩ := Hydrozoan.EventualDecision.runsRecur Replica T c k R hfair
  exact ⟨b, hkb, hRb, fun U hsync hpop V hcov =>
    runDecidesBelow U T R b c hT hcard hsync hc hspan hRb hlead hpop V hcov⟩

end EventualDecision

end OptimalHydrozoan

end LeanDag
