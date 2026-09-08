import LeanDag.Hydrozoan.Helpers.EventualDecision
/-!
# Proof: eventual decision

Generated.
-/

namespace LeanDag

namespace Hydrozoan
namespace EventualDecision

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ _
  exact ⟨fun U => runDecidesBelow U, runsRecur Replica⟩

/-- **The ledger does not stall** (the composed corollary): under a fair
schedule, past every slot `k` and round `R` there is a bound `b` such
that any universe in which `T` is synchronised and fills the run's span
has every slot below `b` decided on any view caught up to the run's
last decision round. -/
theorem ledgerProgress :
    ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
      [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
      [S : Slots Replica],
    ∀ (T : Finset Replica) (R k c : ℕ),
      T ⊆ (Correct : Finset Replica) → q Replica ≤ T.card →
      0 < c → (hydrozoanAnchored Replica BlockId).SpansEligible c →
      FairRunOn T c →
      ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
        ∀ (U : BlockUniverse Replica BlockId),
          SynchronisedOn U T R →
          (∀ r, S.slotRound b ≤ r → r ≤ S.slotRound (b + c - 1) + 2 →
            PopulatedOn U T r) →
          ∀ V : View U, V.CoversUpto (S.slotRound (b + c - 1) + 2) →
          ∀ i, i < b → ∃ v, Decided U V i v := by
  intro Replica BlockId _ _ _ _ _ S T R k c hT hcard hc hspan hfair
  obtain ⟨b, hkb, hRb, hlead⟩ := runsRecur Replica T c k R hfair
  exact ⟨b, hkb, hRb, fun U hsync hpop V hcov =>
    runDecidesBelow U T R b c hT hcard hsync hc hspan hRb hlead hpop V hcov⟩

end EventualDecision
end Hydrozoan

end LeanDag
