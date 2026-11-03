import LeanDag.Scheme.HybridRow.Statement
import LeanDag.Scheme.Helpers.Hydrozoan
/-!
# The Hybrid Mysticeti row against Hydrozoan — proof

The equality reads the row part by part (`Helpers/Hydrozoan.lean`);
safety is the family's at a covered row; progress, coverage and
inclusion are the family's support laws at Hydrozoan's fault model.
-/

namespace LeanDag

namespace Scheme

namespace HybridRow

open Properties

theorem slowRow : SlowRow := by
  intro Replica BlockId _ _ _ F σ
  exact hydrozoanSlow_eq σ

theorem onHydrozoan : OnHydrozoan := by
  intro Replica BlockId _ _ _ F p σ hσ hcov hcm hcert
  have hq : Hydrozoan.q Replica ≤ Fintype.card Replica := by unfold Hydrozoan.q; omega
  obtain ⟨hw, hw3⟩ := covered_waves hcov
  exact ⟨Scheme.safety hσ ⟨card_compl_nonByzantine, hq, hcov⟩,
    Support.progress (familySupport_commits (le_q_slack hcm)),
    familySupport_ofCoverage correct_subset_nonByzantine hw hw3 (le_q_slack hcert)⟩

theorem withSelfParent : WithSelfParent := by
  intro Replica BlockId _ _ _ F p σ hσ hcov hcm
  have hq : Hydrozoan.q Replica ≤ Fintype.card Replica := by unfold Hydrozoan.q; omega
  exact ⟨Scheme.safety hσ ⟨card_compl_nonByzantine, hq, hcov⟩,
    Support.liveness (familySupport_commits (le_q_slack hcm)) commitsCandidate
      (selfParent fun _ _ h => h.clause.2) (noEquiv correct_subset_nonByzantine)⟩

theorem holds : Statement := ⟨slowRow, onHydrozoan, withSelfParent⟩

end HybridRow

end Scheme

end LeanDag
