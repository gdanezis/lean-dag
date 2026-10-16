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
  intro Replica BlockId _ _ _ F σ hσ
  have hq : Hydrozoan.q Replica ≤ Fintype.card Replica := by unfold Hydrozoan.q; omega
  exact ⟨Scheme.safety hσ card_compl_nonByzantine hq hybridMysticeti_covered,
    Support.progress (familySupport_commits hybridMysticeti_commit_le),
    familySupport_ofCoverage correct_subset_nonByzantine (show 2 ≤ 3 by omega)
      (fun _ => show 3 ≤ 3 by omega) hybridMysticeti_cert_le⟩

theorem withSelfParent : WithSelfParent := by
  intro Replica BlockId _ _ _ F σ hσ
  have hq : Hydrozoan.q Replica ≤ Fintype.card Replica := by unfold Hydrozoan.q; omega
  exact ⟨Scheme.safety hσ card_compl_nonByzantine hq hybridMysticeti_covered,
    Support.liveness (familySupport_commits hybridMysticeti_commit_le) commitsCandidate
      (selfParent fun _ _ h => h.clause.2) (noEquiv correct_subset_nonByzantine)⟩

theorem holds : Statement := ⟨slowRow, onHydrozoan, withSelfParent⟩

end HybridRow

end Scheme

end LeanDag
