import LeanDag.Hydrozoan.ThresholdArithmetic.Statement
/-!
# Threshold arithmetic — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

namespace ThresholdArithmetic

theorem holds : Statement := by
  intro Replica _ _ F
  have hn := F.card_replicas
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [CertUniqueness, FastUniqueness, FastStarvation, SlowCollectible,
      AnchorSeesSlow, AnchorSeesFast, qCert, qFast, qSlow, qWeak, q, p] <;>
    omega

end ThresholdArithmetic

end Hydrozoan

end LeanDag
