import LeanDag.OptimalHydrozoan.Helpers.Grounding

/-!
# Optimal-Hydrozoan: grounding — proof

Generated. Fairness is Hydrozoan's theorem, reused; the two
universe-level conjuncts come from the Optimal helpers.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace Grounding

theorem holds : Statement :=
  ⟨Hydrozoan.Grounding.waveRobinFair, hypothesesRealizable, groundedProgress⟩

end Grounding

end OptimalHydrozoan

end LeanDag
