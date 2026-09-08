import LeanDag.OptimalHydrozoan.Helpers.Grounding
/-!
# Optimal-Hydrozoan: grounding — proof

Generated.
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
