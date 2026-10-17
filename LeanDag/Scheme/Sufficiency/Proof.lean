import LeanDag.Scheme.Sufficiency.Statement
import LeanDag.Scheme.Helpers.Sufficiency
/-!
# The table's inequalities suffice for agreement — proof

Each family's laws (`Helpers/Sufficiency.lean`, `coveredLaws`) give
agreement under the invariant.
-/

namespace LeanDag

namespace Scheme

namespace Sufficiency

theorem coveredAgree : CoveredAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ hHon hq hfam
  exact AnchoredRule.agreeOn (coveredLaws σ hHon hq hfam).2.2.2 (fun _ _ h => h)

theorem holds : Statement := coveredAgree

end Sufficiency

end Scheme

end LeanDag
