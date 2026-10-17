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
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ ht
  exact AnchoredRule.agree (coveredLaws σ ht).2.2.2

theorem holds : Statement := coveredAgree

end Sufficiency

end Scheme

end LeanDag
