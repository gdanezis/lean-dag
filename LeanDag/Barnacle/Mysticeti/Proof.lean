import LeanDag.Barnacle.Mysticeti.Statement
import LeanDag.Barnacle.Helpers.Anchored
/-!
# Barnacle over Mysticeti — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace Barnacle

namespace Mysticeti

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _
  exact ofAnchored_laws coreLaws

end Mysticeti

end Barnacle

end LeanDag
