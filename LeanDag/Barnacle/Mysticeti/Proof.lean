import LeanDag.Barnacle.Mysticeti.Statement
import LeanDag.Barnacle.Helpers.Anchored
/-!
# Barnacle over Mysticeti — proof

Generated proof layer; not part of the audit surface. The laws are
`ofAnchored_laws` at the core's laws (`coreLaws`).
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
