import LeanDag.Steelhead.Interface.Statement
import LeanDag.Steelhead.Helpers.Compose
/-!
# The interface composes — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Compose.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Interface

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro rules hl hr ht
    exact compose_laws rules hl hr ht
  · intro rules S V₁ V₂ k v₁ v₂ hl hr ht h₁ h₂
    exact compose_decided_unique rules hl hr ht h₁ h₂
  · intro w
    exact steelheadAnchored_eq_compose w
  · exact periodicClass

end Interface

end Steelhead

end LeanDag
