import LeanDag.KPartialDag.Agreement.Statement
import LeanDag.KPartialDag.Helpers.Rule
/-!
# Agreement of the commit rule — proof

The laws are `kRule_laws`; agreement is the anchored relation's
`decided_unique` at them.
-/

namespace LeanDag

namespace KPartialDag

namespace Agreement

theorem laws : Laws := by
  intro Validator BlockId Payload _ _ _ _ K hK
  exact kRule_laws hK

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ S U K V₁ V₂ k v₁ v₂ hK h₁ h₂
  exact (kRule K).decided_unique (kRule_laws hK) trivial h₁ V₂ v₂ h₂

theorem holds : Statement := ⟨laws, agrees⟩

end Agreement

end KPartialDag

end LeanDag
