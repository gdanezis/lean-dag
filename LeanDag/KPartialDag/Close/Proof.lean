import LeanDag.KPartialDag.Close.Statement
import LeanDag.KPartialDag.Helpers.Close
/-!
# Closing the channel — proof

Each result is a helper of `Helpers/Close.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Close

theorem closes : Closes := by
  intro Validator BlockId Payload _ _ _ _ _ p U tl T G δ τ γ μ R N K D Δ c r₀ cl hrow hlive h hγ
    hδ hγτ hK hF hc hspan fair hgap hcl
  exact h.exists_closesAfter hrow hlive hγ hδ hγτ hK hF hc hspan fair hgap hcl

theorem serves : Serves := by
  intro Validator BlockId Payload _ _ _ _ _ p U K D H H' cl g n hrow hH hH' hdec hcl
  exact ⟨hdec.mono hrow hH hH', closesAfter_mono hH hH' hdec hcl⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ p U K D H₁ H₂ cl g₁ g₂ n₁ n₂ hrow hK hH₁ hH₂ h₁ hc₁ h₂
    hc₂
  exact closesAfter_agree hrow hK hH₁ hH₂ h₁ hc₁ h₂ hc₂

theorem holds : Statement := ⟨closes, serves, agrees⟩

end Close

end KPartialDag

end LeanDag
