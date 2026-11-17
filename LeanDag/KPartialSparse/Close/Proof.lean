import LeanDag.KPartialSparse.Close.Statement
import LeanDag.KPartialSparse.Helpers.Close
/-!
# Sparse K-partial DAG — closing the channel, proof

Each result is a helper of `Helpers/Close.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Close

theorem closes : Closes := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U tl T G δ τ γ R N K D Δ c r₀ cl hrow hlink
    hdeep hI hlive hDK h hγ hδ hγτ hF hsl hc hspan fair hgap hcl
  exact h.exists_closesAfter hrow hlink hdeep hI hlive hDK hγ hδ hγτ hF hsl hc hspan fair hgap hcl

theorem serves : Serves := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K D H H' cl g n hH hH' hdec hcl
  exact ⟨hdec.mono hH hH', closesAfter_mono hH hH' hdec hcl⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K D H₁ H₂ cl g₁ g₂ n₁ n₂ hrow hdeep hI hH₁
    hH₂ h₁ hc₁ h₂ hc₂
  exact closesAfter_agree hrow hdeep hI hH₁ hH₂ h₁ hc₁ h₂ hc₂

theorem holds : Statement := ⟨closes, serves, agrees⟩

end Close

end KPartialSparse

end LeanDag
