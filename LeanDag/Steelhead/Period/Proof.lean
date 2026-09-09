import LeanDag.Steelhead.Period.Statement
import LeanDag.Steelhead.Helpers.Period
/-!
# The period sequence — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Period.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Period

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U ws wa I
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coin upd k₀ V₁ V₂ j k₁ k₂ hwa h₁ h₂
    exact periodAt_unique hwa h₁ h₂
  · intro coin upd k₀ N V₁ V₂ per₁ per₂ k v₁ v₂ hws hwa hN hk h₁ h₂ d₁ d₂
    exact adaptive_decided_unique hws hwa hN hk h₁ h₂ d₁ d₂
  · intro coin upd k₀ V j k hp hall
    exact exists_periodAt_succ hp hall
  · intro coin upd k₀ V c N hwa hI hrun hV j hN
    exact periodAt_of_clause hwa hI hrun hV j hN

end Period

end Steelhead

end LeanDag
