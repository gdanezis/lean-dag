import LeanDag.KPartialDag.Node.Statement
import LeanDag.KPartialDag.Helpers.Node
/-!
# What a node reads — proof

Each result is a helper of `Helpers/Node.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Node

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ p U U' K H A L r ρ hb
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  exact ⟨⟨linkedIn_congr hb, linkedIn_congr hb'⟩, ⟨fetchedIn_congr hb, fetchedIn_congr hb'⟩⟩

theorem fetchable : Fetchable := by
  intro Validator BlockId Payload _ _ _ _ U K H A ρ hA hρ hsub
  exact fetchedIn_of_subset hA hρ hsub

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ _ S p U K H V k v hrow hH hHV h
  exact h.decided hrow hH hHV

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ p U K H₁ H₂ k v₁ v₂ hrow hK hH₁ hH₂ h₁ h₂
  exact h₁.agree hrow hK hH₁ hH₂ h₂

theorem holds : Statement := ⟨local_, fetchable, sound, agrees⟩

end Node

end KPartialDag

end LeanDag
