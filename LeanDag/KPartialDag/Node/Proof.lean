import LeanDag.KPartialDag.Node.Statement
import LeanDag.KPartialDag.Helpers.Node
/-!
# What a node reads — proof

Locality is `linkedIn_congr` and `fetchedIn_congr` both ways; holding the
sub-DAG fetches it by `fetchedIn_of_subset`; soundness is
`NodeDecided.decided`; and two nodes agree by soundness on the full view and
`decided_unique` at the rule's laws.
-/

namespace LeanDag

namespace KPartialDag

namespace Node

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ U U' K H A L r hb
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  exact ⟨⟨linkedIn_congr hb, linkedIn_congr hb'⟩, ⟨fetchedIn_congr hb, fetchedIn_congr hb'⟩⟩

theorem fetchable : Fetchable := by
  intro Validator BlockId Payload _ _ _ _ U K H A hsub
  exact fetchedIn_of_subset hsub

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ _ S K U H V k v hH hHV h
  exact h.decided hH hHV

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ K U H₁ H₂ k v₁ v₂ hK hH₁ hH₂ h₁ h₂
  exact (kRule K).decided_unique (kRule_laws hK) trivial
    (h₁.decided (V := View.full U) hH₁ hH₁) (View.full U) v₂
    (h₂.decided (V := View.full U) hH₂ hH₂)

theorem holds : Statement := ⟨local_, fetchable, sound, agrees⟩

end Node

end KPartialDag

end LeanDag
