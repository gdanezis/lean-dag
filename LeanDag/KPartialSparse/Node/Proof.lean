import LeanDag.KPartialSparse.Node.Statement
import LeanDag.KPartialSparse.Helpers.Node
/-!
# Sparse K-partial DAG — what a node reads, proof

Each result is a helper of `Helpers/Node.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Node

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ p U U' K H A L r ρ hb hr
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  have hr' : ∀ i ∈ H, ∀ j ∈ (U'.block i).refs, (U.block j).round = (U'.block j).round :=
    fun i hi j hj => (hr i hi j (hb i hi ▸ hj)).symm
  exact ⟨⟨linkedIn_congr hb hr, linkedIn_congr hb' hr'⟩,
    ⟨fetchedIn_congr hb hr, fetchedIn_congr hb' hr'⟩⟩

theorem fetchable : Fetchable := by
  intro Validator BlockId Payload _ _ _ _ _ _ U K H A ρ hsub
  exact fetchedIn_of_subset hsub

theorem bounded : Bounded := by
  intro Validator BlockId Payload _ _ _ _ _ _ U K H A ρ hA hρ hH
  exact fetchedIn_of_band hA hρ hH

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K H V k v hH hHV h
  exact h.decided hH hHV

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K H₁ H₂ k v₁ v₂ hrow hdeep hI hH₁ hH₂ h₁ h₂
  exact h₁.agree hrow hdeep hI hH₁ hH₂ h₂

theorem checked : Checked := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U U' K t H L
  exact ⟨fun hb => ⟨backs_congr hb, backs_congr fun i hi => (hb i hi).symm⟩,
    checks_of_buildsChecked⟩

theorem holds : Statement := ⟨local_, fetchable, bounded, sound, agrees, checked⟩

end Node

end KPartialSparse

end LeanDag
