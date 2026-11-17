import LeanDag.KPartialSparse.Agreement.Statement
import LeanDag.KPartialSparse.Helpers.Rule
/-!
# Sparse K-partial DAG — agreement, proof

The laws are `sRule_laws`; agreement is the anchored relation's
`decided_unique` at them; the rows are arithmetic.
-/

namespace LeanDag

namespace KPartialSparse

namespace Agreement

open KPartialDag Scheme

theorem laws : Laws := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ p K hrow hdeep
  exact sRule_laws hrow hdeep

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ S p U K V₁ V₂ k v₁ v₂ hrow hdeep hI h₁ h₂
  exact (sRule p K).decided_unique (sRule_laws hrow hdeep) hI h₁ V₂ v₂ h₂

theorem rows : Rows := by
  intro Validator _ _ F Cr
  have := F.card_validators
  have := Cr.card_validators
  refine ⟨fun hc => ⟨Or.inl ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩, spread_arith_zero hc F.card_validators⟩,
    fun hc => Or.inl ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩,
    fun hc h5 => Or.inr ⟨rfl, rfl, ?_, ?_, ?_⟩, Or.inl ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩,
    fun h5 => ⟨Or.inr ⟨rfl, rfl, ?_, ?_, ?_⟩, spread_arith h5⟩⟩ <;>
    simp only [Params.mysticeti, Params.cordialMinersPS, Params.hybridMysticeti,
      Params.blueBottlePS, Params.orcaella] <;> omega

theorem holds : Statement := ⟨laws, agrees, rows⟩

end Agreement

end KPartialSparse

end LeanDag
