import LeanDag.KPartialDag.Agreement.Statement
import LeanDag.KPartialDag.Helpers.Rule
import LeanDag.Scheme.Helpers.Votes
/-!
# Agreement of the commit rule — proof

The laws are `kRule_laws`; agreement is the anchored relation's
`decided_unique` at them; conformance is the scheme's
`certsAt_eq_votesFor`, `certsAt_eq_certificatesAt` and `blamersAt_eq`.
-/

namespace LeanDag

namespace KPartialDag

namespace Agreement

open Scheme

theorem laws : Laws := by
  intro Validator BlockId Payload _ _ _ _ p K hrow hK
  exact kRule_laws hrow hK

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ S p U K V₁ V₂ k v₁ v₂ hrow hK h₁ h₂
  exact (kRule p K).decided_unique (kRule_laws hrow hK) trivial h₁ V₂ v₂ h₂

theorem conforms : Conforms := by
  intro Validator BlockId Payload _ _ _ _ _ p σ U K A L k hrow
  have hd : ∀ b ∈ U.ids, DistinctRefs U b := fun b hb i hi j hj hc =>
    (U.valid b hb).clause i hi j hj hc
  have hcerts : certsAt p σ U L (U.block L).round = certsFor p U L (U.block L).round := by
    unfold certsFor
    rcases hrow with ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩
    · rw [if_pos hv, hw]
      exact certsAt_eq_votesFor σ p hv hw hd rfl
    · rw [if_neg (by simp [hv]), hw]
      exact certsAt_eq_certificatesAt σ p hv hw hd rfl
  have hoff : p.voteOffset = 1 := by
    rcases hrow with ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩
    · rw [Params.voteOffset_of_true hv, hw]
    · rw [Params.voteOffset_of_false hv (by omega), hw]
  refine ⟨hcerts, blamersAt_eq σ p hoff k, fun hA hl => ?_⟩
  obtain ⟨X, hX, hXa, hXn⟩ := hl
  refine hXn.trans (Finset.card_le_card (Finset.image_subset_image fun C hC => ?_))
  exact Finset.mem_filter.mpr ⟨hcerts ▸ hX hC, mem_history_of_avail hA (hXa C hC).1⟩

theorem rows : Rows := by
  intro Validator _ _ F
  have := F.card_validators
  refine ⟨⟨Or.inr ⟨rfl, rfl, rfl, ?_⟩, ?_⟩, ⟨Or.inr ⟨rfl, rfl, rfl, ?_⟩, ?_⟩, fun h5 =>
    ⟨Or.inl ⟨rfl, rfl, ?_, ?_⟩, ?_⟩⟩ <;>
    simp only [LiveRow, Params.mysticeti, Params.cordialMinersPS, Params.blueBottlePS,
      Params.TwoRound, Params.ThreeRound] <;> omega

theorem holds : Statement := ⟨laws, agrees, conforms, rows⟩

end Agreement

end KPartialDag

end LeanDag
