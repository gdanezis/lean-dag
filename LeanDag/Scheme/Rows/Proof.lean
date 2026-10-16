import LeanDag.Scheme.Rows.Statement
import LeanDag.Scheme.HybridRow.Proof
/-!
# Every row, safe and live — proof

Each row is covered by its inequalities and has its commit threshold within
the quorum, by arithmetic; the family's safety, liveness at the core
(`Scheme.lives`) and at the hybrid fault model (`HybridRow.withSelfParent`)
then apply.
-/

namespace LeanDag

namespace Scheme

namespace Rows

open Properties

theorem coreRows : CoreRows := by
  intro Validator BlockId Payload _ _ _ F σ hσ
  have hn := F.card_validators
  have hq : Fintype.card Validator - F.f ≤ Fintype.card Validator := Nat.sub_le _ _
  refine ⟨⟨Scheme.safety hσ card_compl_correct_le hq (Or.inr (Or.inl ⟨rfl, le_rfl, rfl, ?_⟩)),
      Scheme.lives subset_rfl (by simp [Params.cordialMinersPS])⟩,
    ⟨Scheme.safety hσ card_compl_correct_le hq
      (Or.inr (Or.inl ⟨rfl, by simp [Params.cordialMinersAsync], rfl, ?_⟩)),
      Scheme.lives subset_rfl (by simp [Params.cordialMinersAsync])⟩⟩ <;>
  · simp only [Params.ThreeRound, Params.cordialMinersPS, Params.cordialMinersAsync]
    omega

theorem hybridRows : HybridRows := by
  intro Replica BlockId _ _ _ F σ hσ
  have hn := F.card_replicas
  have sl := fun p hcov hcm => HybridRow.withSelfParent Replica BlockId p σ hσ hcov hcm
  refine ⟨fun hb => ⟨sl _ (Or.inl ⟨rfl, le_rfl, ?_, ?_⟩) ?_, sl _ (Or.inl ⟨rfl, by simp [Params.asyncOrcaella], ?_, ?_⟩) ?_⟩,
    sl _ hybridMysticeti_covered ?_, fun w hw => sl _ (Or.inr (Or.inl ⟨rfl, hw, rfl, ?_⟩)) ?_,
    fun hf => ⟨sl _ (Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, le_rfl, hf, ?_⟩))) ?_,
      sl _ (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [Params.asyncNemoNemo], le_rfl, hf, ?_⟩))) ?_⟩⟩ <;>
  simp only [Params.TwoRound, Params.ThreeRound, Params.TwoRoundCrash, Params.orcaella,
    Params.asyncOrcaella, Params.hybridMysticeti, Params.hybridMahiMahi, Params.nemoNemo,
    Params.asyncNemoNemo, Hydrozoan.q] <;> omega

theorem asyncRows : AsyncRows := by
  intro n f c
  refine ⟨fun hn => ⟨?_, ?_, ?_⟩, fun hn => ?_, fun hn => ?_, fun hn => ?_,
    fun hn => ⟨?_, ?_⟩⟩ <;>
  simp only [Params.AsyncReady, Params.voteOffset, Params.mahiMahi, Params.cordialMinersAsync,
    Params.blueBottleAsync, Params.asyncOrcaella, Params.asyncNemoNemo, Params.hybridMahiMahi,
    Bool.false_eq_true, if_false, if_true] <;>
  exact ⟨by omega, by simp, by omega,
    fun _ => ⟨by omega, by omega⟩, by omega⟩

theorem holds : Statement := ⟨coreRows, hybridRows, asyncRows⟩

end Rows

end Scheme

end LeanDag
