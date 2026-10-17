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
  obtain ⟨-, -, hps, has⟩ := (Table.rowsCovered _ F.f 0).1 (by omega)
  exact ⟨⟨Scheme.safety hσ card_compl_correct_le hq hps,
      Scheme.lives subset_rfl (by simp [Params.cordialMinersPS])⟩,
    ⟨Scheme.safety hσ card_compl_correct_le hq has,
      Scheme.lives subset_rfl (by simp [Params.cordialMinersAsync])⟩⟩

theorem hybridRows : HybridRows := by
  intro Replica BlockId _ _ _ F σ hσ
  have hn := F.card_replicas
  have hc := Table.rowsCovered (Fintype.card Replica) F.f F.c
  have sl := fun p hcov hcm => HybridRow.withSelfParent Replica BlockId p σ hσ hcov hcm
  refine ⟨fun hb => ⟨sl _ (hc.2.2.1 hb).1 ?_, sl _ (hc.2.2.1 hb).2 ?_⟩,
    sl _ (hc.2.2.2.1 (by omega)).1 ?_, fun w hw => sl _ ((hc.2.2.2.1 (by omega)).2 w hw) ?_,
    fun hf => ⟨sl _ (by simpa [Hydrozoan.q, hf] using (hc.2.2.2.2 (by omega)).1) ?_,
      sl _ (by simpa [Hydrozoan.q, hf] using (hc.2.2.2.2 (by omega)).2) ?_⟩⟩
  all_goals
    simp only [Params.orcaella, Params.asyncOrcaella, Params.hybridMysticeti,
      Params.hybridMahiMahi, Params.nemoNemo, Params.asyncNemoNemo, Hydrozoan.q]
    omega

theorem asyncRows : AsyncRows := by
  intro n f c
  refine ⟨fun hn => ⟨?_, ?_, ?_⟩, fun hn => ?_, fun hn => ?_, fun hn => ?_,
    fun hn => ⟨?_, ?_⟩⟩ <;>
  simp only [Params.AsyncReady, Params.CertFits, Params.voteOffset, Params.mahiMahi,
    Params.cordialMinersAsync, Params.blueBottleAsync, Params.asyncOrcaella, Params.asyncNemoNemo, Params.hybridMahiMahi,
    Bool.false_eq_true, if_false, if_true] <;>
  exact ⟨by omega, by simp, ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩, by omega⟩

theorem holds : Statement := ⟨coreRows, hybridRows, asyncRows⟩

end Rows

end Scheme

end LeanDag
