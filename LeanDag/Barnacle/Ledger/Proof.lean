import LeanDag.Barnacle.Ledger.Statement
import LeanDag.Barnacle.Agreement.Proof
import LeanDag.Barnacle.Helpers.Ledger
/-!
# BN5 — proof

Generated proof layer; not part of the audit surface. Agreement is BN3
read through `ledgerOf_congr`; the prefix is `List.range_add`; integrity
is `List.nodup_flatMap` with the two helper halves.
-/

namespace LeanDag

namespace Barnacle

namespace Ledger

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hRa hRc P upd C₀ hanc
  refine ⟨?_, ?_, ?_⟩
  · -- BN5a.
    intro U V₁ V₂ K₁ K₂ R₁ R₂
    have hrange : ∀ k, k < min K₁ K₂ → R₁.rangeLedger k = R₂.rangeLedger k := by
      intro k hkm
      have h := Agreement.holds Validator BlockId Payload R hRa P upd C₀ hanc
        U V₁ V₂ K₁ K₂ R₁ R₂
      obtain ⟨hs, hc, _, hrest⟩ := h k (by omega)
      obtain ⟨_, hv⟩ := hrest hkm
      have hs' : R₁.start (k + 1) = R₂.start (k + 1) := (h (k + 1) (by omega)).1
      unfold PartialRun.rangeLedger
      rw [← hs, ← hc, ← hs']
      exact ledgerOf_congr (fun κ h1 h2 => hv κ (round_of_mem_interval R₁ h1 h2).1
        (round_of_mem_interval R₁ h1 h2).2)
    refine ⟨hrange, fun K hK => ?_⟩
    induction K with
    | zero => rfl
    | succ K ih =>
      unfold PartialRun.ledgerUpto at *
      rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (by omega),
        List.flatMap_cons, List.flatMap_cons, hrange K (by omega), List.flatMap_nil, List.flatMap_nil]
  · -- BN5b.
    intro U V K Rn K₁ K₂ hKK
    unfold PartialRun.ledgerUpto
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKK
    rw [List.range_add, List.flatMap_append]
    exact List.prefix_append _ _
  · -- BN5c.
    intro U V K Rn K' hK'
    unfold PartialRun.ledgerUpto
    rw [List.nodup_flatMap]
    refine ⟨fun k hkm => rangeLedger_nodup hRc Rn (by rw [List.mem_range] at hkm; omega), ?_⟩
    have hpw : (List.range K').Pairwise (fun a b => a < b ∧ b < K') := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_range]
      rw [List.length_range] at hj
      exact ⟨hij, hj⟩
    exact hpw.imp (fun h => rangeLedger_disjoint hRc Rn h.1 (by omega))

end Ledger

end Barnacle

end LeanDag
