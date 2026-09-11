import LeanDag.Adaptive.Agreement.Statement
import LeanDag.Adaptive.Helpers.Agreement
/-!
# AL13 — proof

Generated proof layer; not part of the audit surface. `configAgree` with
`anchor_agree` and `vdct_agree`.
-/

namespace LeanDag

namespace Adaptive

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR P upd C₀ hanc U V₁ V₂ K₁ K₂ R₁ R₂ k hkm
  obtain ⟨hs, hc, hb⟩ := configAgree hR hanc R₁ R₂ k hkm
  refine ⟨hs, hc, hb, fun hlt => ?_⟩
  have ha := anchor_agree hR R₁ R₂ ⟨hs, hc, hb⟩ (by omega) (by omega)
  refine ⟨ha, fun κ h₁ h₂ => ?_⟩
  exact vdct_agree hR R₁ R₂ hc (by omega) (by omega) h₁ h₂
    (by rw [← hs, ← hc]; exact h₁) (by rw [← hc, ← ha]; exact h₂)

end Adaptive

end LeanDag
