import LeanDag.Adaptive.Conservativity.Statement
/-!
# AL15 — proof

Generated proof layer; not part of the audit surface. AL15a is an
induction along `update` under the constant rule; AL15b rewrites each
`closed` verdict along it.
-/

namespace LeanDag

namespace Adaptive

namespace Conservativity

open Barnacle

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R P C₀
  have hcount : ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
      (Rn : SegRun R P (constRule R) C₀ U V K),
      ∀ k, k ≤ K → Rn.cfg k = C₀ ∧ Rn.backoff k = 0 := by
    intro U V K Rn k
    induction k with
    | zero => intro _; exact ⟨Rn.init.2.1, Rn.init.2.2⟩
    | succ k ih =>
      intro hk
      obtain ⟨hc, hb⟩ := ih (by omega)
      obtain ⟨⟨A, hA⟩, _⟩ := Rn.anchor_commits k (by omega)
      have e := Rn.update k (by omega) A hA
      simp only [constRule] at e
      rw [hc, hb] at e
      exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
  refine ⟨hcount, ?_⟩
  intro U V K Rn k hkK κ h1 h2
  obtain ⟨hc, _⟩ := hcount U V K Rn k (by omega)
  have hd := Rn.closed k hkK κ (by rw [hc]; exact h1) (by rw [hc]; exact h2)
  rw [hc] at hd
  exact hd


end Conservativity

end Adaptive

end LeanDag
