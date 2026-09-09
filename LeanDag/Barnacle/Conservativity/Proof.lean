import LeanDag.Barnacle.Conservativity.Statement
import LeanDag.Barnacle.Helpers.Schedule
/-!
# BN6 — proof

Generated proof layer; not part of the audit surface. BN6a is an
induction along `update` under the constant rule; BN6b transports each
`closed` verdict to `Sched 1` by `Sched_congr`.
-/

namespace LeanDag

namespace Barnacle

namespace Conservativity

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R P getLeader hk
  have hcount : ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
      (Rn : PartialRun R P getLeader hk (constRule R) U V K),
      ∀ k, k ≤ K → Rn.count k = 1 ∧ Rn.backoff k = 0 := by
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
  have hd := Rn.closed k hkK κ (by rw [hc, Nat.div_one]; exact h1)
    (by rw [hc, Nat.div_one, Rn.start_succ k hkK, hc, Nat.div_one]; omega)
  rw [Sched_congr getLeader hk hc (Rn.count_pos k) (Rn.count_le k) Nat.one_pos P.max_pos] at hd
  exact hd

end Conservativity

end Barnacle

end LeanDag
