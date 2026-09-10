import LeanDag.Barnacle.Aimd.Statement
/-!
# BN7 — proof

Generated proof layer; not part of the audit surface. The arithmetic of
`min`, `max`, truncated subtraction and `2 ^ backoff ≥ 1`, and the two
branches of the health test.
-/

namespace LeanDag

namespace Barnacle

namespace Aimd

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R P lead hl
  have hpow : ∀ b : ℕ, 1 ≤ 2 ^ b := fun b => Nat.one_le_two_pow
  have hmax := P.max_pos
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- BN7a: bounds, and the interval is carried.
    intro C backoff U V A
    exact ⟨fun r => count_le P _ _ _, rfl⟩
  · -- BN7b: healthy, below the cap.
    intro m backoff h
    show max 1 (min P.maxLeaders (m + 1)) = m + 1
    omega
  · -- BN7b: at the cap.
    intro backoff
    show max 1 (min P.maxLeaders (P.maxLeaders + 1)) = P.maxLeaders
    omega
  · -- BN7c: unhealthy, above the floor.
    intro m backoff h hm
    have := hpow backoff
    show max 1 (min P.maxLeaders (m - 2 ^ backoff)) < m
    rw [Nat.max_def, Nat.min_def]; split_ifs <;> omega
  · -- BN7c: the step.
    intro m backoff h hm
    have := hpow backoff
    show max 1 (min P.maxLeaders (m - 2 ^ backoff)) = m - 2 ^ backoff
    rw [Nat.max_def, Nat.min_def]; split_ifs <;> omega
  · -- BN7c: the floor.
    intro backoff
    have := hpow backoff
    show max 1 (min P.maxLeaders (1 - 2 ^ backoff)) = 1
    rw [Nat.max_def, Nat.min_def]; split_ifs <;> omega
  · -- BN7d: the test.
    intro C backoff U V A h
    refine ⟨?_, ?_⟩ <;> simp only [rule, decide_eq_true h, if_pos, Config.uniform_slotsAt]
  · -- BN7e: the rule ignores the view.
    intro _ _ _ _ _ _
    rfl

end Aimd

end Barnacle

end LeanDag
