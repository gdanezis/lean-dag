import LeanDagTest.Barnacle.Rules.Nemo.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Nemo.Properties
/-!
# Barnacle over Nemo-Nemo — proof

Generated proof layer; not part of the audit surface. The pigeonhole's
bound `2 · (n − majority) + 1 ≤ n` holds at every `n`.
-/

namespace LeanDag

namespace Barnacle

namespace Nemo

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ _ _
  exact NemoProperties.descent

theorem majority_bound (n : ℕ) (hn : 0 < n) :
    2 * (n - LeanDag.Nemo.majority (Fin n)) + 1 ≤ n := by
  unfold LeanDag.Nemo.majority
  rw [Fintype.card_fin]
  omega

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _
    exact ofAnchored_laws LeanDag.Nemo.nemoLaws
  · intro n hn C BlockId Payload _ C hC
    have hbound : (nemoLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n))
          + 1 ≤ n := by
      change 2 * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n)) + 1 ≤ n
      rw [Fintype.card_fin]
      exact majority_bound n hn
    exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload) (Nat.succ_pos 1) hbound C hC

end Nemo

end Barnacle

end LeanDag
