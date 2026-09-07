import LeanDag.Barnacle.Nemo.Statement
import LeanDag.Barnacle.Helpers.Anchored
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Nemo.Properties
/-!
# Barnacle over Nemo-Nemo — proof

Generated proof layer; not part of the audit surface. The laws are
`ofAnchored_laws` at Nemo's laws; the descent laws are
`descent_of_support` at the vote support, with the reliable set
everyone; round-robin liveness is BN9e at the majority slack and wave
length `2`, whose bound holds at every `n`.
-/

namespace LeanDag

namespace Barnacle

namespace Nemo

theorem descent : Descent := by
  intro Validator BlockId Payload _ _ _ _
  exact descent_of_support (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (Properties.voteSupport _) (Timed.voteSupport_ofCoverage _)
    (NemoProperties.voteSupport_commits LeanDag.Nemo.CrashFaults.card_pos)
    NemoProperties.indirect (by change 1 ≤ 1 + 1; omega) fun _ _ _ h => h

/-- The pigeonhole's committee bound holds for the majority slack at
every `n`: `2 · (n − majority) + 1 ≤ n`. -/
theorem majority_bound (n : ℕ) (hn : 0 < n) :
    2 * (n - LeanDag.Nemo.majority (Fin n)) + 1 ≤ n := by
  unfold LeanDag.Nemo.majority
  rw [Fintype.card_fin]
  omega

theorem holds : Statement := by
  refine ⟨?_, descent, ?_⟩
  · intro Validator BlockId Payload _ _ _
    exact ofAnchored_laws LeanDag.Nemo.nemoLaws
  · intro n hn C BlockId Payload _ w hk m hm hmax
    have hbound : (nemoLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n))
          + 1 ≤ n := by
      change 2 * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n)) + 1 ≤ n
      rw [Fintype.card_fin]
      exact majority_bound n hn
    exact liveOn_roundRobin hn _ (descent (Fin n) BlockId Payload) (Nat.succ_pos 1) hbound hk m
      hm hmax

end Nemo

end Barnacle

end LeanDag
