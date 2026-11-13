import LeanDag.Scheme.Compose.Statement
import LeanDag.Scheme.Crash.Proof
import LeanDag.Integration.SchemeCheckpoint
/-!
# The mechanisms composed — proof

The checkpoint bridge (`Integration.liveCommitFinalized_scheme`) needs the
wave of the slot populated and its candidates certified by the validators
following the signing rule; the responsive precondition gives both
(`live_of_reactiveLive`), and the crash precondition is the responsive one
(`Crash.live`).
-/

namespace LeanDag

namespace Scheme

namespace Compose

theorem checkpointsResponsive : CheckpointsResponsive := by
  intro Validator BlockId Payload Value _ _ _ _ P _ honest p σ q f _ M E vm rel ht hc hcm S U Pr V
    slot hlive hcov hlead
  obtain ⟨hq, N, -, -, hall⟩ := live_of_reactiveLive hc.1 hc.2 hlive
  obtain ⟨hpop, hcert⟩ := hall slot (le_refl _) (Nat.lt_succ_self _) hlead
  exact Integration.liveCommitFinalized_scheme M E vm ht hcm S Pr hq hpop hcert hcov hlead

theorem checkpointsCrash : CheckpointsCrash := by
  intro Validator BlockId Payload Value _ _ _ _ P _ honest p σ q f _ M E vm rel ht hc hcm S U Pr V
    slot hlive hcov hlead
  exact checkpointsResponsive Validator BlockId Payload Value P honest p σ q f M E vm rel ht hc hcm
    S U Pr V slot (Crash.live Validator BlockId Payload P honest p σ rel S U V M.alive slot
      (slot + 1) hlive) hcov hlead

theorem holds : Statement := ⟨checkpointsResponsive, checkpointsCrash⟩

end Compose

end Scheme

end LeanDag
