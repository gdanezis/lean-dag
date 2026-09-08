import LeanDag.Barnacle.Live.Statement
import LeanDag.Barnacle.Progress.Proof
import LeanDag.Barnacle.Helpers.Heads
/-!
# BN11 — proof

Generated proof layer; not part of the audit surface. `holds` is BN8b with
its liveness clause discharged from a schedule's heads runs;
`runsExist_roundRobin` is round-robin as one such schedule.
-/

namespace LeanDag

namespace Barnacle

namespace Live

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R slack c₀ getLeader hagree hD hw hheads P hk upd hbnd
  exact (Progress.holds Validator BlockId Payload R hagree P getLeader hk upd hbnd c₀).2
    fun m hm hmax => liveOn_of_headsRun getLeader hk m hm hmax hD hw hheads

/-- **Round-robin meets the heads-run hypothesis** once the committee bound
`waveLength * slack + 1 ≤ n` holds, at gap `n + waveLength - 1`. -/
theorem runsExist_roundRobin {n : ℕ} (hn : 0 < n) {BlockId Payload : Type}
    [DecidableEq BlockId] (R : LiveRule (Fin n) BlockId Payload) {slack : ℕ}
    (hagree : Properties.Agree R.toBaseRule.toDagRule) (hD : R.Descent slack)
    (hw : 0 < R.waveLength) (hbound : R.waveLength * slack + 1 ≤ n)
    (P : Params) (hk : Keyed (roundRobin n hn) P.maxLeaders)
    (upd : UpdateRule R.toBaseRule) (hbnd : UpdBounded P upd) :
    RunsExist R P (roundRobin n hn) hk upd (n + R.waveLength - 1) :=
  holds (Fin n) BlockId Payload R slack _ (roundRobin n hn) hagree hD hw
    (fun T hT => roundRobin_headsRun n hn T slack R.waveLength (by simpa using hT) hbound)
    P hk upd hbnd

end Live

end Barnacle

end LeanDag
