import LeanDag.Barnacle.Live.Statement
import LeanDag.Barnacle.Progress.Proof
import LeanDag.Barnacle.Mysticeti.Proof
import LeanDag.Barnacle.MysticetiLive.Proof
import LeanDag.Barnacle.Odontoceti.Proof
import LeanDag.Barnacle.Nemo.Proof
/-!
# BN11 — proof

Generated proof layer; not part of the audit surface. `generic_holds` is
BN8b with its liveness clause discharged from a schedule's heads runs; each
conjunct is that theorem at one rule, under round-robin.
-/

namespace LeanDag

namespace Barnacle

namespace Live

theorem generic_holds : GenericStatement := by
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
  generic_holds (Fin n) BlockId Payload R slack _ (roundRobin n hn) hagree hD hw
    (fun T hT => roundRobin_headsRun n hn T slack R.waveLength (by simpa using hT) hbound)
    P hk upd hbnd

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn F BlockId Payload _ P hk upd hbnd
    have hbound : 3 * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      omega
    exact runsExist_roundRobin hn _ MysticetiProperties.agree
      (MysticetiLive.descent (Fin n) BlockId Payload) (Nat.succ_pos 2) hbound P hk upd hbnd
  · intro n hn F BlockId Payload _ P hk upd hbnd
    have hbound : 2 * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      omega
    exact runsExist_roundRobin hn _ OdontocetiProperties.agree
      (Odontoceti.descent (Fin n) BlockId Payload) (Nat.succ_pos 1) hbound P hk upd hbnd
  · intro n hn C BlockId Payload _ P hk upd hbnd
    have hbound : 2 * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n)) + 1 ≤ n := by
      rw [Fintype.card_fin]
      exact Nemo.majority_bound n hn
    exact runsExist_roundRobin hn _ NemoProperties.agree
      (Nemo.descent (Fin n) BlockId Payload) (Nat.succ_pos 1) hbound P hk upd hbnd

end Live

end Barnacle

end LeanDag
