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
  intro Validator BlockId Payload _ _ _ R slack c₀ head hagree hD hw hheads P B upd hbnd hbh C₀ hC₀
  intro h₀ U V Rnd N hgood
  exact (Progress.holds Validator BlockId Payload R hagree P B upd hbnd C₀ _ hbh c₀).2
    (fun C _ hCh => liveOn_of_headsRun C hD hw (by rw [hCh]; exact hheads)) h₀ hC₀ U V Rnd N
    (fun C hC _ => hgood C hC)

theorem holdsFrom : StatementFrom := by
  intro Validator BlockId Payload _ _ _ R slack c₀ head hagree hD hw hheads P B upd hbnd hbh C₀ δ
    h₀ hQ₀ U V N hcov hgood K hK
  obtain ⟨Rn, -, -⟩ := everyHeight_from (Q := fun C => C.head = head) hagree hbnd hbh
    (fun C _ hCh => liveOn_of_headsRun C hD hw (by rw [hCh]; exact hheads))
    (fun C _ hCh => settlesBelow_of_headsRun C hD hw (by rw [hCh]; exact hheads))
    h₀ hQ₀ hcov hgood K hK
  exact ⟨Rn⟩

/-- **Round-robin meets the heads-run hypothesis** once the committee bound
`waveLength * slack + 1 ≤ n` holds, at gap `n + waveLength - 1`. -/
theorem runsExist_roundRobin {n : ℕ} (hn : 0 < n) {BlockId Payload : Type}
    [DecidableEq BlockId] (R : LiveRule (Fin n) BlockId Payload) {slack : ℕ}
    (hagree : Properties.Agree R.toBaseRule.toDagRule) (hD : R.Descent slack)
    (hw : 0 < R.waveLength) (hbound : R.waveLength * slack + 1 ≤ n)
    (P : Params) (B : Boundary (Fin n)) (upd : UpdateRule R.toBaseRule)
    (hbnd : UpdBounded P upd) (hbh : UpdKeeps upd (fun C => C.head = roundRobin n hn))
    (C₀ : Config (Fin n)) (hC₀ : C₀.head = roundRobin n hn) :
    RunsExist R P B upd C₀ (n + R.waveLength - 1) :=
  holds (Fin n) BlockId Payload R slack _ (roundRobin n hn) hagree hD hw
    (fun T hT => roundRobin_headsRun n hn T slack R.waveLength (by simpa using hT) hbound)
    P B upd hbnd hbh C₀ hC₀

end Live

end Barnacle

end LeanDag
