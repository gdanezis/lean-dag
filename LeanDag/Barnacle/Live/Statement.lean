import LeanDag.Barnacle.Progress.Statement
import LeanDag.Barnacle.Model.Heads
/-!
# BN11 — the mechanism over any rule, end to end

BN8b gives runs of every height *given* the liveness clause; this file
discharges the clause. `RunsExist` is BN8b's consequent assumed of
nothing, and `Statement` says a rule reaches it whenever it has
agreement and the descent laws and its schedule's good leaders come in
runs of a wave. Round-robin is one such schedule, at gap
`n + waveLength - 1` under the committee bound
`waveLength * slack + 1 ≤ n` (`Proof.lean`).

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Live

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Runs of every height, with no clause left over.** BN8b's
conclusion: on a DAG good from genesis, every height whose horizon fits
under `N` is reached — on any view caught up to `N`, which is what a
validator that has received everything up to the horizon holds. -/
def RunsExist (R : LiveRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R.toBaseRule) (c : ℕ) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N →
    R.toBaseRule.CoversUpto U V N → Rnd ≤ 1 →
    ∀ K, horizon P R c K ≤ N →
      Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V K)

/-- **BN11 — every height, for any rule and any schedule.** A rule with
agreement and the descent laws reaches every height under a schedule whose
good leaders come in runs of a wave; the gap is the schedule's own `c₀`. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload) (slack c₀ : ℕ)
    (getLeader : ℕ → Validator),
    Properties.Agree R.toBaseRule.toDagRule →
    R.Descent slack → 0 < R.waveLength →
    (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun getLeader T R.waveLength c₀) →
    ∀ (P : Params) (hk : Keyed getLeader P.maxLeaders) (upd : UpdateRule R.toBaseRule),
      UpdBounded P upd →
      RunsExist R P getLeader hk upd c₀


end Live

end Barnacle

end LeanDag
