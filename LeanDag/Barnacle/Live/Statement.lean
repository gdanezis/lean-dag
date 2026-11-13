import LeanDag.Barnacle.Progress.Statement
import LeanDag.Barnacle.Model.Heads
/-!
# BN11 — the mechanism over any rule, end to end

BN8b gives runs of every height *given* the liveness clause; this file
discharges the clause. `RunsExist` is BN8b's consequent assumed of
nothing but the genesis bounds, and `Statement` says a rule reaches it
whenever it has agreement and the descent laws and the heads of its
configurations' rounds come in runs of a wave. Round-robin is one such schedule, at gap
`n + waveLength - 1` under the committee bound
`waveLength * slack + 1 ≤ n` (`Proof.lean`).

`RunsExistFrom` is the same consequent when a configuration's schedule is
good only `δ` rounds after its start, its validators not yet knowing it
before, and only up to the round its step needs, unless the run has
already moved past it; `StatementFrom` says the same rules reach it.

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
    (B : Boundary Validator) (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator)
    (c : ℕ) : Prop :=
  C₀.InBounds P →
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ),
    (∀ C : Config Validator, C.InBounds P → R.Good C.sched U Rnd N) →
    R.toBaseRule.CoversUpto U V N → Rnd ≤ 1 →
    ∀ K, horizon P R c K ≤ N →
      Nonempty (Run R.toBaseRule P B upd C₀ U V K)

/-- **BN11 — every height, for any rule and any schedule.** A rule with
agreement and the descent laws reaches every height under a schedule whose
good leaders come in runs of a wave; the gap is the schedule's own `c₀`. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload) (slack c₀ : ℕ)
    (head : ℕ → Validator),
    Properties.Agree R.toBaseRule.toDagRule →
    R.Descent slack → 0 < R.waveLength →
    (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun head T R.waveLength c₀) →
    ∀ (P : Params) (B : Boundary Validator) (upd : UpdateRule R.toBaseRule),
      UpdBounded P upd → UpdKeeps upd (fun C => C.head = head) →
      -- on a genesis configuration whose heads are the schedule's
      ∀ C₀ : Config Validator, C₀.head = head → RunsExist R P B upd C₀ c₀



/-- **Runs of every height, each configuration's schedule good from `δ`
past its start.** The goodness asked of a run of height `K` whose current
configuration meets `Q`: its schedule is good from `δ` past its start up
to the round its step needs, or the run already extends past it. -/
def RunsExistFrom (R : LiveRule Validator BlockId Payload) (P : Params)
    (B : Boundary Validator) (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator)
    (Q : Config Validator → Prop) (c δ : ℕ) : Prop :=
  C₀.InBounds P → Q C₀ →
  ∀ (U : R.Universe) (V : R.View U) (N : ℕ), R.toBaseRule.CoversUpto U V N →
    (∀ K (Rn : Run R.toBaseRule P B upd C₀ U V K), Q (Rn.cfg K) →
      R.Good (Rn.cfg K).sched U (Rn.start K + δ)
          (Rn.start K + max (P.maxInterval + 1) δ + 2 * c + R.waveLength) ∨
        ∃ Rn' : Run R.toBaseRule P B upd C₀ U V (K + 1),
          Rn'.start (K + 1) ≤ Rn.start K + max (P.maxInterval + 1) δ + c ∧
            Q (Rn'.cfg (K + 1))) →
    ∀ K, horizonFrom P R c δ K ≤ N → Nonempty (Run R.toBaseRule P B upd C₀ U V K)

/-- **BN11 with a learning delay**: the same rules reach every height when
each configuration's schedule is good only from `δ` past its start. -/
def StatementFrom : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload) (slack c₀ : ℕ)
    (head : ℕ → Validator),
    Properties.Agree R.toBaseRule.toDagRule →
    R.Descent slack → 0 < R.waveLength →
    (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun head T R.waveLength c₀) →
    ∀ (P : Params) (B : Boundary Validator) (upd : UpdateRule R.toBaseRule),
      UpdBounded P upd → UpdKeeps upd (fun C => C.head = head) →
      ∀ (C₀ : Config Validator) (δ : ℕ),
        RunsExistFrom R P B upd C₀ (fun C => C.head = head) c₀ δ

end Live

end Barnacle

end LeanDag
