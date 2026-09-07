import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Nemo.Carrier
import LeanDag.Nemo.Liveness
/-!
# Barnacle over Nemo-Nemo — statement

The crash-fault rule at a bare majority, `n ≥ 2f + 1` (report §15), as
a base rule with its laws — its safety needs no fault class at all — as
a live rule whose good DAGs are `Timed.Good` at Nemo's fault model — any
synchronised, populated majority, the reliable set being everyone — with
its descent laws at the slack such a majority may miss, `n − majority`,
and the paper's A4 for it under round-robin: live at every leader count
with gap `n + 1`, at every `n`. The crash bound is consumed nowhere in
the proofs; it is what makes `Good` satisfiable, the live set being a
majority. Both rules are `ofAnchored` at `nemoAnchored`.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Nemo-Nemo as a base rule**: its anchored rule. No fault class: the
crash-fault universe's safety needs none. -/
def nemo : BaseRule Validator BlockId Payload :=
  ofAnchored (Nemo.nemoAnchored Validator BlockId Payload)

/-- **Nemo-Nemo as a live rule**, at Nemo's fault model: a DAG is good
when a majority is synchronised from `Rnd` and populates the rounds to
`N`. -/
def nemoLive [Nemo.CrashFaults Validator] : LiveRule Validator BlockId Payload :=
  liveOfAnchored (Nemo.nemoAnchored Validator BlockId Payload)
    (NemoProperties.nemoReliability Validator Nemo.CrashFaults.card_pos)

namespace Nemo

/-- **Nemo-Nemo satisfies the laws**, with no fault class in sight. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId],
    BaseRule.Laws (nemo (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

/-- **Nemo-Nemo has the descent laws at the slack a majority may miss**,
`n − majority`: its good set is any synchronised majority, which misses
`n − majority` validators — at `n = 2f + 1` exactly `f`, and more above
the bound. The crash bound enters liveness only through `Good` being
satisfiable, the live set being a majority. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LeanDag.Nemo.CrashFaults Validator] [DecidableEq BlockId],
    (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      (Fintype.card Validator - LeanDag.Nemo.majority Validator)

/-- **Nemo-Nemo under round-robin is live at every count**, with gap
`n + 1`, for every `n`: the pigeonhole's bound `2 · (n − majority) + 1 ≤ n`
holds unconditionally. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [LeanDag.Nemo.CrashFaults (Fin n)] (BlockId Payload : Type)
    [DecidableEq BlockId] (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m)
    (hmax : m ≤ w),
    (nemoLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end Nemo

end Barnacle

end LeanDag
