import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Nemo.Carrier
import LeanDag.Nemo.Liveness
/-!
# Barnacle over Nemo-Nemo — statement

The crash-fault rule at a bare majority (report §15) as a base rule with
its laws — safety needs no fault class — as a live rule whose good DAGs
are any synchronised, populated majority, with its descent laws at slack
`n − majority`, and A4 for it under round-robin with gap `n + 1` at every
`n`. The crash bound is what makes `Good` satisfiable, and is consumed
nowhere else. Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Nemo-Nemo as a base rule**, with no fault class. -/
def nemo : BaseRule Validator BlockId Payload :=
  ofAnchored (Nemo.nemoAnchored Validator BlockId Payload)

/-- **Nemo-Nemo as a live rule**, at Nemo's fault model. -/
def nemoLive [Nemo.CrashFaults Validator] : LiveRule Validator BlockId Payload :=
  liveOfAnchored (Nemo.nemoAnchored Validator BlockId Payload)
    (NemoProperties.nemoReliability Validator Nemo.CrashFaults.card_pos)

namespace Nemo

/-- **Nemo-Nemo satisfies the laws**, with no fault class in sight. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId],
    BaseRule.Laws (nemo (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

/-- **Nemo-Nemo has the descent laws at slack `n − majority`**, what a
majority may miss: `f` at `n = 2f + 1`, more above the bound. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LeanDag.Nemo.CrashFaults Validator] [DecidableEq BlockId],
    (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      (Fintype.card Validator - LeanDag.Nemo.majority Validator)

/-- **Nemo-Nemo under round-robin is live at every count**, with gap
`n + 1`, at every `n`. -/
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
