import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.FinWhale.Carrier
/-!
# Barnacle over FinWhale — statement

FinWhale as a base rule with its laws, as a live rule with its descent
laws at slack `f`, and A4 for it under round-robin. Both are
`ofAnchored` at `finWhaleAnchored`: the universe is FinWhale's own
`Dag`, the wave length three — what the rule's eligibility reads — and
the direct predicate `DirectCommit`, as a view evaluates it.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **FinWhale as a base rule**: its anchored rule. -/
def finWhale : BaseRule Validator BlockId Payload :=
  ofAnchored (LeanDag.FinWhale.finWhaleAnchored Validator BlockId Payload)

/-- **FinWhale as a live rule**, at the core's fault model. -/
def finWhaleLive : LiveRule Validator BlockId Payload :=
  liveOfAnchored (LeanDag.FinWhale.finWhaleAnchored Validator BlockId Payload)
    (coreReliability Validator)

namespace FinWhale

/-- **FinWhale satisfies the laws.** -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LeanDag.FinWhale.Params Validator] [LinearOrder BlockId],
    BaseRule.Laws (finWhale (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

/-- **FinWhale has the descent laws at slack `f`.** -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LeanDag.FinWhale.Params Validator] [LinearOrder BlockId],
    (finWhaleLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **FinWhale under round-robin is live at every count**, with gap `n + 2`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)] [LeanDag.FinWhale.Params (Fin n)]
    (BlockId Payload : Type) [LinearOrder BlockId]
    (W : ℕ) (hk : Keyed (roundRobin n hn) W) (m : ℕ) (hm : 0 < m) (hmax : m ≤ W),
    (finWhaleLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 2)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end FinWhale

end Barnacle

end LeanDag
