import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Odontoceti.Carrier
/-!
# Barnacle over Odontoceti — statement

The two-round rule at `n ≥ 5f + 1` (report §10) as a base rule with its
laws, as a live rule with its descent laws at slack `f`, and A4 for it
under round-robin with gap `n + 1`. The ids carry a linear order, for the
indirect rule's tie-break. Statements only; the proofs live in
`Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Odontoceti as a base rule**: its anchored rule. -/
def odontoceti [Faults5 Validator] : BaseRule Validator BlockId Payload :=
  ofAnchored (Odontoceti.odontocetiAnchored Validator BlockId Payload)

/-- **Odontoceti as a live rule**, at the core's fault model. -/
def odontocetiLive [Faults5 Validator] : LiveRule Validator BlockId Payload :=
  liveOfAnchored (Odontoceti.odontocetiAnchored Validator BlockId Payload)
    (coreReliability Validator)

namespace Odontoceti

/-- **Odontoceti satisfies the laws**: O5 is the agreement law. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId],
    BaseRule.Laws (odontoceti (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

/-- **Odontoceti has the descent laws at slack `f`.** -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults5 Validator] [LinearOrder BlockId],
    (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **Odontoceti under round-robin is live at every count**, with gap
`n + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults5 (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (C : Config (Fin n)) (hC : C.head = roundRobin n hn),
    (odontocetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      C.sched (n + 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end Odontoceti

end Barnacle

end LeanDag
