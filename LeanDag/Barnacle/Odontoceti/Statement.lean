import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Odontoceti.Carrier
/-!
# Barnacle over Odontoceti — statement

The two-round rule at `n ≥ 5f + 1` (report §10; the paper's Blue
Bottle) as a base rule with its laws, as a live rule with its descent
laws at slack `f`, and the paper's A4 for it under round-robin: live at
every leader count with gap `n + 1`. Both are `ofAnchored` at
`odontocetiAnchored`; the ids carry a linear order, which the indirect
rule uses to commit the least candidate that passes its test, and which
supplies the interface's decidable equality.
Statements only; the proofs live in `Proof.lean`.
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

/-- **Odontoceti has the descent laws at slack `f`**: O7 is the direct
commit of a good leader's slot; the indirect rule commits the least
candidate with a thick link, or skips. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults5 Validator] [LinearOrder BlockId],
    (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **Odontoceti under round-robin is live at every count**, with gap
`n + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults5 (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (odontocetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end Odontoceti

end Barnacle

end LeanDag
