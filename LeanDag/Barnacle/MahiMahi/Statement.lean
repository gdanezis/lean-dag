import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.MahiMahi.Carrier
/-!
# Barnacle over Mahi-Mahi — statement

The wave-`w` rule as a base rule with its laws, as a live rule with its
descent laws at slack `f`, and A4 for it under round-robin. The
committee bound round-robin needs, `w · f + 1 ≤ n`, is a hypothesis: the
fault model gives `3f + 1 ≤ n`, and a longer wave asks for more.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Mahi-Mahi as a base rule**, at wave `w`. -/
def mahiMahi [Faults Validator] (w : ℕ) : BaseRule Validator BlockId Payload :=
  ofAnchored (MahiMahi.mahiMahiAnchored Validator BlockId Payload w)

/-- **Mahi-Mahi as a live rule**, at the core's fault model. -/
def mahiMahiLive [Faults Validator] (w : ℕ) : LiveRule Validator BlockId Payload :=
  liveOfAnchored (MahiMahi.mahiMahiAnchored Validator BlockId Payload w)
    (coreReliability Validator)

namespace MahiMahi

/-- **Mahi-Mahi satisfies the laws** at every wave of length at least two. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (w : ℕ), 2 ≤ w →
    BaseRule.Laws (mahiMahi (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)

/-- **Mahi-Mahi has the descent laws at slack `f`**, at every wave of
length at least four — the length its support's coverage law needs. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] (w : ℕ), 4 ≤ w →
    (mahiMahiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w).Descent
      F.f

/-- **Mahi-Mahi under round-robin is live at every count**, with gap
`n + w − 1`, on a committee of at least `w · f + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (w : ℕ), 4 ≤ w → w * F.f + 1 ≤ n →
    ∀ (W : ℕ) (hk : Keyed (roundRobin n hn) W) (m : ℕ) (hm : 0 < m) (hmax : m ≤ W),
    (mahiMahiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload) w).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + w - 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end MahiMahi

end Barnacle

end LeanDag
