import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Hybrid.Carrier
/-!
# Barnacle over Orcaella — statement

The hybrid two-round rule at `n ≥ 5·fb + 3·fc + 1` (`LeanDag/Hybrid/`)
as a base rule with its laws, as a live rule with its descent laws at
slack `fb + fc`, and A4 for it under round-robin with gap `n + 1`. The
universes are the records satisfying `HonestNoEquiv`, the hypothesis of
every hybrid safety theorem, for which the interface has no slot. Every
statement is parameterized by an admissible indirect threshold `k`
(`Hybrid.Admissible`), whose interval's nonemptiness is the committee
bound. Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Orcaella as a base rule**, at indirect threshold `k`. -/
def orcaella [HybridFaults Validator] (k : ℕ) : BaseRule Validator BlockId Payload :=
  ofAnchoredOn (Hybrid.hybridAnchored Validator BlockId Payload k) HonestNoEquiv

/-- **Orcaella as a live rule**, at the derived fault model. -/
def orcaellaLive [HybridFaults Validator] (k : ℕ) : LiveRule Validator BlockId Payload :=
  liveOfAnchoredOn (Hybrid.hybridAnchored Validator BlockId Payload k) HonestNoEquiv
    (coreReliability Validator)

namespace Orcaella

/-- **Orcaella satisfies the laws** at every admissible threshold. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [HybridFaults Validator] [LinearOrder BlockId] (k : ℕ),
    Hybrid.Admissible Validator k →
    BaseRule.Laws (orcaella (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k)

/-- **Orcaella has the descent laws at slack `fb + fc`**, consuming no
admissibility. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [H : HybridFaults Validator] [LinearOrder BlockId] (k : ℕ),
    Hybrid.Admissible Validator k →
    (orcaellaLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k).Descent
      (H.fb + H.fc)

/-- **Orcaella under round-robin is live at every count**, with gap
`n + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [HybridFaults (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (k : ℕ), Hybrid.Admissible (Fin n) k →
    ∀ (C : Config (Fin n)) (hC : C.head = roundRobin n hn),
    (orcaellaLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload) k).LiveOn
      C.sched (n + 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end Orcaella

end Barnacle

end LeanDag
