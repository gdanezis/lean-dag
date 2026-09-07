import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Hybrid.Carrier
/-!
# Barnacle over Orcaella — statement

The hybrid two-round rule at `n ≥ 5·fb + 3·fc + 1` (`LeanDag/Hybrid/`;
the paper's Orcaella) as a base rule with its laws, as a live rule with
its descent laws at slack `fb + fc`, and the paper's A4 for it under
round-robin: live at every leader count with gap `n + 1`. The mixed
bound enters only through the reliable set — the fully-correct class,
which carries the hybrid quorum `q = n − fb − fc`.

Two points where the instantiation carries the hybrid model's shape:

* **The universe bundles `HonestNoEquiv`.** The hybrid model's one
  genuinely new assumption — a crash-prone validator authors at most
  one block per round too — is a hypothesis of every hybrid safety
  theorem, and the interface's `agree` law has no slot for it. The rule
  is therefore `ofAnchoredOn` at that invariant: the universes are the
  records satisfying it, which is the interface's design — the fault
  class lives on the instantiation, never on the interface.
* **The indirect threshold is a parameter.** The hybrid indirect rule
  works at any `k` in the admissible interval
  `2·fb + fc + 1 ≤ k ≤ n − 3·fb − 2·fc`, whose nonemptiness *is* the
  committee bound, so every statement below is parameterized by an
  admissible `k`. The paper's link size is the top end
  `kRel = n − 3·fb − 2·fc` (`Hybrid.admissible_kRel`); setting `fc = 0`
  recovers Odontoceti's committee (`Hybrid/Conservativity.lean`).

The ids carry a linear order, which the indirect rule uses to commit
the least candidate that passes its test.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Orcaella as a base rule**, at indirect threshold `k`: the hybrid
anchored rule over the universes whose honest class — crash-prone
validators included — does not equivocate. -/
def orcaella [HybridFaults Validator] (k : ℕ) : BaseRule Validator BlockId Payload :=
  ofAnchoredOn (Hybrid.hybridAnchored Validator BlockId Payload k) HonestNoEquiv

/-- **Orcaella as a live rule**, at the derived fault model: `Correct` is
the fully-correct class and the quorum is `n − fb − fc`. -/
def orcaellaLive [HybridFaults Validator] (k : ℕ) : LiveRule Validator BlockId Payload :=
  liveOfAnchoredOn (Hybrid.hybridAnchored Validator BlockId Payload k) HonestNoEquiv
    (coreReliability Validator)

namespace Orcaella

/-- **Orcaella satisfies the laws** at every admissible threshold:
agreement is the hybrid safety theorem, consuming the bundled
`HonestNoEquiv` and the admissibility of `k`. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [HybridFaults Validator] [LinearOrder BlockId] (k : ℕ),
    Hybrid.Admissible Validator k →
    BaseRule.Laws (orcaella (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k)

/-- **Orcaella has the descent laws at slack `fb + fc`**: the direct
commit of a good leader's slot needs only the reliable set — this is
the one place the mixed bound enters — and the indirect rule commits
the least candidate with a `k`-thick link, or skips. -/
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
    ∀ (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (orcaellaLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload) k).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 1)

/-- The laws, the descent laws, and liveness under round-robin — each
at every admissible threshold. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end Orcaella

end Barnacle

end LeanDag
