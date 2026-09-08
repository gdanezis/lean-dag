import LeanDag.Barnacle.Model.Window
/-!
# BN2 — the window is agreed

The paper's Window Agreement lemma (`barnacle.md` §6): two honest
validators that commit the anchor compute the same window. The window a
validator measures on is the anchor's causal history, determined by the
anchor alone — whichever view holds the anchor holds its whole history,
by A2 (`DagRule.viewComplete`) — so restricting it to two different
views yields one set. A field of the carrier rather than a law, so this
holds of every rule.

* **BN2a, the history is in view** — a view holding `A` holds
  `historyFrom (block U) A`.
* **BN2b, window agreement** — two views holding `A` restrict its history
  to the same set.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Window

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN2a, the history is in view**: a view holding a block holds its
whole causal history. A2 is what carries it — views are closed under
references, and the history is what references reach. -/
def HistoryInView (R : BaseRule Validator BlockId Payload) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (A : BlockId),
    A ∈ R.viewIds V → historyFrom (R.block U) A ⊆ R.viewIds V

/-- **BN2b, window agreement**: two validators holding the anchor compute
the same window — the anchor's history restricted to either view is the
history itself, so the two restrictions coincide. -/
def WindowAgreement (R : BaseRule Validator BlockId Payload) : Prop :=
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (A : BlockId),
    A ∈ R.viewIds V₁ → A ∈ R.viewIds V₂ →
    historyFrom (R.block U) A ∩ R.viewIds V₁ = historyFrom (R.block U) A ∩ R.viewIds V₂

/-- **The window is agreed, for every base rule** — no laws and no
properties: closure is a field of the carrier
(`Properties.DagRule.viewComplete`), which every view type already
carries. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload),
    HistoryInView R ∧ WindowAgreement R

end Window

end Barnacle

end LeanDag
