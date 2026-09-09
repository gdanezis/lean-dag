import LeanDag.Adaptive.Basic
import LeanDag.Properties.Carrier
/-!
# The adaptive policy

The reassignment rule, packaged with the clauses it owes. `pick` maps
the universe and a verdict function to a leader assignment; `adapted` is
the measurability clause — the leader of slot `k` is a function of the
verdicts of epochs `≤ epochOf k − 2` and of nothing else, the view
included, and it is the whole of what safety consumes. The lag of two
is the least that makes the adaptive fixpoint well-founded (`adaptive-leaders.md`
§2); `base_prefix` pins epochs `0` and `1` to the base schedule, since
epoch `2` is the first with a two-epoch-old prefix to read. The policy
reads a protocol's carrier only, so it is stated over
`Properties.DagRule`; a rule's own `AdaptivePolicy` is this structure at
its carrier, and lives with the pairing in `Integration/`.
-/

namespace LeanDag

namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- A Hammerhead-style reassignment policy over a carrier: epoch length,
the rule, and the clauses it owes. Fairness is deliberately not here:
safety must hold for arbitrary, even adversarial, adapted policies. -/
structure Policy (R : DagRule Validator BlockId Payload) [S : Slots Validator] where
  /-- The epoch length, in slots. -/
  W : ℕ
  W_pos : 0 < W
  /-- One leader per round, for the whole arc. -/
  inj : Function.Injective S.slotRound
  /-- The reassignment rule: from the universe, the validator's view of
  it and a verdict function, the leader of each slot. -/
  pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator
  /-- **Adaptedness.** The leader of slot `k` reads the verdicts of
  epochs `≤ epochOf k − 2` and nothing else — not the view either. -/
  adapted : ∀ (U : R.Universe) (V₁ V₂ : R.View U) v w k,
    (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
    pick U V₁ v k = pick U V₂ w k
  /-- Epochs `0` and `1` run the base schedule. -/
  base_prefix : ∀ (U : R.Universe) (V : R.View U) v k, epochOf W k < 2 →
    pick U V v k = S.leader k

namespace Policy

variable {R : DagRule Validator BlockId Payload} [S : Slots Validator]

/-- The constant policy: reassign nothing. The conservativity anchor —
under it the adaptive development must collapse onto the base one. -/
def const (W : ℕ) (hW : 0 < W) (hinj : Function.Injective S.slotRound) : Policy R where
  W := W
  W_pos := hW
  inj := hinj
  pick _ _ _ k := S.leader k
  adapted _ _ _ _ _ _ _ := rfl
  base_prefix _ _ _ _ _ := rfl

@[simp] theorem const_pick (W : ℕ) (hW : 0 < W) (hinj : Function.Injective S.slotRound)
    (U : R.Universe) (V : R.View U) (v : ℕ → Option BlockId) (k : ℕ) :
    (const (R := R) W hW hinj).pick U V v k = S.leader k := rfl

end Policy

end Adaptive

end LeanDag
