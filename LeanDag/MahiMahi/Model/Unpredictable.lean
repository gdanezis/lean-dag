import LeanDag.MahiMahi.Model.Good
/-!
# Mahi-Mahi — the unpredictable-leader clause

The hypothesis under which the rule is live with no network assumption
(`mahi-mahi.md` §5): in every stretch of `c` consecutive waves, the
schedule names a validator whose block the DAG actually committed. It
relates the schedule to the DAG rather than fixing a target set, since
under asynchrony only the DAG's shape guarantees a commit. Both the
single-hit and run forms quantify only below a horizon `N`, since
`good` is empty past some round in any finite DAG. Definitions only.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Two universes agree up to round `d`**: the same ids at rounds `≤ d`,
denoting the same blocks — what MM2′ consumes, since `good` at a wave is
fixed by the rounds up to its decision round. -/
structure AgreeUpto (U₁ U₂ : BlockUniverse Validator BlockId Payload) (d : ℕ) : Prop where
  /-- The ids at rounds `≤ d` coincide. -/
  ids : ∀ i, (i ∈ U₁.ids ∧ (U₁.block i).round ≤ d) ↔ (i ∈ U₂.ids ∧ (U₂.block i).round ≤ d)
  /-- And they denote the same blocks. -/
  block : ∀ i ∈ U₁.ids, (U₁.block i).round ≤ d → U₁.block i = U₂.block i

section Slots

variable [S : Slots Validator]

/-- **The single-hit form.** In every window of `c` slots whose decision
rounds lie below the horizon `N`, the schedule names a committed
candidate at least once. -/
def UnpredictableWithin (U : BlockUniverse Validator BlockId Payload)
    (w c N : ℕ) : Prop :=
  ∀ k,
    -- the window's last decision round lies below the horizon
    (mahiMahiAnchored Validator BlockId Payload w).decisionRound (k + c) ≤ N →
    -- some slot of the window is led by a validator whose block commits
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U w k'

/-- **The run form.** In every window of `c` slots below the horizon, a
run of `d` consecutive slots whose leaders are all committed candidates.
The bound reads the last slot of the latest possible run, `k + c + d − 1`,
so that small universes are not vacuously covered. -/
def UnpredictableRunWithin (U : BlockUniverse Validator BlockId Payload)
    (w c d N : ℕ) : Prop :=
  ∀ k,
    -- the latest run's last decision round lies below the horizon
    (mahiMahiAnchored Validator BlockId Payload w).decisionRound (k + c + d - 1) ≤ N →
    -- some run of d slots starting in the window is led by committed candidates
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ good U w (k' + i)

/-! A run of `c` slots spanning eligibility — every slot below its start
eligible for its last slot — is the relation's `SpansEligible` at wave
`w`; at one leader per round it holds for `c = w`. -/

end Slots

end MahiMahi

end LeanDag
