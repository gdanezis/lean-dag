import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Helpers.DagRule
/-!
# AL13 — the segmented configuration sequence is agreed

Safety for a run whose output stops at each configuration's boundary
while its decisions reach the anchor that closes the span
(`adaptive-leaders.md` §9): two validators adopt the same sequence of
configurations and the same verdicts, for **any update rule** that does
not read the view, with no synchrony, fairness or window hypothesis.

* **AL13, segmented runs agree** — two runs closed to any two heights,
  over any two views, from one genesis configuration, agree on every
  configuration up to the lower height and on every verdict each has
  decided.

The anchors need no hypothesis relating them. Each run reaches its own,
and the lesser of the two lies inside the other's reach by
`Config.roundOf_mono`, where that run's `anchor_least` makes it a skip
and the first run's `anchor_commits` makes it a commit.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Adaptive

namespace Agreement

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **AL13, segmented runs agree.** Two runs over one universe from one
genesis configuration — whatever views, whatever heights `K₁`, `K₂` —
agree on `start`, `cfg` and `backoff` up to `min K₁ K₂`, and below it on
the anchor and on every verdict of the decided span. The span is the
rounds after `start k` through the anchor's own round, which reaches past
the boundary `start (k + 1)` that bounds the output. -/
def SegRunAgreement (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) : Prop :=
  -- One universe and one genesis configuration; two validators, holding
  -- views `V₁` and `V₂` of it, whose runs are closed up to heights `K₁`
  -- and `K₂`.
  Anchored R upd →
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : SegRun R P upd C₀ U V₁ K₁) (R₂ : SegRun R P upd C₀ U V₂ K₂),
    -- For every configuration both have reached …
    ∀ k, k ≤ min K₁ K₂ →
      -- … they agree on when it takes force, on the configuration itself,
      -- and on its back-off.
      R₁.start k = R₂.start k ∧ R₁.cfg k = R₂.cfg k ∧ R₁.backoff k = R₂.backoff k ∧
      -- And for every configuration both have *closed* — found its anchor —
      (k < min K₁ K₂ →
        -- they agree on which slot the anchor is …
        R₁.anchor k = R₂.anchor k ∧
        -- … and on the verdict of every slot of the decided span: rounds
        -- after `start k`, through the anchor's own round.
        ∀ κ, R₁.start k < (R₁.cfg k).roundOf κ →
          (R₁.cfg k).roundOf κ ≤ (R₁.cfg k).roundOf (R₁.anchor k) →
            R₁.vdct k κ = R₂.vdct k κ)

/-- Agreement of the segmented configuration sequence and the verdicts,
for every base rule with agreement, every parameter set, every genesis
configuration and **every update rule**. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload),
    Properties.Agree R.toDagRule →
    ∀ (P : Params) (upd : UpdateRule R) (C₀ : Config Validator),
      SegRunAgreement R P upd C₀

end Agreement

end Adaptive

end LeanDag
