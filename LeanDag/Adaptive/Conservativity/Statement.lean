import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Helpers.DagRule
/-!
# AL15 — conservativity

Under the constant rule the segmented arc collapses onto the genesis
configuration `C₀` (`adaptive-leaders.md` §9): every configuration is
that one, and every verdict of a run is a verdict of `C₀.sched`. The
constant score **is** the constant rule (`Score.rule_const`), so this is
what a score that reassigns nothing does.

* **AL15a, the configuration never moves** — `cfg k = C₀` and
  `backoff k = 0` at every configuration the run determines.
* **AL15b, the verdicts are the base verdicts** — every verdict of the
  decided span is derived against `C₀.sched`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Adaptive

namespace Conservativity

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **AL15a, the configuration never moves** under the constant rule. -/
def ConstConfig (R : BaseRule Validator BlockId Payload) (P : Params)
    (C₀ : Config Validator) : Prop :=
  -- Any run — any universe, any view, any height — whose update rule is
  -- `constRule`, the rule that returns the configuration and back-off it
  -- was given.
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : SegRun R P (constRule R) C₀ U V K),
    -- Every configuration the run determines — `0` to `K` — is the initial
    -- one. (Above `K` the run holds no data.)
    ∀ k, k ≤ K → Rn.cfg k = C₀ ∧ Rn.backoff k = 0

/-- **AL15b, the verdicts are the base verdicts**: every verdict of a run
under the constant rule is a verdict of the initial schedule. -/
def ConstDecided (R : BaseRule Validator BlockId Payload) (P : Params)
    (C₀ : Config Validator) : Prop :=
  -- The same runs.
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : SegRun R P (constRule R) C₀ U V K),
    -- For every closed configuration `k` and every slot `κ` of its range —
    -- the slots whose round lies after `start k` and at or before the
    -- anchor's —
    ∀ k, k < K → ∀ κ, Rn.start k < C₀.roundOf κ → C₀.roundOf κ ≤ C₀.roundOf (Rn.anchor k) →
      -- the run's verdict is a verdict of the initial schedule, which is
      -- the base development's own whenever that configuration is uniform
      -- at one leader.
      R.Decided C₀.sched V κ (Rn.vdct k κ)

/-- Conservativity, for every base rule and parameter set. No law of the
rule is consumed. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload) (P : Params)
    (C₀ : Config Validator),
    ConstConfig R P C₀ ∧ ConstDecided R P C₀


end Conservativity

end Adaptive

end LeanDag
