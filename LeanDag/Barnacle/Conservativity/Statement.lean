import LeanDag.Barnacle.Model.Run
/-!
# BN6 — conservativity

Under the constant rule the arc collapses onto the base development at
one leader (`barnacle.md` §6): every configuration has the initial
count and back-off, and every verdict of a run is a verdict of the
one-leader schedule `Sched 1`.

* **BN6a, the count never moves** — under `constRule`, `count k = 1` and
  `backoff k = 0` at every configuration the run determines, `k ≤ K`.
* **BN6b, the verdicts are the base verdicts** — every verdict of the run
  is derived against `Sched 1`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Conservativity

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN6a, the count never moves** under the constant rule. -/
def ConstCount (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  -- Any run — any universe, any view, any height — whose update rule is
  -- `constRule`, the rule that returns the count and back-off it was given.
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : PartialRun R P getLeader hk (constRule R) U V K),
    -- Every configuration the run determines — `0` to `K` — is the initial
    -- one: one leader, no back-off. (Above `K` the run holds no data.)
    ∀ k, k ≤ K → Rn.count k = 1 ∧ Rn.backoff k = 0

/-- **BN6b, the verdicts are the base verdicts**: every verdict of a run
under the constant rule is a verdict of the one-leader schedule. -/
def ConstDecided (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  -- The same runs.
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : PartialRun R P getLeader hk (constRule R) U V K),
    -- For every closed configuration `k` and every slot `κ` of its range —
    -- at one leader per round slot `κ` *is* round `κ`, so the range is the
    -- rounds after `start k`, up to the anchor —
    ∀ k, k < K → ∀ κ, Rn.start k < κ → κ ≤ Rn.anchor k →
      -- the run's verdict is a verdict of the one-leader schedule
      -- `Sched 1`, the base development's own. (`Nat.one_pos` and
      -- `P.max_pos` discharge `0 < 1` and `1 ≤ maxLeaders`.)
      R.Decided (Sched getLeader hk 1 Nat.one_pos P.max_pos) V κ (Rn.vdct k κ)

/-- Conservativity, for every base rule, parameter set and keyed leader
function. No law of the rule is consumed. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload)
    (P : Params) (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders),
    ConstCount R P getLeader hk ∧ ConstDecided R P getLeader hk

end Conservativity

end Barnacle

end LeanDag
