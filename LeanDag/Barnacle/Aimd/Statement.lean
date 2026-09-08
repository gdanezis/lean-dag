import LeanDag.Barnacle.Model.Window
/-!
# BN7 — the AIMD rule

What the paper says of its update (`barnacle.md` §4, §6): the count
stays in `[1, maxLeaders]`; a healthy window raises it by one, a cap
excepted, and resets the back-off; an unhealthy window lowers it by
`2^backoff`, a floor excepted, and doubles the next step.

* **BN7a, bounds** — the rule's count is in `[1, maxLeaders]`, whatever
  the input.
* **BN7b, healthy** — below the cap, one more leader and a reset
  back-off; at the cap, the cap.
* **BN7c, unhealthy** — above the floor, strictly fewer leaders by
  `2^backoff` and the back-off incremented; at the floor, the floor.
* **BN7d, the test** — the rule is healthy exactly when
  `den · observed ≥ num · expected`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Aimd

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN7a, bounds**: the rule's count lies in `[1, maxLeaders]` for
every input — a run under the AIMD rule never leaves the range
`Sched` is defined on. -/
def RuleBounds (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (m backoff : ℕ) (U : R.Universe) (V : R.View U) (A : BlockId),
    0 < (rule R P getLeader hk m backoff U V A).1 ∧
      (rule R P getLeader hk m backoff U V A).1 ≤ P.maxLeaders

/-- **BN7b, healthy**: below the cap the count rises by one and the
back-off resets; at the cap it stays. -/
def Healthy (P : Params) : Prop :=
  (∀ m backoff, m < P.maxLeaders → update P m backoff true = (m + 1, 0)) ∧
    ∀ backoff, update P P.maxLeaders backoff true = (P.maxLeaders, 0)

/-- **BN7c, unhealthy**: above the floor the count falls, by `2^backoff`
when that keeps it above one, and the back-off is incremented; at the
floor the count stays. -/
def Unhealthy (P : Params) : Prop :=
  (∀ m backoff, 1 < m → (update P m backoff false).1 < m ∧
    (update P m backoff false).2 = backoff + 1) ∧
  (∀ m backoff, 2 ^ backoff < m → (update P m backoff false).1 = m - 2 ^ backoff) ∧
    ∀ backoff, (update P 1 backoff false).1 = 1

/-- **BN7d, the test**: for a count in range, the rule takes the healthy
step exactly when `den · observed ≥ num · expected`. -/
def Test (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (m backoff : ℕ) (hm : 0 < m) (hmax : m ≤ P.maxLeaders) (U : R.Universe)
    (V : R.View U) (A : BlockId),
    rule R P getLeader hk m backoff U V A =
      update P m backoff
        (decide (P.num * expected R P m ≤ P.den * observed R P getLeader hk U A m hm hmax))

/-- **BN7e, the rule is anchored.** It does not read the view, so two
validators holding the anchor take the same step — the condition BN3
asks of an update rule. -/
def RuleAnchored (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  Anchored R (rule R P getLeader hk)

/-- The AIMD rule, for every base rule, parameter set and keyed leader
function. No law of the rule is consumed. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload)
    (P : Params) (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders),
    RuleBounds R P getLeader hk ∧ Healthy P ∧ Unhealthy P ∧ Test R P getLeader hk ∧
      RuleAnchored R P getLeader hk

end Aimd

end Barnacle

end LeanDag
