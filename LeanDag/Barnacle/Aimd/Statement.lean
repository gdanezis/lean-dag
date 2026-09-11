import LeanDag.Barnacle.Aimd.Rule
/-!
# BN7 — the AIMD rule

What the paper says of its update (`barnacle.md` §4, §6): the count
stays in `[1, maxLeaders]`; a healthy window raises it by one, a cap
excepted, and resets the back-off; an unhealthy window lowers it by
`2^backoff`, a floor excepted, and doubles the next step.

* **BN7a, bounds** — every round of the emitted configuration is at most
  `maxLeaders` slots wide, and its interval is the one it was given.
* **BN7b, healthy** — below the cap, one more leader; at the cap, the cap.
* **BN7c, unhealthy** — above the floor, strictly fewer leaders, by
  `2^backoff` where that keeps the count above one; at the floor, the
  floor.
* **BN7d, the test** — the rule takes the healthy step, and resets the
  back-off, exactly when `den · observed ≥ num · expected`.
* **BN7e, the rule is anchored** — it does not read the view.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Aimd

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN7a, bounds**: the configuration the rule emits has no round wider
than `maxLeaders`, and carries forward the interval it was given — which
is what `UpdBounded` asks, the widths' positivity being a `Config` field
and the interval's bounds being inherited from the configuration read. -/
def RuleBounds (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders) : Prop :=
  ∀ (C : Config Validator) (backoff : ℕ) (U : R.Universe) (V : R.View U)
    (v : ℕ → Option BlockId) (A : BlockId),
    (∀ r, (rule R P lead hl C backoff U V v A).1.slotsAt r ≤ P.maxLeaders) ∧
      (rule R P lead hl C backoff U V v A).1.interval = C.interval

/-- **BN7b, healthy**: below the cap the count rises by one; at the cap
it stays. -/
def Healthy (P : Params) : Prop :=
  (∀ m backoff, m < P.maxLeaders → count P m backoff true = m + 1) ∧
    ∀ backoff, count P P.maxLeaders backoff true = P.maxLeaders

/-- **BN7c, unhealthy**: above the floor the count falls, by `2^backoff`
when that keeps it above one; at the floor it stays. -/
def Unhealthy (P : Params) : Prop :=
  (∀ m backoff, 1 < m → m ≤ P.maxLeaders → count P m backoff false < m) ∧
  (∀ m backoff, 2 ^ backoff < m → m ≤ P.maxLeaders →
    count P m backoff false = m - 2 ^ backoff) ∧
    ∀ backoff, count P 1 backoff false = 1

/-- **BN7d, the test**: the rule installs one width throughout, on the
leaders it was given and at the interval it was given, and it is the
integer comparison `den · observed ≥ num · expected` that picks which
width and what becomes of the back-off — the healthy step when the
comparison holds and the unhealthy one when it fails, so "exactly when"
is both directions. -/
def Test (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders) : Prop :=
  ∀ (C : Config Validator) (backoff : ℕ) (U : R.Universe) (V : R.View U)
    (v : ℕ → Option BlockId) (A : BlockId),
    -- the leaders and the interval are the ones read, either way
    (rule R P lead hl C backoff U V v A).1.lead = lead ∧
    (rule R P lead hl C backoff U V v A).1.interval = C.interval ∧
    -- the comparison holds: the healthy width, and the back-off resets
    (P.num * expected R C (R.block U A).round ≤ P.den * observed R C U A →
      (rule R P lead hl C backoff U V v A).1.slotsAt =
        fun _ => count P (C.slotsAt (R.block U A).round) backoff true) ∧
    (P.num * expected R C (R.block U A).round ≤ P.den * observed R C U A →
      (rule R P lead hl C backoff U V v A).2 = 0) ∧
    -- it fails: the unhealthy width, and the back-off steps on
    (¬ (P.num * expected R C (R.block U A).round ≤ P.den * observed R C U A) →
      (rule R P lead hl C backoff U V v A).1.slotsAt =
        fun _ => count P (C.slotsAt (R.block U A).round) backoff false) ∧
    (¬ (P.num * expected R C (R.block U A).round ≤ P.den * observed R C U A) →
      (rule R P lead hl C backoff U V v A).2 = backoff + 1)

/-- **BN7e, the rule is anchored.** It does not read the view, so two
validators holding the anchor take the same step — the condition BN3
asks of an update rule. -/
def RuleAnchored (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders) : Prop :=
  Anchored R (rule R P lead hl)

/-- The AIMD rule, for every base rule, parameter set and keyed leader
function. No law of the rule is consumed. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload)
    (P : Params) (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders),
    RuleBounds R P lead hl ∧ Healthy P ∧ Unhealthy P ∧ Test R P lead hl ∧
      RuleAnchored R P lead hl

end Aimd

end Barnacle

end LeanDag
