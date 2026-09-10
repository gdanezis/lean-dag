import LeanDag.Barnacle.Model.Schedule
import Mathlib.Order.Interval.Finset.Nat

/-!
# Barnacle: the window, the count, and the AIMD rule

The paper's Algorithm 3 (`barnacle.md` §4): from the committed anchor's
causal history over the last `interval` rounds, count the slots the
direct rule decides, and compare with the number of slots those rounds
offered. The window is the anchor's history view
(`BaseRule.historyView`); the threshold is the integer pair
`(num, den)`, the paper's `0.96` being `(96, 100)`. The AIMD step the
comparison feeds is `Aimd/Rule.lean`, which carries the arithmetic its
configuration needs and so cannot live here.

Both counts are read off the configuration in force, which fixes the
interval and the slots of each round, so neither depends on the rounds
being of one width.

**Trusted core of the arc: definitions only.** The `Decidable` instance
is by `inferInstanceAs`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The mechanism's parameters: the caps on a configuration's widths and
interval, and the health threshold `num / den`. The interval itself is a
configuration's own, so a reconfiguration may change it; `maxInterval`
is the bound a horizon is computed against. -/
structure Params where
  /-- The upper bound on the leader count. -/
  maxLeaders : ℕ
  /-- The upper bound on a configuration's interval. -/
  maxInterval : ℕ
  /-- The threshold's numerator. -/
  num : ℕ
  /-- The threshold's denominator. -/
  den : ℕ
  max_pos : 0 < maxLeaders

namespace BaseRule

/-- Slot `κ` of schedule `S` has a candidate directly committed on view
`V`. The unit the window count counts. -/
def SlotDirect (R : BaseRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (V : R.View U) (κ : ℕ) : Prop :=
  ∃ L ∈ R.ids U, R.IsLeaderBlock S U κ L ∧ R.DirectCommitIn V L (S.slotRound κ)

instance instDecidableSlotDirect (R : BaseRule Validator BlockId Payload)
    (S : Slots Validator) (U : R.Universe) (V : R.View U) (κ : ℕ) :
    Decidable (R.SlotDirect S U V κ) :=
  inferInstanceAs (Decidable (∃ L ∈ R.ids U, R.IsLeaderBlock S U κ L ∧
    R.DirectCommitIn V L (S.slotRound κ)))

end BaseRule

/-- **The window count** (`CountDirectCommits`): the slots of the
`C.interval + 1` rounds up to the anchor's whose candidate is directly
committed on the anchor's history view; zero when the anchor is absent.
Those are the slots `κ` with `C.cum (r − C.interval) ≤ κ < C.cum (r + 1)`
for the anchor's round `r`, and the truncated subtraction is what stops
the window at round `0`. -/
def observed (R : BaseRule Validator BlockId Payload)
    (C : Config Validator) (U : R.Universe) (A : BlockId) : ℕ :=
  if hA : A ∈ R.ids U then
    ((Finset.Ico (C.cum ((R.block U A).round - C.interval))
        (C.cum ((R.block U A).round + 1))).filter
      (fun κ => R.SlotDirect C.sched U (R.historyView U A hA) κ)).card
  else 0

/-- **The expected count** (`ExpectedCommits`): the slots offered by the
rounds of the window old enough to have been decided — those from
`r − C.interval` through `r − waveLength`, for the anchor's round `r`.
At one width `m` this is the paper's `(interval − waveLength + 1) · m`. -/
def expected (R : BaseRule Validator BlockId Payload) (C : Config Validator) (r : ℕ) : ℕ :=
  C.cum (r - R.waveLength + 1) - C.cum (r - C.interval)

/-- The constant rule: reconfigure nothing. The conservativity anchor —
under it the arc collapses onto the base development at one leader. -/
def constRule (R : BaseRule Validator BlockId Payload) : UpdateRule R :=
  fun C b _ _ _ => (C, b)

end Barnacle

end LeanDag
