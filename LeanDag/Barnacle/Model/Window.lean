import LeanDag.Barnacle.Model.Schedule
import Mathlib.Data.Finset.Prod

/-!
# Barnacle: the window, the count, and the AIMD rule

The paper's Algorithm 3 (`barnacle.md` §4): from the committed anchor's
causal history over the last `interval` rounds, count the slots the
direct rule decides, compare with the number expected at the current
leader count, and move the count up by one or down by `2^backoff`. The
window is the anchor's history view (`BaseRule.historyView`); the
threshold is the integer pair `(num, den)`, the paper's `0.96` being
`(96, 100)`.

**Trusted core of the arc: definitions only.** The `Decidable` instance
is by `inferInstanceAs`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The mechanism's parameters: the reconfiguration interval in rounds,
the cap on the leader count, and the health threshold `num / den`. -/
structure Params where
  /-- Rounds between reconfigurations. -/
  interval : ℕ
  /-- The upper bound on the leader count. -/
  maxLeaders : ℕ
  /-- The threshold's numerator. -/
  num : ℕ
  /-- The threshold's denominator. -/
  den : ℕ
  /-- **Rounds between an anchor and the count it sets taking effect.**
  Barnacle alone may install a count at the next round, and does at
  `gap = 0`. A mechanism reading the same verdicts on a lag needs the
  count settled before it reads it: an adaptive leader schedule at epoch
  length `W` asks for `2 * W`, since the gap's rounds run at the old
  count and so hold at least `gap` slots. The configuration's range
  extends over the gap, so the horizon grows by `gap` per configuration
  (`Model/Live.lean`) and nothing else changes. -/
  gap : ℕ
  interval_pos : 0 < interval
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
`interval + 1` rounds up to the anchor's, at count `m`, whose candidate
is directly committed on the anchor's history view; zero when the
anchor is absent. The `d ≤ round` guard keeps truncated subtraction from
over-counting round `0`. -/
def observed (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (U : R.Universe) (A : BlockId) (m : ℕ) (hm : 0 < m) (hmax : m ≤ P.maxLeaders) : ℕ :=
  if hA : A ∈ R.ids U then
    ((Finset.range (P.interval + 1) ×ˢ Finset.range m).filter (fun dl : ℕ × ℕ =>
      dl.1 ≤ (R.block U A).round ∧
      R.SlotDirect (Sched getLeader hk m hm hmax) U (R.historyView U A hA)
        (m * ((R.block U A).round - dl.1) + dl.2))).card
  else 0

/-- **The expected count** (`ExpectedCommits`): `interval − waveLength +
1` rounds of `m` slots each, at count `m`; below `waveLength ≤ interval`
the subtraction truncates. -/
def expected (R : BaseRule Validator BlockId Payload) (P : Params) (m : ℕ) : ℕ :=
  (P.interval - R.waveLength + 1) * m

namespace Aimd

/-- **Additive increase, multiplicative decrease.** A healthy window
raises the count by one, capped at `maxLeaders`, and resets the back-off;
an unhealthy one lowers it by `2^backoff`, floored at one, and doubles
the next step. -/
def update (P : Params) (m backoff : ℕ) (healthy : Bool) : ℕ × ℕ :=
  if healthy then (min (m + 1) P.maxLeaders, 0)
  else (max (m - 2 ^ backoff) 1, backoff + 1)

/-- **The paper's `UpdateLeaders`** as an update rule: healthy when
`den · observed ≥ num · expected`; total, returning the initial state
outside `[1, maxLeaders]`, which no run reaches. -/
def rule (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) :
    UpdateRule R :=
  fun m backoff U _V A =>
    if hm : 0 < m ∧ m ≤ P.maxLeaders then
      update P m backoff
        (decide (P.num * expected R P m ≤
          P.den * observed R P getLeader hk U A m hm.1 hm.2))
    else (1, 0)

end Aimd

/-- The constant rule: reconfigure nothing. The conservativity anchor —
under it the arc collapses onto the base development at one leader. -/
def constRule (R : BaseRule Validator BlockId Payload) : UpdateRule R :=
  fun m b _ _ _ => (m, b)

end Barnacle

end LeanDag
