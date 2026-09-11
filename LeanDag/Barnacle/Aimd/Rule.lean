import LeanDag.Barnacle.Model.Window
/-!
# Barnacle: the AIMD step

`UpdateLeaders` (`barnacle.md` §4): compare the window count with the
count the window's scoring rounds offered and move the leader count up
by one or down by `2^backoff`, then install a configuration of that
width on the same leaders and the same interval.

This is not a `Model/` file, though it is a definition the run is
parametric in: building the emitted `Config` needs the two bounds on
`count` as theorems, and `Model/` files carry no theorems.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

namespace Aimd

/-- **Additive increase, multiplicative decrease.** A healthy window
raises the count by one and resets the back-off; an unhealthy one lowers
it by `2^backoff` and doubles the next step. Both are capped at
`maxLeaders` and floored at one, so the count is in range whatever the
configuration it reads was, and agrees with the paper's for a count
already in range. -/
def count (P : Params) (m backoff : ℕ) (healthy : Bool) : ℕ :=
  max 1 (min P.maxLeaders (if healthy then m + 1 else m - 2 ^ backoff))

theorem count_pos (P : Params) (m backoff : ℕ) (healthy : Bool) :
    0 < count P m backoff healthy := by
  unfold count; omega

theorem count_le (P : Params) (m backoff : ℕ) (healthy : Bool) :
    count P m backoff healthy ≤ P.maxLeaders := by
  have := P.max_pos
  unfold count; omega

/-- **The paper's `UpdateLeaders`** as an update rule: healthy when
`den · observed ≥ num · expected`, and the next configuration is the
same leaders and the same interval at the new count. The count it
adjusts is the width of the anchor's own round, which is the last round
the window measured. -/
def rule (R : BaseRule Validator BlockId Payload) (P : Params)
    (lead : ℕ → ℕ → Validator) (hl : LeadKeyed lead P.maxLeaders) : UpdateRule R :=
  fun C backoff U _V _v A =>
    let r := (R.block U A).round
    let healthy := decide (P.num * expected R C r ≤ P.den * observed R C U A)
    let m := count P (C.slotsAt r) backoff healthy
    (Config.uniform lead hl m (count_pos P _ _ _) (count_le P _ _ _) C.interval,
      if healthy then 0 else backoff + 1)

end Aimd

end Barnacle

end LeanDag
