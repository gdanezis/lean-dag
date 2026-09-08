import LeanDag.Common.Validators
/-!
# FinWhale — the committee, and the two thresholds it fixes

FinWhale [LF26] adds a two-round fast path to Mysticeti's commit rule at
committee `n = 3f + 2p − 1`, where `p` (`1 ≤ p ≤ f`) is a threshold
parameter, not a second fault class: it counts missing votes, whatever
their cause, and safety assumes nothing about it. Two thresholds follow
— the slow-path quorum `spQuorum = 2f + p` and the fast-path threshold
`fastCard = n − p` — and every counting argument in the arc is about
one of them. `Params` extends `Faults` rather than replacing it, and
the committee equation is stated additively, `n + 1 = 3f + 2p`, so no
truncated subtraction reaches `omega`. This file is definitions only;
the arithmetic is `Counting.lean`.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]

/-- **FinWhale's committee**: `n = 3f + 2p − 1`, with `1 ≤ p ≤ f`. -/
class Params (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] where
  /-- How many round-`(r+1)` votes the fast path can do without. -/
  p : ℕ
  /-- The fast path tolerates at least one missing vote: a threshold of
  `n` votes, requiring every validator, is not admitted. -/
  p_pos : 1 ≤ p
  /-- The fast path does not tolerate more missing votes than there may
  be faults. -/
  p_le_f : p ≤ F.f
  /-- `n = 3f + 2p − 1`, written additively. -/
  card_add_one : Fintype.card Validator + 1 = 3 * F.f + 2 * p

variable [F : Faults Validator] [P : Params Validator]

/-- The slow-path quorum, the paper's `⌈(n+f+1)/2⌉`. -/
def spQuorum (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Params Validator] : ℕ :=
  2 * Faults.f Validator + Params.p Validator

/-- The fast-path threshold: `n − p` distinct voters one round above. -/
def fastCard (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Params Validator] : ℕ :=
  Fintype.card Validator - Params.p Validator

end FinWhale

end LeanDag
