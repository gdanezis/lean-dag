import Mathlib.Data.Nat.Basic
/-!
# Steelhead — the wavelength function

Steelhead composes two commit rules over one DAG by giving every round a
wavelength: the rounds a slot proposed there reads to decide, `ws` for a
synchronous slot and `wa` for an asynchronous one (`steelhead.md` §1).
Which is which is a function of the round number alone — the period
`k` makes every `k`-th round asynchronous — so the mode is an
interpretation of the DAG and touches no block.

**Definitions only.** The rule that consumes a wavelength function is in
`Decision.lean`; the results about it are stated in
`<Result>/Statement.lean` files and proved in their `Proof.lean`.

The two ends of the dial are wavelength functions too: `k = 1` is
`periodic ws wa 1`, which is `wa` at every round (`Nat.mod_one`), and
`k = ∞` is the constant `fun _ => ws`. Both are Mahi-Mahi's rule at one
wave, the second Mysticeti's when `ws = 3` (`Safety/Statement.lean`,
SH4).
-/

namespace LeanDag

namespace Steelhead

/-- **The periodic wavelength**: `wa` at every `k`-th round, `ws` at the
others. The paper's `w(r) = wa if r mod k = 0 else ws`. At `k = 0` Lean's
`r % 0 = r` makes only round `0` asynchronous. No result excludes that
period and none needs to: SH8 reads `2 ≤ k` off its own `2 ≤ ws ≤ k`,
and the period results hold at every period. -/
def periodic (ws wa k : ℕ) : ℕ → ℕ := fun r => if r % k = 0 then wa else ws

/-- A round is **asynchronous** under the period `k` when it is a multiple
of `k`: its slot is decided by the asynchronous rule with a coin-elected
leader. -/
def IsAsync (k r : ℕ) : Prop := r % k = 0

instance (k r : ℕ) : Decidable (IsAsync k r) := inferInstanceAs (Decidable (_ = _))

end Steelhead

end LeanDag
