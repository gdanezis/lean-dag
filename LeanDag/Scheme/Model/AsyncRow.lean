import LeanDag.Scheme.Model.Params
/-!
# The asynchronous rows

`Params.AsyncRow p n f c b`: `p` is an asynchronous row of the table at
committee `n`, `f` Byzantine and `c` crashed validators, with `b` buffer
rounds.

Definitions only.
-/

namespace LeanDag

namespace Scheme

namespace Params

/-- **An asynchronous row** at its committee, with its buffer rounds `b`:
Mahi-Mahi at waves four (`b = 1`) and five (`b = 2`) and Cordial Miners
Async (`b = 2`) from `3f + 1`, Blue Bottle Async from `5f + 1`, Async
Orcaella from `5f + 3c + 1`, Hybrid Mahi-Mahi at waves four and five from
`3f + 2c + 1`, and Async Nemo-Nemo from `2c + 1`. -/
def AsyncRow (p : Params) (n f c b : ℕ) : Prop :=
  (c = 0 ∧ 3 * f + 1 ≤ n ∧ ((p = mahiMahi 4 n f ∧ b = 1) ∨ (p = mahiMahi 5 n f ∧ b = 2) ∨
    (p = cordialMinersAsync n f ∧ b = 2))) ∨
  (c = 0 ∧ 5 * f + 1 ≤ n ∧ p = blueBottleAsync n f ∧ b = 1) ∨
  (5 * f + 3 * c + 1 ≤ n ∧ p = asyncOrcaella n f c ∧ b = 1) ∨
  (3 * f + 2 * c + 1 ≤ n ∧ ((p = hybridMahiMahi 4 n f c ∧ b = 1) ∨
    (p = hybridMahiMahi 5 n f c ∧ b = 2))) ∨
  (f = 0 ∧ 2 * c + 1 ≤ n ∧ p = asyncNemoNemo n c ∧ b = 1)

end Params

end Scheme

end LeanDag
