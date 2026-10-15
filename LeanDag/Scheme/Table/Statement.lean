import LeanDag.Scheme.Model.Params
/-!
# The scheme's table — statement

`docs/scheme.md` §2: what the scheme's "Reading the table" paragraph
claims of its rows, checked as arithmetic. `q` is the number of
previous-round blocks every block references, `certThreshold` in the
scheme, and `n − f − c` where the scheme solves for its rows.

* `RowsHold`: every published row with a direct skip satisfies its
  family's inequalities and the liveness bounds; the rows with no direct
  skip (`skipThreshold = n`) satisfy the inequalities and the bounds on
  the other two thresholds; the derived rows satisfy what their published
  counterpart does; Orcaella holds at every `n ≥ 5f + 3c + 1`.
* `TwoRoundBound`, `ThreeRoundBound`: the inequalities and the liveness
  bounds force `n ≥ 5f + 3c + 1` and `n ≥ 3f + 2c + 1`, and at those
  committees force Orcaella's and Hybrid Mysticeti's thresholds.
* `NemoNotTwoRound`: Nemo-Nemo is no solution of the two-round
  inequalities: at `f = 0` and `c ≥ 1` its commit and link sum to
  `c + 2 < n + 1`. Its committee `2c + 1` is below the bound `3c + 1`
  the inequalities give at `f = 0`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Table

open Params

/-- **Every row satisfies its family's conditions.** -/
def RowsHold : Prop :=
  ∀ f c : ℕ,
    -- Mysticeti and Mahi-Mahi at `n = 3f + 1`
    (ThreeRound (mysticeti (3 * f + 1) f) (3 * f + 1) f (2 * f + 1) ∧
      Live (mysticeti (3 * f + 1) f) (3 * f + 1) f 0) ∧
    (∀ w, ThreeRound (mahiMahi w (3 * f + 1) f) (3 * f + 1) f (2 * f + 1) ∧
      Live (mahiMahi w (3 * f + 1) f) (3 * f + 1) f 0) ∧
    -- Cordial Miners: the inequalities, and the bounds but the skip's
    (ThreeRound (cordialMinersPS (3 * f + 1) f) (3 * f + 1) f (2 * f + 1) ∧
      (cordialMinersPS (3 * f + 1) f).commitThreshold ≤ 2 * f + 1 ∧
      (cordialMinersPS (3 * f + 1) f).certThreshold ≤ 2 * f + 1) ∧
    (ThreeRound (cordialMinersAsync (3 * f + 1) f) (3 * f + 1) f (2 * f + 1)) ∧
    -- Blue Bottle at `n = 5f + 1`, both waves
    (TwoRound (blueBottlePS (5 * f + 1) f) (5 * f + 1) f (4 * f + 1) ∧
      Live (blueBottlePS (5 * f + 1) f) (5 * f + 1) f 0) ∧
    (TwoRound (blueBottleAsync (5 * f + 1) f) (5 * f + 1) f (4 * f + 1) ∧
      Live (blueBottleAsync (5 * f + 1) f) (5 * f + 1) f 0) ∧
    -- Orcaella and Async Orcaella at every committee from the bound up
    (∀ n, 5 * f + 3 * c + 1 ≤ n →
      (TwoRound (orcaella n f c) n f (n - f - c) ∧ Live (orcaella n f c) n f c) ∧
      (TwoRound (asyncOrcaella n f c) n f (n - f - c) ∧ Live (asyncOrcaella n f c) n f c)) ∧
    -- Hybrid Mysticeti and Hybrid Mahi-Mahi at `n = 3f + 2c + 1`
    (ThreeRound (hybridMysticeti (3 * f + 2 * c + 1) f c) (3 * f + 2 * c + 1) f
        (2 * f + c + 1) ∧
      Live (hybridMysticeti (3 * f + 2 * c + 1) f c) (3 * f + 2 * c + 1) f c) ∧
    (∀ w, ThreeRound (hybridMahiMahi w (3 * f + 2 * c + 1) f c) (3 * f + 2 * c + 1) f
        (2 * f + c + 1) ∧
      Live (hybridMahiMahi w (3 * f + 2 * c + 1) f c) (3 * f + 2 * c + 1) f c)

/-- **The two-round inequalities force Orcaella.** With `q = n − f − c`
and the liveness bounds, `n ≥ 5f + 3c + 1`; at `n = 5f + 3c + 1` the
commit, skip and link thresholds are Orcaella's. -/
def TwoRoundBound : Prop :=
  ∀ (p : Params) (n f c : ℕ),
    TwoRound p n f (n - f - c) → Live p n f c →
      5 * f + 3 * c + 1 ≤ n ∧
      (n = 5 * f + 3 * c + 1 →
        p.commitThreshold = (orcaella n f c).commitThreshold ∧
        p.skipThreshold = (orcaella n f c).skipThreshold ∧
        p.linkSize = (orcaella n f c).linkSize)

/-- **The three-round inequalities force Hybrid Mysticeti.** With
`q = certThreshold` and the liveness bounds, `n ≥ 3f + 2c + 1`; at
`n = 3f + 2c + 1` the commit, skip and certificate thresholds are Hybrid
Mysticeti's, and at `c = 0` Mysticeti's. -/
def ThreeRoundBound : Prop :=
  ∀ (p : Params) (n f c : ℕ),
    ThreeRound p n f p.certThreshold → Live p n f c →
      3 * f + 2 * c + 1 ≤ n ∧
      (n = 3 * f + 2 * c + 1 →
        p.commitThreshold = (hybridMysticeti n f c).commitThreshold ∧
        p.skipThreshold = (hybridMysticeti n f c).skipThreshold ∧
        p.certThreshold = (hybridMysticeti n f c).certThreshold ∧
        (c = 0 → p.commitThreshold = (mysticeti n f).commitThreshold ∧
          p.skipThreshold = (mysticeti n f).skipThreshold ∧
          p.certThreshold = (mysticeti n f).certThreshold))

/-- **Nemo-Nemo is no two-round solution**: at `n = 2c + 1`, `f = 0`,
`q = n − c` and `c ≥ 1`, its second inequality fails, while its first and
third hold. -/
def NemoNotTwoRound : Prop :=
  ∀ c : ℕ, 1 ≤ c →
    ¬ TwoRound (nemoNemo (2 * c + 1) c) (2 * c + 1) 0 (c + 1) ∧
    2 * c + 1 + 0 + 1 ≤ (nemoNemo (2 * c + 1) c).skipThreshold +
      (nemoNemo (2 * c + 1) c).linkSize ∧
    (nemoNemo (2 * c + 1) c).linkSize + (2 * c + 1) + 0 ≤
      (nemoNemo (2 * c + 1) c).commitThreshold + (c + 1)

/-- The table's claims, together. -/
def Statement : Prop := RowsHold ∧ TwoRoundBound ∧ ThreeRoundBound ∧ NemoNotTwoRound

end Table

end Scheme

end LeanDag
