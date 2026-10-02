import LeanDag.RedSnapper.Model.Faults

/-!
# Witness: the fault model and the two thresholds

Concrete `Faults` instances, checked by `decide`, so the class's
hypotheses are demonstrably not contradictory, and the two thresholds
pinned at the committees the paper writes its constants for.

* `Fin 4`, `f = 1`, validator `0` Byzantine: the tight `3f + 1`
  committee. `quorum = half = 3` — the paper's single `2f + 1` — and the
  `Five` bound fails.
* `Fin 6`, `f = 1`, validator `5` Byzantine: the tight `5f + 1`
  committee, with its `Five` instance. `quorum = 5` and `half = 3` — the
  paper's `4f + 1` and `2f + 1` — and `⌈quorum/2⌉ = half`, the exposure
  seam of `Revocation/Statement.lean` at equality.
* `Fin 5`, `f = 1`: the committee between the two — a strict revocation
  threshold exists (`half = 3 < quorum = 4`) but a quorum of votes need
  not expose it (`⌈4/2⌉ = 2 < 3`), the regime `docs/red-snapper.md` §0
  turns on.
* `Fin 8`, `f = 1`, no actual fault: a `Five` instance above the tight
  committee, so the bound's direction is pinned.
* The tight committees at `f = 2` with no actual fault: the thresholds
  read only the bound. At `n = 7` the two coincide at `5`; at `n = 11`
  they are `9` and `5`.

What this guards: `quorum` is `n − f` and `half` is `2f + 1`, not the
other way round, and neither reads the actual Byzantine set.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

/-- Four validators, `f = 1`, validator `0` Byzantine: the tight `3f + 1`
committee. -/
instance fourValidators : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

-- At `n = 3f + 1` the two thresholds coincide: the paper's one `2f + 1`.
example : quorum (Fin 4) = 3 ∧ half (Fin 4) = 3 := by decide

-- The correct pool is the complement of the actual Byzantine set.
example : (Correct : Finset (Fin 4)) = {1, 2, 3} := by decide

-- Four validators do not meet the second protocol's bound.
example : ¬ (5 * fourValidators.f + 1 ≤ Fintype.card (Fin 4)) := by decide

/-- Six validators, `f = 1`, validator `5` Byzantine: the tight `5f + 1`
committee. -/
instance sixValidators : Faults (Fin 6) where
  f := 1
  byzantine := {5}
  card_validators := by decide
  card_byzantine := by decide

instance : Five (Fin 6) where
  card_validators := by decide

-- The paper's `4f + 1` and `2f + 1`.
example : quorum (Fin 6) = 5 ∧ half (Fin 6) = 3 := by decide

-- The exposure seam at equality: `⌈5/2⌉ = 3 = half`.
example : (quorum (Fin 6) + 1) / 2 = half (Fin 6) := by decide

/-- The tight `3f + 1` committee with no actual fault: the thresholds
read only the bound `f`. -/
@[instance_reducible]
def tight (f : ℕ) : Faults (Fin (3 * f + 1)) where
  f := f
  byzantine := ∅
  card_validators := by simp
  card_byzantine := by simp

/-- The tight `5f + 1` committee with no actual fault. -/
@[instance_reducible]
def tightFive (f : ℕ) : Faults (Fin (5 * f + 1)) where
  f := f
  byzantine := ∅
  card_validators := by simp only [Fintype.card_fin]; omega
  card_byzantine := by simp

instance : Faults (Fin 7) := tight 2
instance : Faults (Fin 11) := tightFive 2

instance : Five (Fin 11) where
  card_validators := by decide

-- `f = 2`: at `n = 7` the thresholds coincide at `5`; at `n = 11` the
-- quorum climbs to `9` while `half` stays at `5`.
example : quorum (Fin 7) = 5 ∧ half (Fin 7) = 5 := by decide
example : quorum (Fin 11) = 9 ∧ half (Fin 11) = 5 := by decide

-- With no actual fault everyone is correct, whatever the bound.
example : (Correct : Finset (Fin 7)) = Finset.univ := by decide

/-- Five validators, `f = 1`, validator `4` Byzantine: above `3f + 1`,
below `5f + 1`. -/
instance fiveValidators : Faults (Fin 5) where
  f := 1
  byzantine := {4}
  card_validators := by decide
  card_byzantine := by decide

-- Strict but not exposed: `half < quorum`, yet `half > ⌈quorum/2⌉`.
example : quorum (Fin 5) = 4 ∧ half (Fin 5) = 3 := by decide
example : half (Fin 5) < quorum (Fin 5) := by decide
example : ¬ (half (Fin 5) ≤ (quorum (Fin 5) + 1) / 2) := by decide
example : ¬ (5 * fiveValidators.f + 1 ≤ Fintype.card (Fin 5)) := by decide

/-- Eight validators, `f = 1`, no actual fault: a `5f + 1` committee with
room to spare. -/
instance eightValidators : Faults (Fin 8) where
  f := 1
  byzantine := ∅
  card_validators := by decide
  card_byzantine := by decide

instance : Five (Fin 8) where
  card_validators := by decide

-- The bound is `5f + 1 ≤ n`, not the reverse: at `n = 8` only one
-- direction holds.
example : 5 * eightValidators.f + 1 < Fintype.card (Fin 8) := by decide
example : quorum (Fin 8) = 7 ∧ half (Fin 8) = 3 := by decide

end RedSnapper

end LeanDagTest
