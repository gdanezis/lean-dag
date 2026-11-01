import LeanDagTest.DoS.TwoFaults
import LeanDagTest.DoS.Exposure
import LeanDag.DoS.Pedigree
/-!
# The general bound at `f = 2`

`dos-equivocation-and-growth.md` §5, the multi-equivocator witness.

`Ufault` is exactly the case `Adoption.lean`'s unique-equivocator theorem
cannot touch: **both** Byzantine validators equivocate and both are exposed
at the merge, so no choice of `X` leaves the others unexposed. The pedigree
machinery closes it: `card_history_le` bounds every history with no
hypothesis beyond `DoSValid`, at any fault budget.

The constant is enormous — `(3f+1)·(3f+2)^(3f+1) = 7·8⁷` at `f = 2`, against
an actual history of 20 blocks — but the point is its *shape*: constant in
`r`. C1′ asked for exactly that (`card_historyBlocksOf_le`): a per-author
per-round contribution that cannot compound down the rounds, whatever the
number of equivocators.
-/

namespace LeanDagTest

open LeanDag

/-! ## Two equivocators, both exposed — the case beyond `Adoption.lean` -/

-- Both Byzantine validators are exposed in the round-3 block's history, so
-- the unique-equivocator hypothesis genuinely fails here.
example : (exposedTo Ufault 19).card = 2 := by decide

-- Each equivocator's content is two chains: its two genesis blocks.
example : topsOf Ufault 19 0 = {0, 7} := by decide
example : topsOf Ufault 19 1 = {1, 8} := by decide

-- Honest authors: one chain each.
example : topsOf Ufault 19 2 = {19} := by decide

/-! ## C1′ and the general bound, applied -/

/-- **C1′ applied** at `f = 2`: validator 0's per-round contribution to the
history is bounded by `c(f) = 8⁷`, with no unique-equivocator hypothesis.
(The actual count at round 0 is `2` — the two geneses.) -/
example : ∀ n, (historyBlocksOf Ufault 19 0 n).card ≤ (3 * 2 + 2) ^ (3 * 2 + 1) :=
  fun n => card_historyBlocksOf_le ufault_dosValid (by decide) 0 n

example : (historyBlocksOf Ufault 19 0 0).card = 2 := by decide

/-- **The general bound applied**: the whole 20-block history is bounded
linearly in its round, both equivocators notwithstanding. -/
example : (history Ufault 19).card
    ≤ (Fintype.card (Fin 7)) * ((Fintype.card (Fin 7) + 1)) ^ (Fintype.card (Fin 7))
      * ((Ufault.block 19).round + 1) :=
  card_history_le ufault_dosValid (by decide)

example : (history Ufault 19).card = 20 := by decide

/-- The tops count behind it: even with the budget fully spent, no author's
chain count exceeds the pedigree ceiling. -/
example : ∀ X : Fin 7, (topsOf Ufault 19 X).card ≤ (3 * 2 + 2) ^ (3 * 2 + 1) :=
  fun X => card_topsOf_le_pow ufault_dosValid (by decide) X

/-! ## The tightened constants

Anchored pedigrees cut the ceilings by orders of magnitude. At `f = 2` with
both equivocators exposed (`e = 2`):

* per exposed author: `(3f+1-e)·e^(e-1) = 5·2 = 10` chains (actual: 2);
* per author per round: `c(f) = 1 + 3f·f^(f-1) = 13` (was `8⁷ = 2 097 152`);
* per round: `3f+1 + 3f^(f+1) = 31`;
* whole history: `(3f+1 + 3f^(f+1))·(r+1) = 31·4 = 124` (was `7·8⁷·4`);
  actual: 20. -/

/-- **The sharp per-author count applied**: validator 0's chains are bounded
by `(3f+1-e)·e^(e-1) = 10`, and there are `2`. -/
example : (topsOf Ufault 19 0).card ≤
    (Fintype.card (Fin 7) - (exposedTo Ufault 19).card) *
      (exposedTo Ufault 19).card ^ ((exposedTo Ufault 19).erase 0).card :=
  card_topsOf_le_of_exposed ufault_dosValid (by decide) (by decide)

example : (Fintype.card (Fin 7) - (exposedTo Ufault 19).card) *
    (exposedTo Ufault 19).card ^ ((exposedTo Ufault 19).erase 0).card = 10 := by decide

/-- **C1′, tightened, applied**: at most `13` blocks per author per round. -/
example : ∀ n, (historyBlocksOf Ufault 19 0 n).card ≤
    1 + (Fintype.card (Fin 7) - 1) * Faults.f (Fin 7) ^ (Faults.f (Fin 7) - 1) :=
  fun n => card_historyBlocksOf_le' ufault_dosValid (by decide) 0 n

example : 1 + (Fintype.card (Fin 7) - 1) * Faults.f (Fin 7) ^ (Faults.f (Fin 7) - 1) = 13 := by
  decide

/-- **C1′ per round, applied**: at most `31` blocks of the history at any
one round. -/
example : ∀ k, ((history Ufault 19).filter fun i => (Ufault.block i).round = k).card ≤
    Fintype.card (Fin 7) + (Fintype.card (Fin 7) - 1) * Faults.f (Fin 7) ^ Faults.f (Fin 7) :=
  card_historyAt_le ufault_dosValid (by decide)

/-- **The tightened total applied**: `20 ≤ 31·4`. -/
example : (history Ufault 19).card ≤
    (Fintype.card (Fin 7) + (Fintype.card (Fin 7) - 1) * Faults.f (Fin 7) ^ Faults.f (Fin 7))
      * ((Ufault.block 19).round + 1) := by
  simpa using card_history_le' ufault_dosValid (by decide) 0

example : (Fintype.card (Fin 7) + (Fintype.card (Fin 7) - 1) * Faults.f (Fin 7) ^ Faults.f (Fin 7)) = 31 := by
  decide

/-- At `f = 1` the tightened total is exactly the adoption theorem's `7(r+1)`
— on `Umerge`: `12 ≤ 7·4`. -/
example : (history Umerge 12).card ≤
    (Fintype.card (Fin 4) + (Fintype.card (Fin 4) - 1) * Faults.f (Fin 4) ^ Faults.f (Fin 4))
      * ((Umerge.block 12).round + 1) := by
  simpa using card_history_le' umerge_dosValid (by decide) 0

example : (Fintype.card (Fin 4) + (Fintype.card (Fin 4) - 1) * Faults.f (Fin 4) ^ Faults.f (Fin 4)) = 7 := by
  decide

end LeanDagTest
