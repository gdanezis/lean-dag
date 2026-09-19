import LeanDag.Hydrozoan.Delivery.Proof
import LeanDagTest.Hydrozoan.PrefixAgreement
/-!
# Witness: delivered sequences

`delivered` computed on the settled slots of `U5`, under both keys the
statement names. `U5` holds an equivocation — blocks 7 and 8 are both
replica 0's round-1 block — so the keys disagree, and the witness shows
how: under a block's own id both twins are delivered, under
`authorRound` the second is dropped. The listing `lin5` is a toy (the
twins, the first leader, then the leader itself), chosen so that the two
committed leaders' lists overlap and the filter has work to do; it is
not `U5`'s causal history.

Then the three conjuncts of `holds` applied on this data.
-/

namespace LeanDagTest

namespace Hydrozoan

open LeanDag LeanDag.Hydrozoan Hydrozoan.PrefixAgreement Hydrozoan.Delivery

/-- A toy per-leader listing: the equivocating twins 7 and 8, block 2,
then the leader. Two leaders' lists overlap in the first three. -/
def lin5 (b : Fin 39) : List (Fin 39) := [7, 8, 2, b]

-- The twins share a key, and are distinct blocks.
example : authorRound U5.block 7 = authorRound U5.block 8 := by decide

-- The unfiltered ledger repeats the overlap.
example : ledger lin5 g5 5 = [7, 8, 2, 2, 7, 8, 2, 31] := rfl

-- By block id: every repeat dropped, both twins delivered.
example : delivered id lin5 g5 5 = [7, 8, 2, 31] := by decide

-- By author and round, the paper's key: the second twin is dropped too.
example : delivered (authorRound U5.block) lin5 g5 5 = [7, 2, 31] := by decide

-- The shorter replica delivers a prefix, under either key.
example : delivered id lin5 g5b 1 = [7, 8, 2] := by decide
example : delivered (authorRound U5.block) lin5 g5b 1 = [7, 2] := by decide

/-- `g5` decides below 5 in the full view. -/
theorem vfull5_g5 : DecidesBelow U5 Vfull5 g5 5 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · exact Decided.directCommit (by decide) (Or.inl (by decide))
  · exact Decided.directSkip (by decide)
  · exact Decided.directSkip (by decide)
  · exact Decided.directSkip (by decide)
  · exact Decided.directCommit (by decide) (Or.inl (by decide))

/-- `g5b` decides below 1 in the second view. -/
theorem v5b_g5b : DecidesBelow U5 V5b g5b 1 := by
  intro k hk
  have hcase : k = 0 := by omega
  subst hcase
  exact Decided.directCommit (by decide) (Or.inl (by decide))

-- `holds`, first conjunct: no author-and-round is delivered twice.
example : ((delivered (authorRound U5.block) lin5 g5 5).map (authorRound U5.block)).Nodup :=
  (Delivery.holds (Fin 7) (Fin 39) U5).1 _ (authorRound U5.block) lin5 g5 5

-- Second conjunct: the two replicas' delivered sequences, across views
-- and horizons, under the paper's key.
example : delivered (authorRound U5.block) lin5 g5b 1 <+:
    delivered (authorRound U5.block) lin5 g5 5 :=
  (Delivery.holds (Fin 7) (Fin 39) U5).2.1 _ (authorRound U5.block) lin5 V5b Vfull5 g5b g5 1 5
    (by omega) v5b_g5b vfull5_g5

-- Third conjunct: block 8 is in the ledger and not delivered, and its
-- key is — by its twin.
example : ∃ c ∈ delivered (authorRound U5.block) lin5 g5 5,
    authorRound U5.block c = authorRound U5.block 8 :=
  ((Delivery.holds (Fin 7) (Fin 39) U5).2.2 _ (authorRound U5.block) lin5 g5 5).2 8 (by decide)

end Hydrozoan

end LeanDagTest
