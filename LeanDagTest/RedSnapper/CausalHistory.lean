import LeanDag.RedSnapper.Helpers.Stance
import LeanDagTest.RedSnapper.Universe

/-!
# Witness: reachability, inclusion, candidates, conflicts

`Reaches`, `Includes`, `IsCandidate` and `Conflicted` exercised on the
universe `U` of `RedSnapperTest.Universe`. The predicates are bare
`Prop`s over reachability; each is decided through its computable
surrogate in `Helpers/Stance.lean` (`history`, `txsIn`, `candidates`)
and bridged by the surrogate's faithfulness lemma.

Pinned: a direct and a multi-hop reach, a non-reach across twins;
inclusion of a transaction carried two rounds below and non-inclusion of
one carried beside; the invalid `tx 3` and the mixed `tx 2` at the
candidate gate (the first refused, the second admitted); the conflict on
`o0` visible at id `9` and not below it, and the invalid rival at id `7`
making no conflict.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 16384

-- The direction of `Reaches`, pinned without any helper: the relation
-- steps from a block to its parents, never upward.
example : Reaches U 9 4 :=
  Relation.ReflTransGen.single (show (4 : Fin 16) ∈ (U.block 9).parents by decide)
example : ¬ Reaches U 0 9 := by
  intro h
  rcases h.cases_head with h | ⟨j, hj, -⟩
  · exact absurd h (by decide)
  · exact absurd (show (j : Fin 16) ∈ (U.block 0).parents from hj) (by simp [U, lk])

-- Direct reference, multi-hop reach, and a non-reach: id 9 reaches twin
-- 4 but not twin 5.
example : Reaches U 9 4 := Reaches.single (by decide)
example : Reaches U 13 4 :=
  (mem_history_iff (U := U) (b := 13) (i := 4) (by decide)).mp (by decide)
example : ¬ Reaches U 9 5 := fun h =>
  (by decide : (5 : Fin 16) ∉ history U 9) ((mem_history_iff (by decide)).mpr h)

-- The computed histories.
example : history U 9 = {0, 1, 2, 3, 4, 6, 7, 9} := by decide
example : history U 10 = {0, 1, 2, 3, 5, 6, 7, 10} := by decide

-- Inclusion: `tx 0` is carried by ids 4 and 6, two rounds below 13;
-- `tx 1` is carried beside id 6, not below it.
example : Includes U 13 0 := (mem_txsIn_iff (by decide)).mp (by decide)
example : ¬ Includes U 6 1 := fun h => (by decide : (1 : Fin 4) ∉ txsIn U 6)
  ((mem_txsIn_iff (by decide)).mpr h)

-- The transactions each block includes.
example : txsIn U 9 = {0, 1, 3} ∧ txsIn U 11 = {0, 1, 2, 3} := by decide

-- Candidates: valid, spending the object, included. The invalid `tx 3`
-- is refused at id 7 although carried there; `tx 1` is not a candidate
-- at id 6, which does not include it; the mixed `tx 2` contends for
-- `o1`.
example : IsCandidate U 9 0 0 ∧ IsCandidate U 9 0 1 := by
  refine ⟨(mem_candidates_iff (by decide)).mp (by decide),
    (mem_candidates_iff (by decide)).mp (by decide)⟩
example : ¬ IsCandidate U 7 0 3 := fun h => (by decide : (3 : Fin 4) ∉ candidates U 7 0)
  ((mem_candidates_iff (by decide)).mpr h)
example : ¬ IsCandidate U 6 0 1 := fun h => (by decide : (1 : Fin 4) ∉ candidates U 6 0)
  ((mem_candidates_iff (by decide)).mpr h)
example : IsCandidate U 11 1 2 := (mem_candidates_iff (by decide)).mp (by decide)

example : candidates U 9 0 = {0, 1} ∧ candidates U 7 0 = {1} ∧ candidates U 11 1 = {2} := by
  decide

-- Conflicts: visible at id 9 and above, not at id 6 (one candidate) nor
-- at id 7 (one valid candidate), and never on `o1`.
example : Conflicted U 9 0 := (conflicted_iff (by decide)).mpr (by decide)
example : Conflicted U 13 0 := (conflicted_iff (by decide)).mpr (by decide)
example : ¬ Conflicted U 6 0 := fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide)
example : ¬ Conflicted U 7 0 := fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide)
example : ¬ Conflicted U 11 1 := fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide)

end RedSnapper

end LeanDagTest
