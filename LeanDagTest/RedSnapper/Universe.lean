import LeanDag.RedSnapper.Helpers.Block
import LeanDag.RedSnapper.Model.View
import LeanDagTest.RedSnapper.Model

/-!
# Witness: transactions, a block universe with faults, and a view

Concrete instances of `Model/Block.lean`, `Model/Universe.lean` and
`Model/View.lean`, checked by `decide`, so the structures are
demonstrably satisfiable and each condition bites.

* **Transactions.** Four transactions over two object versions: `0`, `1`
  and `3` spend `o0`, `2` spends `o1`; `3` is invalid; `2` is mixed.
  So `0` and `1` conflict, `3` is a conflicting but invalid rival, and
  `2` is the mixed candidate for the other object.
* **The universe** `U`, over `fourValidators` (`Fin 4`, `f = 1`,
  validator `0` Byzantine), sixteen ids with id `15` junk outside the
  universe. Genesis `0`–`3`. Round 1: Byzantine `0` equivocates — twin
  `4` carries `tx 0` and declares `ack 0` on `o0`, twin `5` carries
  `tx 1` and declares `ack 1`; correct `1` (id `6`) carries `tx 0` and
  ACKs it; correct `2` (id `7`) carries `tx 1` and the invalid `tx 3`
  and declares nothing; correct `3` (id `8`) carries the mixed `tx 2`.
  Round 2: `1` (id `9`, parents `{4, 6, 7}`) sees the conflict and
  declares `⊥`; `2` (id `10`, parents `{5, 6, 7}`) reaches twin `5`
  only; `3` (id `11`) ACKs `tx 2` on `o1`; Byzantine `0` (id `12`,
  parents `{5, 7, 8}`) declares `ack 0` after `ack 1` in its own
  history — a switch the discipline forbids to correct validators only.
  Round 3: `1` (id `13`, parents `{9, 10, 11}`) reaches both twins; `2`
  (id `14`, parents `{9, 10, 12}`) reaches the switch. Every correct
  block references its author's previous block.
* **The negatives.** Unguarded non-equivocation is false in `U`; a
  correct block without its self-parent is rejected by `self_parent`;
  each `ValidWrt` field rejects a malformed block.
* **A view** `V` withholding twin `5` and everything above it; the same
  id set plus id `10` is not reference-closed, and a set holding the
  junk id is not a subset of the universe.
* **A Byzantine validator off the chain** (`UByz`): validator `0`
  produces no round-1 block and its round-2 block links no block of its
  own — admitted, because `self_parent` is guarded by `Correct`;
  unguarded, the universe is refuted. Every correct validator, by
  contrast, has a block at every round below its own.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 16384

/-- Four transactions over two object versions: `0`, `1`, `3` spend
`o0`, `2` spends `o1`; `3` is invalid; `2` is mixed. -/
instance fourTxs : Transactions (Fin 4) (Fin 2) where
  input := fun tx => if tx = 2 then 1 else 0
  Valid := fun tx => tx ≠ 3
  Mixed := fun tx => tx = 2

example : Conflict (0 : Fin 4) 1 ∧ Conflict (0 : Fin 4) 3 := by decide
example : ¬ Conflict (0 : Fin 4) 2 ∧ ¬ Conflict (1 : Fin 4) 1 := by decide
example : Owned (0 : Fin 4) ∧ ¬ Owned (2 : Fin 4) := by decide
example : Transactions.Valid (0 : Fin 4) ∧ ¬ Transactions.Valid (3 : Fin 4) := by decide

/-- The sixteen-id table described in the module docstring. -/
def lk : Fin 16 → Block (Fin 4) (Fin 16) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 0, parents := {0, 1, 3}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {1, 3}, declares := fun _ => none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {2}, declares := fun _ => none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 1, parents := {4, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 3, parents := {6, 7, 8}, txs := ∅,
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {5, 7, 8}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 13 then
    { round := 3, author := 1, parents := {9, 10, 11}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 14 then
    { round := 3, author := 2, parents := {9, 10, 12}, txs := ∅, declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- The witness universe: ids `0`–`14`, id `15` junk. -/
def U : Universe (Fin 4) (Fin 16) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 15
  block := lk
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The guard does real work: without the `Correct` restriction,
-- non-equivocation is false in `U` — ids 4 and 5 are a Byzantine
-- equivocation.
example :
    ¬ (∀ i ∈ U.ids, ∀ j ∈ U.ids,
      (U.block i).author = (U.block j).author →
      (U.block i).round = (U.block j).round → i = j) := by
  decide

-- `self_parent` bites: the same table with correct validator `1`'s
-- round-1 block referencing `{0, 2, 3}` instead of its own genesis block
-- is rejected — although every other universe condition still holds.
def lkNoChain : Fin 16 → Block (Fin 4) (Fin 16) (Fin 4) (Fin 2) :=
  Function.update lk 6
    { round := 1, author := 1, parents := {0, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }

example :
    ¬ (∀ i ∈ Finset.univ.erase (15 : Fin 16),
      (lkNoChain i).author ∈ (Correct : Finset (Fin 4)) → 0 < (lkNoChain i).round →
      ∃ j ∈ (lkNoChain i).parents, (lkNoChain j).author = (lkNoChain i).author) := by
  decide

example : ∀ i ∈ Finset.univ.erase (15 : Fin 16), ValidWrt lkNoChain (lkNoChain i) := by
  decide

-- `predecessor` bites: a round-2 block referencing genesis blocks.
example :
    ¬ ValidWrt lk
      { round := 2, author := 2, parents := {0, 1, 2}, txs := ∅,
        declares := fun _ => none } := by
  decide

-- `distinct_authors` bites: parents include both twins of author `0`
-- (three ids, so `quorum` alone counts only two authors — make it four
-- ids so that `quorum` passes and only distinctness fails).
example :
    ¬ ValidWrt lk
      { round := 2, author := 2, parents := {4, 5, 6, 7}, txs := ∅,
        declares := fun _ => none } := by
  decide

-- `quorum` bites: two distinct authors, one short of `quorum = 3`.
example :
    ¬ ValidWrt lk
      { round := 1, author := 2, parents := {0, 1}, txs := ∅,
        declares := fun _ => none } := by
  decide

/-- A validator's local view: everything below and beside twin `4`, with
twin `5` withheld and so ids `10`, `12`, `13`, `14` undelivered. -/
def V : View U where
  ids := {0, 1, 2, 3, 4, 6, 7, 8, 9, 11}
  subset_ids := by decide
  complete := by decide

-- Adding id `10` without its parent `5` breaks reference-closure.
example :
    ¬ (∀ i ∈ ({0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11} : Finset (Fin 16)),
      ∀ j ∈ (U.block i).parents, j ∈ ({0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11} : Finset (Fin 16))) := by
  decide

-- A set holding the junk id is not a subset of the universe.
example : ¬ (({0, 15} : Finset (Fin 16)) ⊆ U.ids) := by decide

/-- Nine ids: genesis `0`–`3`; round 1 — `4`, `5`, `6` by the correct
validators `1`, `2`, `3`; round 2 — `7` by correct `1`, and `8` by
Byzantine `0`, which produced no round-1 block and links no block of its
own. -/
def lkByz : Fin 9 → Block (Fin 4) (Fin 9) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 7 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅, declares := fun _ => none }
  else
    { round := 2, author := 0, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }

/-- A universe in which the Byzantine validator skips a round and never
links itself. -/
def UByz : Universe (Fin 4) (Fin 9) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkByz
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The `Correct` guard bites: unguarded, `UByz` is refuted.
example :
    ¬ (∀ i ∈ UByz.ids, 0 < (UByz.block i).round →
      ∃ j ∈ (UByz.block i).parents, (UByz.block j).author = (UByz.block i).author) := by
  decide

-- Byzantine `0` has no round-1 block at all.
example : ¬ ∃ i ∈ UByz.ids, (UByz.block i).author = 0 ∧ (UByz.block i).round = 1 := by decide

-- Every correct author has a block at every round below its own: the
-- chain admits no gap.
example : ∀ i ∈ UByz.ids, (UByz.block i).author ∈ (Correct : Finset (Fin 4)) →
    ∀ r ≤ (UByz.block i).round, ∃ j ∈ UByz.ids,
      (UByz.block j).author = (UByz.block i).author ∧ (UByz.block j).round = r := by
  decide

end RedSnapper

end LeanDagTest
