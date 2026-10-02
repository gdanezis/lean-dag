import LeanDag.RedSnapper.Helpers.Five
import LeanDagTest.RedSnapper.FiveCerts

/-!
# Witness hardening: the 5f+1 certificates and the move rule

Adopted from the Phase 7 vacuity audit — the mutants the `FiveCerts`
universes alone do not kill.

* **`U6Eq`** — the equivocation-voided anti-vote (D7 at the `IsAntiVote`
  level). Byzantine `5` declares `ack 0` and `⊥` in twin genesis blocks;
  a round-2 block reaching both twins reads a stance of `none` — it is
  an anti-vote against **nothing**, neither `ack 0` nor `⊥` — while a
  block reaching exactly one twin reads that twin. A mutant `IsAntiVote`
  that picks *any* latest declarer (dropping uniqueness) would count the
  double-reader against both values.
* **`U6Late`** — a stale refutation does not license a move. Validator
  0's round-2 self-parent (id 12) carries a genuine refutation of
  `ack 0`; by round 3 all three anti-voters have legally moved back to
  `ack 0` (each over its own refutation), so the round-3 move
  `ack 0 → ⊥` at id 17 sees **zero** anti-voters among its own parents:
  `MoveDiscipline` fails. This kills the causal-history weakening of the
  move rule — the paper source's *older*, commented-out `Movable`
  accepted a refutation anywhere in the history — which every
  `FiveCerts` example satisfies.
* **`U6Redecl`** — a same-value redeclaration is free: `U6Full` with
  id 12 redeclaring its standing `ack 0`, no refutation anywhere, and
  `MoveDiscipline` still holds — the `s' ≠ s` escape is load-bearing.
* **`U6Bad` boundary pins** — the mover's block sees exactly
  `half − 1 = 2` anti-voters (`¬ IsRefutation` direct), while its
  *sibling* id 15 does carry a refutation of `ack 0`: the
  `¬ MoveDiscipline U6Bad` witness genuinely tests "among the mover's
  own parents", not "nowhere in the universe".
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

-- The `half − 1` boundary, direct; the sibling refutation.
example : ¬ IsRefutation U6Bad 14 0 (.ack 0) := fun h =>
  absurd ((isRefutation_iff (by decide)).mp h) (by decide)
example : IsRefutation U6Bad 15 0 (.ack 0) := (isRefutation_iff (by decide)).mpr (by decide)

/-- Fourteen ids, id 13 junk: genesis 0–4 correct plus the declaring
twins 5 (`ack 0`) and 6 (`⊥`) of Byzantine author 5; round-1 blocks 7
(sees twin 5) and 8 (sees twin 6) and 9–11; Byzantine round-2 block 12
over 7–11 reaches both twins and declares nothing. -/
def lkEq : Fin 14 → Block (Fin 6) (Fin 14) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 5 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 5 then
    { round := 0, author := 5, parents := ∅, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 0, author := 5, parents := ∅, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 5}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 6}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 5, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Eq : Universe (Fin 6) (Fin 14) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 13
  block := lkEq
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Both twins visible: the stance is voided, and the block anti-votes
-- against nothing; one twin visible: that twin is read.
example : latestDeclarers U6Eq 5 0 12 = {5, 6} := by decide
example : StanceIs U6Eq 5 0 12 none := (stanceIs_none_iff (by decide)).mpr (by decide)
example : ¬ IsAntiVote U6Eq 12 0 (.ack 0) := fun h =>
  absurd ((isAntiVote_iff (by decide)).mp h) (by decide)
example : ¬ IsAntiVote U6Eq 12 0 .bot := fun h =>
  absurd ((isAntiVote_iff (by decide)).mp h) (by decide)
example : StanceIs U6Eq 5 0 7 (some (.ack 0)) :=
  (stanceIs_some_iff (by decide)).mpr (by decide)

/-- Nineteen ids, id 18 junk: a refutation of `ack 0` at validator 0's
round-2 self-parent goes stale — its three anti-voters legally return to
`ack 0` at round 2 — so validator 0's round-3 retraction sees no
anti-voter among its own parents. -/
def lkLate : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 17 then
    { round := 3, author := 0, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Late : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkLate
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The refutation exists at the self-parent — and each round-2 return
-- carries its own — but not at the moving block: the rule reads the
-- mover's own parents, not its history.
example : IsRefutation U6Late 12 0 (.ack 0) := (isRefutation_iff (by decide)).mpr (by decide)
example : IsRefutation U6Late 14 0 .bot := (isRefutation_iff (by decide)).mpr (by decide)
example : IsRefutation U6Late 15 0 (.ack 1) := (isRefutation_iff (by decide)).mpr (by decide)
example : ¬ IsRefutation U6Late 17 0 (.ack 0) := fun h =>
  absurd ((isRefutation_iff (by decide)).mp h) (by decide)
example : ¬ MoveDiscipline U6Late := fun h => absurd (moveDiscipline_iff.mp h) (by decide)

/-- `lkFull` with id 12 redeclaring its standing `ack 0`. -/
def lkFullRedecl : Fin 15 → Block (Fin 6) (Fin 15) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else lkFull i

def U6Redecl : Universe (Fin 6) (Fin 15) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 14
  block := lkFullRedecl
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- A same-value redeclaration needs no refutation: the `s' ≠ s` escape
-- of the move rule is load-bearing.
example : StanceIs U6Redecl 0 0 6 (some (.ack 0)) :=
  (stanceIs_some_iff (by decide)).mpr (by decide)
example : (U6Redecl.block 12).declares 0 = some (.ack 0) := by decide
example : ¬ IsRefutation U6Redecl 12 0 (.ack 0) := fun h =>
  absurd ((isRefutation_iff (by decide)).mp h) (by decide)
example : MoveDiscipline U6Redecl := moveDiscipline_iff.mpr (by decide)

end RedSnapper

end LeanDagTest
