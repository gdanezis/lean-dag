import LeanDag.RedSnapper.Helpers.Stance
import LeanDagTest.RedSnapper.Universe

/-!
# Witness: stances read from the DAG, and the stance discipline

`StanceIs`, `AckedBefore` and `StanceDiscipline` exercised on the
universe `U` of `RedSnapperTest.Universe`, decided through the
surrogates of `Helpers/Stance.lean` (`declarers`, `latestDeclarers`,
`NoReturnDec`, `NoSwitchDec`) and bridged by their faithfulness lemmas.

* **Latest wins.** Correct validator `1` declares `ack 0` on `o0` at
  round 1 (id 6) and `⊥` at round 2 (id 9): its stance is `ack 0` at
  id 6, `⊥` at ids 9 and 13, and not `ack 0` at id 9.
* **Never declared.** Validator `2` never declares on `o0`: `none` at
  id 10; validator `3` has `ack 2` on `o1` at id 11 and `none` at id 8.
* **Equivocation, at the latest round only (D7).** Byzantine `0`'s
  twins 4 and 5 both declare on `o0`. At id 13, which reaches both, the
  stance is `none`; at id 9, which reaches twin 4 only, it is `ack 0`;
  at id 10, twin 5 only, `ack 1`; at id 14, which reaches both twins
  *and* the round-2 block 12, the latest declaring round holds one
  block and the stance is `ack 0` again.
* **`AckedBefore`.** True for `1` at id 9 (through id 6), false for `2`
  at id 10, true for Byzantine `0` at id 10 (through twin 5).
* **The discipline.** `U` satisfies it although Byzantine `0` switches
  `ack 1 → ack 0` along its own history (id 12 above id 5): the guard is
  `Correct`, and without it the switch clause fails on `U`. A second
  universe `UBad`, in which correct `1` returns from `⊥` to `ack 0` and
  correct `2` switches `ack 0 → ack 1`, is refuted clause by clause. A
  third universe `UKeep`, in which correct `1` re-ACKs and correct `2`
  re-declares `⊥`, shows the automaton's two self-loops permitted —
  without it a discipline forbidding `tx → tx` or `⊥ → ⊥` would pass
  every test — and pins the skip/unlock discrimination: `⊥` twice with
  no prior ACK is not `AckedBefore`, `ack` twice is.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096

-- The declaring and latest-declaring blocks.
example : declarers U 1 0 13 = {6, 9} ∧ latestDeclarers U 1 0 13 = {9} := by decide
example : latestDeclarers U 0 0 13 = {4, 5} ∧ latestDeclarers U 0 0 14 = {12} := by decide
example : declarers U 2 0 10 = ∅ := by decide

-- Latest wins: validator 1 on `o0`.
example : StanceIs U 1 0 6 (some (.ack 0)) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : StanceIs U 1 0 9 (some .bot) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : StanceIs U 1 0 13 (some .bot) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : ¬ StanceIs U 1 0 9 (some (.ack 0)) := fun h =>
  absurd ((stanceIs_some_iff (by decide)).mp h) (by decide)

-- Never declared: `none`. Validator 3 on `o1`.
example : StanceIs U 2 0 10 none := (stanceIs_none_iff (by decide)).mpr (by decide)
example : StanceIs U 3 1 11 (some (.ack 2)) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : StanceIs U 3 1 8 none := (stanceIs_none_iff (by decide)).mpr (by decide)

-- Equivocation at the latest declaring round voids the stance; one twin
-- in view, or a later declaration above both, does not.
example : StanceIs U 0 0 13 none := (stanceIs_none_iff (by decide)).mpr (by decide)
example : StanceIs U 0 0 9 (some (.ack 0)) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : StanceIs U 0 0 10 (some (.ack 1)) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : StanceIs U 0 0 14 (some (.ack 0)) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : ¬ StanceIs U 0 0 13 (some (.ack 0)) := fun h =>
  absurd ((stanceIs_some_iff (by decide)).mp h) (by decide)

-- `AckedBefore`.
example : AckedBefore U 1 0 9 := (ackedBefore_iff (by decide)).mpr (by decide)
example : ¬ AckedBefore U 2 0 10 := fun h => absurd ((ackedBefore_iff (by decide)).mp h) (by decide)
example : AckedBefore U 0 0 10 := (ackedBefore_iff (by decide)).mpr (by decide)

-- The discipline holds on `U` — and only because of the `Correct`
-- guard: Byzantine 0 switches `ack 1 → ack 0` along its own history.
example : StanceDiscipline U := stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example :
    ¬ (∀ b ∈ U.ids, ∀ p ∈ historyIn U b, (U.block p).author = (U.block b).author → p ≠ b →
      ∀ (o : Fin 2) (tx tx' : Fin 4), (U.block b).declares o = some (Stance.ack tx) →
        (U.block p).declares o = some (Stance.ack tx') → tx' = tx) := by
  decide

/-- Ten ids: genesis `0`–`3`; round 1 — `4` by correct `1` declaring `⊥`
on `o0`, `5` by correct `2` declaring `ack 0` on `o1`, `6` by correct
`3`, `7` by Byzantine `0`; round 2 — `8` by `1` returning to `ack 0` on
`o0`, `9` by `2` switching to `ack 1` on `o1`. -/
def lkBad : Fin 10 → Block (Fin 4) (Fin 10) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 1 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 2, author := 2, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 1 then some (.ack 1) else none }

/-- A well-formed universe whose correct validators break the
discipline. -/
def UBad : Universe (Fin 4) (Fin 10) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkBad
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Clause by clause: `1` returns from `⊥`, `2` switches transactions.
example : ¬ NoReturnDec UBad := by unfold NoReturnDec; decide
example : ¬ NoSwitchDec UBad := by unfold NoSwitchDec; decide
example : ¬ StanceDiscipline UBad := fun h =>
  absurd (stanceDiscipline_iff.mp h).1 (by unfold NoReturnDec; decide)

-- Both clauses hold on `U`, named separately.
example : NoReturnDec U ∧ NoSwitchDec U := by unfold NoReturnDec NoSwitchDec; decide

/-- Ten ids: genesis `0`–`3`; round 1 — `4` by correct `1` ACKing `tx 0`
on `o0`, `5` by correct `2` declaring `⊥` on `o0`, `6` by correct `3`,
`7` by Byzantine `0`; round 2 — `8` by `1` ACKing `tx 0` again
(`tx → tx`), `9` by `2` declaring `⊥` again (`⊥ → ⊥`). -/
def lkKeep : Fin 10 → Block (Fin 4) (Fin 10) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 2, author := 2, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }

/-- A universe whose correct validators keep their stances. -/
def UKeep : Universe (Fin 4) (Fin 10) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkKeep
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The automaton's two self-loops are permitted, and they really occur:
-- an earlier own declaring block sits below each repeated declaration.
example : StanceDiscipline UKeep :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : (UKeep.block 4).declares 0 = some (.ack 0) ∧ (UKeep.block 8).declares 0 = some (.ack 0)
    ∧ (UKeep.block 4).author = (UKeep.block 8).author ∧ 4 ∈ historyIn UKeep 8 := by decide
example : (UKeep.block 5).declares 0 = some .bot ∧ (UKeep.block 9).declares 0 = some .bot
    ∧ (UKeep.block 5).author = (UKeep.block 9).author ∧ 5 ∈ historyIn UKeep 9 := by decide
example : StanceIs UKeep 1 0 8 (some (.ack 0)) := (stanceIs_some_iff (by decide)).mpr (by decide)
example : StanceIs UKeep 2 0 9 (some .bot) := (stanceIs_some_iff (by decide)).mpr (by decide)

-- The skip/unlock discrimination: `⊥` twice with no ACK before is not
-- `AckedBefore`; an ACK repeated is.
example : AckedBefore UKeep 1 0 8 := (ackedBefore_iff (by decide)).mpr (by decide)
example : ¬ AckedBefore UKeep 2 0 9 := fun h =>
  absurd ((ackedBefore_iff (by decide)).mp h) (by decide)

/-! ### Arc audit: `stanceIs_none_iff` is never used in the .mp polarity:
no witness refutes a `none` stance where a unique latest declarer
exists. -/

example : ¬ StanceIs U 1 0 6 none := fun h =>
  absurd ((stanceIs_none_iff (by decide)).mp h) (by decide)

end RedSnapper

end LeanDagTest
