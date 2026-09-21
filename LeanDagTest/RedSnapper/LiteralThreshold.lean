import LeanDag.RedSnapper.Helpers.Five
import LeanDag.RedSnapper.Five.FullCertSafety.Statement
import LeanDagTest.RedSnapper.Universe

/-!
# Witness: the literal `4f + 1` threshold above `n = 5f + 1`

RS6's exclusion lemmas hold at every `n ≥ 3f + 1` because the full
certificate is read at `quorum = n − f`. The paper writes the threshold
as the constant `4f + 1`, which equals `n − f` only at `n = 5f + 1`.
Above it the constant is too small, and the lemma the move rule rests
on — no refutation of `ack tx` at or above a full certificate — fails
(record finding 19).

`sevenValidators` is `n = 7`, `f = 1`: `quorum = 6`, `half = 3`, and the
literal threshold is `5`. On `ULit`, validators `0..3` and the Byzantine
`6` ACK `tx 0` in round 1 while the correct `4, 5` stand at `⊥`. Block
`14` sees the five ACKs: a certificate at the literal threshold, not at
the quorum. In round 2 the Byzantine validator declares `⊥`, and round
3's block `20` sees three anti-votes — `4`, `5`, and the Byzantine — a
refutation of `ack tx 0`, one round above the literal certificate, with
no correct validator having moved. At the quorum the same count is
impossible: six ACKs leave one author outside, and the Byzantine one
makes two, below `half`.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Seven validators, `6` Byzantine: `n = 5f + 2`. -/
instance sevenValidators : Faults (Fin 7) where
  f := 1
  byzantine := {6}
  card_validators := by decide
  card_byzantine := by decide

example : quorum (Fin 7) = 6 ∧ half (Fin 7) = 3 ∧ 4 * (sevenValidators.f) + 1 = 5 := by decide

/-- The mutant: a full certificate at the paper's literal `4f + 1`. -/
def IsLiteralFullCert {Validator BlockId Tx Obj : Type*} [Fintype Validator]
    [DecidableEq Validator] [F : Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (C : BlockId) (tx : Tx) : Prop :=
  AtLeast U (4 * F.f + 1) (U.block C).parents fun b => IsFastVote U b tx

/-- Twenty-one ids. Genesis `0..6`, `0` carrying `tx 0`; round 1 `7..13`;
round 2 `14, 15, 16` (validators `0, 1, 2`), `17, 18` (validators
`4, 5`), `19` (Byzantine `6`, now at `⊥`); round 3 `20` (validator
`4`). -/
def lkLit : Fin 21 → Block (Fin 7) (Fin 21) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else ∅, declares := fun _ => none }
  else if h : (i : ℕ) < 11 then
    { round := 1, author := ⟨(i : ℕ) - 7, by omega⟩, parents := {0, 1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 12 then
    { round := 1, author := 5, parents := {0, 1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 13 then
    { round := 1, author := 6, parents := {0, 1, 2, 3, 4, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 0, parents := {7, 8, 9, 10, 11, 13}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 1, parents := {7, 8, 9, 10, 11, 12}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 2, parents := {7, 8, 9, 10, 11, 12}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 17 then
    { round := 2, author := 4, parents := {7, 8, 9, 10, 11, 12}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 18 then
    { round := 2, author := 5, parents := {7, 8, 9, 10, 11, 12}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 19 then
    { round := 2, author := 6, parents := {8, 9, 10, 11, 12, 13}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else
    { round := 3, author := 4, parents := {14, 15, 16, 17, 18, 19}, txs := ∅,
      declares := fun _ => none }

def ULit : Universe (Fin 7) (Fin 21) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkLit
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- No correct validator ever moves: the move rule holds.
example : MoveDiscipline ULit := moveDiscipline_iff.mpr (by decide)

-- Block 14 is a certificate at the literal threshold, not at the quorum.
example : IsLiteralFullCert ULit 14 0 :=
  (atLeast_parents_fastVote_iff (by decide)).mpr (by decide)
example : ¬ IsFullCert ULit 14 0 := fun h =>
  absurd ((isFullCert_iff (by decide)).mp h) (by decide)

-- One round above it, block 20 refutes `ack tx 0`: RS6's
-- `CommitExcludesRefutation`, read at the literal threshold, fails.
example : (ULit.block 14).round ≤ (ULit.block 20).round := by decide
example : IsRefutation ULit 20 0 (Stance.ack 0) :=
  (isRefutation_iff (by decide)).mpr (by decide)

-- At the quorum the lemma's conclusion holds on the same universe: no
-- block is a full certificate, so none sits under the refutation.
example : ∀ C ∈ ULit.ids, ¬ IsFullCertDec ULit C 0 := by decide

end RedSnapper

end LeanDagTest
