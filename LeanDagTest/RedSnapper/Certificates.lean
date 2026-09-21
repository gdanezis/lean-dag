import LeanDag.RedSnapper.Helpers.Certificates
import LeanDag.RedSnapper.CertificateExclusion.Statement
import LeanDagTest.RedSnapper.Stance

/-!
# Witness: certificates

Two universes over `fourValidators` (`quorum = half = 3`), decided
through the surrogates of `Helpers/Certificates.lean`.

* **`UCert`** — a certificate forms, propagates, and is later retracted.
  Round 1: all four validators carry `tx 0` and ACK it (Byzantine `0`
  also with a twin, id 19, unreferenced). Round 2: every block's three
  parents are fast votes and every block keeps its ACK, so every round-2
  block is a certificate — a quorum of certificates at round 2
  (`FastQuorumAt`). Round 3 carries the rival `tx 1`, so the conflict is
  visible from there; every block above round 2 has a certificate in its
  history (`HasCert`, the propagation claim instantiated). Round 4:
  validators `1, 2, 3` retract — unlock votes, since each ACKed — and
  round 5's block is an unlock certificate: an ack certificate at round
  2 and an unlock certificate at round 5 coexist, so
  `AckUnlockExclusionBelow`'s round condition cannot be dropped. Id 15
  (round 4) sees a quorum of fast votes among its parents yet stands at
  `⊥`: `CertVisible` and not a certificate — the block's own ACK is
  indispensable.
* **`USkip`** — a skip certificate forms. Round 1: validators `1, 2, 3`
  carry both `tx 0` and `tx 1`, see the conflict at once, and declare
  `⊥` without ever ACKing — skip votes; Byzantine `0` ACKs `tx 0`.
  Round 2: the block by `1` over the three skip voters is a skip
  certificate; the block by `0` over one ACK and two skips is neither a
  certificate nor a skip certificate. No block of `USkip` certifies
  `tx 0`: the Byzantine ACK does not make one. Validator `1` also
  declares `⊥` on `o1`, where nothing conflicts — no vote.
* **`AtLeast` counts authors.** Three fast votes by two authors (twin 19
  beside id 4) do not reach `3`; three by three authors do; two do not.

Both universes satisfy the stance discipline.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper LeanDag.RedSnapper.CertificateExclusion

set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096

/-- Twenty-one ids, id 20 junk: the table described in the module
docstring. -/
def lkCert : Fin 21 → Block (Fin 4) (Fin 21) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 0, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 12 then
    { round := 3, author := 1, parents := {8, 9, 10}, txs := {1}, declares := fun _ => none }
  else if (i : ℕ) = 13 then
    { round := 3, author := 2, parents := {9, 10, 11}, txs := {1}, declares := fun _ => none }
  else if (i : ℕ) = 14 then
    { round := 3, author := 3, parents := {9, 10, 11}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 15 then
    { round := 4, author := 1, parents := {12, 13, 14}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 16 then
    { round := 4, author := 2, parents := {12, 13, 14}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 17 then
    { round := 4, author := 3, parents := {12, 13, 14}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 18 then
    { round := 5, author := 1, parents := {15, 16, 17}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 19 then
    { round := 1, author := 0, parents := {0, 1, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- The certificate universe: ids `0`–`19`, id `20` junk. -/
def UCert : Universe (Fin 4) (Fin 21) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 20
  block := lkCert
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UCert :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- Round 1: fast votes, including the Byzantine twin.
example : IsFastVote UCert 5 0 ∧ IsFastVote UCert 19 0 :=
  ⟨(isFastVote_iff (by decide)).mpr (by decide), (isFastVote_iff (by decide)).mpr (by decide)⟩

-- Round 2: every block is a certificate; a quorum of certificates at
-- round 2, none at round 1 (genesis parents vote nothing).
example : IsFastCert UCert 8 0 ∧ IsFastCert UCert 9 0 :=
  ⟨(isFastCert_iff (by decide)).mpr (by decide), (isFastCert_iff (by decide)).mpr (by decide)⟩
example : FastQuorumAt UCert 2 0 := fastQuorumAt_iff.mpr (by decide)
example : ¬ FastQuorumAt UCert 1 0 := fun h => absurd (fastQuorumAt_iff.mp h) (by decide)
example : ¬ IsFastCert UCert 5 0 := fun h => absurd ((isFastCert_iff (by decide)).mp h) (by decide)

-- Propagation, instantiated: every block above round 2 has a
-- certificate in its history; a round-2 block has one too (itself),
-- a round-1 block has none.
example : ∀ b ∈ UCert.ids, 2 < (UCert.block b).round → HasCertDec UCert b 0 := by decide
example : HasCert UCert 18 0 := (hasCert_iff (by decide)).mpr (by decide)
example : HasCert UCert 9 0 := (hasCert_iff (by decide)).mpr (by decide)
example : ¬ HasCert UCert 5 0 := fun h => absurd ((hasCert_iff (by decide)).mp h) (by decide)

-- The conflict becomes visible at round 3, and round 4 retracts: unlock
-- votes, since each validator had ACKed.
example : ¬ Conflicted UCert 11 0 := fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide)
example : Conflicted UCert 12 0 := (conflicted_iff (by decide)).mpr (by decide)
example : IsUnlockVote UCert 15 0 := (isUnlockVote_iff (by decide)).mpr (by decide)
example : ¬ IsSkipVote UCert 15 0 := fun h => absurd ((isSkipVote_iff (by decide)).mp h) (by decide)

-- Id 15 sees a quorum of fast votes among its parents but stands at `⊥`:
-- a certificate is visible, and 15 is not one.
example : CertVisible UCert 15 0 := (certVisible_iff (by decide)).mpr (by decide)
example : ¬ IsFastCert UCert 15 0 := fun h => absurd ((isFastCert_iff (by decide)).mp h) (by decide)
example : ¬ IsFastVote UCert 15 0 := fun h => absurd ((isFastVote_iff (by decide)).mp h) (by decide)
-- ... and a certificate is visible at id 12 through a parent's history.
example : CertVisible UCert 12 0 := (certVisible_iff (by decide)).mpr (by decide)

-- Round 5: an unlock certificate, three rounds above the ack certificate
-- at round 2. The round condition of `AckUnlockExclusionBelow` is
-- indispensable.
example : IsUnlockCert UCert 18 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ IsSkipCert UCert 18 0 := fun h => absurd ((isSkipCert_iff (by decide)).mp h) (by decide)
example : IsFastCert UCert 8 0 ∧ IsUnlockCert UCert 18 0 ∧
    ¬ ((UCert.block 18).round ≤ (UCert.block 8).round) :=
  ⟨(isFastCert_iff (by decide)).mpr (by decide), (isUnlockCert_iff (by decide)).mpr (by decide),
    by decide⟩

-- `AtLeast` counts authors: three fast votes by two authors fall short.
example : AtLeast UCert 3 {5, 6, 7} (fun b => IsFastVoteDec UCert b 0) :=
  atLeast_iff_filter.mpr (by decide)
example : ¬ AtLeast UCert 3 {5, 6} (fun b => IsFastVoteDec UCert b 0) := fun h =>
  absurd (atLeast_iff_filter.mp h) (by decide)
example : ¬ AtLeast UCert 3 {4, 19, 5} (fun b => IsFastVoteDec UCert b 0) := fun h =>
  absurd (atLeast_iff_filter.mp h) (by decide)
example : IsFastVoteDec UCert 4 0 ∧ IsFastVoteDec UCert 19 0 ∧ IsFastVoteDec UCert 5 0 := by
  decide

/-- Twelve ids, id 11 junk: the skip universe described in the module
docstring. -/
def lkSkip : Fin 12 → Block (Fin 4) (Fin 12) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0, 1},
      declares := fun _ => some .bot }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {5, 6, 7}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 0, parents := {4, 5, 6}, txs := {3},
      declares := fun o => if o = 0 then some (.ack 3) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅, declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- The skip universe: ids `0`–`10`, id `11` junk. -/
def USkip : Universe (Fin 4) (Fin 12) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 11
  block := lkSkip
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline USkip :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- Skip votes: `⊥` with the conflict visible and no ACK before.
example : IsSkipVote USkip 5 0 ∧ IsSkipVote USkip 6 0 ∧ IsSkipVote USkip 7 0 :=
  ⟨(isSkipVote_iff (by decide)).mpr (by decide), (isSkipVote_iff (by decide)).mpr (by decide),
    (isSkipVote_iff (by decide)).mpr (by decide)⟩
example : ¬ IsUnlockVote USkip 5 0 := fun h =>
  absurd ((isUnlockVote_iff (by decide)).mp h) (by decide)

-- `⊥` on `o1`, where nothing conflicts: no vote.
example : ¬ IsBotVote USkip 5 1 := fun h => absurd ((isBotVote_iff (by decide)).mp h) (by decide)

-- A skip certificate at round 2 over the three skip voters; the block
-- over one ACK and two skips is neither a certificate nor a skip
-- certificate.
example : IsSkipCert USkip 8 0 := (isSkipCert_iff (by decide)).mpr (by decide)
example : IsUnlockCert USkip 8 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ IsSkipCert USkip 9 0 := fun h => absurd ((isSkipCert_iff (by decide)).mp h) (by decide)
example : ¬ IsFastCert USkip 9 0 := fun h => absurd ((isFastCert_iff (by decide)).mp h) (by decide)

-- No block of `USkip` certifies `tx 0`: the Byzantine ACK does not make
-- a certificate, and `AckSkipExclusion` has its skip side witnessed.
example : ∀ C ∈ USkip.ids, ¬ IsFastCertDec USkip C 0 := by decide

-- An ACK for the invalid `tx 3`, included and declared, is no fast vote:
-- the `Valid` gate.
example : Includes USkip 9 3 ∧ StanceIs USkip 0 0 9 (some (.ack 3)) :=
  ⟨(mem_txsIn_iff (by decide)).mp (by decide), (stanceIs_some_iff (by decide)).mpr (by decide)⟩
example : ¬ IsFastVote USkip 9 3 := fun h => absurd ((isFastVote_iff (by decide)).mp h) (by decide)

end RedSnapper

end LeanDagTest
