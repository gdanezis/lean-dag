import LeanDag.RedSnapper.Helpers.Five
import LeanDag.RedSnapper.Five.FullCertSafety.Statement
import LeanDagTest.RedSnapper.Stance

/-!
# Witness: the 5f+1 certificates and the move rule

Four universes over `sixValidators` (`Fin 6`: `f = 1`, Byzantine `5`,
`quorum = 5`, `half = 3` — the two thresholds split natively), decided
through the surrogates of `Helpers/Five.lean`.

* **`U6Full`** — a full certificate forms. Genesis `0` carries `tx 0`;
  round 1: the five correct validators ACK it, Byzantine `5` declares
  `⊥` (the lone anti-voter). Round 2: id 12 over the five ACKs is a full
  certificate; id 13 over four of them and the Byzantine `⊥` is not
  (four authors < `quorum`) but is a half certificate — the two
  thresholds told apart on one block. One anti-voter beside a full
  certificate is no refutation: the premises of
  `CommitExcludesRefutation` are co-satisfiable up to the excluded
  object, and its conclusion checks concretely.
* **`U6Ref`** — refutations and both legal move shapes. Round 1: three
  ACKs for `tx 0`, one `⊥`, one rival ACK for `tx 1` (and the Byzantine
  rival ACK). Round 2: id 14 is a refutation of `ack 0` (`⊥` + two
  rival ACKs — three authors), over which its author legally moves
  `ack 0 → ⊥`; id 15 is a refutation of `⊥` **split across rival
  transactions** (two ACKs for `tx 0`, two for `tx 1` — no half
  certificate for either, the algorithm-versus-lemma-text gap of
  finding 8), over which its author legally moves `⊥ → ack 0` — the
  coin-style move `StanceDiscipline` forbids: `MoveDiscipline` holds
  and `StanceDiscipline` fails in one universe, which is why the
  `3f+1` automaton is not assumed at `5f+1`.
* **`U6Bad`** — `U6Ref` with id 14's parents swapped so only two
  anti-voters are visible: the same move now violates `MoveDiscipline`.
* **`U6Unlock`** — a full unlock certificate: five correct validators
  stand at `⊥` on an object with **no conflict anywhere** while Byzantine
  `5` ACKs alone; §8's unlock
  vote carries no conflict clause, and the §7-style `IsBotVote`-gated
  mutant counts nothing here. Id 13 over four `⊥`-standers is refused —
  the `quorum` pinned.

Anti-vote polarity, pinned in `U6Ref`: `⊥` counts against an ACK, a
rival ACK counts against an ACK, any ACK counts against `⊥`, the stance
itself does not count, and an undeclared stance (`none`) never counts.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper LeanDag.RedSnapper.FullCertSafety

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Fifteen ids, id 14 junk: genesis 0–5 (0 carries `tx 0`), five ACKs
and a Byzantine `⊥` at round 1, the full and half certificates at
round 2. -/
def lkFull : Fin 15 → Block (Fin 6) (Fin 15) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else ∅, declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Full : Universe (Fin 6) (Fin 15) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 14
  block := lkFull
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : MoveDiscipline U6Full := moveDiscipline_iff.mpr (by decide)

-- The full certificate at five vote authors; four are refused; the half
-- certificate at three — the two thresholds split on one block.
example : IsFullCert U6Full 12 0 := (isFullCert_iff (by decide)).mpr (by decide)
example : ¬ IsFullCert U6Full 13 0 := fun h =>
  absurd ((isFullCert_iff (by decide)).mp h) (by decide)
example : IsHalfCert U6Full 13 0 := (isHalfCert_iff (by decide)).mpr (by decide)

-- One anti-voter beside a full certificate is no refutation
-- (`CommitExcludesRefutation`'s premises co-satisfiable, its conclusion
-- concrete), and no full unlock certificate forms
-- (`CommitExcludesUnlock`'s conclusion concrete).
example : IsAntiVote U6Full 11 0 (.ack 0) := (isAntiVote_iff (by decide)).mpr (by decide)
example : ¬ IsRefutation U6Full 13 0 (.ack 0) := fun h =>
  absurd ((isRefutation_iff (by decide)).mp h) (by decide)
example : ¬ IsFullUnlockCert U6Full 13 0 := fun h =>
  absurd ((isFullUnlockCert_iff (by decide)).mp h) (by decide)

/-- Seventeen ids, id 16 junk: genesis 0–5 (0 carries `tx 0`, 1 carries
`tx 1`), the split round 1, the two refutations and the two legal moves
at round 2. -/
def lkRef : Fin 17 → Block (Fin 6) (Fin 17) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else if (i : ℕ) = 1 then {1} else ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
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
    { round := 2, author := 2, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Ref : Universe (Fin 6) (Fin 17) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 16
  block := lkRef
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The discriminator: the move rule holds — both changes carry their
-- refutations — while the `3f+1` automaton is violated by the
-- `⊥ → ack` move of validator 3 (ids 9 then 15).
example : MoveDiscipline U6Ref := moveDiscipline_iff.mpr (by decide)
example : ¬ StanceDiscipline U6Ref := fun h =>
  absurd (stanceDiscipline_iff.mp h) (by unfold NoReturnDec NoSwitchDec; decide)

-- Anti-vote polarity: `⊥` and a rival ACK count against an ACK, an ACK
-- counts against `⊥`; the stance itself and an undeclared stance do
-- not.
example : IsAntiVote U6Ref 9 0 (.ack 0) := (isAntiVote_iff (by decide)).mpr (by decide)
example : IsAntiVote U6Ref 10 0 (.ack 0) := (isAntiVote_iff (by decide)).mpr (by decide)
example : IsAntiVote U6Ref 7 0 .bot := (isAntiVote_iff (by decide)).mpr (by decide)
example : ¬ IsAntiVote U6Ref 7 0 (.ack 0) := fun h =>
  absurd ((isAntiVote_iff (by decide)).mp h) (by decide)
example : ¬ IsAntiVote U6Ref 2 0 (.ack 0) := fun h =>
  absurd ((isAntiVote_iff (by decide)).mp h) (by decide)

-- The two refutations; the refutation of `⊥` is split across rival
-- transactions, and neither rival reaches a half certificate — the
-- lemma-text's half-certificate premise would miss it (finding 8).
example : IsRefutation U6Ref 14 0 (.ack 0) := (isRefutation_iff (by decide)).mpr (by decide)
example : IsRefutation U6Ref 15 0 .bot := (isRefutation_iff (by decide)).mpr (by decide)
example : ¬ IsHalfCert U6Ref 15 0 := fun h =>
  absurd ((isHalfCert_iff (by decide)).mp h) (by decide)
example : ¬ IsHalfCert U6Ref 15 1 := fun h =>
  absurd ((isHalfCert_iff (by decide)).mp h) (by decide)

-- `SingleStance`'s premises live: fast votes for two genuinely
-- conflicting transactions exist (on different blocks, as the theorem
-- forces).
example : Conflict (T := inferInstance) (0 : Fin 4) 1 := ⟨by decide, by decide⟩
example : IsFastVote U6Ref 6 0 := (isFastVote_iff (by decide)).mpr (by decide)
example : IsFastVote U6Ref 10 1 := (isFastVote_iff (by decide)).mpr (by decide)

/-- `U6Ref` with id 14's parents swapped to `{6, 7, 8, 9, 10}`: only two
anti-voters visible, the same move now bare. -/
def lkRefBad : Fin 17 → Block (Fin 6) (Fin 17) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkRef i

def U6Bad : Universe (Fin 6) (Fin 17) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 16
  block := lkRefBad
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ MoveDiscipline U6Bad := fun h => absurd (moveDiscipline_iff.mp h) (by decide)

/-- Fifteen ids, id 14 junk: five correct `⊥`-standers on a conflict-free
object, the full unlock certificate at round 2, its four-author mutant
refused. -/
def lkUnlock : Fin 15 → Block (Fin 6) (Fin 15) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else ∅, declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Unlock : Universe (Fin 6) (Fin 15) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 14
  block := lkUnlock
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : MoveDiscipline U6Unlock := moveDiscipline_iff.mpr (by decide)

-- The full unlock certificate at five `⊥` authors; four are refused.
example : IsFullUnlockCert U6Unlock 12 0 :=
  (isFullUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ IsFullUnlockCert U6Unlock 13 0 := fun h =>
  absurd ((isFullUnlockCert_iff (by decide)).mp h) (by decide)

-- No conflict anywhere: the `⊥` stances are not `IsBotVote`s, so the
-- §7-style conflict-gated mutant of the unlock vote counts nothing
-- while the certificate stands — §8's unlock vote is bare `⊥`.
example : StanceIs U6Unlock 0 0 6 (some Stance.bot) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)
example : ¬ Conflicted U6Unlock 6 0 := fun h =>
  absurd ((conflicted_iff (by decide)).mp h) (by decide)
example : ¬ AtLeast U6Unlock (quorum (Fin 6)) (U6Unlock.block 12).parents
    (fun b => IsBotVote U6Unlock b 0) := fun h =>
  absurd (atLeast_iff_filter.mp ((atLeast_congr fun b hb =>
    isBotVote_iff (U6Unlock.complete 12 (by decide) b hb)).mp h)) (by decide)

-- And no full certificate beside it (`CommitExcludesUnlock`'s
-- conclusion, concrete).
example : ¬ IsFullCert U6Unlock 12 0 := fun h =>
  absurd ((isFullCert_iff (by decide)).mp h) (by decide)

-- The Byzantine lone ACKer anti-votes against `⊥`, yet no refutation of
-- `⊥` forms beside the full unlock certificate
-- (`UnlockExcludesRefutation`'s conclusion, concrete).
example : IsAntiVote U6Unlock 11 0 .bot := (isAntiVote_iff (by decide)).mpr (by decide)
example : ¬ IsRefutation U6Unlock 13 0 .bot := fun h =>
  absurd ((isRefutation_iff (by decide)).mp h) (by decide)

end RedSnapper

end LeanDagTest
