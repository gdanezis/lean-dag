import LeanDag.RedSnapper.Helpers.Voting
import LeanDag.RedSnapper.Uncontested.Statement
import LeanDag.RedSnapper.ConflictResolution.Statement
import LeanDagTest.RedSnapper.Verdict

/-!
# Witness: the voting rule, synchrony, and the liveness scenarios

The Phase 6 hypotheses shown satisfiable end to end, on the universes
their conclusions are exhibited in — the liveness analogue of pinning a
fault model.

* **`ULive`, RS4's scenario**: validators `1, 2, 3` (validator `0`
  silent, Byzantine), a sole valid owned transaction carried by `1`'s
  round-1 block, everyone synchronised and populated; the voting rule
  holds, every RS4 hypothesis is pinned true, and the conclusion —
  `FastQuorumAt` at round 3 — is exhibited, with the `fastFinal`
  verdict on top.
* **`UTri`, the all-skip conflict (the paper's Case 2)**: both
  candidates visible from round 1, every correct block re-declares `⊥`;
  RS5's hypotheses hold, the trichotomy's unlock branch is exhibited at
  round 3, and with anchors `[12]` the release fires and both
  candidates are dropped.
* **`UKeep2`, the kept ACK (the paper's Case 1)**: certificates form at
  round 2 before the rival appears in `9`'s block; the conflicted
  correct validators keep their ACK under `CertVisible` — the
  `keep_certVisible` clause satisfied non-vacuously — and the
  trichotomy's certificate branch is exhibited at round 4.
* **Negatives.** The voting rule fails on `UBiv` (its round-3 blocks
  are conflicted and silent — `conflicted_declares` bites, and this is
  why the safety witnesses are not liveness witnesses); `UMix` is not
  synchronised (its round-2 blocks miss a correct round-1 block);
  `UByz` is populated on `Correct` at round 1 but not on everyone — the
  `T`-relativity of `PopulatedOn` doing work.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- RS4's scenario: fourteen ids, id 13 junk. Round 1 — `4` (validator
`1`) carries and ACKs `tx 0`, `5` and `6` (validators `2`, `3`) see
nothing yet; rounds 2 and 3 — everyone references all correct blocks
below and stands at `ack 0`. -/
def lkLive : Fin 14 → Block (Fin 4) (Fin 14) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 7 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 2, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 3, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 3, author := 1, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 11 then
    { round := 3, author := 2, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 12 then
    { round := 3, author := 3, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- RS4's universe: ids `0`–`12`, id `13` junk. -/
def ULive : Universe (Fin 4) (Fin 14) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 13
  block := lkLive
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Every hypothesis of RS4, satisfied at once.
example : StanceDiscipline ULive :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule ULive := votingRule_iff.mpr (by decide)
example : SynchronisedOn ULive (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULive (Correct : Finset (Fin 4)) 2 ∧
    PopulatedOn ULive (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide
example : (ULive.block 4).author ∈ (Correct : Finset (Fin 4)) ∧ Includes ULive 4 0 :=
  ⟨by decide, (mem_txsIn_iff (by decide)).mp (by decide)⟩

-- No rival is included anywhere: `tx 0`'s conflicts are `tx 1` and
-- `tx 3`, and no block carries either.
example : ∀ tx' : Fin 4, Conflict (0 : Fin 4) tx' →
    ∀ b ∈ ULive.ids, ¬ Includes ULive b tx' := by
  intro tx' hc b hb h
  have hmem : tx' ∈ txsIn ULive b := (mem_txsIn_iff hb).mpr h
  clear h
  revert b tx'
  decide

-- The conclusion: a quorum of certificates two rounds after the
-- carrier, and the consensusless verdict on top of it.
example : FastQuorumAt ULive 3 0 := fastQuorumAt_iff.mpr (by decide)

/-- An empty anchor sequence over `ULive`. -/
def ALive : Anchors ULive where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

example : TxVerdict ULive ALive (View.full ULive) 0 .finalized :=
  TxVerdict.fastFinal (r := 3) (by decide) (fastQuorumAtInView_iff.mpr (by decide))

/-- RS5's all-skip scenario: fourteen ids, id 13 junk. Both candidates
carried by every correct round-1 block; `⊥` declared and re-declared at
every round. -/
def lkTri : Fin 14 → Block (Fin 4) (Fin 14) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 2, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 3, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 3, author := 1, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 3, author := 2, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 12 then
    { round := 3, author := 3, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- RS5's all-skip universe: ids `0`–`12`, id `13` junk. -/
def UTri : Universe (Fin 4) (Fin 14) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 13
  block := lkTri
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- RS5's hypotheses, satisfied at once: the discipline, the rule, the
-- conflicted correct carrier at round 1, synchrony and population.
example : StanceDiscipline UTri :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule UTri := votingRule_iff.mpr (by decide)
example : Conflicted UTri 4 0 := (conflicted_iff (by decide)).mpr (by decide)
example : SynchronisedOn UTri (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn UTri (Correct : Finset (Fin 4)) 2 := by
  unfold PopulatedOn; decide

-- The trichotomy's unlock branch at round 3: no certificate exists
-- anywhere, and each correct round-3 block is an unlock certificate.
example : ∀ C ∈ UTri.ids, ¬ IsFastCertDec UTri C 0 := by decide
example : IsUnlockCert UTri 10 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : IsUnlockCert UTri 12 0 := (isUnlockCert_iff (by decide)).mpr (by decide)

/-- The single anchor 12 over `UTri`: correct-authored, at round
`r + 2`. -/
def ATri : Anchors UTri where
  seq := [12]
  mem := by decide
  chained := by simp

-- Anchor resolution, the release branch: the object resolves at the
-- anchor and both candidates are dropped there.
example : ResolvesAt UTri ATri 0 0 := resolvesAt_iff.mpr (by decide)
example : TxVerdict UTri ATri (View.full UTri) 0 .dropped :=
  TxVerdict.resolveDrop (i := 0) (a := 12) rfl (resolvesAt_iff.mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))
example : TxVerdict UTri ATri (View.full UTri) 1 .dropped :=
  TxVerdict.resolveDrop (i := 0) (a := 12) rfl (resolvesAt_iff.mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))

/-- The kept-ACK scenario: sixteen ids, id 15 junk. Round 1 — everyone
(Byzantine `0` included) carries and ACKs `tx 0`; round 2 — the correct
blocks certify it, and `9` also carries the rival `tx 1`: the conflict
is born at round 2 with certificates already visible; rounds 3 and 4 —
the conflicted correct validators keep their ACK, a certificate visible
among their parents each round. -/
def lkKeep2 : Fin 16 → Block (Fin 4) (Fin 16) (Fin 4) (Fin 2) := fun i =>
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
    { round := 2, author := 1, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 11 then
    { round := 3, author := 1, parents := {8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 12 then
    { round := 3, author := 2, parents := {8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 13 then
    { round := 3, author := 3, parents := {8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 14 then
    { round := 4, author := 1, parents := {11, 12, 13}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- The kept-ACK universe: ids `0`–`14`, id `15` junk. -/
def UKeep2 : Universe (Fin 4) (Fin 16) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 15
  block := lkKeep2
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- RS5's hypotheses with the conflict carrier at round 2, and the
-- `keep_certVisible` clause satisfied non-vacuously: `9` and the
-- round-3 and round-4 blocks all keep their ACK under a visible
-- conflict.
example : StanceDiscipline UKeep2 :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule UKeep2 := votingRule_iff.mpr (by decide)
example : Conflicted UKeep2 9 0 := (conflicted_iff (by decide)).mpr (by decide)
example : SynchronisedOn UKeep2 (Correct : Finset (Fin 4)) 2 := by
  unfold SynchronisedOn; decide
example : PopulatedOn UKeep2 (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide
example : Conflicted UKeep2 14 0 ∧ (UKeep2.block 14).declares 0 = some (.ack 0) :=
  ⟨(conflicted_iff (by decide)).mpr (by decide), by decide⟩

-- The trichotomy's certificate branch at round 4 (`r = 2`): a certified
-- candidate in the history, and no unlock certificate anywhere.
example : IsCandidate UKeep2 14 0 0 ∧ HasCert UKeep2 14 0 :=
  ⟨(mem_candidates_iff (by decide)).mp (by decide), (hasCert_iff (by decide)).mpr (by decide)⟩
example : ¬ IsUnlockCert UKeep2 14 0 := fun h =>
  absurd ((isUnlockCert_iff (by decide)).mp h) (by decide)

-- Negatives: the voting rule fails on `UBiv` — its round-3 blocks are
-- conflicted and silent, so `conflicted_declares` bites; `UMix` is not
-- synchronised (its round-2 blocks miss a correct round-1 block); and
-- `UByz` is populated on `Correct` at round 1 but not on everyone.
example : ¬ VotingRule UBiv := fun h => absurd (votingRule_iff.mp h) (by decide)
example : ¬ SynchronisedOn UMix (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn UByz (Correct : Finset (Fin 4)) 1 := by
  unfold PopulatedOn; decide
example : ¬ PopulatedOn UByz (Finset.univ : Finset (Fin 4)) 1 := by
  unfold PopulatedOn; decide

end RedSnapper

end LeanDagTest
