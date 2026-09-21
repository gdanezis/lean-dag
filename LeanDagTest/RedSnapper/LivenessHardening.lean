import LeanDagTest.RedSnapper.Liveness

/-!
# Witness: liveness hardening

The batch after the Phase 6 vacuity audit, adopted from its compiled
probes.

* **A genuine unlock scenario** (`UUnlk`): two validators ACK rival
  candidates before seeing the conflict, then retract — unlock votes,
  not skip votes — and the trichotomy's unlock branch holds at `r + 2`
  where its `IsSkipCert` mutant is false, and neither branch holds at
  `r + 1`. `UTri` alone could not tell those mutants apart.
* **`PopulatedOn (r₀ + 2)` is load-bearing** (`ULiveT`, `ULive`
  truncated at round 2): every other RS4 hypothesis holds and the
  conclusion fails; and on `ULive` itself the conclusion is pinned to
  exactly round `r₀ + 2`.
* **The synchrony gate's boundary**: `SynchronisedOn UKeep2 Correct 1`
  is true under the definition and false under the `R ≤ round` mutant
  (a round-1 block misses a correct genesis block); the `R + 1 < round`
  mutant is caught by the existing `UMix` negative, shown here.
* **Per-clause negatives** (`UN1`–`UN4`): one tiny universe per
  `VotingRule` clause, each refuting exactly the clause named — `UN4`
  with the other four proved to hold.
* **`PopulatedOn` counts the actual set, not the bound** (`UQ`, over
  the faultless `Faults (Fin 7)`): a round meets the quorum bound on
  distinct authors while a correct validator is absent.
* Re-pinned beside their statements: validity and the `Owned` gate of
  RS4's transaction, first pinned in `RedSnapperTest.Universe`.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

-- RS4's transaction, valid and owned (also pinned in
-- `RedSnapperTest.Universe`).
example : Transactions.Valid (0 : Fin 4) ∧ Owned (0 : Fin 4) := by decide

-- A. Completeness of the UTri trichotomy pin: block 11 was skipped.
example : IsUnlockCert UTri 11 0 := (isUnlockCert_iff (by decide)).mpr (by decide)

-- B. SynchronisedOn boundary. True fact not currently pinned:
example : SynchronisedOn UKeep2 (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide

-- B'. The `R ≤ round` mutant of the gate is FALSE on UKeep2 at R = 1
-- (block 5, round 1, author 1, misses correct genesis block 3):
example : ¬ (∀ b ∈ UKeep2.ids, (UKeep2.block b).author ∈ (Correct : Finset (Fin 4)) →
    1 ≤ (UKeep2.block b).round →
    ∀ b' ∈ UKeep2.ids, (UKeep2.block b').author ∈ (Correct : Finset (Fin 4)) →
      (UKeep2.block b').round + 1 = (UKeep2.block b).round →
      b' ∈ (UKeep2.block b).parents) := by
  decide

-- B''. The `R + 1 < round` mutant is TRUE on UMix at R = 1, i.e. the
-- existing negative ¬SynchronisedOn UMix 1 does catch that mutant:
example : (∀ b ∈ UMix.ids, (UMix.block b).author ∈ (Correct : Finset (Fin 4)) →
    1 + 1 < (UMix.block b).round →
    ∀ b' ∈ UMix.ids, (UMix.block b').author ∈ (Correct : Finset (Fin 4)) →
      (UMix.block b').round + 1 = (UMix.block b).round →
      b' ∈ (UMix.block b).parents) := by
  decide

-- C. FastLiveness conclusion-round mutants on ULive:
example : ¬ FastQuorumAt ULive 2 0 := fun h => absurd (fastQuorumAt_iff.mp h) (by decide)
example : ¬ FastQuorumAt ULive 4 0 := fun h => absurd (fastQuorumAt_iff.mp h) (by decide)

-- D. Truncated ULive: rounds 0–2 only. Every FastLiveness hypothesis
-- except PopulatedOn (r₀+2) holds, and the conclusion fails: the
-- statement mutant that drops the r₀+2 population is FALSE.
def ULiveT : Universe (Fin 4) (Fin 14) (Fin 4) (Fin 2) where
  ids := ((((Finset.univ.erase 13).erase 12).erase 11).erase 10)
  block := lkLive
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline ULiveT :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule ULiveT := votingRule_iff.mpr (by decide)
example : SynchronisedOn ULiveT (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULiveT (Correct : Finset (Fin 4)) 2 := by
  unfold PopulatedOn; decide
example : ¬ PopulatedOn ULiveT (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide
example : (ULiveT.block 4).author ∈ (Correct : Finset (Fin 4)) ∧ Includes ULiveT 4 0 :=
  ⟨by decide, (mem_txsIn_iff (by decide)).mp (by decide)⟩
example : ∀ tx' : Fin 4, Conflict (0 : Fin 4) tx' →
    ∀ b ∈ ULiveT.ids, ¬ Includes ULiveT b tx' := by
  intro tx' hc b hb h
  have hmem : tx' ∈ txsIn ULiveT b := (mem_txsIn_iff hb).mpr h
  clear h
  revert b tx'
  decide
example : ¬ FastQuorumAt ULiveT 3 0 := fun h => absurd (fastQuorumAt_iff.mp h) (by decide)

-- E. UUnlk: validators 1 and 2 ACK rival candidates at round 1 before
-- either sees the conflict; validator 3 carries both and skips; at
-- round 2 all three stand at ⊥ (two unlock votes, one skip vote);
-- round 3 blocks are unlock certificates but NOT skip certificates,
-- and no ack certificate exists. Refutes both the IsSkipCert mutant of
-- the trichotomy's unlock branch and the r+1 conclusion mutant.
def lkUnlk : Fin 14 → Block (Fin 4) (Fin 14) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 1) else none }
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

def UUnlk : Universe (Fin 4) (Fin 14) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 13
  block := lkUnlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Every RS5 hypothesis, carrier b₀ = 6 at r = 1.
example : StanceDiscipline UUnlk :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule UUnlk := votingRule_iff.mpr (by decide)
example : Conflicted UUnlk 6 0 := (conflicted_iff (by decide)).mpr (by decide)
example : SynchronisedOn UUnlk (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn UUnlk (Correct : Finset (Fin 4)) 2 := by
  unfold PopulatedOn; decide

-- Genuine unlock votes: prior ACKers now at ⊥ — not skip votes.
example : IsUnlockVote UUnlk 7 0 ∧ ¬ IsSkipVote UUnlk 7 0 :=
  ⟨(isUnlockVote_iff (by decide)).mpr (by decide),
   fun h => absurd ((isSkipVote_iff (by decide)).mp h) (by decide)⟩

-- The trichotomy's unlock branch holds at r + 2 = 3 ...
example : IsUnlockCert UUnlk 10 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : IsUnlockCert UUnlk 11 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : IsUnlockCert UUnlk 12 0 := (isUnlockCert_iff (by decide)).mpr (by decide)

-- ... but the IsSkipCert mutant of that branch is FALSE there, and so
-- is the certificate branch: the mutant statement is refuted.
example : ¬ IsSkipCert UUnlk 10 0 :=
  fun h => absurd ((isSkipCert_iff (by decide)).mp h) (by decide)
example : ∀ C ∈ UUnlk.ids, ∀ tx : Fin 4, ¬ IsFastCertDec UUnlk C tx := by decide

-- The r+1 conclusion mutant is FALSE at the round-2 blocks: neither
-- branch holds one round early.
example : ¬ IsUnlockCert UUnlk 7 0 :=
  fun h => absurd ((isUnlockCert_iff (by decide)).mp h) (by decide)
example : ¬ HasCert UUnlk 7 0 :=
  fun h => absurd ((hasCert_iff (by decide)).mp h) (by decide)
example : ¬ HasCert UUnlk 7 1 :=
  fun h => absurd ((hasCert_iff (by decide)).mp h) (by decide)

-- F. The no-rival premise is stronger than the algorithm needs: an
-- INVALID rival (tx 3, Conflict 0 3 holds) included by one block voids
-- the premise while every hypothesis and the conclusion still hold.
def lkLiveInv : Fin 14 → Block (Fin 4) (Fin 14) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {3}, declares := fun _ => none }
  else lkLive i

def ULiveInv : Universe (Fin 4) (Fin 14) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 13
  block := lkLiveInv
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline ULiveInv :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule ULiveInv := votingRule_iff.mpr (by decide)
example : SynchronisedOn ULiveInv (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULiveInv (Correct : Finset (Fin 4)) 2 ∧
    PopulatedOn ULiveInv (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide
-- The conclusion still holds: the invalid rival changes nothing.
example : FastQuorumAt ULiveInv 3 0 := fastQuorumAt_iff.mpr (by decide)
-- The UNGATED premise of finding 18 is void — the invalid rival is
-- "included" — which is why RS4's premise gates rivals by validity:
example : ¬ (∀ tx' : Fin 4, Conflict (0 : Fin 4) tx' →
    ∀ b ∈ ULiveInv.ids, ¬ Includes ULiveInv b tx') := by
  intro h
  exact h 3 (by decide) 6 (by decide) ((mem_txsIn_iff (by decide)).mp (by decide))

-- ... while the gated premise holds here, so the fixed RS4 applies.
example : ∀ tx' : Fin 4, Transactions.Valid tx' → Conflict (0 : Fin 4) tx' →
    ∀ b ∈ ULiveInv.ids, ¬ Includes ULiveInv b tx' := by
  intro tx' hv hc b hb h
  have hmem : tx' ∈ txsIn ULiveInv b := (mem_txsIn_iff hb).mpr h
  clear h
  revert b tx'
  decide

/-- Genesis 0–3 plus one round-1 block by correct validator 1; the
round-1 block's content is the parameter. -/
def lk1 (txs : Finset (Fin 4)) (d : Option (Stance (Fin 4))) :
    Fin 6 → Block (Fin 4) (Fin 6) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := txs,
      declares := fun o => if o = 0 then d else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

-- N1: ack for a transaction that is nowhere in the history.
def UN1 : Universe (Fin 4) (Fin 6) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 5
  block := lk1 ∅ (some (.ack 0))
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ (∀ b ∈ UN1.ids, (UN1.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), (UN1.block b).declares o = some (Stance.ack tx) →
      tx ∈ candidates UN1 b o) := by decide
example : ¬ VotingRule UN1 := fun h => absurd (votingRule_iff.mp h) (by decide)

-- N2: ⊥ with no visible conflict.
def UN2 : Universe (Fin 4) (Fin 6) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 5
  block := lk1 ∅ (some .bot)
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ (∀ b ∈ UN2.ids, (UN2.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ o : Fin 2, (UN2.block b).declares o = some Stance.bot →
      1 < (candidates UN2 b o).card) := by decide
example : ¬ VotingRule UN2 := fun h => absurd (votingRule_iff.mp h) (by decide)

-- N3: a sole candidate visible, the author silent — ack_sole bites.
def UN3 : Universe (Fin 4) (Fin 6) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 5
  block := lk1 {0} none
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ (∀ b ∈ UN3.ids, (UN3.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), tx ∈ candidates UN3 b o →
      (∀ tx' ∈ candidates UN3 b o, tx' = tx) →
      ¬ StanceSomeDec UN3 (UN3.block b).author o b Stance.bot →
      StanceSomeDec UN3 (UN3.block b).author o b (Stance.ack tx)) := by decide
example : ¬ VotingRule UN3 := fun h => absurd (votingRule_iff.mp h) (by decide)

-- N4: an ACK kept under a visible conflict with no certificate visible.
def UN4 : Universe (Fin 4) (Fin 6) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 5
  block := lk1 {0, 1} (some (.ack 0))
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ (∀ b ∈ UN4.ids, (UN4.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), 1 < (candidates UN4 b o).card →
      (UN4.block b).declares o = some (Stance.ack tx) →
      CertVisibleDec UN4 b tx) := by decide
-- ... while the other four clauses all hold on UN4: clause-attributed.
example : (∀ b ∈ UN4.ids, (UN4.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), (UN4.block b).declares o = some (Stance.ack tx) →
      tx ∈ candidates UN4 b o) ∧
    (∀ b ∈ UN4.ids, (UN4.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ o : Fin 2, (UN4.block b).declares o = some Stance.bot →
      1 < (candidates UN4 b o).card) ∧
    (∀ b ∈ UN4.ids, (UN4.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), tx ∈ candidates UN4 b o →
      (∀ tx' ∈ candidates UN4 b o, tx' = tx) →
      ¬ StanceSomeDec UN4 (UN4.block b).author o b Stance.bot →
      StanceSomeDec UN4 (UN4.block b).author o b (Stance.ack tx)) ∧
    (∀ b ∈ UN4.ids, (UN4.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ o : Fin 2, 1 < (candidates UN4 b o).card → (UN4.block b).declares o ≠ none) := by
  decide
example : ¬ VotingRule UN4 := fun h => absurd (votingRule_iff.mp h) (by decide)

/-- The population-versus-bound universe, over the faultless committee
`tight 2 : Faults (Fin 7)` (`RedSnapperTest.Model`): seven genesis
blocks and a round 1 authored by validators `0`–`4` only. -/
def lkQ : Fin 13 → Block (Fin 7) (Fin 13) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if h : (i : ℕ) < 12 then
    { round := 1, author := ⟨(i : ℕ) - 7, by omega⟩, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- Ids `0`–`11`, id `12` junk. -/
def UQ : Universe (Fin 7) (Fin 13) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 12
  block := lkQ
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Everyone is correct; validators 5 and 6 author nothing at round 1,
-- yet the round meets the quorum bound on distinct authors: the
-- count-to-the-bound mutant of `PopulatedOn` is true where the
-- definition is false.
example : (Correct : Finset (Fin 7)) = Finset.univ := by decide
example : ¬ PopulatedOn UQ (Correct : Finset (Fin 7)) 1 := by
  unfold PopulatedOn; decide
example : quorum (Fin 7) ≤ (authorsOf UQ.block (blocksAt UQ 1)).card := by decide

/-! ### Arc audit: `VotingRule.conflicted_declares` has no clause-attributed
negative: ¬VotingRule UBiv also breaks ack_sole. UN5 isolates it. -/

def UN5 : Universe (Fin 4) (Fin 6) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 5
  block := lk1 {0, 1} none
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- conflicted_declares fails ...
example : ¬ (∀ b ∈ UN5.ids, (UN5.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ o : Fin 2, 1 < (candidates UN5 b o).card → (UN5.block b).declares o ≠ none) := by
  decide
example : ¬ VotingRule UN5 := fun h => absurd (votingRule_iff.mp h) (by decide)

-- ... while the other four clauses hold: clause-attributed.
example : (∀ b ∈ UN5.ids, (UN5.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), (UN5.block b).declares o = some (Stance.ack tx) →
      tx ∈ candidates UN5 b o) ∧
    (∀ b ∈ UN5.ids, (UN5.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ o : Fin 2, (UN5.block b).declares o = some Stance.bot →
      1 < (candidates UN5 b o).card) ∧
    (∀ b ∈ UN5.ids, (UN5.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), tx ∈ candidates UN5 b o →
      (∀ tx' ∈ candidates UN5 b o, tx' = tx) →
      ¬ StanceSomeDec UN5 (UN5.block b).author o b Stance.bot →
      StanceSomeDec UN5 (UN5.block b).author o b (Stance.ack tx)) ∧
    (∀ b ∈ UN5.ids, (UN5.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), 1 < (candidates UN5 b o).card →
      (UN5.block b).declares o = some (Stance.ack tx) →
      CertVisibleDec UN5 b tx) := by decide

-- And ack_sole indeed ALSO fails on UBiv (block 7: sole candidate tx 1,
-- author silent): the committed ¬VotingRule UBiv is not attributable to
-- conflicted_declares.
example : ¬ (∀ b ∈ UBiv.ids, (UBiv.block b).author ∈ (Correct : Finset (Fin 4)) →
    ∀ (o : Fin 2) (tx : Fin 4), tx ∈ candidates UBiv b o →
      (∀ tx' ∈ candidates UBiv b o, tx' = tx) →
      ¬ StanceSomeDec UBiv (UBiv.block b).author o b Stance.bot →
      StanceSomeDec UBiv (UBiv.block b).author o b (Stance.ack tx)) := by decide
/-! ### Arc audit: RS5's AnchorDecides LEFT disjunct is never exhibited under
live premises: UKeep2 (VotingRule holds) has no anchors. Anchor 14
finalizes the kept candidate by resolveCommit. -/

def AKeep2 : Anchors UKeep2 where
  seq := [14]
  mem := by decide
  chained := by simp

example : TxVerdict UKeep2 AKeep2 (View.full UKeep2) 0 .finalized :=
  TxVerdict.resolveCommit (i := 0) (a := 14) rfl
    ((conflicted_iff (by decide)).mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))
    (fun h => absurd (deadAt_iff.mp h) (by decide))

end RedSnapper

end LeanDagTest
