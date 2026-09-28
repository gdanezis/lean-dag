import LeanDag.RedSnapper.Helpers.Certificates
import LeanDag.RedSnapper.CertificateExclusion.Statement
import LeanDagTest.RedSnapper.Certificates

/-!
# Witness: certificate hardening

The batch after the Phase 4 vacuity audit, adopted from its compiled
probes.

* **Thresholds split** (`UF1`, `UF2` over `fiveValidators`:
  `quorum = 4`, `half = 3`). Every earlier certificate witness lives at
  `Fin 4`, where the two thresholds coincide, so a mutant swapping them
  passed the whole suite. `UF1` pins the ack certificate and the fast
  quorum at `quorum` (three fast-vote parents and three certificate
  authors are not enough) and the unlock certificate at `half`; `UF2`
  pins the skip certificate at `half`.
* **RS2 is not a tautology of the DAG.** On undisciplined universes each
  exclusivity claim fails: `UReturn` (a `⊥ → ack` return) carries an ack
  certificate beside a skip certificate and beside an unlock certificate
  at a LOWER round — the premises of `AckSkipExclusion` and
  `AckUnlockExclusionBelow` are co-satisfiable, and only the discipline
  refutes them; `USwitch` (an `ack → ack'` switch) certifies both
  conflicting transactions, refuting `CertUniqueness` and
  `HonestSingleAck`.
* **The `Correct` guard of `HonestSingleAck` is load-bearing**
  (`UByzTwin`): a disciplined universe whose Byzantine author fast-votes
  both conflicting transactions through twins — the guard-free variant is
  false.
* **`FastQuorumAt` counts authors** (`UTwinCert`): three certificate
  blocks by two authors (a Byzantine twin pair) are no fast quorum — the
  arc formalizes the author-counting reading, not the paper's literal
  block count (`docs/red-snapper.md` §3, finding 2).
* **Missing polarities on `UCert`**: `CertVisible` refuted at a round-1
  block, `IsUnlockCert` refuted at the certificate block 8, and the
  inherited-stance unlock vote at id 18 (declares nothing; the `⊥` is
  read from round 4).
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper LeanDag.RedSnapper.CertificateExclusion

set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096

-- Missing polarities on the committed universes.
example : ¬ CertVisible UCert 5 0 := fun h =>
  absurd ((certVisible_iff (by decide)).mp h) (by decide)
example : ¬ IsUnlockCert UCert 8 0 := fun h =>
  absurd ((isUnlockCert_iff (by decide)).mp h) (by decide)
example : IsUnlockVote UCert 18 0 := (isUnlockVote_iff (by decide)).mpr (by decide)

example : quorum (Fin 5) = 4 ∧ half (Fin 5) = 3 := by decide

/-- Ack/unlock universe at `n = 5`: round 1 acks by 0–3; round 2 certs by
0,1,2 and a fast vote by 3 over only three fast-vote parents; round 3
retractions by 1,2,3; round 4 an unlock certificate over exactly
`half = 3` retractors. -/
def lkF1 : Fin 20 → Block (Fin 5) (Fin 20) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 5 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 0, parents := {0, 1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 1, parents := {0, 1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 2, parents := {0, 1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 3, parents := {0, 1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 4, parents := {1, 2, 3, 4}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 0, parents := {5, 6, 7, 8}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 1, parents := {5, 6, 7, 8}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 2, parents := {5, 6, 7, 8}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 3, parents := {6, 7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 4, parents := {6, 7, 8, 9}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 15 then
    { round := 3, author := 1, parents := {11, 12, 13, 14}, txs := {1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 16 then
    { round := 3, author := 2, parents := {11, 12, 13, 14}, txs := {1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 17 then
    { round := 3, author := 3, parents := {11, 12, 13, 14}, txs := {1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 18 then
    { round := 3, author := 4, parents := {11, 12, 13, 14}, txs := ∅, declares := fun _ => none }
  else
    { round := 4, author := 1, parents := {15, 16, 17, 18}, txs := ∅, declares := fun _ => none }

def UF1 : Universe (Fin 5) (Fin 20) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkF1
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UF1 :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- Certificates at the quorum: id 10 has four fast-vote parent authors.
example : IsFastCert UF1 10 0 := (isFastCert_iff (by decide)).mpr (by decide)

-- Id 13 is a fast vote over exactly `half = 3` fast-vote parent authors:
-- NOT a certificate. A mutant `IsFastCert` at `half` calls it one.
example : IsFastVote UF1 13 0 := (isFastVote_iff (by decide)).mpr (by decide)
example : AtLeast UF1 (half (Fin 5)) (UF1.block 13).parents (fun b => IsFastVoteDec UF1 b 0) :=
  atLeast_iff_filter.mpr (by decide)
example : ¬ IsFastCert UF1 13 0 := fun h => absurd ((isFastCert_iff (by decide)).mp h) (by decide)

-- Round 2 holds exactly three certificate authors: no fast quorum. A
-- mutant `FastQuorumAt` at `half` fires.
example : ¬ FastQuorumAt UF1 2 0 := fun h => absurd (fastQuorumAt_iff.mp h) (by decide)
example : AtLeast UF1 (half (Fin 5)) (blocksAt UF1 2) (fun C => IsFastCertDec UF1 C 0) :=
  atLeast_iff_filter.mpr (by decide)

-- Round 4: an unlock certificate over exactly `half = 3` retractors —
-- below the quorum. A mutant `IsUnlockCert` at `quorum` refuses it.
example : IsUnlockCert UF1 19 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ AtLeast UF1 (quorum (Fin 5)) (UF1.block 19).parents (fun b => IsBotVoteDec UF1 b 0) :=
  fun h => absurd (atLeast_iff_filter.mp h) (by decide)

/-- Skip universe at `n = 5`: three skip voters at round 1, a skip
certificate at round 2 over exactly `half = 3 < quorum = 4` authors. -/
def lkF2 : Fin 11 → Block (Fin 5) (Fin 11) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 5 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 0, parents := {0, 1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 1, parents := {0, 1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 2, parents := {0, 1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 3, parents := {0, 1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 4, parents := {1, 2, 3, 4}, txs := ∅, declares := fun _ => none }
  else
    { round := 2, author := 1, parents := {6, 7, 8, 9}, txs := ∅, declares := fun _ => none }

def UF2 : Universe (Fin 5) (Fin 11) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkF2
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UF2 :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- A skip certificate over exactly `half = 3` skip-vote authors, below the
-- quorum: a mutant `IsSkipCert` at `quorum` refuses it.
example : IsSkipCert UF2 10 0 := (isSkipCert_iff (by decide)).mpr (by decide)
example : IsUnlockCert UF2 10 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ AtLeast UF2 (quorum (Fin 5)) (UF2.block 10).parents (fun b => IsSkipVoteDec UF2 b 0) :=
  fun h => absurd (atLeast_iff_filter.mp h) (by decide)

/-- `⊥ → ack` (no_return violated): skip votes at round 1, a skip/unlock
certificate at round 2 whose own block re-ACKs, a fast certificate at
round 3. Ack cert and skip cert coexist; unlock cert at round 2 ≤ 3. -/
def lkR : Fin 12 → Block (Fin 4) (Fin 12) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {0, 1, 2}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 3, author := 1, parents := {8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }

def UReturn : Universe (Fin 4) (Fin 12) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkR
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ StanceDiscipline UReturn :=
  fun h => absurd (stanceDiscipline_iff.mp h) (by unfold NoReturnDec NoSwitchDec; decide)

-- The premises of AckSkipExclusion are co-satisfiable: an ack certificate
-- (id 11, round 3) and a skip certificate on its input (id 8, round 2).
example : IsFastCert UReturn 11 0 := (isFastCert_iff (by decide)).mpr (by decide)
example : IsSkipCert UReturn 8 0 := (isSkipCert_iff (by decide)).mpr (by decide)
example : ¬ AckSkipExclusion UReturn := fun h =>
  h 11 (by decide) 8 (by decide) 0
    ((isFastCert_iff (by decide)).mpr (by decide))
    ((isSkipCert_iff (by decide)).mpr (by decide))

-- ... and of AckUnlockExclusionBelow: the unlock certificate sits BELOW
-- the ack certificate's round. Only the discipline refutes this.
example : IsUnlockCert UReturn 8 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ AckUnlockExclusionBelow UReturn := fun h =>
  h 11 (by decide) 8 (by decide) 0
    ((isFastCert_iff (by decide)).mpr (by decide))
    ((isUnlockCert_iff (by decide)).mpr (by decide))
    (by decide)

/-- `ack → ack'` (no_switch violated): everyone ACKs `tx 0` at round 1;
author 1 certifies `tx 0` at round 2 while 0 (Byz), 2, 3 switch to the
conflicting `tx 1`; author 2 certifies `tx 1` at round 3. -/
def lkS : Fin 13 → Block (Fin 4) (Fin 13) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 0, parents := {4, 5, 6}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else
    { round := 3, author := 2, parents := {9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }

def USwitch : Universe (Fin 4) (Fin 13) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkS
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ StanceDiscipline USwitch :=
  fun h => absurd (stanceDiscipline_iff.mp h) (by unfold NoReturnDec NoSwitchDec; decide)

-- Certificates for both conflicting transactions coexist.
example : IsFastCert USwitch 8 0 := (isFastCert_iff (by decide)).mpr (by decide)
example : IsFastCert USwitch 12 1 := (isFastCert_iff (by decide)).mpr (by decide)
example : ¬ CertUniqueness USwitch := fun h =>
  h 8 (by decide) 12 (by decide) 0 1 (by decide)
    ((isFastCert_iff (by decide)).mpr (by decide))
    ((isFastCert_iff (by decide)).mpr (by decide))

-- A correct author (2) fast-votes both conflicting transactions.
example : ¬ HonestSingleAck USwitch := fun h =>
  h 6 (by decide) 10 (by decide) (by decide) (by decide) 0 1 (by decide)
    ((isFastVote_iff (by decide)).mpr (by decide))
    ((isFastVote_iff (by decide)).mpr (by decide))

/-- Disciplined universe in which the Byzantine author 0 twins at round 1
and fast-votes both conflicting transactions: the `Correct` guard of
`HonestSingleAck` forbids nothing a Byzantine author does. -/
def lkT : Fin 6 → Block (Fin 4) (Fin 6) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 1, author := 0, parents := {1, 2, 3}, txs := {1},
      declares := fun o => if o = 0 then some (.ack 1) else none }

def UByzTwin : Universe (Fin 4) (Fin 6) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkT
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UByzTwin :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

example : IsFastVote UByzTwin 4 0 ∧ IsFastVote UByzTwin 5 1 ∧ Conflict (0 : Fin 4) 1 ∧
    (UByzTwin.block 4).author = (UByzTwin.block 5).author ∧
    (UByzTwin.block 4).author ∉ (Correct : Finset (Fin 4)) :=
  ⟨(isFastVote_iff (by decide)).mpr (by decide), (isFastVote_iff (by decide)).mpr (by decide),
    by decide, by decide, by decide⟩

-- The guard-free variant of HonestSingleAck is FALSE here even under the
-- discipline: dropping `Correct` breaks the theorem.
example : ¬ (∀ b ∈ UByzTwin.ids, ∀ b' ∈ UByzTwin.ids,
    (UByzTwin.block b').author = (UByzTwin.block b).author →
    ∀ tx tx' : Fin 4, Conflict tx tx' → IsFastVote UByzTwin b tx →
      ¬ IsFastVote UByzTwin b' tx') := fun h =>
  h 4 (by decide) 5 (by decide) (by decide) 0 1 (by decide)
    ((isFastVote_iff (by decide)).mpr (by decide))
    ((isFastVote_iff (by decide)).mpr (by decide))

/-- Round 1: all four ACK `tx 0`. Round 2: certificates by author 1
(id 8) and by the Byzantine author 0 twice (twins 9, 10) — three
certificate blocks, two authors. -/
def lkTC : Fin 11 → Block (Fin 4) (Fin 11) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 0, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else
    { round := 2, author := 0, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }

def UTwinCert : Universe (Fin 4) (Fin 11) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkTC
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UTwinCert :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- Three certificate blocks at round 2 ...
example : ((blocksAt UTwinCert 2).filter fun C => IsFastCertDec UTwinCert C 0).card = 3 := by
  decide
-- ... by two authors: no fast quorum. A block-counting mutant fires.
example : ¬ FastQuorumAt UTwinCert 2 0 := fun h => absurd (fastQuorumAt_iff.mp h) (by decide)

end RedSnapper

end LeanDagTest
