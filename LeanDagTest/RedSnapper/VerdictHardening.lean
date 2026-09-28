import LeanDag.RedSnapper.Helpers.Dead
import LeanDag.RedSnapper.TxAgreement.Statement
import LeanDagTest.RedSnapper.Verdict

/-!
# Witness: verdict hardening

The batch after the Phase 5 vacuity audit, adopted from its compiled
probes.

* **RS3 is falsifiable, and the discipline is load-bearing** (`UND`):
  validators skip-vote, re-ACK (a `no_return` violation), certify, then
  switch to the rival (a `no_switch` violation). `tx 0` is both
  fast-finalized and dropped at the anchor, and the rival is finalized
  too: `VerdictAgreement` and `NoConflictingFinal` are provably false
  there — so neither is a tautology of the DAG, and `StanceDiscipline`
  in RS3's statement does the work.
* **`Anchors.chained` is load-bearing**: the unchainable list
  `[13, 12]` over `UBiv` would commit and drop `tx 0` at once; the
  five facts of the loophole are pinned, and `¬ Reaches UBiv 12 13` is
  why the list cannot be built.
* **The `Owned` gate carries `MixedViaAnchor`** — pinned with an empty
  anchor list over `UMix`.
* **The skip route's round quorum is `quorum`, not `half`** (`USkip5`,
  at `n = 5`: `quorum = 4`, `half = 3`): three skip-certificate
  authors are a `half` but not a quorum, so `SkipQuorumAtInView` is
  false — a `half` mutant fires; and each skip certificate itself needs
  only `half` skip voters — a `quorum` mutant refuses it (with
  `UF2`'s pin). D1's reading, now discriminated on the skip side too.
* **The skip quorum reads the view**: a partial view of `USkip2`
  holding one of the three skip-certificate blocks has no quorum.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Rounds: 0 genesis (tx 0 in block 1, tx 1 in block 2); 1 — skip votes by
1,2,3 (blocks 4,5,6); 2 — skip cert (7, Byz 0) and re-ACKs of tx 0 (8,9,10:
no_return violations); 3 — certs for tx 0 (11,12,13) and the anchor 14 (Byz 0,
parents {7,8,9}: sees the skip cert, no cert); 4 — switch to ack tx 1
(15,16,17: no_switch violations); 5 — certs for tx 1 (18,19,20). -/
def lkND : Fin 21 → Block (Fin 4) (Fin 21) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 1 then {0} else if (i : ℕ) = 2 then {1} else ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 2, author := 0, parents := {4, 5, 6}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 2, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {4, 5, 6}, txs := ∅,
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
    { round := 3, author := 0, parents := {7, 8, 9}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 15 then
    { round := 4, author := 1, parents := {11, 12, 13}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 16 then
    { round := 4, author := 2, parents := {11, 12, 13}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 17 then
    { round := 4, author := 3, parents := {11, 12, 13}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 18 then
    { round := 5, author := 1, parents := {15, 16, 17}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 19 then
    { round := 5, author := 2, parents := {15, 16, 17}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else
    { round := 5, author := 3, parents := {15, 16, 17}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }

def UND : Universe (Fin 4) (Fin 21) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkND
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def AND1 : Anchors UND where
  seq := [14]
  mem := by decide
  chained := by simp

-- The discipline fails: 8 (ack 0) after 4 (⊥), same correct author 1.
example : ¬ StanceDiscipline UND := fun h =>
  (h.no_return 8 (by decide) (by decide) 4 (by decide) (by decide)
    ((mem_history_iff (by decide)).mp (by decide)) (by decide) 0 0 (by decide)) (by decide)

-- Both fates for tx 0.
example : TxVerdict UND AND1 (View.full UND) 0 .finalized :=
  TxVerdict.fastFinal (r := 3) (by decide) (fastQuorumAtInView_iff.mpr (by decide))

example : TxVerdict UND AND1 (View.full UND) 0 .dropped :=
  TxVerdict.resolveDrop (i := 0) (a := 14) rfl (resolvesAt_iff.mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))

-- VerdictAgreement is falsifiable (so its statement is not trivially true, and
-- StanceDiscipline is load-bearing).
example : ¬ TxAgreement.VerdictAgreement UND AND1 := fun h =>
  Fate.noConfusion (h (View.full UND) (View.full UND) 0 .finalized .dropped
    (TxVerdict.fastFinal (r := 3) (by decide) (fastQuorumAtInView_iff.mpr (by decide)))
    (TxVerdict.resolveDrop (i := 0) (a := 14) rfl (resolvesAt_iff.mpr (by decide))
      ((mem_candidates_iff (by decide)).mp (by decide))))

-- The conflicting tx 1 is also fast-finalized: NoConflictingFinal falsifiable.
example : TxVerdict UND AND1 (View.full UND) 1 .finalized :=
  TxVerdict.fastFinal (r := 5) (by decide) (fastQuorumAtInView_iff.mpr (by decide))

example : ¬ TxAgreement.NoConflictingFinal UND AND1 := fun h =>
  h (View.full UND) (View.full UND) 0 1
    (TxVerdict.fastFinal (r := 3) (by decide) (fastQuorumAtInView_iff.mpr (by decide)))
    (TxVerdict.fastFinal (r := 5) (by decide) (fastQuorumAtInView_iff.mpr (by decide)))
    (by decide)

-- Were [13, 12] an admissible anchor list over UBiv, index 0 (block 13)
-- would satisfy every resolveCommit premise for tx 0 while index 1
-- (block 12) satisfies every resolveDrop premise: a verdict
-- disagreement. Only Anchors.chained forbids the list — the five facts
-- below are the loophole, pinned.

example : ¬ Reaches UBiv 12 13 := fun h =>
  (by decide : (13 : Fin 16) ∉ history UBiv 12) ((mem_history_iff (by decide)).mpr h)

example : Conflicted UBiv 13 0 := (conflicted_iff (by decide)).mpr (by decide)

example : HasCert UBiv 13 0 := (hasCert_iff (by decide)).mpr (by decide)

example : ¬ DeadGiven UBiv 13 (fun _ => False) 0 := fun h =>
  absurd ((deadGiven_iff (Rb := fun _ => false) (by decide) (fun _ => by simp)).mp h)
    (by decide)

example : ResolveReadyGiven UBiv 12 (fun _ => False) 0 :=
  (resolveReadyGiven_iff (Rb := fun _ => false) (by decide) (fun _ => by simp)).mpr
    (by decide)

-- The Owned gate carries MixedViaAnchor: the mixed tx 2 of UMix has a
-- full fast quorum, and over an empty anchor list no anchor certificate
-- exists — a gateless fastFinal would finalize it and refute the claim.
-- (For VerdictAgreement the gate is not load-bearing: a mixed fast
-- final would carry a certificate quorum and agree like an owned one.)

def AMixEmpty : Anchors UMix where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

example : Transactions.Mixed (2 : Fin 4) ∧ FastQuorumAtInView UMix (View.full UMix) 2 2 :=
  ⟨by decide, fastQuorumAtInView_iff.mpr (by decide)⟩

example : ¬ ∃ (i : ℕ) (a : Fin 12), AMixEmpty.seq[i]? = some a ∧ HasCert UMix a 2 := by
  rintro ⟨i, a, hi, -⟩
  simp [AMixEmpty] at hi

/-- The skip-threshold split at `n = 5` (`fiveValidators`): genesis
`0`–`4`; round 1 — `5` (Byzantine? no: validator `0`, correct here)
ACKs `tx 0`, `6`, `7`, `8` (validators `1`, `2`, `3`) carry both
candidates and skip-vote, `9` (Byzantine `4`); round 2 — `10`, `11`,
`12` are skip certificates over the three skip voters. Id `13` junk. -/
def lkSkip5 : Fin 14 → Block (Fin 5) (Fin 14) (Fin 4) (Fin 2) := fun i =>
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
  else if (i : ℕ) = 10 then
    { round := 2, author := 1, parents := {6, 7, 8, 9}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 2, parents := {6, 7, 8, 9}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 3, parents := {6, 7, 8, 9}, txs := ∅, declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- The skip-threshold universe: ids `0`–`12`, id `13` junk. -/
def USkip5 : Universe (Fin 5) (Fin 14) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 13
  block := lkSkip5
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline USkip5 :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- Each skip certificate stands at exactly `half = 3` skip voters, below
-- the quorum of `4`: a `quorum`-mutant of `IsSkipCert` refuses it.
example : IsSkipCert USkip5 10 0 := (isSkipCert_iff (by decide)).mpr (by decide)
example : ¬ AtLeast USkip5 (quorum (Fin 5)) (USkip5.block 10).parents
    (fun b => IsSkipVoteDec USkip5 b 0) := fun h =>
  absurd (atLeast_iff_filter.mp h) (by decide)

-- Three skip-certificate authors are a `half` but not a round quorum:
-- the skip route reads `quorum`, and a `half`-mutant fires here.
example : ¬ SkipQuorumAtInView USkip5 (View.full USkip5) 2 0 := fun h =>
  absurd (skipQuorumAtInView_iff.mp h) (by decide)
example : half (Fin 5) ≤
    (authorsOf USkip5.block (((blocksAt USkip5 2) ∩ (View.full USkip5).ids).filter
      fun C => IsSkipCertDec USkip5 C 0)).card := by decide

/-- A partial view of `USkip2` holding one skip-certificate block. -/
def VSkipPart : View USkip2 where
  ids := {0, 1, 2, 3, 4, 5, 6, 7, 8}
  subset_ids := by decide
  complete := by decide

-- The skip quorum reads the view: one certificate author is no quorum.
example : ¬ SkipQuorumAtInView USkip2 VSkipPart 2 0 := fun h =>
  absurd (skipQuorumAtInView_iff.mp h) (by decide)

/-! ### Arc audit: UCert/ACert: unpinned discriminating facts on the committed
bivalent-retraction universe. -/

-- The unlock certificate at anchor 18 does NOT kill tx 0 (the
-- "unlock is bivalent, never witnesses death" clause of DeadGiven —
-- a mutant adding IsUnlockCert to DeadGiven passes the current suite).
example : ¬ DeadAt UCert ACert 1 0 := fun h => absurd (deadAt_iff.mp h) (by decide)

-- Anchor 18 has the conflict, the unlock evidence, and a certified
-- ALIVE candidate: not release-ready — the middle conjunct of
-- ResolveReadyGiven biting on its own (never exercised in the suite).
example : ¬ ResolveReadyAt UCert ACert 1 0 := fun h =>
  absurd (resolveReadyAt_iff.mp h) (by decide)
example : ¬ ReleasedBelow UCert ACert 2 0 := fun h =>
  absurd ((releasedBelow_iff 2 0).mp h) (by decide)

-- CertVisible through a parent's HasCert ONLY: id 18's parents are all
-- ⊥ voters (no fast-vote quorum), yet the certificate is in a parent's
-- history — the second disjunct exercised alone for the first time.
example : CertVisible UCert 18 0 := (certVisible_iff (by decide)).mpr (by decide)
example : ¬ AtLeast UCert (quorum (Fin 4)) (UCert.block 18).parents
    (fun b => IsFastVoteDec UCert b 0) := fun h =>
  absurd (atLeast_iff_filter.mp h) (by decide)

end RedSnapper

end LeanDagTest
