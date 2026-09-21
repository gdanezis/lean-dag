import LeanDag.RedSnapper.Helpers.Voting
import LeanDag.RedSnapper.Helpers.VotingFive
import LeanDag.RedSnapper.Uncontested.Statement
import LeanDag.RedSnapper.Five.Uncontested.Statement
import LeanDagTest.RedSnapper.Liveness
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness: the 5f+1 voting rule and uncontested liveness

RS10's hypotheses shown satisfiable end to end, on the universes its
conclusions are exhibited in, and the `5f+1` voting rule told apart
from the `3f+1` one.

* **`ULive`, the owned scenario** — RS4's universe read under the
  `5f+1` rule: the same sole owned transaction, the same synchrony; the
  rule holds, every correct round-3 block is a full certificate, and
  `fullFinal` follows with no anchor.
* **`UMixLive`, the mixed scenario** — `UMixSix` with the carrier
  standing at its own transaction: a sole *mixed* transaction, carried
  at genesis, ACKed by the five correct validators at round 1, fully
  certified by block `12` at round 2. Both rules hold. No anchor, no
  verdict (`FreezeHardening`'s `AMixSix`, on the same table below the
  carrier); with `12` committed, `mixedFinal` fires at `5f+1` and
  `finalizeOnCommit` at `3f+1` — the C5 branch of both liveness lemmas.
* **The rule discriminates.** `UMixSix` itself fails `ack_sole`: its
  carrier sees a sole candidate and stays silent.
* **`UFrzBot`, the second origin of `⊥`** — genesis `0` carries both
  rivals and is the trigger; validator `1`'s round-1 block references
  the other five, sees no candidate at all, and freezes at `⊥`. No
  conflict is visible from the declaring block — the `3f+1` rule's
  `bot_conflicted` is false here — and the `5f+1` rule holds through
  the marker. Remove the marker (`UFrzBotBare`) and `bot_contested`
  fails; point it at a genesis block that sees no conflict
  (`UFrzBotStray`) and `freeze_triggered` fails.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### The owned scenario: `ULive` under the `5f+1` rule -/

example : VotingRuleFive ULive := votingRuleFive_of_dec (by decide)

-- Every correct block of the certificate round is a full certificate ...
example : ∀ C ∈ ULive.ids, (ULive.block C).author ∈ (Correct : Finset (Fin 4)) →
    (ULive.block C).round = 3 → IsFullCertDec ULive C 0 := by decide

-- ... and one observed certificate finalises the owned transaction.
example : VerdictFive ULive ALive (View.full ULive) (· ≤ ·) 0 Fate.finalized :=
  .fullFinal (C := 10) (by decide) (by decide) ((isFullCert_iff (by decide)).mpr (by decide))

/-! ### The mixed scenario: `UMixLive` -/

/-- `lkMixSix` with the carrier, genesis `0`, standing at the mixed
`tx 2` it carries. -/
def lkMixLive : Fin 13 → Block (Fin 6) (Fin 13) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 0 then
    { round := 0, author := 0, parents := ∅, txs := {2},
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else lkMixSix i

def UMixLive : Universe (Fin 6) (Fin 13) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkMixLive
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Every hypothesis of RS10's mixed claim, and of RS4's anchor claim.
example : VotingRuleFive UMixLive := votingRuleFive_of_dec (by decide)
example : VotingRule UMixLive := votingRule_iff.mpr (by decide)
example : Transactions.Mixed (2 : Fin 4) ∧ Transactions.Valid (2 : Fin 4) := by decide
example : SynchronisedOn UMixLive (Correct : Finset (Fin 6)) 0 := by
  unfold SynchronisedOn; decide
example : PopulatedOn UMixLive (Correct : Finset (Fin 6)) 1 := by
  unfold PopulatedOn; decide
example : (UMixLive.block 0).author ∈ (Correct : Finset (Fin 6)) ∧ Includes UMixLive 0 2 :=
  ⟨by decide, (mem_txsIn_iff (by decide)).mp (by decide)⟩
example : ∀ tx' : Fin 4, ¬ Conflict (2 : Fin 4) tx' := by decide
example : (UMixLive.block 12).author ∈ (Correct : Finset (Fin 6)) ∧
    (UMixLive.block 12).round = 2 := by decide

-- The conclusion: the certificate-round block carries a full certificate.
example : IsFullCert UMixLive 12 2 := (isFullCert_iff (by decide)).mpr (by decide)

/-- The certificate block of `UMixLive`, committed. -/
def AMixLive : Anchors UMixLive where
  seq := [12]
  mem := by decide
  chained := by simp

-- The mixed transaction is final at the anchor, under either protocol.
example : VerdictFive UMixLive AMixLive (View.full UMixLive) (· ≤ ·) 2 Fate.finalized :=
  .mixedFinal (i := 0) (a := 12) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) Reaches.refl
    ((isFullCert_iff (by decide)).mpr (by decide))
example : TxVerdict UMixLive AMixLive (View.full UMixLive) 2 Fate.finalized :=
  .finalizeOnCommit (i := 0) (a := 12) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))

/-! ### The rule discriminates: a silent carrier fails `ack_sole` -/

example : ¬ VotingRuleFive UMixSix := fun h =>
  absurd ((stanceIs_some_iff (by decide)).mp
    (h.ack_sole 0 (by decide) (by decide) 1 2
      ((mem_candidates_iff (by decide)).mp (by decide))
      (fun tx' h' => by
        have hmem := (mem_candidates_iff (b := (0 : Fin 13)) (by decide)).mpr h'
        clear h'
        revert tx'
        decide)
      (fun hs => absurd ((stanceIs_some_iff (by decide)).mp hs) (by decide))))
    (by decide)

/-! ### The second origin of `⊥`: frozen with no conflict in sight -/

/-- Seven ids: genesis `0` carries both rivals; validator `1`'s round-1
block `6` references the other five genesis blocks and freezes at `⊥`
on the trigger `0`. -/
def lkFrzBot : Fin 7 → Block (Fin 6) (Fin 7) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0, 1} else ∅, declares := fun _ => none }
  else
    { round := 1, author := 1, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 0 else none }

def UFrzBot : Universe (Fin 6) (Fin 7) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkFrzBot
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The trigger sees the conflict; the freezing block sees no candidate.
example : Triggers UFrzBot 0 0 := (triggers_iff (by decide)).mpr (by decide)
example : ¬ Conflicted UFrzBot 6 0 := fun h =>
  absurd ((conflicted_iff (by decide)).mp h) (by decide)
example : (UFrzBot.block 6).author ∈ (Correct : Finset (Fin 6)) ∧
    (UFrzBot.block 6).declares 0 = some Stance.bot := by decide

-- The `5f+1` rule holds, through the marker; the `3f+1` rule does not.
example : VotingRuleFive UFrzBot := votingRuleFive_of_dec (by decide)
example : FreezeDiscipline UFrzBot := freezeDiscipline_iff.mpr (by decide)
example : ¬ VotingRule UFrzBot := fun h => absurd (votingRule_iff.mp h) (by decide)

/-- `lkFrzBot` with the marker removed: a bare `⊥`, no conflict. -/
def lkFrzBotBare : Fin 7 → Block (Fin 6) (Fin 7) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 6 then
    { round := 1, author := 1, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkFrzBot i

def UFrzBotBare : Universe (Fin 6) (Fin 7) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkFrzBotBare
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ VotingRuleFive UFrzBotBare := fun h =>
  (h.bot_contested 6 (by decide) (by decide) 0 (by decide)).elim
    (fun hc => absurd ((conflicted_iff (by decide)).mp hc) (by decide))
    (fun hf => absurd hf (by decide))

/-- `lkFrzBot` with the marker naming genesis `1`, which sees no
conflict. -/
def lkFrzBotStray : Fin 7 → Block (Fin 6) (Fin 7) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 6 then
    { round := 1, author := 1, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 1 else none }
  else lkFrzBot i

def UFrzBotStray : Universe (Fin 6) (Fin 7) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkFrzBotStray
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ VotingRuleFive UFrzBotStray := fun h =>
  absurd ((triggers_iff (by decide)).mp
    (h.freeze_triggered 6 (by decide) (by decide) 0 1 (by decide))) (by decide)

end RedSnapper

end LeanDagTest
