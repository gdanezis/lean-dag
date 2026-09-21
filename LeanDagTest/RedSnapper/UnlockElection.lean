import LeanDag.RedSnapper.Five.RecoverySafety.Statement
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness: a full unlock certificate empties the election

RS7's `UnlockEmptiesElection` — the second clause of the paper's Lemma
recovery-reflects — on universes that really hold a full unlock
certificate *and* frozen validators. (`U6Unlock` and `U6Frag` hold the
certificate but no marker: on them the claim is vacuously true, and
they are not used here.)

* **`U6RecUnlock`** — `U6Rec` with all five correct validators at `⊥`
  from round 1, republished with the markers. Block `12` is a full
  unlock certificate; anchor `6`, below it, still triggers and anchor
  `17` resolves. Both disciplines hold and nothing is eligible — the
  claim's conclusion, by `decide`. Two routes drop `tx 0`:
  `fullUnlockDrop` on the certificate and `recoveryDropBot` at the
  resolution, the drop/drop pair.
* **The move rule is needed (`U6UnlockMove`)** — the same round 1, but
  validators `0, 1, 2` freeze at `ack 0`: a move off `⊥` with no
  refutation. The freeze rule holds, the move rule does not, the unlock
  certificate stands — and `tx 0` is eligible.
* **The freeze rule is needed (`U6UnlockThaw`)** — validators `0, 1, 2`
  freeze at `ack 0` in round 1, then move to `⊥` in round 2 under a
  genuine refutation (three anti-votes among their parents): legal
  moves, above their own markers. The move rule holds, the freeze rule
  does not; a round-3 block sees five validators at `⊥` — and `tx 0` is
  eligible at validator `3`'s round-2 block, which reads the three
  frozen ACKs.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- `lkRec` with validators `0, 1, 2` at `⊥` in round 1. -/
def lkUnlockMove : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkRec i

/-- `lkUnlockMove` with the markers of validators `0, 1, 2` republishing
`⊥`. -/
def lkRecUnlock : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else lkUnlockMove i

def U6RecUnlock : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecUnlock
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `U6RecUnlock`: the trigger and the
resolving anchor. -/
def ARecUnlock : Anchors U6RecUnlock where
  seq := [6, 17]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- Both hypotheses of the claim hold ...
example : MoveDiscipline U6RecUnlock := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6RecUnlock := freezeDiscipline_iff.mpr (by decide)

-- ... its premise is live: a full unlock certificate, with a marker
-- quorum under the resolving anchor ...
example : IsFullUnlockCert U6RecUnlock 12 0 :=
  (isFullUnlockCert_iff (by decide)).mpr (by decide)
example : FreezeQuorum U6RecUnlock 6 0 17 := (freezeQuorum_iff (by decide)).mpr (by decide)
example : ResolvesFiveAt U6RecUnlock ARecUnlock 0 0 1 := resolvesFiveAt_iff.mpr (by decide)

-- ... and its conclusion holds: nothing is eligible.
private theorem recUnlock_empty : ∀ tx : Fin 4, ¬ EligibleFiveDec U6RecUnlock 6 17 0 tx := by
  decide

-- Two routes drop the same candidate.
example : VerdictFive U6RecUnlock ARecUnlock (View.full U6RecUnlock) (· ≤ ·) 0 Fate.dropped :=
  .fullUnlockDrop (C := 12) (b := 12) (by decide)
    ((isFullUnlockCert_iff (by decide)).mpr (by decide)) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
example : VerdictFive U6RecUnlock ARecUnlock (View.full U6RecUnlock) (· ≤ ·) 0 Fate.dropped :=
  .recoveryDropBot (i := 0) (j := 1) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun tx' h => recUnlock_empty tx' ((eligibleFive_iff (by decide)).mp h))

/-! ### The move rule is needed -/

def U6UnlockMove : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkUnlockMove
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : FreezeDiscipline U6UnlockMove := freezeDiscipline_iff.mpr (by decide)
example : ¬ MoveDiscipline U6UnlockMove := fun h =>
  absurd (moveDiscipline_iff.mp h) (by decide)

example : ¬ RecoverySafety.UnlockEmptiesElection U6UnlockMove := fun h =>
  h 0 6 17 (by decide) ⟨12, by decide, (isFullUnlockCert_iff (by decide)).mpr (by decide)⟩ 0
    ((eligibleFive_iff (by decide)).mpr (by decide))

/-! ### The freeze rule is needed -/

/-- Eighteen ids. Round 1: validators `0, 1, 2` freeze at `ack 0`,
validators `3, 4` and Byzantine `5` stand at `⊥`. Round 2: `0, 1, 2`
reference the three anti-voters and move to `⊥`; `3` and `4` reference
the five correct round-1 blocks. Round 3: block `17` over the five
correct round-2 blocks. -/
def lkUnlockThaw : Fin 18 → Block (Fin 6) (Fin 18) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else if (i : ℕ) = 1 then {1} else ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 0 else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 0 else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 0 else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 3, author := 0, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }

def U6UnlockThaw : Universe (Fin 6) (Fin 18) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkUnlockThaw
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The moves are legal — each carries a refutation of the old stance ...
example : MoveDiscipline U6UnlockThaw := moveDiscipline_iff.mpr (by decide)
example : IsRefutation U6UnlockThaw 12 0 (Stance.ack 0) :=
  (isRefutation_iff (by decide)).mpr (by decide)
-- ... but they sit above the movers' own markers.
example : ¬ FreezeDiscipline U6UnlockThaw := fun h =>
  absurd (freezeDiscipline_iff.mp h) (by decide)

example : ¬ RecoverySafety.UnlockEmptiesElection U6UnlockThaw := fun h =>
  h 0 0 15 (by decide) ⟨17, by decide, (isFullUnlockCert_iff (by decide)).mpr (by decide)⟩ 0
    ((eligibleFive_iff (by decide)).mpr (by decide))

end RedSnapper

end LeanDagTest
