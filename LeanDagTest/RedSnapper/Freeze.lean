import LeanDag.RedSnapper.Helpers.Freeze
import LeanDag.RedSnapper.Model.Five.Verdict
import LeanDagTest.RedSnapper.FiveCerts

/-!
# Witness: freeze and the deterministic recovery

The recovery pipeline end to end over `sixValidators` (`quorum = 5`,
`half = 3`, Byzantine `5`), decided through the surrogates of
`Helpers/Freeze.lean`.

* **`U6Rec`** — a full recovery with a committed winner. Genesis `0`
  and `1` carry the rivals `tx 0` and `tx 1`; round 1 splits three ACKs
  for `tx 0` against two `⊥`. The anchors are `[0, 6, 17, 22]`: genesis
  `0` sees no conflict (`¬ Triggers` — the least-index clause is
  load-bearing, `TriggerAt` holds at index 1 and at neither 0 nor 2);
  the round-1 anchor `6` sees the conflict and no certificate and
  triggers. At round 2 the five correct validators freeze on anchor `6`,
  each republishing its stance; the round-3 anchor `17` is the first
  with a marker quorum (`ResolvesFiveAt` at `(1, 2)`, and *not* at
  `(1, 3)` although the round-4 anchor `22` also sees the markers — the
  one-shot pinned). The election: three frozen ACKs make `tx 0` eligible
  (`half` exactly), `tx 1` supported by nobody — `recoveryFinal`
  finalises `tx 0` and `recoveryDropLoser` drops `tx 1`.
* **`U6RecBot`** — the same skeleton with frozen stances split
  `2 / 2 / 1` (`tx 0` / `⊥` / `tx 1`): nothing reaches `half`, `W` is
  empty, and `recoveryDropBot` drops both candidates.
* **`U6RecBad`** — a correct validator declares a *different* value
  above its own marker: `FreezeDiscipline` refused.
* Consensusless verdicts: `fullFinal` on `U6Full`'s certificate and
  `fullUnlockDrop` on `U6Unlock`'s, each over the full view and empty
  anchors.
* Marker fidelity: the Byzantine validator publishes no marker
  (`¬ Frozen`), and an anchor below the markers sees no quorum.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Twenty-four ids, id 23 junk: the recovery table described in the
module docstring. -/
def lkRec : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
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
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 17 then
    { round := 3, author := 0, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 18 then
    { round := 3, author := 1, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 19 then
    { round := 3, author := 2, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 20 then
    { round := 3, author := 3, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 21 then
    { round := 3, author := 4, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 22 then
    { round := 4, author := 0, parents := {17, 18, 19, 20, 21}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Rec : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRec
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `U6Rec`: genesis, the trigger, the
resolving anchor, and one more. -/
def ARec : Anchors U6Rec where
  seq := [0, 6, 17, 22]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => ?_)
      (List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)

-- Both disciplines hold: same-value republication at the markers, no
-- moves anywhere.
example : MoveDiscipline U6Rec := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6Rec := freezeDiscipline_iff.mpr (by decide)

-- The trigger: the genesis anchor sees no conflict, the round-1 anchor
-- triggers; the trigger index is exactly 1.
example : ¬ Triggers U6Rec 0 0 := fun h => absurd ((triggers_iff (by decide)).mp h) (by decide)
example : Triggers U6Rec 6 0 := (triggers_iff (by decide)).mpr (by decide)
example : TriggerAt U6Rec ARec 0 1 := triggerAt_iff.mpr (by decide)
example : ¬ TriggerAt U6Rec ARec 0 0 := fun h => absurd (triggerAt_iff.mp h) (by decide)
example : ¬ TriggerAt U6Rec ARec 0 2 := fun h => absurd (triggerAt_iff.mp h) (by decide)

-- The markers: five correct freezers, no Byzantine marker; no quorum
-- below the markers, a quorum at the resolving anchor.
example : Frozen U6Rec 6 0 0 17 := (frozen_iff (by decide)).mpr (by decide)
example : ¬ Frozen U6Rec 6 5 0 17 := fun h => absurd ((frozen_iff (by decide)).mp h) (by decide)
example : ¬ FreezeQuorum U6Rec 6 0 6 := fun h =>
  absurd ((freezeQuorum_iff (by decide)).mp h) (by decide)
example : FreezeQuorum U6Rec 6 0 17 := (freezeQuorum_iff (by decide)).mpr (by decide)

-- The resolution is one-shot at the index pair `(1, 2)`: the round-4
-- anchor also sees the markers and is refused.
example : ResolvesFiveAt U6Rec ARec 0 1 2 := resolvesFiveAt_iff.mpr (by decide)
example : ¬ ResolvesFiveAt U6Rec ARec 0 1 3 := fun h =>
  absurd (resolvesFiveAt_iff.mp h) (by decide)

-- The election: three frozen ACKs make `tx 0` eligible at exactly
-- `half`; `tx 1` has no support.
example : EligibleFive U6Rec 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ¬ EligibleFive U6Rec 6 17 0 1 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)

-- The recovery verdicts: `tx 0` finalised, the loser `tx 1` dropped.
example : VerdictFive U6Rec ARec (View.full U6Rec) (· ≤ ·) 0 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)
example : VerdictFive U6Rec ARec (View.full U6Rec) (· ≤ ·) 1 Fate.dropped :=
  .recoveryDropLoser (tx' := 0) (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _) (by decide)

/-- `lkRec` with the frozen stances split `2 / 2 / 1`: validator 2
freezes on `⊥`, validator 4 on the rival `tx 1`. -/
def lkRecBot : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else lkRec i

def U6RecBot : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecBot
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def ARecBot : Anchors U6RecBot where
  seq := [0, 6, 17, 22]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => ?_)
      (List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)

example : MoveDiscipline U6RecBot := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6RecBot := freezeDiscipline_iff.mpr (by decide)

-- The split election: nothing reaches `half`, and both candidates are
-- dropped at the resolution.
example : ¬ EligibleFive U6RecBot 6 17 0 0 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)
example : ¬ EligibleFive U6RecBot 6 17 0 1 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)

private theorem recBot_empty : ∀ tx' : Fin 4, ¬ EligibleFiveDec U6RecBot 6 17 0 tx' := by
  decide

example : VerdictFive U6RecBot ARecBot (View.full U6RecBot) (· ≤ ·) 0 Fate.dropped :=
  .recoveryDropBot (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun tx' h => recBot_empty tx' ((eligibleFive_iff (by decide)).mp h))
example : VerdictFive U6RecBot ARecBot (View.full U6RecBot) (· ≤ ·) 1 Fate.dropped :=
  .recoveryDropBot (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun tx' h => recBot_empty tx' ((eligibleFive_iff (by decide)).mp h))

/-- `lkRec` with validator 0 declaring the rival above its own marker:
the frozen stance is not permanent. -/
def lkRecBad : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 17 then
    { round := 3, author := 0, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else lkRec i

def U6RecBad : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecBad
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ FreezeDiscipline U6RecBad := fun h =>
  absurd (freezeDiscipline_iff.mp h) (by decide)

-- The consensusless routes: one observed certificate decides.
def AFull : Anchors U6Full where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

def AUnlock : Anchors U6Unlock where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

example : VerdictFive U6Full AFull (View.full U6Full) (· ≤ ·) 0 Fate.finalized :=
  .fullFinal (C := 12) (by decide) (by decide)
    ((isFullCert_iff (by decide)).mpr (by decide))
example : VerdictFive U6Unlock AUnlock (View.full U6Unlock) (· ≤ ·) 0 Fate.dropped :=
  .fullUnlockDrop (C := 12) (b := 12) (by decide)
    ((isFullUnlockCert_iff (by decide)).mpr (by decide)) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))

end RedSnapper

end LeanDagTest
