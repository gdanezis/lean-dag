import LeanDag.RedSnapper.Helpers.Freeze
import LeanDag.RedSnapper.Model.Five.Verdict
import LeanDag.RedSnapper.Five.RecoverySafety.Proof
import LeanDagTest.RedSnapper.Freeze

/-!
# Witness hardening: freeze and the deterministic recovery

Adopted from the Phase 8 vacuity audit — the shapes the `Freeze`
universes alone do not pin.

* **`U6RecFull`** — `RecoveryReflects`' premises are co-satisfiable: a
  full certificate and a resolution coexist, `W = {tx 0}` live, and
  *both* routes (`fullFinal` and `recoveryFinal`) finalise the same
  transaction from one universe — the only live cross-route pair of
  `VerdictAgreement`, witnessed end to end. Plus the least-clause
  verifications on `U6Rec`: anchor 17 *does* trigger and anchor 22
  *does* see the marker quorum, so the committed `¬ TriggerAt … 2` and
  `¬ ResolvesFiveAt … (1, 3)` pins fail exactly on the least-index
  clauses.
* **`U6RecTie`** — a two-member `W` (three frozen supporters each, the
  Byzantine as the sixth freezer): under `(· ≤ ·)` the winner is `tx 0`
  and `tx 1` drops; under `(· ≥ ·)` the verdicts flip — the shared
  order is demonstrably load-bearing, and Byzantine membership in `F`
  and in `W`-support (the paper's `F ⊆ Π`) is pinned.
* **`U6RecBare` / `U6RecWrong` / `U6RecJunk`** — Byzantine marker
  shapes: a bare marker (no declaration) counts toward the freeze
  quorum and supports nothing, while `FreezeDiscipline` — which binds
  correct authors only — still holds; a marker naming the wrong anchor
  counts toward nothing and blocks the resolution; a marker naming the
  junk id is representable and inert (`ValidWrt` constrains no
  marker).
* **`U4`** — the `Five` gate is tight: at the tight `3f + 1` committee
  a full certificate coexists with an *empty* election
  (`¬ RecoveryReflects`, `¬ RecoverySafetyBot`), while the generic
  `RecoverySafetyWin` still instantiates — finding 20's boundary,
  machine-checked in both directions.
* **`U6Mut`** — the paper reads `Stance(id, o, A)` at the *anchor*: a
  Byzantine freezer that re-declares above its marker steers the real
  election one way while a mutant reading the marker block's
  declaration elects the other — the read point separated.
* **`U6RecPre`** — the one-shot clause is paper-exact: a universe whose
  markers sit in the trigger's own history (unreachable under the real
  protocol, where markers causally follow the trigger's commit) sees a
  marker quorum at the trigger anchor itself, and the resolution
  refuses to fire — `Resolves` scans every committed anchor before
  `j`, the trigger included.
* **`U6RecNoDecl` / `U6RecBadAck`** — `FreezeDiscipline` refuted clause
  by clause: a correct bare marker refutes `freeze_declares`, a correct
  first ACK of an invalid transaction refutes `ack_candidate` (with
  `MoveDiscipline` pinned to still hold), complementing `U6RecBad`'s
  `freeze_final` refutation.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### Reflects premises live: cert + resolution coexist; least-clause verifications -/

-- (2) The least-clause verifications over the existing U6Rec.
example : Triggers U6Rec 17 0 := (triggers_iff (by decide)).mpr (by decide)
example : FreezeQuorum U6Rec 6 0 22 := (freezeQuorum_iff (by decide)).mpr (by decide)

/-- `lkRec` with all five correct validators at `ack 0` throughout:
round 1 unanimous, markers unanimous. Block 12 (parents 6–10) is then a
full certificate for `tx 0`, while anchor 6 (round 1) still triggers —
the certificate is not in its history. -/
def lkRecFull : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else lkRec i

def U6RecFull : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecFull
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def ARecFull : Anchors U6RecFull where
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

-- Both disciplines hold.
example : MoveDiscipline U6RecFull := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6RecFull := freezeDiscipline_iff.mpr (by decide)

-- The full certificate exists (block 12), yet anchor 6 still triggers:
-- the certificate is outside the trigger anchor's history.
example : IsFullCert U6RecFull 12 0 := (isFullCert_iff (by decide)).mpr (by decide)
example : Triggers U6RecFull 6 0 := (triggers_iff (by decide)).mpr (by decide)
example : ResolvesFiveAt U6RecFull ARecFull 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

-- Reflects' conclusion, live: tx 0 is eligible and uniquely so.
example : EligibleFive U6RecFull 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ∀ tx' : Fin 4, EligibleFiveDec U6RecFull 6 17 0 tx' → tx' = 0 := by decide

-- Both routes derive `finalized` for tx 0 — VerdictAgreement's premises
-- are co-satisfiable across the certificate and recovery routes.
example : VerdictFive U6RecFull ARecFull (View.full U6RecFull) (· ≤ ·) 0 Fate.finalized :=
  .fullFinal (C := 12) (by decide) (by decide)
    ((isFullCert_iff (by decide)).mpr (by decide))
example : VerdictFive U6RecFull ARecFull (View.full U6RecFull) (· ≤ ·) 0 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)

/-! ### A two-member `W`: the tie-break order decides the winner -/

/-- `lkRec` with validators 3,4 at `ack 1` (rounds 1 and 2), and the
Byzantine 5 publishing a marker block 11 that declares `ack 1` and
freezes on anchor 6; block 16 references it. -/
def lkRecTie : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else lkRec i

def U6RecTie : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecTie
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def ARecTie : Anchors U6RecTie where
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

example : MoveDiscipline U6RecTie := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6RecTie := freezeDiscipline_iff.mpr (by decide)

-- The Byzantine marker counts toward F (paper fidelity: F ⊆ Π, not
-- Correct), and the resolution fires at (1, 2).
example : Frozen U6RecTie 6 5 0 17 := (frozen_iff (by decide)).mpr (by decide)
example : ResolvesFiveAt U6RecTie ARecTie 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

-- Two-member W: both rivals eligible, each at exactly half = 3.
example : EligibleFive U6RecTie 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : EligibleFive U6RecTie 6 17 0 1 := (eligibleFive_iff (by decide)).mpr (by decide)

private theorem tie_elig : ∀ tx' : Fin 4, EligibleFiveDec U6RecTie 6 17 0 tx' → tx' ≤ 1 := by
  decide

-- Under (· ≤ ·) the winner is tx 0 and tx 1 is the dropped loser ...
example : VerdictFive U6RecTie ARecTie (View.full U6RecTie) (· ≤ ·) 0 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)
example : VerdictFive U6RecTie ARecTie (View.full U6RecTie) (· ≤ ·) 1 Fate.dropped :=
  .recoveryDropLoser (tx' := 0) (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _) (by decide)

-- ... and under the reversed order (· ≥ ·) the verdicts flip: the
-- tie-break carries the decision.
example : VerdictFive U6RecTie ARecTie (View.full U6RecTie) (· ≥ ·) 1 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun tx' h => tie_elig tx' ((eligibleFive_iff (by decide)).mp h))
example : VerdictFive U6RecTie ARecTie (View.full U6RecTie) (· ≥ ·) 0 Fate.dropped :=
  .recoveryDropLoser (tx' := 1) (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun tx' h => tie_elig tx' ((eligibleFive_iff (by decide)).mp h)) (by decide)

/-! ### Byzantine marker shapes: bare, wrong-anchor, junk-id -/

/-- `lkRec` with validator 4 unfrozen (block 16 keeps its `⊥` stance but
carries no marker), the Byzantine block 11 carrying a bare marker for
anchor 6 with no declaration, and block 16 referencing it. -/
def lkRecBare : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun _ => none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkRec i

def U6RecBare : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecBare
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def ARecBare : Anchors U6RecBare where
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

-- FreezeDiscipline holds despite the declaration-less Byzantine marker.
example : MoveDiscipline U6RecBare := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6RecBare := freezeDiscipline_iff.mpr (by decide)

-- The bare marker counts toward F; only four correct markers exist, so
-- the Byzantine one completes the quorum; the resolution fires and tx 0
-- (three correct frozen ACKs) is still the unique eligible transaction.
example : Frozen U6RecBare 6 5 0 17 := (frozen_iff (by decide)).mpr (by decide)
example : FreezeQuorum U6RecBare 6 0 17 := (freezeQuorum_iff (by decide)).mpr (by decide)
example : ResolvesFiveAt U6RecBare ARecBare 0 1 2 := resolvesFiveAt_iff.mpr (by decide)
example : EligibleFive U6RecBare 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ∀ tx' : Fin 4, EligibleFiveDec U6RecBare 6 17 0 tx' → tx' = 0 := by decide

/-- `lkRecBare` with the Byzantine marker naming genesis 0 instead of
the trigger anchor 6. -/
def lkRecWrong : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun _ => none,
      freezes := fun o => if o = 0 then some 0 else none }
  else lkRecBare i

def U6RecWrong : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecWrong
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def ARecWrong : Anchors U6RecWrong where
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

-- The wrong-anchor marker does not count toward the trigger's quorum:
-- four correct markers are not enough, and nothing resolves.
example : ¬ Frozen U6RecWrong 6 5 0 17 := fun h =>
  absurd ((frozen_iff (by decide)).mp h) (by decide)
example : Frozen U6RecWrong 0 5 0 17 := (frozen_iff (by decide)).mpr (by decide)
example : ¬ FreezeQuorum U6RecWrong 6 0 17 := fun h =>
  absurd ((freezeQuorum_iff (by decide)).mp h) (by decide)
example : ¬ ResolvesFiveAt U6RecWrong ARecWrong 0 1 2 := fun h =>
  absurd (resolvesFiveAt_iff.mp h) (by decide)
example : ¬ ResolvesFiveAt U6RecWrong ARecWrong 0 1 3 := fun h =>
  absurd (resolvesFiveAt_iff.mp h) (by decide)

/-- A marker naming the junk id 23 — not a block of the universe at all
— is representable: `ValidWrt` never reads `freezes`. -/
def lkRecJunk : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun _ => none,
      freezes := fun o => if o = 0 then some 23 else none }
  else lkRecBare i

def U6RecJunk : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecJunk
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : Frozen U6RecJunk 23 5 0 17 := (frozen_iff (by decide)).mpr (by decide)

/-! ### The `Five` gate is tight: Reflects and Bot fail at the 3f+1 committee -/

/-- Thirteen ids: genesis 0–3 (1 carries `tx 0`, 2 carries `tx 1`);
round 1: Byzantine 0 (block 4) and correct 1,2 (blocks 5,6) ACK `tx 0`,
correct 3 (block 7) at `⊥`; round 2: block 8 (author 1) is the full
certificate for `tx 0` AND author 1's marker, block 10 (author 3) and
block 11 (Byzantine) are `⊥` markers; round 3: block 12 (author 3) is
the resolving anchor over parents {8, 10, 11}. Author 2 never
freezes. -/
def lk4 : Fin 13 → Block (Fin 4) (Fin 13) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 1 then {0} else if (i : ℕ) = 2 then {1} else ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none,
      freezes := fun o => if o = 0 then some 5 else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 5 else none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 0, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 5 else none }
  else if (i : ℕ) = 12 then
    { round := 3, author := 3, parents := {8, 10, 11}, txs := ∅,
      declares := fun _ => none }
  else -- id 9 junk
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U4 : Universe (Fin 4) (Fin 13) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 9
  block := lk4
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- Anchors: block 5 (round 1, author 1) triggers; block 12 resolves. -/
def A4 : Anchors U4 where
  seq := [5, 12]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

example : MoveDiscipline U4 := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U4 := freezeDiscipline_iff.mpr (by decide)

-- The full certificate exists ...
example : IsFullCert U4 8 0 := (isFullCert_iff (by decide)).mpr (by decide)

-- ... the object resolves at (0, 1) ...
example : ResolvesFiveAt U4 A4 0 0 1 := resolvesFiveAt_iff.mpr (by decide)
example : FreezeQuorum U4 5 0 12 := (freezeQuorum_iff (by decide)).mpr (by decide)

-- ... and yet W is empty: the reflection fails at 3f+1.
private theorem u4_empty : ∀ tx : Fin 4, ¬ EligibleFiveDec U4 5 12 0 tx := by decide

example : ¬ RecoverySafety.RecoveryReflects U4 := fun h =>
  u4_empty 0 ((eligibleFive_iff (by decide)).mp
    (h 0 5 12 0 (by decide) ((freezeQuorum_iff (by decide)).mpr (by decide))
      (by decide) ⟨8, by decide,
        (isFullCert_iff (by decide)).mpr (by decide)⟩).1)

example : ¬ RecoverySafety.RecoverySafetyBot U4 := fun h =>
  h 0 5 12 (by decide) ((freezeQuorum_iff (by decide)).mpr (by decide))
    (fun tx he => u4_empty tx ((eligibleFive_iff (by decide)).mp he))
    0 (by decide) 8 (by decide)
    ((isFullCert_iff (by decide)).mpr (by decide))

/-! ### The stance is read at the anchor, not at the marker -/

/-- Nineteen ids. Genesis 0–5 (0 carries `tx 0`, 1 carries `tx 1`).
Round 1: correct 0,1 at `ack 0` (ids 6,7), correct 2,3 at `ack 1`
(ids 8,9), correct 4 at `⊥` (id 10); Byzantine 5's block 11 declares
`ack 1` AND freezes on anchor 6. Round 2: correct markers 12–16
(0,1 ack 0; 2,3 ack 1; 4 `⊥`); Byzantine block 18 re-declares `ack 0`
above its own marker. Round 3: the resolving anchor 17 (author 0) over
parents {12, 13, 14, 15, 18} — marker 16 stays outside its history, so
F = {0, 1, 2, 3, 5} with |F| = quorum = 5. -/
def lkMut : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
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
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
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
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 6 else none }
  else if (i : ℕ) = 18 then
    { round := 2, author := 5, parents := {7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else -- 17: the resolving anchor
    { round := 3, author := 0, parents := {12, 13, 14, 15, 18}, txs := ∅,
      declares := fun _ => none }

def U6Mut : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkMut
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def AMut : Anchors U6Mut where
  seq := [0, 6, 17]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => ?_)
      (List.pairwise_singleton _ _))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)

example : MoveDiscipline U6Mut := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6Mut := freezeDiscipline_iff.mpr (by decide)

example : ResolvesFiveAt U6Mut AMut 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

/-- The mutant: stances counted from the marker blocks' declarations. -/
def EligibleFiveMarkerDec (U : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2))
    (aₖ a : Fin 19) (o : Fin 2) (tx : Fin 4) : Prop :=
  tx ∈ candidates U a o ∧
    half (Fin 6) ≤ (Finset.univ.filter fun id => ∃ m ∈ historyIn U a,
      (U.block m).author = id ∧ (U.block m).freezes o = some aₖ ∧
        (U.block m).declares o = some (Stance.ack tx)).card

instance (U : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2)) (aₖ a : Fin 19) (o : Fin 2)
    (tx : Fin 4) : Decidable (EligibleFiveMarkerDec U aₖ a o tx) := by
  unfold EligibleFiveMarkerDec; infer_instance

-- Real: the Byzantine's stance at the anchor is its LATEST declaration
-- `ack 0` (block 18, above its marker), so W = {tx 0}.
example : EligibleFive U6Mut 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ¬ EligibleFive U6Mut 6 17 0 1 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)

-- Mutant: the marker declared `ack 1`, so the mutant elects the rival.
example : EligibleFiveMarkerDec U6Mut 6 17 0 1 := by decide
example : ¬ EligibleFiveMarkerDec U6Mut 6 17 0 0 := by decide

-- The real winner under (· ≤ ·) is tx 0 — steered by the Byzantine's
-- post-marker flip, exactly as the paper's `Stance(id, o, A)` read
-- allows.
example : VerdictFive U6Mut AMut (View.full U6Mut) (· ≤ ·) 0 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)

/-! ### The one-shot clause scans every anchor before the resolution (paper-exact) -/

/-- Genesis 0 declares `ack 0` (it carries `tx 0`, so candidacy holds);
genesis 1–4 declare `⊥`; all five freeze on block 6 already at
genesis. No block declares anything afterwards. -/
def lkRecPre : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else if (i : ℕ) = 1 then {1} else ∅,
      declares := fun o =>
        if o = 0 ∧ (i : ℕ) = 0 then some (.ack 0)
        else if o = 0 ∧ (i : ℕ) < 5 then some .bot else none,
      freezes := fun o => if o = 0 ∧ (i : ℕ) < 5 then some 6 else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun _ => none }
  else if h : (i : ℕ) < 11 then
    { round := 1, author := ⟨i - 6, by omega⟩, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun _ => none }
  else if h : (i : ℕ) < 17 then
    { round := 2, author := ⟨i - 12, by omega⟩, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if h : (i : ℕ) < 22 then
    { round := 3, author := ⟨i - 17, by omega⟩, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 22 then
    { round := 4, author := 0, parents := {17, 18, 19, 20, 21}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6RecPre : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecPre
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

def ARecPre : Anchors U6RecPre where
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

-- Both disciplines hold: the model does not constrain WHEN a correct
-- validator freezes.
example : MoveDiscipline U6RecPre := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline U6RecPre := freezeDiscipline_iff.mpr (by decide)

-- Anchor 6 triggers, and its OWN history already carries the quorum of
-- markers naming it ...
example : TriggerAt U6RecPre ARecPre 0 1 := triggerAt_iff.mpr (by decide)
example : FreezeQuorum U6RecPre 6 0 6 := (freezeQuorum_iff (by decide)).mpr (by decide)

-- ... and the resolution refuses to fire at (1, 2): the one-shot
-- clause scans every committed anchor before `j`, the trigger itself
-- included — the paper's Resolves, exactly.
example : ¬ ResolvesFiveAt U6RecPre ARecPre 0 1 2 := fun h =>
  absurd (resolvesFiveAt_iff.mp h) (by decide)

/-! ### FreezeDiscipline refuted clause by clause -/

def lkRecNoDecl : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none,
      freezes := fun o => if o = 0 then some 6 else none }
  else lkRec i

def U6RecNoDecl : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecNoDecl
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : MoveDiscipline U6RecNoDecl := moveDiscipline_iff.mpr (by decide)
example : ¬ FreezeDiscipline U6RecNoDecl := fun h =>
  absurd (freezeDiscipline_iff.mp h) (by decide)

def lkRecBadAck : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 3) else none }
  else lkRec i

def U6RecBadAck : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecBadAck
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : MoveDiscipline U6RecBadAck := moveDiscipline_iff.mpr (by decide)
example : ¬ FreezeDiscipline U6RecBadAck := fun h =>
  absurd (freezeDiscipline_iff.mp h) (by decide)

/-! ### The mixed route: a fully certified mixed transaction is final at
a committed anchor above the certificate, and nowhere else. -/

/-- Thirteen ids over `sixValidators`: genesis 0 carries the mixed
`tx 2` (input `o1`); round 1: the five correct validators ACK it,
Byzantine 5 declares `⊥`; round 2: block 12 over the five ACKs. -/
def lkMixSix : Fin 13 → Block (Fin 6) (Fin 13) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {2} else ∅, declares := fun _ => none }
  else if h : (i : ℕ) < 11 then
    { round := 1, author := ⟨(i : ℕ) - 6, by omega⟩, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 1 then some .bot else none }
  else
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }

def UMixSix : Universe (Fin 6) (Fin 13) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkMixSix
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : MoveDiscipline UMixSix := moveDiscipline_iff.mpr (by decide)

-- The mixed transaction is fully certified ...
example : Transactions.Mixed (2 : Fin 4) ∧ ¬ Owned (2 : Fin 4) := by decide
example : IsFullCert UMixSix 12 2 := (isFullCert_iff (by decide)).mpr (by decide)

-- ... and a candidate of the certificate block.
example : IsCandidate UMixSix 12 1 2 := (mem_candidates_iff (by decide)).mp (by decide)

-- With no committed anchor, no finalized verdict is derivable: the
-- consensusless route is shut to a mixed transaction (D9), and the
-- anchor route has no anchor.
def AMixSix : Anchors UMixSix where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

example : ¬ VerdictFive UMixSix AMixSix (View.full UMixSix) (· ≤ ·) 2 Fate.finalized := by
  intro h
  cases h with
  | fullFinal ho _ _ => exact ho (by decide)
  | mixedFinal _ hi _ _ _ _ => simp [AMixSix] at hi
  | recoveryFinal hres hi hj helig hmin => simp [AMixSix] at hi

-- Commit the certificate block as an anchor, and `mixedFinal` fires.
def AMixSixCert : Anchors UMixSix where
  seq := [12]
  mem := by decide
  chained := by simp

example : VerdictFive UMixSix AMixSixCert (View.full UMixSix) (· ≤ ·) 2 Fate.finalized :=
  .mixedFinal (i := 0) (a := 12) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) Reaches.refl
    ((isFullCert_iff (by decide)).mpr (by decide))

-- An anchor below the certificate does not: block 6 is a round-1 ACK,
-- and nothing in its history carries the certificate.
def AMixSixBelow : Anchors UMixSix where
  seq := [6]
  mem := by decide
  chained := by simp

private theorem mixSix_no_cert_below :
    ∀ C ∈ historyIn UMixSix 6, ¬ IsFullCertDec UMixSix C 2 := by decide

example : ¬ VerdictFive UMixSix AMixSixBelow (View.full UMixSix) (· ≤ ·) 2
    Fate.finalized := by
  intro h
  cases h with
  | fullFinal ho _ _ => exact ho (by decide)
  | mixedFinal _ hi _ hC hr hcert =>
      have ha := List.mem_of_getElem? hi
      simp only [AMixSixBelow, List.mem_singleton] at ha
      subst ha
      exact mixSix_no_cert_below _ ((mem_historyIn_iff (by decide)).mpr ⟨hC, hr⟩)
        ((isFullCert_iff hC).mp hcert)
  | recoveryFinal hres hi hj helig hmin =>
      obtain ⟨-, hij, ⟨aₖ, a, hlk, hla, -⟩, -⟩ := hres
      have h1 := (List.getElem?_eq_some_iff.mp hlk).1
      have h2 := (List.getElem?_eq_some_iff.mp hla).1
      simp [AMixSixBelow] at h1 h2
      omega

/-! ### Arc audit: `EligibleFive`'s `Frozen` conjunct is never discriminating:
a mutant counting bare standers passes the committed suite. -/

/-- `lkRecBare` with validator 2's round-2 block declaring `ack 0` but
carrying NO marker: three validators stand at `ack 0` at anchor 17, but
only two of them frozen. -/
def lkRecNoF : Fin 24 → Block (Fin 6) (Fin 24) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else lkRecBare i

def U6RecNoF : Universe (Fin 6) (Fin 24) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkRecNoF
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Real definition: only two frozen supporters — not eligible.
example : ¬ EligibleFive U6RecNoF 6 17 0 0 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)

-- Mutant (Frozen conjunct dropped): three bare standers reach `half`.
example : (0 : Fin 4) ∈ candidates U6RecNoF 17 0 ∧
    half (Fin 6) ≤ (Finset.univ.filter fun id =>
      StanceSomeDec U6RecNoF id (0 : Fin 2) 17 (Stance.ack 0)).card := by decide
/-! ### Arc audit: The two behavioural hypotheses coexist: the committed U6Rec
satisfies StanceDiscipline as well as Move+Freeze (never pinned). -/

example : StanceDiscipline U6Rec :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

end RedSnapper

end LeanDagTest
