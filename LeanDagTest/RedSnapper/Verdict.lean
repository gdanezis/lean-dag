import LeanDag.RedSnapper.Helpers.Dead
import LeanDag.RedSnapper.TxAgreement.Statement
import LeanDagTest.RedSnapper.Certificates

/-!
# Witness: anchors, death, and verdicts

The Phase 5 layer exercised end to end, decided through the surrogates
of `Helpers/Dead.lean`.

* **Anchors.** `[12, 18]` over `UCert` is chained; the unreferenced twin
  19 is reachable from nothing, so no chained sequence can put it below
  18.
* **The four routes on `UCert`.** The full view derives `fastFinal` for
  `tx 0` from the round-2 quorum of certificates; a partial view holding
  only two of the four certificate blocks derives nothing — views
  under-report. At the single anchor 12, `resolveCommit` finalizes
  `tx 0` (certified, alive) and `resolveDropRival` drops `tx 1`.
* **`UBiv`, the bivalent case, end to end.** Validators `1, 2, 3` ACK
  `tx 0`; the rival `tx 1` arrives; `2` retracts, `3` and Byzantine `0`
  skip — an unlock certificate at id 12 — while `1`'s certificate (id 8)
  forms but stays **outside** id 12's history. With anchors `[12]`:
  `ResolvesAt 0` fires, both candidates are dropped by `resolveDrop`,
  and no finalization constructor is derivable — the object is released
  by consensus with a hidden certificate in existence, exactly the
  paper's bivalent scenario. With anchors `[12, 15]`, the certificate
  surfaces at anchor 15: `HasCert` holds there, but the transaction is
  `DeadAt 1` — released below — and anchor 15 is release-ready yet does
  **not** resolve (the one-shot: anchor 12 already did). The release
  recursion demonstrably does work.
* **`USkip2`.** Three skip-certificate blocks at round 2 give the skip
  quorum; `skipDecide` drops both candidates.
* **`UMix`.** A mixed transaction certified and uncontested at anchor 11
  is finalized by `finalizeOnCommit` — the `MixedViaAnchor` scenario —
  while the round-2 certificate quorum for it exists and the `Owned`
  gate keeps the consensusless route shut (`¬ Owned 2`,
  `RedSnapperTest.Universe`).
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Chained anchors over `UCert`: block 18 reaches block 12. -/
def ACert : Anchors UCert where
  seq := [12, 18]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => by simp at hx)
      List.Pairwise.nil)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- The unreferenced twin 19 cannot sit below 18 in any chained sequence.
example : ¬ Reaches UCert 18 19 := fun h =>
  (by decide : (19 : Fin 21) ∉ history UCert 18) ((mem_history_iff (by decide)).mpr h)

-- `fastFinal` from the round-2 certificate quorum, in the full view.
example : TxVerdict UCert ACert (View.full UCert) 0 .finalized :=
  TxVerdict.fastFinal (r := 2) (by decide) (fastQuorumAtInView_iff.mpr (by decide))

/-- A view holding only two of the four round-2 certificate blocks. -/
def VPart : View UCert where
  ids := {0, 1, 2, 3, 4, 5, 6, 7, 10, 11}
  subset_ids := by decide
  complete := by decide

-- Views under-report: the partial view has no quorum; the full view
-- does.
example : FastQuorumAtInView UCert (View.full UCert) 2 0 :=
  fastQuorumAtInView_iff.mpr (by decide)
example : ¬ FastQuorumAtInView UCert VPart 2 0 := fun h =>
  absurd (fastQuorumAtInView_iff.mp h) (by decide)

/-- The single anchor 12 over `UCert`. -/
def ACert1 : Anchors UCert where
  seq := [12]
  mem := by decide
  chained := by simp

-- `resolveCommit` finalizes the certified live candidate at anchor 12,
-- and `resolveDropRival` drops its rival.
example : TxVerdict UCert ACert1 (View.full UCert) 0 .finalized :=
  TxVerdict.resolveCommit (i := 0) (a := 12) rfl
    ((conflicted_iff (by decide)).mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))
    (fun h => absurd (deadAt_iff.mp h) (by decide))
example : TxVerdict UCert ACert1 (View.full UCert) 1 .dropped :=
  TxVerdict.resolveDropRival (i := 0) (a := 12) rfl
    ((mem_candidates_iff (by decide)).mp (by decide))
    ⟨0, by decide, (mem_candidates_iff (by decide)).mp (by decide),
      (hasCert_iff (by decide)).mpr (by decide),
      fun h => absurd (deadAt_iff.mp h) (by decide)⟩

/-- The bivalent universe: sixteen ids over `fourValidators`. Round 1 —
`4` (Byzantine `0`), `5` (`1`), `6` (`2`) carry and ACK `tx 0`; `7`
(`3`) carries the rival `tx 1`. Round 2 — `8` (`1`, parents
`{4, 5, 6}`) re-ACKs over three fast votes: the certificate; `9` (`2`)
retracts (`⊥`, an unlock vote), `10` (`3`) and `11` (Byzantine `0`)
declare `⊥` never having ACKed in their histories (skip votes) — all
three over `{5, 6, 7}`, which excludes the certificate. Round 3 — `12`
(`2`, parents `{9, 10, 11}`): an unlock certificate, blind to the
certificate; `13` (`1`, parents `{8, 9, 10}`) carries the certificate
onward; `14` (`3`). Round 4 — `15` (`2`, parents `{12, 13, 14}`): sees
both the release evidence and the certificate. -/
def lkBiv : Fin 16 → Block (Fin 4) (Fin 16) (Fin 4) (Fin 2) := fun i =>
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
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {1}, declares := fun _ => none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 2, author := 0, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 12 then
    { round := 3, author := 2, parents := {9, 10, 11}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 13 then
    { round := 3, author := 1, parents := {8, 9, 10}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 14 then
    { round := 3, author := 3, parents := {9, 10, 11}, txs := ∅, declares := fun _ => none }
  else
    { round := 4, author := 2, parents := {12, 13, 14}, txs := ∅, declares := fun _ => none }

/-- The bivalent universe. -/
def UBiv : Universe (Fin 4) (Fin 16) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkBiv
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UBiv :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

-- The hidden certificate and the blind unlock certificate.
example : IsFastCert UBiv 8 0 := (isFastCert_iff (by decide)).mpr (by decide)
example : IsUnlockCert UBiv 12 0 := (isUnlockCert_iff (by decide)).mpr (by decide)
example : ¬ IsSkipCert UBiv 12 0 := fun h => absurd ((isSkipCert_iff (by decide)).mp h) (by decide)
example : ¬ HasCert UBiv 12 0 := fun h => absurd ((hasCert_iff (by decide)).mp h) (by decide)

/-- Anchors `[12]`: the release anchor alone. -/
def ABiv : Anchors UBiv where
  seq := [12]
  mem := by decide
  chained := by simp

-- The object resolves at the first anchor, and both candidates are
-- dropped by consensus — the bivalent case decided.
example : ResolvesAt UBiv ABiv 0 0 := resolvesAt_iff.mpr (by decide)
example : TxVerdict UBiv ABiv (View.full UBiv) 0 .dropped :=
  TxVerdict.resolveDrop (i := 0) (a := 12) rfl (resolvesAt_iff.mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))
example : TxVerdict UBiv ABiv (View.full UBiv) 1 .dropped :=
  TxVerdict.resolveDrop (i := 0) (a := 12) rfl (resolvesAt_iff.mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))

-- No finalization is derivable: one certificate is not a quorum, and
-- the anchor's history holds no certificate at all.
example : ¬ TxVerdict UBiv ABiv (View.full UBiv) 0 .finalized := by
  intro h
  cases h with
  | fastFinal ho hq =>
      obtain ⟨t, hts, hP, hk⟩ := hq
      have hall : ∀ C ∈ UBiv.ids, IsFastCertDec UBiv C 0 → C = 8 := by decide
      have hsub : t ⊆ {8} := by
        intro C hC
        have hCid : C ∈ UBiv.ids :=
          mem_ids_of_mem_blocksAt (Finset.mem_inter.mp (hts hC)).1
        simp [hall C hCid ((isFastCert_iff hCid).mp (hP C hC))]
      have hle := Finset.card_le_card (authorsOf_mono (U := UBiv) hsub)
      have h1 : (authorsOf UBiv.block ({8} : Finset (Fin 16))).card = 1 := by decide
      have h3 : quorum (Fin 4) = 3 := by decide
      omega
  | @finalizeOnCommit i a hi hc hnc hcert =>
      cases i with
      | zero =>
          obtain rfl : (12 : Fin 16) = a := Option.some.inj hi
          exact absurd ((hasCert_iff (by decide)).mp hcert) (by decide)
      | succ n =>
          rw [show ABiv.seq = [12] from rfl] at hi
          simp at hi
  | @resolveCommit i a hi hc hcand hcert hlive =>
      cases i with
      | zero =>
          obtain rfl : (12 : Fin 16) = a := Option.some.inj hi
          exact absurd ((hasCert_iff (by decide)).mp hcert) (by decide)
      | succ n =>
          rw [show ABiv.seq = [12] from rfl] at hi
          simp at hi

/-- Anchors `[12, 15]`: the certificate surfaces at the second anchor. -/
def A2Biv : Anchors UBiv where
  seq := [12, 15]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => by simp at hx)
      List.Pairwise.nil)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- At anchor 15 the certificate is visible but the transaction is dead —
-- released below — and the anchor is release-ready yet does not
-- resolve: anchor 12 already did. The recursion and the one-shot, both
-- at work.
example : HasCert UBiv 15 0 := (hasCert_iff (by decide)).mpr (by decide)
example : DeadAt UBiv A2Biv 1 0 := deadAt_iff.mpr (by decide)
example : ReleasedBelow UBiv A2Biv 1 0 := (releasedBelow_iff 1 0).mpr (by decide)
example : ResolveReadyAt UBiv A2Biv 1 0 := resolveReadyAt_iff.mpr (by decide)
example : ¬ ResolvesAt UBiv A2Biv 1 0 := fun h => absurd (resolvesAt_iff.mp h) (by decide)
example : ResolvesAt UBiv A2Biv 0 0 := resolvesAt_iff.mpr (by decide)

/-- The skip-quorum universe: as `USkip`, with all three correct
validators certifying the skip at round 2. -/
def lkSkip2 : Fin 12 → Block (Fin 4) (Fin 12) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {5, 6, 7}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅, declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

/-- The skip-quorum universe: ids `0`–`10`, id `11` junk. -/
def USkip2 : Universe (Fin 4) (Fin 12) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 11
  block := lkSkip2
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline USkip2 :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

/-- An empty anchor sequence: the consensusless routes stand alone. -/
def ASkip2 : Anchors USkip2 where
  seq := []
  mem := by decide
  chained := List.Pairwise.nil

-- The skip quorum drops both candidates, mixed or owned alike.
example : SkipQuorumAtInView USkip2 (View.full USkip2) 2 0 :=
  skipQuorumAtInView_iff.mpr (by decide)
example : TxVerdict USkip2 ASkip2 (View.full USkip2) 0 .dropped :=
  TxVerdict.skipDecide (r := 2) (b := 8) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (skipQuorumAtInView_iff.mpr (by decide))
example : TxVerdict USkip2 ASkip2 (View.full USkip2) 1 .dropped :=
  TxVerdict.skipDecide (r := 2) (b := 8) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (skipQuorumAtInView_iff.mpr (by decide))

/-- The mixed universe: everyone ACKs the mixed `tx 2` on `o1` at
round 1; three certificates at round 2; an anchor at round 3. -/
def lkMix : Fin 12 → Block (Fin 4) (Fin 12) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 0, parents := {0, 1, 2}, txs := {2},
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 1, parents := {0, 1, 2}, txs := {2},
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := {2},
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := {2},
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 8 then
    { round := 2, author := 1, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 9 then
    { round := 2, author := 2, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else if (i : ℕ) = 10 then
    { round := 2, author := 3, parents := {5, 6, 7}, txs := ∅,
      declares := fun o => if o = 1 then some (.ack 2) else none }
  else
    { round := 3, author := 1, parents := {8, 9, 10}, txs := ∅, declares := fun _ => none }

/-- The mixed universe: ids `0`–`11`. -/
def UMix : Universe (Fin 4) (Fin 12) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkMix
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UMix :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)

/-- The single anchor 11 over `UMix`. -/
def AMix : Anchors UMix where
  seq := [11]
  mem := by decide
  chained := by simp

-- The mixed transaction is finalized through the anchor: uncontested,
-- certified — the `MixedViaAnchor` scenario. The certificate quorum for
-- it exists at round 2, and only the `Owned` gate keeps the
-- consensusless route shut (`¬ Owned 2`, `RedSnapperTest.Universe`).
example : TxVerdict UMix AMix (View.full UMix) 2 .finalized :=
  TxVerdict.finalizeOnCommit (i := 0) (a := 11) rfl
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))
example : FastQuorumAtInView UMix (View.full UMix) 2 2 :=
  fastQuorumAtInView_iff.mpr (by decide)

end RedSnapper

end LeanDagTest
