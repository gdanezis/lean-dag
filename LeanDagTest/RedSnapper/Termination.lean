import LeanDag.RedSnapper.Helpers.Voting
import LeanDag.RedSnapper.Termination.Statement
import LeanDagTest.RedSnapper.Liveness
import LeanDagTest.RedSnapper.MixedRecovery

/-!
# Witness: termination, and the late candidate

* **`UTriLate`, the late candidate.** RS5's all-skip table over
  `threeTxs`, plus one round-4 block of validator `1` carrying a third
  valid transaction on the same object, `tx 2`. With anchors `[12, 13]`
  the transaction is in the global order, its object released at the
  earlier anchor, where it is not yet a candidate. `releasedDrop` drops
  it, and it is the only route that does: every derivation of a drop
  goes through a release at an earlier anchor — the skip route is shut
  (one block at round 4 is no quorum), no certificate exists for a rival
  to drop it, and the later anchor does not resolve the object a second
  time. Nor can it be finalized.
* **`ULiveLong`, `Decided`'s premises, uncontested.** `ULive` continued
  to round 5 with the correct round-5 block `16` committed:
  `finalizeOnCommit`.
* **`ULiveRival`, the rival seen only at the anchor.** The same run, but
  a Byzantine round-3 block carries the rival `tx 1` and validator `1`
  references it at round 4. No valid rival is included by the anchor's
  own round-3 block — the premise RS11 reads — while one *is* included
  in the universe, so RS4's global premise is false here. The anchor
  sees the conflict and commits `tx 0` by `resolveCommit`, alive; and the
  rival, a candidate of that anchor beside a finalized and certified
  `tx 0`, is dropped — `DecidedAgainst`'s second case, on data.
* **`UTriLong`, `Decided`'s premises, contested.** RS5's all-skip table
  continued to round 5. With the round-5 anchor alone the object
  resolves at the given anchor itself (`resolveDrop`); with the round-3
  anchor committed too it resolves there, and the given anchor drops
  `tx 0` by `releasedDrop` — here not the only route, since `tx 0` is a
  candidate of the release anchor as well.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### The late candidate -/

/-- `lkTri` over `threeTxs`, with id `13` a round-4 block of validator
`1` carrying the late `tx 2`; id `14` junk. -/
def lkTriLate : Fin 15 → Block (Fin 4) (Fin 15) (Fin 3) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if h : (i : ℕ) < 7 then
    { round := 1, author := ⟨(i : ℕ) - 3, by omega⟩, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if h : (i : ℕ) < 10 then
    { round := 2, author := ⟨(i : ℕ) - 6, by omega⟩, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if h : (i : ℕ) < 13 then
    { round := 3, author := ⟨(i : ℕ) - 9, by omega⟩, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 13 then
    { round := 4, author := 1, parents := {10, 11, 12}, txs := {2},
      declares := fun o => if o = 0 then some .bot else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def UTriLate : Universe (Fin 4) (Fin 15) (Fin 3) (Fin 2) where
  ids := Finset.univ.erase 14
  block := lkTriLate
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : StanceDiscipline UTriLate :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule UTriLate := votingRule_iff.mpr (by decide)

/-- The release anchor and the late block. -/
def ATriLate₂ : Anchors UTriLate where
  seq := [12, 13]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- The object is released at anchor 12; the late transaction is a
-- candidate of block 13 and of no other block.
example : ResolvesAt UTriLate ATriLate₂ 0 0 := resolvesAt_iff.mpr (by decide)
private theorem late_only_at : ∀ b ∈ UTriLate.ids, (2 : Fin 3) ∈ candidates UTriLate b 0 →
    b = 13 := by decide

-- With both anchors committed, the late candidate is dropped.
example : TxVerdict UTriLate ATriLate₂ (View.full UTriLate) 2 Fate.dropped :=
  .releasedDrop (i := 1) (j := 0) (a := 13) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide)
    (resolvesAt_iff.mpr (by decide))

-- It is the only route: every derivation of a drop for `tx 2` goes
-- through a release at an earlier anchor. The skip route is shut (one
-- block at round 4 is no quorum), no certificate exists for a rival to
-- drop it, and neither anchor resolves the object with it as a candidate.
private theorem late_no_skip_quorum : ¬ AtLeast UTriLate (quorum (Fin 4))
    (blocksAt UTriLate 4 ∩ (View.full UTriLate).ids) fun C => IsSkipCert UTriLate C 0 :=
  fun h => absurd (skipQuorumAtInView_iff.mp h) (by decide)
private theorem late_no_cert : ∀ tx : Fin 3, ∀ C ∈ UTriLate.ids, ¬ IsFastCertDec UTriLate C tx := by
  decide
private theorem late_no_second : ¬ ResolvesAt UTriLate ATriLate₂ 1 0 := fun h =>
  absurd (resolvesAt_iff.mp h) (by decide)

example (h : TxVerdict UTriLate ATriLate₂ (View.full UTriLate) 2 Fate.dropped) :
    ∃ i j, j < i ∧ ResolvesAt UTriLate ATriLate₂ j 0 := by
  cases h with
  | @skipDecide r b hb hcand hq =>
      exfalso
      have hbid := mem_ids_of_mem_blocksAt (Finset.mem_inter.mp hb).1
      have hcand' : IsCandidate UTriLate b 0 2 := hcand
      have hb13 := late_only_at b hbid ((mem_candidates_iff hbid).mpr hcand')
      subst hb13
      have hr : (UTriLate.block 13).round = r :=
        (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2
      have h4 : (UTriLate.block 13).round = 4 := by decide
      obtain rfl : r = 4 := by omega
      exact late_no_skip_quorum hq
  | releasedDrop _ _ hji hres => exact ⟨_, _, hji, hres⟩
  | resolveDropRival _ _ hriv =>
      obtain ⟨tx₀, -, -, ⟨C, hC, hc, -⟩, -⟩ := hriv
      exact absurd ((isFastCert_iff hC).mp hc) (late_no_cert tx₀ C hC)
  | @resolveDrop i a hia hres hcand =>
      exfalso
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hia
      have hcand' : IsCandidate UTriLate a 0 2 := hcand
      have ha13 := late_only_at a (anchor_mem_ids hia) ((mem_candidates_iff
        (anchor_mem_ids hia)).mpr hcand')
      subst ha13
      have hi : i = 1 := by
        simp only [ATriLate₂, List.length_cons, List.length_nil] at hlt
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0
          simp [ATriLate₂] at heq
        · omega
      subst hi
      exact late_no_second hres

-- Nor is it finalized: every finalizing route needs a certificate.
example : ¬ TxVerdict UTriLate ATriLate₂ (View.full UTriLate) 2 Fate.finalized := fun h =>
  let ⟨C, hC, hc⟩ := cert_of_finalized h
  late_no_cert 2 C hC ((isFastCert_iff hC).mp hc)

/-! ### RS11's premises, uncontested -/

/-- `lkLive`'s table continued: rounds 4 and 5 (`13..15`, `16..18`) and one
round-6 block `19`, all referencing the three correct blocks below; id
`20` junk. -/
def lkLiveLong : Fin 21 → Block (Fin 4) (Fin 21) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 4 then
    { round := 1, author := 1, parents := {1, 2, 3}, txs := {0},
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 5 then
    { round := 1, author := 2, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 3, parents := {1, 2, 3}, txs := ∅, declares := fun _ => none }
  else if h : (i : ℕ) < 10 then
    { round := 2, author := ⟨(i : ℕ) - 6, by omega⟩, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if h : (i : ℕ) < 13 then
    { round := 3, author := ⟨(i : ℕ) - 9, by omega⟩, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if h : (i : ℕ) < 16 then
    { round := 4, author := ⟨(i : ℕ) - 12, by omega⟩, parents := {10, 11, 12}, txs := ∅,
      declares := fun _ => none }
  else if h : (i : ℕ) < 19 then
    { round := 5, author := ⟨(i : ℕ) - 15, by omega⟩, parents := {13, 14, 15}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 19 then
    { round := 6, author := 1, parents := {16, 17, 18}, txs := ∅, declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def ULiveLong : Universe (Fin 4) (Fin 21) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 20
  block := lkLiveLong
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The correct round-5 block, committed. -/
def ALiveLong : Anchors ULiveLong where
  seq := [16]
  mem := by decide
  chained := by simp

-- Every hypothesis of `Decided`, for `tx 0` at `r₀ = 1`, `R = 1`, `b₀ = 4`.
example : StanceDiscipline ULiveLong :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule ULiveLong := votingRule_iff.mpr (by decide)
example : (ULiveLong.block 4).author ∈ (Correct : Finset (Fin 4)) ∧
    (ULiveLong.block 4).round = 1 ∧ Includes ULiveLong 4 0 :=
  ⟨by decide, by decide, (mem_txsIn_iff (by decide)).mp (by decide)⟩
example : SynchronisedOn ULiveLong (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULiveLong (Correct : Finset (Fin 4)) 2 ∧
    PopulatedOn ULiveLong (Correct : Finset (Fin 4)) 4 := by
  unfold PopulatedOn; decide
example : (ULiveLong.block 16).author ∈ (Correct : Finset (Fin 4)) ∧
    1 + 4 ≤ (ULiveLong.block 16).round := by decide

-- The conclusion: the given anchor commits the transaction.
example : TxVerdict ULiveLong ALiveLong (View.full ULiveLong) 0 Fate.finalized :=
  .finalizeOnCommit (i := 0) (a := 16) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))

/-! ### The rival seen only at the anchor -/

/-- `lkLiveLong`'s table with id `20` a Byzantine round-3 block carrying
the rival `tx 1`, referenced by validator `1` at round 4; every correct
block that sees the conflict keeps its ACK. -/
def lkLiveRival : Fin 21 → Block (Fin 4) (Fin 21) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 13 then
    { round := 4, author := 1, parents := {10, 11, 12, 20}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if h : 16 ≤ (i : ℕ) ∧ (i : ℕ) < 19 then
    { round := 5, author := ⟨(i : ℕ) - 15, by omega⟩, parents := {13, 14, 15}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 19 then
    { round := 6, author := 1, parents := {16, 17, 18}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 20 then
    { round := 3, author := 0, parents := {7, 8, 9}, txs := {1}, declares := fun _ => none }
  else lkLiveLong i

def ULiveRival : Universe (Fin 4) (Fin 21) (Fin 4) (Fin 2) where
  ids := Finset.univ
  block := lkLiveRival
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The correct round-5 block, committed. -/
def ALiveRival : Anchors ULiveRival where
  seq := [16]
  mem := by decide
  chained := by simp

-- `Decided`'s hypotheses hold, for `tx 0` at `r₀ = 1`, `R = 1`, `b₀ = 4`.
example : StanceDiscipline ULiveRival :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule ULiveRival := votingRule_iff.mpr (by decide)
example : SynchronisedOn ULiveRival (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULiveRival (Correct : Finset (Fin 4)) 2 ∧
    PopulatedOn ULiveRival (Correct : Finset (Fin 4)) 4 := by
  unfold PopulatedOn; decide

-- The rival premise, read where RS11 reads it, holds: the anchor's own
-- round-3 block includes no valid rival. Read globally, as RS4 reads
-- it, it fails: the Byzantine block includes one.
example : ∀ tx' ∈ txsIn ULiveRival 10, tx' = 0 := by decide
example : Transactions.Valid (1 : Fin 4) ∧ Conflict (0 : Fin 4) 1 ∧ Includes ULiveRival 20 1 :=
  ⟨by decide, by decide, (mem_txsIn_iff (by decide)).mp (by decide)⟩

-- The anchor sees the conflict, and commits the certified, alive `tx 0`.
example : Conflicted ULiveRival 16 0 := (conflicted_iff (by decide)).mpr (by decide)
example : TxVerdict ULiveRival ALiveRival (View.full ULiveRival) 0 Fate.finalized :=
  .resolveCommit (i := 0) (a := 16) (by decide) ((conflicted_iff (by decide)).mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide)) ((hasCert_iff (by decide)).mpr (by decide))
    (fun h => absurd (deadAt_iff.mp h) (by decide))

-- `DecidedAgainst`, second case: the rival is a candidate of the anchor,
-- beside a finalized `tx 0` certified under it — and is dropped.
example : TxVerdict ULiveRival ALiveRival (View.full ULiveRival) 1 Fate.dropped :=
  .resolveDropRival (i := 0) (a := 16) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ⟨0, by decide, (mem_candidates_iff (by decide)).mp (by decide),
      (hasCert_iff (by decide)).mpr (by decide),
      fun h => absurd (deadAt_iff.mp h) (by decide)⟩

/-! ### RS11's premises, contested -/

/-- `lkTri`'s table continued: rounds 4 and 5 (`13..15`, `16..18`), every
correct block re-declaring `⊥`; id `19` junk. -/
def lkTriLong : Fin 20 → Block (Fin 4) (Fin 20) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅, txs := ∅, declares := fun _ => none }
  else if h : (i : ℕ) < 7 then
    { round := 1, author := ⟨(i : ℕ) - 3, by omega⟩, parents := {1, 2, 3}, txs := {0, 1},
      declares := fun o => if o = 0 then some .bot else none }
  else if h : (i : ℕ) < 10 then
    { round := 2, author := ⟨(i : ℕ) - 6, by omega⟩, parents := {4, 5, 6}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if h : (i : ℕ) < 13 then
    { round := 3, author := ⟨(i : ℕ) - 9, by omega⟩, parents := {7, 8, 9}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if h : (i : ℕ) < 16 then
    { round := 4, author := ⟨(i : ℕ) - 12, by omega⟩, parents := {10, 11, 12}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if h : (i : ℕ) < 19 then
    { round := 5, author := ⟨(i : ℕ) - 15, by omega⟩, parents := {13, 14, 15}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def UTriLong : Universe (Fin 4) (Fin 20) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 19
  block := lkTriLong
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The release anchor and the correct round-5 block, committed. -/
def ATriLong : Anchors UTriLong where
  seq := [12, 16]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- Every hypothesis of `Decided`, for `tx 0` at `r₀ = 1`, `R = 1`, `b₀ = 4`.
example : StanceDiscipline UTriLong :=
  stanceDiscipline_iff.mpr (by unfold NoReturnDec NoSwitchDec; decide)
example : VotingRule UTriLong := votingRule_iff.mpr (by decide)
example : (UTriLong.block 4).author ∈ (Correct : Finset (Fin 4)) ∧
    (UTriLong.block 4).round = 1 ∧ Includes UTriLong 4 0 :=
  ⟨by decide, by decide, (mem_txsIn_iff (by decide)).mp (by decide)⟩
example : SynchronisedOn UTriLong (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn UTriLong (Correct : Finset (Fin 4)) 2 ∧
    PopulatedOn UTriLong (Correct : Finset (Fin 4)) 4 := by
  unfold PopulatedOn; decide
example : (UTriLong.block 16).author ∈ (Correct : Finset (Fin 4)) ∧
    1 + 4 ≤ (UTriLong.block 16).round := by decide

/-- The round-5 anchor alone. -/
def ATriLong₁ : Anchors UTriLong where
  seq := [16]
  mem := by decide
  chained := by simp

-- With the given anchor alone, the object resolves at it: `resolveDrop`.
example : TxVerdict UTriLong ATriLong₁ (View.full UTriLong) 0 Fate.dropped :=
  .resolveDrop (i := 0) (a := 16) (by decide) (resolvesAt_iff.mpr (by decide))
    ((mem_candidates_iff (by decide)).mp (by decide))

-- With the round-3 anchor committed too, the object resolves there, and
-- the given anchor drops `tx 0` by `releasedDrop`.
example : TxVerdict UTriLong ATriLong (View.full UTriLong) 0 Fate.dropped :=
  .releasedDrop (i := 1) (j := 0) (a := 16) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide)
    (resolvesAt_iff.mpr (by decide))

end RedSnapper

end LeanDagTest
