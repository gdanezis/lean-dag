import LeanDag.RedSnapper.Five.RecoveryTermination.Statement
import LeanDag.RedSnapper.Five.Agreement.Statement
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness: owned and mixed transactions compete in the recovery

The `5f+1` recovery with a *mixed* candidate — the case the owned-only
reading of `Candidates` could not express. `fourTxs` has one mixed
transaction and gives it no rival, so the scenario needs its own table:
`threeTxs`, three valid transactions on `o0`, of which `tx 0` is mixed.

* **`UMixRec`** — `U6Rec`'s table read over `threeTxs`: the rivals are
  the mixed `tx 0` and the owned `tx 1`. One of the two candidates is
  mixed, so under the owned-only reading the trigger anchor saw a single
  candidate and nothing ever triggered; over `Candidates` as the paper
  now has it, anchor `6` triggers, the five correct validators freeze,
  anchor `17` resolves, and the election is the mixed transaction's:
  `recoveryFinal` finalises it and `recoveryDropLoser` drops the owned
  rival. The finalised mixed transaction is a candidate of a committed
  anchor — RS8's `MixedViaAnchor` on data, through the recovery route.
* **Termination's premises** — on `UMixRec` no certificate exists, so
  `ConflictDecides`' marker input is live: the trigger exists and its
  markers are absent up to it and complete under anchor `17`.
* **`UMixRecFull`** — `U6RecFull`'s table over `threeTxs`: all five
  correct validators stand at the mixed `tx 0`, block `12` is its full
  certificate, and anchor `6`, below it, still triggers. Two routes now
  finalise the same mixed transaction — `mixedFinal` at anchor `17`,
  strictly above the certificate, and `recoveryFinal` at the same
  anchor — the cross-route pair RS8's agreement covers; the reflection
  claim's `W = {tx}` is checked for a mixed certificate; the certificate
  in anchor `17`'s history keeps it from triggering, which a mutant
  reading only owned certificates gets wrong; and `ConflictDecides`' C5
  input is live: the certificate lies under committed anchors.
* **`UMixRecLate`** — `UMixRec` with a third transaction first included
  above the resolving anchor: `resolvedDrop` drops it, every other drop
  route is shut, and the winner, a candidate of the same later anchor,
  is dropped by none.
* **The loser of a mixed commit** — on `UMixRecFull`, `certifiedRivalDrop`
  beside `mixedFinal`, in the empty view.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Three valid transactions on `o0`; `0` is mixed, `1` and `2` owned. -/
instance threeTxs : Transactions (Fin 3) (Fin 2) where
  input := fun _ => 0
  Valid := fun _ => True
  Mixed := fun tx => tx = 0

example : Conflict (0 : Fin 3) 1 ∧ Transactions.Mixed (0 : Fin 3) ∧ Owned (1 : Fin 3) := by
  decide

/-- `fourTxs`' transactions `0` and `1` read in `threeTxs`. -/
def recast (t : Fin 4) : Fin 3 := if t = 0 then 0 else if t = 1 then 1 else 2

/-- A `fourTxs` block read over `threeTxs`: the same round, author,
parents, stances and markers. -/
def recastBlock (b : Block (Fin 6) (Fin 24) (Fin 4) (Fin 2)) :
    Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) :=
  { round := b.round, author := b.author, parents := b.parents,
    txs := b.txs.image recast,
    declares := fun o => match b.declares o with
      | some (.ack t) => some (.ack (recast t))
      | some .bot => some .bot
      | none => none,
    freezes := b.freezes }

/-- `lkRec` over `threeTxs`. -/
def lkMixRec : Fin 24 → Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) := fun i =>
  recastBlock (lkRec i)

def UMixRec : Universe (Fin 6) (Fin 24) (Fin 3) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkMixRec
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `UMixRec`: `ARec`'s. -/
def AMixRec : Anchors UMixRec where
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

example : MoveDiscipline UMixRec := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline UMixRec := freezeDiscipline_iff.mpr (by decide)

-- The conflict at the trigger anchor is between a mixed and an owned
-- candidate, and it triggers.
example : IsCandidate UMixRec 6 0 0 ∧ IsCandidate UMixRec 6 0 1 :=
  ⟨(mem_candidates_iff (by decide)).mp (by decide),
    (mem_candidates_iff (by decide)).mp (by decide)⟩
example : ∀ tx ∈ candidates UMixRec 6 0, tx = 0 ∨ tx = 1 := by decide
example : Triggers UMixRec 6 0 := (triggers_iff (by decide)).mpr (by decide)
example : TriggerAt UMixRec AMixRec 0 1 := triggerAt_iff.mpr (by decide)
example : ResolvesFiveAt UMixRec AMixRec 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

-- The election goes to the mixed transaction; the owned rival has no
-- support.
example : EligibleFive UMixRec 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ¬ EligibleFive UMixRec 6 17 0 1 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)

-- The verdicts: the mixed transaction finalised, the owned one dropped.
example : VerdictFive UMixRec AMixRec (View.full UMixRec) (· ≤ ·) 0 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)
example : VerdictFive UMixRec AMixRec (View.full UMixRec) (· ≤ ·) 1 Fate.dropped :=
  .recoveryDropLoser (tx' := 0) (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _) (by decide)

-- The finalised mixed transaction is a candidate of a committed anchor.
example : ∃ (i : ℕ) (a : Fin 24), AMixRec.seq[i]? = some a ∧ IsCandidate UMixRec a 0 0 :=
  ⟨2, 17, by decide, (mem_candidates_iff (by decide)).mp (by decide)⟩

/-! ### The premises of `ConflictDecides`, on data -/

-- No certificate of either kind exists, so the lemma's third case applies
-- and its C5 input on mixed certificates is idle.
example : ∀ C ∈ UMixRec.ids, ¬ IsFullUnlockCertDec UMixRec C 0 := by decide
example : ∀ tx : Fin 3, ∀ C ∈ UMixRec.ids, ¬ IsFullCertDec UMixRec C tx := by decide

-- The committed anchor `6` sees the conflict.
example : Conflicted UMixRec 6 0 := (conflicted_iff (by decide)).mpr (by decide)

-- The marker input: no quorum at or before the trigger index, and every
-- correct validator frozen under the later anchor `17`.
example : ∀ i' ≤ 1, ∀ a', AMixRec.seq[i']? = some a' → ¬ FreezeQuorumDec UMixRec 6 0 a' := by
  decide
example : ∀ v ∈ (Correct : Finset (Fin 6)), FrozenDec UMixRec 6 v 0 17 := by decide

/-! ### A mixed certificate and the recovery agree -/

/-- `lkRecFull` over `threeTxs`. -/
def lkMixRecFull : Fin 24 → Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) := fun i =>
  recastBlock (lkRecFull i)

def UMixRecFull : Universe (Fin 6) (Fin 24) (Fin 3) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkMixRecFull
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `UMixRecFull`: `ARecFull`'s. -/
def AMixRecFull : Anchors UMixRecFull where
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

example : MoveDiscipline UMixRecFull := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline UMixRecFull := freezeDiscipline_iff.mpr (by decide)

-- The mixed transaction is fully certified at round 2; the trigger, one
-- round below, does not see the certificate; the resolving anchor does.
example : IsFullCert UMixRecFull 12 0 := (isFullCert_iff (by decide)).mpr (by decide)
example : Triggers UMixRecFull 6 0 := (triggers_iff (by decide)).mpr (by decide)
example : ResolvesFiveAt UMixRecFull AMixRecFull 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

-- A mixed certificate in the history blocks the trigger. A mutant whose
-- certificate conjunct reads owned transactions only says anchor 17
-- triggers.
example : ¬ Triggers UMixRecFull 17 0 := fun h =>
  absurd ((triggers_iff (by decide)).mp h) (by decide)
example : (∃ tx ∈ candidates UMixRecFull 17 0, ∃ tx' ∈ candidates UMixRecFull 17 0, tx ≠ tx') ∧
    (¬ ∃ b ∈ historyIn UMixRecFull 17, IsFullUnlockCertDec UMixRecFull b 0) ∧
    ¬ ∃ tx ∈ candidates UMixRecFull 17 0, Owned tx ∧
      ∃ b ∈ historyIn UMixRecFull 17, IsFullCertDec UMixRecFull b tx := by decide

-- The reflection claim for a mixed certificate: `W = {tx 0}`.
example : EligibleFive UMixRecFull 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ∀ tx' : Fin 3, EligibleFiveDec UMixRecFull 6 17 0 tx' → tx' = 0 := by decide

-- Two routes, one fate: the anchor route reads the certificate strictly
-- below anchor 17, the recovery route elects the same transaction there.
example : (UMixRecFull.block 12).round < (UMixRecFull.block 17).round := by decide
example : VerdictFive UMixRecFull AMixRecFull (View.full UMixRecFull) (· ≤ ·) 0
    Fate.finalized :=
  .mixedFinal (i := 2) (a := 17) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide)
    ((mem_history_iff (by decide)).mp (by decide))
    ((isFullCert_iff (by decide)).mpr (by decide))
example : VerdictFive UMixRecFull AMixRecFull (View.full UMixRecFull) (· ≤ ·) 0
    Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)

-- `ConflictDecides`' C5 input, live: every full certificate of the mixed
-- transaction — block 12 and the later ones above it — lies under a
-- committed anchor.
example : ∀ C ∈ UMixRecFull.ids, IsFullCertDec UMixRecFull C 0 →
    C ∈ historyIn UMixRecFull 17 ∨ C ∈ historyIn UMixRecFull 22 := by decide
example : ¬ ∀ C ∈ UMixRecFull.ids, IsFullCertDec UMixRecFull C 0 →
    C ∈ historyIn UMixRecFull 17 := by decide

/-! ### A candidate first included above the resolution

`UMixRec` with `tx 2` — a third valid transaction on the same object —
carried by validator `1`'s round-3 block `18`: not in the history of the
resolving anchor `17`, in that of the later anchor `22`. It is in the
global order, its object resolved below it with `tx 0` the winner, and
`resolvedDrop` drops it, every other drop route being shut. The winner,
a candidate of the same later anchor, is dropped by no route. -/

/-- `lkMixRec` with block `18` carrying the late `tx 2`. -/
def lkMixRecLate : Fin 24 → Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) := fun i =>
  if (i : ℕ) = 18 then
    { round := 3, author := 1, parents := {12, 13, 14, 15, 16}, txs := {2},
      declares := fun _ => none }
  else lkMixRec i

def UMixRecLate : Universe (Fin 6) (Fin 24) (Fin 3) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkMixRecLate
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `UMixRecLate`: `AMixRec`'s. -/
def AMixRecLate : Anchors UMixRecLate where
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

example : MoveDiscipline UMixRecLate := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline UMixRecLate := freezeDiscipline_iff.mpr (by decide)

-- The resolution is `UMixRec`'s, and the late transaction is a candidate
-- of the last anchor only.
example : ResolvesFiveAt UMixRecLate AMixRecLate 0 1 2 := resolvesFiveAt_iff.mpr (by decide)
private theorem mixLate_only : ∀ b ∈ UMixRecLate.ids, (2 : Fin 3) ∈ candidates UMixRecLate b 0 →
    b = 18 ∨ b = 22 := by decide
private theorem mixLate_not_eligible : ¬ EligibleFiveDec UMixRecLate 6 17 0 2 := by decide

-- It did not win the resolution, and the anchor above drops it.
example : VerdictFive UMixRecLate AMixRecLate (View.full UMixRecLate) (· ≤ ·) 2 Fate.dropped :=
  .resolvedDrop (i := 1) (j := 2) (m := 3) (aₖ := 6) (aⱼ := 17) (a := 22)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => mixLate_not_eligible ((eligibleFive_iff (by decide)).mp h.1))

-- RS12's premises on this run: no certificate of either kind exists, the
-- conflict is seen by the committed anchor `6`, and the marker input
-- holds as on `UMixRec`.
private theorem mixLate_no_unlock : ∀ C ∈ UMixRecLate.ids,
    ¬ IsFullUnlockCertDec UMixRecLate C 0 := by decide
private theorem mixLate_no_cert : ∀ tx : Fin 3, ∀ C ∈ UMixRecLate.ids,
    ¬ IsFullCertDec UMixRecLate C tx := by decide
example : Conflicted UMixRecLate 6 0 := (conflicted_iff (by decide)).mpr (by decide)
example : ∀ i' ≤ 1, ∀ a', AMixRecLate.seq[i']? = some a' →
    ¬ FreezeQuorumDec UMixRecLate 6 0 a' := by decide
example : ∀ v ∈ (Correct : Finset (Fin 6)), FrozenDec UMixRecLate 6 v 0 17 := by decide

-- Every other drop route is shut for `tx 2`: no unlock certificate, no
-- full certificate for a rival to drop it, and no resolving anchor has it
-- among its candidates (its only anchor is `22`, index 3, where nothing
-- resolves).
example : ∀ C ∈ UMixRecLate.ids, ¬ IsFullUnlockCertDec UMixRecLate C 0 := mixLate_no_unlock
example : ∀ tx : Fin 3, ∀ C ∈ UMixRecLate.ids, ¬ IsFullCertDec UMixRecLate C tx :=
  mixLate_no_cert
example : (22 : Fin 24) ∈ AMixRecLate.seq ∧ (18 : Fin 24) ∉ AMixRecLate.seq ∧
    AMixRecLate.seq[3]? = some 22 := by decide
example : ∀ i < 4, ¬ ResolvesFiveAtDec UMixRecLate AMixRecLate 0 i 3 := by decide

-- The "not the winner" premise is what keeps the route off the winner:
-- `tx 0` is a candidate of anchor `22` too, above the resolution it won,
-- and no route drops it.
private theorem mixLate_res : ∀ i < 4, ∀ j < 4,
    ResolvesFiveAtDec UMixRecLate AMixRecLate 0 i j → i = 1 ∧ j = 2 := by decide
private theorem mixLate_res_at {i j : ℕ} {aₖ aⱼ : Fin 24}
    (hres : ResolvesFiveAt UMixRecLate AMixRecLate 0 i j)
    (hlk : AMixRecLate.seq[i]? = some aₖ) (hlj : AMixRecLate.seq[j]? = some aⱼ) :
    aₖ = 6 ∧ aⱼ = 17 := by
  have hj := (List.getElem?_eq_some_iff.mp hlj).1
  simp only [AMixRecLate, List.length_cons, List.length_nil] at hj
  have hij := hres.2.1
  obtain ⟨rfl, rfl⟩ := mixLate_res i (by omega) j (by omega) (resolvesFiveAt_iff.mp hres)
  simp [AMixRecLate] at hlk hlj
  exact ⟨hlk.symm, hlj.symm⟩
private theorem mixLate_winner : EligibleFive UMixRecLate 6 17 0 0 :=
  (eligibleFive_iff (by decide)).mpr (by decide)

example : IsCandidate UMixRecLate 22 0 0 := (mem_candidates_iff (by decide)).mp (by decide)
example : ¬ VerdictFive UMixRecLate AMixRecLate (View.full UMixRecLate) (· ≤ ·) 0
    Fate.dropped := by
  intro h
  cases h with
  | fullUnlockDrop hC hunlock _ _ =>
      have hid := (View.full UMixRecLate).subset_ids hC
      exact mixLate_no_unlock _ hid ((isFullUnlockCert_iff hid).mp hunlock)
  | observedRivalDrop _ _ _ _ hC hcert =>
      have hid := (View.full UMixRecLate).subset_ids hC
      exact mixLate_no_cert _ _ hid ((isFullCert_iff hid).mp hcert)
  | certifiedRivalDrop _ _ _ hC _ hcert =>
      exact mixLate_no_cert _ _ hC ((isFullCert_iff hC).mp hcert)
  | resolvedDrop hres hlk hlj _ _ _ hnw =>
      obtain ⟨rfl, rfl⟩ := mixLate_res_at hres hlk hlj
      exact hnw ⟨mixLate_winner, fun _ _ => Fin.zero_le _⟩
  | recoveryDropLoser hres hlk hla _ _ hmin hne =>
      obtain ⟨rfl, rfl⟩ := mixLate_res_at hres hlk hla
      exact hne (Fin.le_zero_iff.mp (hmin 0 mixLate_winner)).symm
  | recoveryDropBot hres hlk hla _ hempty =>
      obtain ⟨rfl, rfl⟩ := mixLate_res_at hres hlk hla
      exact hempty 0 mixLate_winner

/-! ### The loser of a mixed commit

On `UMixRecFull` the fully certified transaction is the *mixed* `tx 0`:
final at anchor `17` by `mixedFinal` (above), and at that same anchor
its owned rival `tx 1` is dropped by `certifiedRivalDrop` — in a view
that holds nothing, since both routes read the anchor's history. -/

/-- The empty view over `UMixRecFull`. -/
def VMixRecFullNone : View UMixRecFull where
  ids := ∅
  subset_ids := by decide
  complete := by decide

example : VerdictFive UMixRecFull AMixRecFull VMixRecFullNone (· ≤ ·) 1 Fate.dropped :=
  .certifiedRivalDrop (tx' := 0) (i := 2) (a := 17) (C := 12) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) (by decide)
    ((mem_history_iff (by decide)).mp (by decide))
    ((isFullCert_iff (by decide)).mpr (by decide))
example : VerdictFive UMixRecFull AMixRecFull VMixRecFullNone (· ≤ ·) 0 Fate.finalized :=
  .mixedFinal (i := 2) (a := 17) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide)
    ((mem_history_iff (by decide)).mp (by decide))
    ((isFullCert_iff (by decide)).mpr (by decide))

end RedSnapper

end LeanDagTest
