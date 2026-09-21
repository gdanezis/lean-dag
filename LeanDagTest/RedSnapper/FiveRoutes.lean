import LeanDag.RedSnapper.Helpers.VotingFive
import LeanDag.RedSnapper.Five.RecoveryTermination.Statement
import LeanDagTest.RedSnapper.LivenessHardening
import LeanDagTest.RedSnapper.Coin
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness hardening: which route reads what

* **The anchor route reads the universe and is class-gated.** Over a
  view holding genesis only, with the certificate block committed:
  `U6Full`'s *owned* `tx 0` has no finalized verdict — `fullFinal` needs
  the certificate in the view, and `mixedFinal` is shut to an owned
  transaction — while `UMixSix`'s *mixed* `tx 2`, under the same view,
  is final by `mixedFinal`, which reads the anchor's history and not
  the view.
* **RS4's anchor claim, owned branch.** `ULive` with its round-3 block
  `10` committed: `finalizeOnCommit` finalises the owned `tx 0` — the
  claim has no class gate.
* **`FullVerdict` needs the certificate round.** On `ULiveT` — `ULive`
  cut after round 2 — every other hypothesis holds under the `5f+1`
  rule and no finalized verdict is derivable.
* **The loser of a fast commit** (record finding 33). On `U6RecFull`,
  the owned rival of a fully certified transaction is dropped once the
  certificate is observed (`observedRivalDrop`) or lies under the anchor
  (`certifiedRivalDrop`), has no verdict in a view and under an anchor
  that hold neither, and with the recovery committed is dropped by three
  routes at once.
* **`ConflictDecides`, the unlock case, with no marker anywhere.** On
  `U6Frag` with anchors `[6, 17]` the trigger exists and no validator
  ever freezes: the marker input is false, and is not asked for, since
  block `17` is a full unlock certificate — which decides.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### The anchor route reads the universe and is class-gated -/

/-- The view holding genesis only, over `U6Full`. -/
def VGenFull : View U6Full where
  ids := {0, 1, 2, 3, 4, 5}
  subset_ids := by decide
  complete := by decide

/-- `U6Full`'s certificate block, committed. -/
def AFullCert : Anchors U6Full where
  seq := [12]
  mem := by decide
  chained := by simp

private theorem full_no_cert_in_view : ∀ C ∈ VGenFull.ids, ¬ IsFullCertDec U6Full C 0 := by
  decide

-- Owned: the certificate exists under a committed anchor, and the view
-- that lacks it justifies nothing.
example : IsFullCert U6Full 12 0 := (isFullCert_iff (by decide)).mpr (by decide)
example : ¬ VerdictFive U6Full AFullCert VGenFull (· ≤ ·) 0 Fate.finalized := by
  intro h
  cases h with
  | fullFinal _ hC hcert =>
      exact full_no_cert_in_view _ hC ((isFullCert_iff (VGenFull.subset_ids hC)).mp hcert)
  | mixedFinal hm _ _ _ _ _ => exact absurd hm (by decide)
  | recoveryFinal hres hi hj helig hmin =>
      obtain ⟨-, hij, ⟨aₖ, a, hlk, hla, -⟩, -⟩ := hres
      have h1 := (List.getElem?_eq_some_iff.mp hlk).1
      have h2 := (List.getElem?_eq_some_iff.mp hla).1
      simp [AFullCert] at h1 h2
      omega

/-- The view holding genesis only, over `UMixSix`. -/
def VGenMix : View UMixSix where
  ids := {0, 1, 2, 3, 4, 5}
  subset_ids := by decide
  complete := by decide

-- Mixed: the same view, and the anchor route fires regardless of it.
example : (12 : Fin 13) ∉ VGenMix.ids := by decide
example : VerdictFive UMixSix AMixSixCert VGenMix (· ≤ ·) 2 Fate.finalized :=
  .mixedFinal (i := 0) (a := 12) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) Reaches.refl
    ((isFullCert_iff (by decide)).mpr (by decide))

/-! ### RS4's anchor claim, owned branch -/

/-- `ULive`'s round-3 block of validator `1`, committed. -/
def ALiveCert : Anchors ULive where
  seq := [10]
  mem := by decide
  chained := by simp

example : (ULive.block 10).author ∈ (Correct : Finset (Fin 4)) ∧
    (ULive.block 10).round = 3 ∧ Owned (0 : Fin 4) := by decide
example : TxVerdict ULive ALiveCert (View.full ULive) 0 Fate.finalized :=
  .finalizeOnCommit (i := 0) (a := 10) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))

/-! ### `FullVerdict` needs the certificate round -/

/-- An empty anchor sequence over `ULiveT`. -/
def ALiveT : Anchors ULiveT where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

-- Every other hypothesis of `FullVerdict` holds on the truncated universe ...
example : VotingRuleFive ULiveT := votingRuleFive_of_dec (by decide)
example : SynchronisedOn ULiveT (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULiveT (Correct : Finset (Fin 4)) 2 := by
  unfold PopulatedOn; decide
example : ¬ PopulatedOn ULiveT (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide

-- ... and no finalized verdict is derivable: no block carries a full
-- certificate yet.
private theorem liveT_no_cert : ∀ C ∈ ULiveT.ids, ¬ IsFullCertDec ULiveT C 0 := by decide

example : ¬ VerdictFive ULiveT ALiveT (View.full ULiveT) (· ≤ ·) 0 Fate.finalized := by
  intro h
  cases h with
  | fullFinal _ hC hcert =>
      have hid := (View.full ULiveT).subset_ids hC
      exact liveT_no_cert _ hid ((isFullCert_iff hid).mp hcert)
  | mixedFinal hm _ _ _ _ _ => exact absurd hm (by decide)
  | recoveryFinal hres hi hj helig hmin => simp [ALiveT] at hi

/-! ### `ConflictDecides`, the unlock case, with no marker anywhere -/

/-- `U6Frag`'s trigger and its round-3 block, committed. -/
def AFragUnlock : Anchors U6Frag where
  seq := [6, 17]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- The committed anchor 6 sees the conflict and triggers ...
example : Conflicted U6Frag 6 0 := (conflicted_iff (by decide)).mpr (by decide)
example : TriggerAt U6Frag AFragUnlock 0 0 := triggerAt_iff.mpr (by decide)

-- ... no validator ever freezes, so the marker input is false here ...
example : ∀ v : Fin 6, ∀ a ∈ U6Frag.ids, ¬ FrozenDec U6Frag 6 v 0 a := by decide

-- ... and it is not asked for: a full unlock certificate exists, and
-- drops the candidates.
example : IsFullUnlockCert U6Frag 17 0 := (isFullUnlockCert_iff (by decide)).mpr (by decide)
example : VerdictFive U6Frag AFragUnlock (View.full U6Frag) (· ≤ ·) 0 Fate.dropped :=
  .fullUnlockDrop (C := 17) (b := 17) (by decide)
    ((isFullUnlockCert_iff (by decide)).mpr (by decide)) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))

/-! ### The loser of a fast commit

Record finding 33, on data. On `U6RecFull` the owned `tx 0` holds a full
certificate at block `12`, and the owned rival `tx 1` is valid and a
candidate of every committed anchor — it is in the global order. Until
`FinalizeOnCommitTX`'s first loop covered owned transactions, no route
gave it a verdict. Now: a validator that has observed the certificate
drops it at any committed anchor, even one below the certificate
(`observedRivalDrop`); an anchor that holds the certificate drops it in
every view (`certifiedRivalDrop`); and a validator that holds neither —
a view of rounds 0 and 1, an anchor below the certificate — justifies no
verdict for it, of either fate. With the recovery committed as well,
three routes drop the same loser and three finalise the same winner. -/

/-- `U6RecFull`'s certificate block, committed alone. -/
def ARecFullCert : Anchors U6RecFull where
  seq := [12]
  mem := by decide
  chained := by simp

/-- A round-1 block, below the certificate, committed alone. -/
def ARecFullBelow : Anchors U6RecFull where
  seq := [6]
  mem := by decide
  chained := by simp

/-- The view of rounds 0 and 1: it holds anchor `6`, not the certificate. -/
def VRecFullEarly : View U6RecFull where
  ids := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
  subset_ids := by decide
  complete := by decide

example : Owned (1 : Fin 4) ∧ Transactions.Valid (1 : Fin 4) ∧ Conflict (1 : Fin 4) 0 := by
  decide
example : IsCandidate U6RecFull 6 0 1 := (mem_candidates_iff (by decide)).mp (by decide)
example : Conflicted U6RecFull 6 0 := (conflicted_iff (by decide)).mpr (by decide)
example : VerdictFive U6RecFull ARecFullCert (View.full U6RecFull) (· ≤ ·) 0 Fate.finalized :=
  .fullFinal (C := 12) (by decide) (by decide) ((isFullCert_iff (by decide)).mpr (by decide))

-- The certificate observed: the loser is dropped at an anchor below it.
example : VerdictFive U6RecFull ARecFullBelow (View.full U6RecFull) (· ≤ ·) 1 Fate.dropped :=
  .observedRivalDrop (tx' := 0) (i := 0) (a := 6) (C := 12) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) (by decide) (by decide)
    ((isFullCert_iff (by decide)).mpr (by decide))

-- The certificate under the anchor: dropped in the early view too.
example : VerdictFive U6RecFull ARecFullCert VRecFullEarly (· ≤ ·) 1 Fate.dropped :=
  .certifiedRivalDrop (tx' := 0) (i := 0) (a := 12) (C := 12) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) (by decide) Reaches.refl
    ((isFullCert_iff (by decide)).mpr (by decide))

private theorem recFull_no_unlock : ∀ C ∈ U6RecFull.ids, ¬ IsFullUnlockCertDec U6RecFull C 0 := by
  decide
private theorem recFull_no_cert_rival : ∀ C ∈ U6RecFull.ids, ¬ IsFullCertDec U6RecFull C 1 := by
  decide
private theorem recFull_no_cert_below : ∀ tx : Fin 4, ∀ C ∈ historyIn U6RecFull 6,
    ¬ IsFullCertDec U6RecFull C tx := by decide
private theorem recFull_no_cert_early : ∀ tx : Fin 4, ∀ C ∈ VRecFullEarly.ids,
    ¬ IsFullCertDec U6RecFull C tx := by decide
private theorem recFull_single {A : Anchors U6RecFull} (hA : A.seq.length = 1) {i j : ℕ}
    {aₖ a : Fin 24} (hij : i < j) (hlk : A.seq[i]? = some aₖ) (hla : A.seq[j]? = some a) :
    False := by
  have h1 := (List.getElem?_eq_some_iff.mp hlk).1
  have h2 := (List.getElem?_eq_some_iff.mp hla).1
  omega

-- Neither observed nor under the anchor: no verdict of either fate.
example : ¬ VerdictFive U6RecFull ARecFullBelow VRecFullEarly (· ≤ ·) 1 Fate.dropped := by
  intro h
  cases h with
  | fullUnlockDrop hC hunlock _ _ =>
      have hid := VRecFullEarly.subset_ids hC
      exact recFull_no_unlock _ hid ((isFullUnlockCert_iff hid).mp hunlock)
  | observedRivalDrop _ _ _ _ hC hcert =>
      exact recFull_no_cert_early _ _ hC
        ((isFullCert_iff (VRecFullEarly.subset_ids hC)).mp hcert)
  | certifiedRivalDrop hia _ _ hC hr hcert =>
      have ha := List.mem_of_getElem? hia
      simp only [ARecFullBelow, List.mem_singleton] at ha
      subst ha
      exact recFull_no_cert_below _ _ ((mem_historyIn_iff (by decide)).mpr ⟨hC, hr⟩)
        ((isFullCert_iff hC).mp hcert)
  | resolvedDrop hres hlk hlj _ _ _ _ => exact recFull_single rfl hres.2.1 hlk hlj
  | recoveryDropLoser hres hlk hla _ _ _ _ => exact recFull_single rfl hres.2.1 hlk hla
  | recoveryDropBot hres hlk hla _ _ => exact recFull_single rfl hres.2.1 hlk hla

example : ¬ VerdictFive U6RecFull ARecFullBelow VRecFullEarly (· ≤ ·) 1 Fate.finalized := by
  intro h
  cases h with
  | fullFinal _ hC hcert =>
      exact recFull_no_cert_early _ _ hC
        ((isFullCert_iff (VRecFullEarly.subset_ids hC)).mp hcert)
  | mixedFinal hm _ _ _ _ _ => exact absurd hm (by decide)
  | recoveryFinal hres hlk hla _ _ => exact recFull_single rfl hres.2.1 hlk hla

-- With the recovery committed too (`ARecFull`), three routes drop the
-- loser: the certificate strictly below anchor 17, the election at 17,
-- and the first loop at anchor 22 above the resolution.
example : VerdictFive U6RecFull ARecFull VRecFullEarly (· ≤ ·) 1 Fate.dropped :=
  .certifiedRivalDrop (tx' := 0) (i := 2) (a := 17) (C := 12) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) (by decide)
    ((mem_history_iff (by decide)).mp (by decide))
    ((isFullCert_iff (by decide)).mpr (by decide))
example : VerdictFive U6RecFull ARecFull VRecFullEarly (· ≤ ·) 1 Fate.dropped :=
  .recoveryDropLoser (tx' := 0) (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _) (by decide)
example : VerdictFive U6RecFull ARecFull VRecFullEarly (· ≤ ·) 1 Fate.dropped :=
  .resolvedDrop (i := 1) (j := 2) (m := 3) (aₖ := 6) (aⱼ := 17) (a := 22)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => absurd ((eligibleFive_iff (by decide)).mp h.1) (by decide))

end RedSnapper

end LeanDagTest
