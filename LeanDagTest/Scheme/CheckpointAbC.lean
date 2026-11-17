import LeanDagTest.Scheme.Checkpoint

/-!
# Liveness delivers the checkpoint with an alive-but-corrupt leader

`full4`'s blocks at the Hybrid Mahi-Mahi row, wave four, on four
validators: nobody Byzantine, validator `0` crash-prone, validator `1`
alive-but-corrupt, so `3f + 2c + f_a = 3 < 4`. The row's own committee is
`3f + 2c + 1 = 3`, which admits no AbC validator
(`FaultClasses.resilient_threeRound_iff`); the fourth validator is the
slack the AbC class takes.

Validator `1` leads slot `1`. It produces and certifies with the others,
is counted in the signing quorum and in the reliability quorum, and also
proposes a fork. No commit is supplied: slot `1` reaches second-tier
finality from the hypotheses of `liveCommitFinalized_classes` alone, and
the fork has no certificate. The views differ as in `full4_live`.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme LeanDag.Checkpoint LeanDag.Integration LeanDag.Properties

local instance slackSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-- `full4`'s blocks, with every validator honest for the DAG: the
crash-prone and the alive-but-corrupt validator do not equivocate. -/
def full4h : BlockRecord (Fin 4) (Fin 24) Unit ValidWrt (Finset.univ : Finset (Fin 4)) where
  ids := Finset.univ
  block := mmFullBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The least vote on `full4h`. -/
abbrev σS : VoteSel (Fin 4) (Fin 24) Unit ValidWrt (Finset.univ : Finset (Fin 4)) := leastSel

/-- Hybrid Mahi-Mahi at wave four, `f = 0`, `c = 1`, on four validators. -/
abbrev hmm4 : Params := Params.hybridMahiMahi 4 4 0 1

example : hmm4.commitThreshold = 2 ∧ hmm4.skipThreshold = 2 ∧ hmm4.certThreshold = 3 := by
  decide

/-- The fault classes: validator `0` crash-prone, validator `1`
alive-but-corrupt, nobody Byzantine. -/
def slackClasses : FaultClasses (Fin 4) where
  f := 0
  c := 1
  fa := 1
  byzantine := ∅
  crash := {0}
  abc := {1}
  card_byzantine := by decide
  card_crash := by decide
  card_abc := by decide
  resilient := by decide

/-- The signing faults the classes give, at quorum `3`. -/
def slackSigning : SigningFaults (Fin 4) := slackClasses.signing

example : slackSigning.q = 3 := by decide
example : slackSigning.alive = {1, 2, 3} := by decide
example : slackSigning.reliableSigner = {0, 2, 3} := by decide
example : slackSigning.recoveryCorrect = {2, 3} := by decide

/-- The AbC validator follows the rule, is not a reliable signer, and
leads slot `1`. -/
example : (1 : Fin 4) ∈ slackSigning.alive ∧ (1 : Fin 4) ∉ slackSigning.reliableSigner ∧
    Slots.leader 1 = (1 : Fin 4) := by
  decide

/-- Every validator is honest for the DAG. -/
theorem slack_honest : (Finset.univ : Finset (Fin 4))ᶜ ⊆ slackClasses.byzantine := by decide

/-- The row is covered at the classes' `f = 0` and the core quorum. -/
theorem hmm4_covered :
    hmm4.Covered (Fintype.card (Fin 4)) slackClasses.f (quorumCard (Fin 4)) :=
  Or.inr (Or.inl ⟨rfl, by decide, rfl, by decide, by decide, by decide⟩)

/-- The row tolerates the classes. -/
theorem hmm4Tolerates :
    hmm4.Tolerates (Finset.univ : Finset (Fin 4)) slackClasses.f (quorumCard (Fin 4)) :=
  tolerates_of_classes slackClasses slack_honest (by decide) hmm4_covered

/-- Slots `0`, `1`, `2` commit blocks `0`, `5`, `10` directly. -/
theorem full4h_slot0 :
    (schemeAnchored hmm4 σS).Decided full4h (BlockRecord.View.full full4h) 0 (some 0) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem full4h_slot1 :
    (schemeAnchored hmm4 σS).Decided full4h (BlockRecord.View.full full4h) 1 (some 5) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem full4h_slot2 :
    (schemeAnchored hmm4 σS).Decided full4h (BlockRecord.View.full full4h) 2 (some 10) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- In `full4h` at this row, the only block-valued decisions are slots
`0`, `1`, `2` committing blocks `0`, `5`, `10`, as in `full4_decided_eq`. -/
theorem full4h_decided_eq {V : full4h.View} {s : ℕ} {b : Fin 24}
    (h : (schemeRule hmm4 σS).Decided inferInstance V s (some b)) :
    (s = 0 ∧ b = 0) ∨ (s = 1 ∧ b = 5) ∨ (s = 2 ∧ b = 10) := by
  have hL := AnchoredRule.isLeaderBlock_of_decided h
  have hround : ∀ c : Fin 24, (full4h.block c).round ≤ 5 := by decide
  have hs : s ≤ 5 := by
    have hb := hround b
    have := hL.2.1
    simp at this
    omega
  have hdead : ∀ s', 3 ≤ s' → s' ≤ 5 → ∀ {V' : full4h.View}
      {b' : Fin 24}, ¬ (schemeRule hmm4 σS).Decided inferInstance V' s' (some b') := by
    intro s' h3 h5 V' b' h'
    have hw : hmm4.waveLength = 4 := rfl
    cases h' with
    | directCommit hL' hc =>
      have hle := hc.le
      have hempty : ∀ c : Fin 24, ∀ r, 3 ≤ r →
          (creatorsOf full4h.block (certsAt hmm4 σS full4h c r)).card = 0 := by
        intro c r hr
        have : certsAt hmm4 σS full4h c r = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
          obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
          obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hx
          rw [hw] at hxr
          have := hround x
          omega
        simp [this, creatorsOf]
      have hsr : Slots.slotRound (Fin 4) s' = s' := by simp
      have hct : hmm4.commitThreshold = 2 := rfl
      have h0 := hempty b' (Slots.slotRound (Fin 4) s') (by omega)
      omega
    | @indirectCommit _ j A _ _ hlt helig hj _ _ _ _ _ _ =>
      have hA := (AnchoredRule.isLeaderBlock_of_decided hj).2.1
      have hAr := hround A
      have hwv : (schemeAnchored hmm4 σS).waveAt (Slots.kind (Fin 4) s') = 3 := rfl
      have hel := ((schemeAnchored hmm4 σS).eligible_iff).mp helig
      rw [hwv] at hel
      simp at hA hel
      omega
  interval_cases s
  · exact Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree hmm4Tolerates _ V (BlockRecord.View.full full4h) 0 _ _ h full4h_slot0)⟩
  · exact Or.inr (Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree hmm4Tolerates _ V (BlockRecord.View.full full4h) 1 _ _ h full4h_slot1)⟩)
  · exact Or.inr (Or.inr ⟨rfl, Option.some.inj
      (Scheme.agree hmm4Tolerates _ V (BlockRecord.View.full full4h) 2 _ _ h full4h_slot2)⟩)
  · exact absurd h (hdead 3 (by omega) (by omega))
  · exact absurd h (hdead 4 (by omega) (by omega))
  · exact absurd h (hdead 5 (by omega) (by omega))

/-- The record up to round `4`, the last round of slot `1`'s wave. -/
def full4hUpto4 : full4h.View where
  ids := Finset.univ.filter fun b => (full4h.block b).round ≤ 4
  subset_ids := Finset.subset_univ _
  complete := by decide

/-- Validator `2` holds the record up to round `4`; everyone else holds
the full one. -/
def slackView (v : Fin 4) : full4h.View :=
  if v = 2 then full4hUpto4 else BlockRecord.View.full full4h

example : (slackView 2).ids ≠ (slackView 1).ids := by decide

/-- The fork the AbC validator proposes at slot `1`'s height. -/
def slackFork : CheckpointData ℕ := ⟨2, 0, [0, 99]⟩

example : slackFork ≠ liveVM.checkpointAfterCommit 1 5 := by decide

/-- Rule-following validators propose what their own view settles; the
AbC validator `1` also proposes the fork. -/
def slackExecution : slackSigning.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ height => [(0 : ℕ), 5, 10].take height
  emitted := fun message =>
    (message.sender ∈ slackSigning.alive ∧
      ∃ slot block,
        (schemeRule hmm4 σS).Decided inferInstance (slackView message.sender) slot
          (some block) ∧
        message.checkpoint = liveVM.checkpointAfterCommit slot block) ∨
    (message.sender = 1 ∧ message.checkpoint = slackFork)
  recorded := fun validator checkpoint =>
    validator ∈ slackSigning.recoveryCorrect ∧
      (checkpoint = liveVM.checkpointAfterCommit 0 0 ∨
        checkpoint = liveVM.checkpointAfterCommit 1 5 ∨
        checkpoint = liveVM.checkpointAfterCommit 2 10)
  genesis_prefix := by
    intro message _ _
    simp
  local_extension := by
    intro validator epoch h₁ h₂ _ le
    have h := List.take_prefix h₁ ([(0 : ℕ), 5, 10].take h₂)
    rwa [List.take_take, Nat.min_eq_left le] at h
  emitted_from_state := by
    intro message hm reliable
    rcases hm with ⟨-, slot, block, hdec, hc⟩ | ⟨h1, -⟩
    · rcases full4h_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [hc, liveVM]
    · rw [h1] at reliable
      exact absurd reliable (by decide)
  local_height := by
    intro message hm reliable
    rcases hm with ⟨-, slot, block, hdec, hc⟩ | ⟨h1, -⟩
    · rcases full4h_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [hc, liveVM]
    · rw [h1] at reliable
      exact absurd reliable (by decide)

/-- The AbC validator equivocates: it proposes slot `1`'s checkpoint and
the fork. -/
example : slackExecution.emitted ⟨1, liveVM.checkpointAfterCommit 1 5⟩ :=
  Or.inl ⟨by decide, 1, 5, full4h_slot1, rfl⟩
example : slackExecution.emitted ⟨1, slackFork⟩ := Or.inr ⟨rfl, rfl⟩

/-- A recovery-correct validator's proposal is a committed checkpoint. -/
theorem slackExecution_emitted {message : ChkProp (Fin 4) ℕ}
    (h : slackExecution.emitted message)
    (hv : message.sender ∈ slackSigning.recoveryCorrect) :
    message.checkpoint = liveVM.checkpointAfterCommit 0 0 ∨
      message.checkpoint = liveVM.checkpointAfterCommit 1 5 ∨
      message.checkpoint = liveVM.checkpointAfterCommit 2 10 := by
  rcases h with ⟨-, slot, block, hdec, hc⟩ | ⟨h1, -⟩
  · rcases full4h_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)
  · rw [h1] at hv
    exact absurd hv (by decide)

/-- The signing rule: each rule-following validator, the AbC one
included, proposes what its own view settles. -/
def slackRule :
    SigningFaults.Execution.SigningRule slackSigning slackExecution
      (schemeRule hmm4 σS) inferInstance full4h liveVM where
  quorum := slackClasses.quorum_alive
  view := slackView
  proposes := fun _ hv _ _ hdec => Or.inl ⟨hv, _, _, hdec, rfl⟩
  witnesses := fun v _ _ he Q =>
    ⟨{ sender := v
       certificate := Q
       recorded := fun hv' => ⟨hv', slackExecution_emitted he hv'⟩ },
     rfl⟩

/-- Certification at the family's support is the decider's `IsCert`,
which is decidable. -/
local instance : ∀ (U : (schemeRule hmm4 σS).Universe) (c L : Fin 24),
    Decidable ((familySupport hmm4 σS).Certifies U c L) := fun U c L =>
  inferInstanceAs (Decidable (IsCert hmm4 σS U c L))

/-- Every candidate of slot `1` is certified by every rule-following
validator's decision-round block, the AbC validator's included. -/
theorem slack_certified : ∀ L : Fin 24,
    (schemeRule hmm4 σS).IsCandidate inferInstance full4h 1 L →
    (familySupport hmm4 σS).certifiesAt full4h slackSigning.alive
      (Slots.slotRound (Fin 4) 1) (Slots.kind (Fin 4) 1) L := by
  decide

/-- Each validator's own view covers slot `1`'s wave, rounds `1` to `4`. -/
theorem slackView_covers (v : Fin 4) :
    Properties.CoversUpto (schemeRule hmm4 σS) (slackView v) 4 := by
  unfold slackView
  split
  · exact fun b _ hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  · exact fun b hb _ => by
      change b ∈ (BlockRecord.View.full full4h).ids
      rw [BlockRecord.View.full_ids]
      exact hb

/-- **Liveness delivers the checkpoint with an AbC validator leading**:
production, certification, coverage and a rule-following leader, no
commit supplied. The AbC validator is in the signing quorum and in the
reliability quorum `slackClasses.isQuorum_alive`. -/
theorem slack_live :
    ∃ L, (schemeRule hmm4 σS).IsCandidate inferInstance full4h 1 L ∧
      Nonempty (SigningFaults.Execution.FinalityQC slackSigning slackExecution
        (liveVM.checkpointAfterCommit 1 L)) :=
  liveCommitFinalized_classes slackClasses slackExecution liveVM slack_honest
    hmm4Tolerates.2.1 hmm4_covered (by decide) _ slackRule
    (fun n h1 h2 => by revert h1 h2; revert n; decide)
    slack_certified (fun v _ => slackView_covers v) (by decide)

/-- The hypotheses are not vacuous: slot `1` has a candidate, and every
rule-following validator has a block at the decision round, round `4`,
for `slack_certified` to speak of. -/
example : (schemeRule hmm4 σS).IsCandidate inferInstance full4h 1 5 := by decide
example : ∀ v ∈ slackSigning.alive,
    ∃ c, (full4h.block c).creator = v ∧ (full4h.block c).round = 4 := by decide

/-- The block liveness finds is slot `1`'s candidate, so the finalized
checkpoint is the committed one. -/
theorem slack_live_committed :
    Nonempty (SigningFaults.Execution.FinalityQC slackSigning slackExecution
      (liveVM.checkpointAfterCommit 1 5)) := by
  obtain ⟨L, hL, hF⟩ := slack_live
  have hall : ∀ L : Fin 24,
      (schemeRule hmm4 σS).IsCandidate inferInstance full4h 1 L → L = 5 := by decide
  obtain rfl := hall L hL
  exact hF

/-- **The AbC validator's fork has no certificate**: it alone proposes
it, two signers short of the quorum. -/
theorem slack_fork_uncertified :
    IsEmpty (SigningFaults.Execution.CheckpointQC slackSigning slackExecution slackFork) := by
  refine ⟨fun Q => ?_⟩
  have hsub : Q.signers ⊆ {1} := by
    intro v hv
    rcases Q.messages v hv with ⟨-, slot, block, hdec, hc⟩ | ⟨h1, -⟩
    · have hc' : slackFork = liveVM.checkpointAfterCommit slot block := hc
      rcases full4h_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd hc' (by decide)
    · have h1' : v = 1 := h1
      exact Finset.mem_singleton.mpr h1'
  have hcard := Finset.card_le_card hsub
  have hq := Q.quorum
  have h3 : slackSigning.q = 3 := by decide
  simp at hcard
  omega

/-! ## The commit path at the classes -/

/-- Slot `1` commits on the record up to round `4` too. -/
theorem full4h_slot1_upto4 :
    (schemeAnchored hmm4 σS).Decided full4h full4hUpto4 1 (some 5) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- Every rule-following validator, the AbC one included, settled slot
`1` on its own view. -/
theorem slack_all_decided :
    ∀ v ∈ slackSigning.alive,
      ∃ b, (schemeRule hmm4 σS).Decided inferInstance (slackView v) 1 (some b) := by
  intro v _
  by_cases hv : v = 2
  · exact ⟨5, by rw [slackView, if_pos hv]; exact full4h_slot1_upto4⟩
  · exact ⟨5, by rw [slackView, if_neg hv]; exact full4h_slot1⟩

/-- **A given commit finalizes with an AbC validator in the quorum**,
through `commitFinalized_classes`. -/
theorem slack_commit_finalized :
    Nonempty (SigningFaults.Execution.FinalityQC slackSigning slackExecution
      (liveVM.checkpointAfterCommit 1 5)) :=
  commitFinalized_classes slackClasses slackExecution liveVM slack_honest
    hmm4Tolerates.2.1 hmm4_covered _ slackRule full4h_slot1 slack_all_decided

/-! ## The classes at other committees

`FaultClasses` assumes the resilience bound and nothing else of the
committee, so it is inhabited at the committees `HybridFaults` excludes,
and with a Byzantine and an AbC validator together at a two-round
committee. These are parameter witnesses; no record is built. -/

/-- Hybrid Mysticeti's committee `3f + 2c + 1` at `f = c = 1`: six
validators, no room for an AbC validator. -/
def hybridMystClasses : FaultClasses (Fin 6) where
  f := 1
  c := 1
  fa := 0
  byzantine := {0}
  crash := {1}
  abc := ∅
  card_byzantine := by decide
  card_crash := by decide
  card_abc := by decide
  resilient := by decide

example : hybridMystClasses.signing.q = 4 ∧ hybridMystClasses.signing.alive.card = 4 := by
  decide

/-- Nemo-Nemo's committee `2c + 1` at `c = 1`. -/
def nemoClasses : FaultClasses (Fin 3) where
  f := 0
  c := 1
  fa := 0
  byzantine := ∅
  crash := {0}
  abc := ∅
  card_byzantine := by decide
  card_crash := by decide
  card_abc := by decide
  resilient := by decide

example : nemoClasses.signing.q = 2 ∧ nemoClasses.signing.alive.card = 2 := by decide

/-- Blue Bottle's committee `5f + 1` at `f = 1`, with `f_a = 2f + c = 2`
AbC validators beside the Byzantine one, by `resilient_of_twoRound`. -/
def blueBottleClasses : FaultClasses (Fin 6) where
  f := 1
  c := 0
  fa := 2
  byzantine := {0}
  crash := ∅
  abc := {1, 2}
  card_byzantine := by decide
  card_crash := by decide
  card_abc := by decide
  resilient := FaultClasses.resilient_of_twoRound (by decide) (by decide)

example : blueBottleClasses.signing.q = 5 ∧ blueBottleClasses.signing.alive.card = 5 ∧
    blueBottleClasses.signing.reliableSigner.card = 3 := by
  decide

/-- The parameter hypotheses of `liveCommitFinalized_classes` hold
together with `f > 0` and `f_a > 0`: the Blue Bottle row is covered at
the classes' `f` and its commit threshold is within `n − f − c`. -/
example : (Params.blueBottlePS 6 1).Covered (Fintype.card (Fin 6)) blueBottleClasses.f 5 ∧
    (Params.blueBottlePS 6 1).commitThreshold ≤
      Fintype.card (Fin 6) - blueBottleClasses.f - blueBottleClasses.c :=
  ⟨Or.inl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, by decide⟩

#print axioms slack_live_committed
#print axioms slack_commit_finalized
#print axioms slack_fork_uncertified

end Scheme

end LeanDagTest
