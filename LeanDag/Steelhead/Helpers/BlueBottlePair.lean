import LeanDag.Steelhead.BlueBottlePair.Statement
import LeanDag.Steelhead.Helpers.Compose
import LeanDag.AsyncBlueBottle.Helpers.Decision
/-!
# Helpers — the `5f + 1` pair

Generated lemma infrastructure for `BlueBottlePair/Statement.lean`; not
part of the audit surface. Every claim splits on the kind and hands the
slot to the rule that owns it: Odontoceti at kind `0` and Async
BlueBottle elsewhere, each from its own arc. The rung count and the
tie-break match by `rfl` on both branches, which is what lets the
composite's laws come from `compose_laws`.

The handover is the one place the pair costs more than the `3f + 1` one.
There the rung's link is a certificate, unique per slot, so the tie is
empty and `indirectCommit_single` applies. Here both halves let several
candidates of one slot pass the indirect test, so the commit has to be
identified with the tie-break's choice, which each arc supplies as the
strong form of its fourth law: a direct commit is the only same-slot
candidate that passes.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## SH-BB16a and SH-BB16d, the family -/

/-- **SH-BB16a.** Odontoceti's laws at kind `0` and Async BlueBottle's elsewhere. -/
theorem halvesLawful : HalvesLawful Validator BlockId Payload := by
  intro κ
  unfold blueBottlePair
  split
  · exact Odontoceti.odontocetiLaws
  · exact AsyncBlueBottle.asyncBlueBottleLaws

/-- Both halves run a single rung. -/
theorem pair_rungs (κ : ℕ) :
    (blueBottlePair Validator BlockId Payload κ).rungs =
      (blueBottlePair Validator BlockId Payload 0).rungs := by
  unfold blueBottlePair; split <;> rfl

/-- Both halves break ties by the least candidate. -/
theorem pair_tie (κ : ℕ) :
    (blueBottlePair Validator BlockId Payload κ).tie =
      (blueBottlePair Validator BlockId Payload 0).tie := by
  unfold blueBottlePair; split <;> rfl

/-- Both halves know the same of a committed anchor: nothing. -/
theorem pair_anchor (κ : ℕ) :
    (blueBottlePair Validator BlockId Payload κ).Anchor =
      (blueBottlePair Validator BlockId Payload 0).Anchor := by
  unfold blueBottlePair; split <;> rfl

/-- **SH-BB16d.** -/
theorem pairAgreesOnRungsAndTie : PairAgreesOnRungsAndTie Validator BlockId Payload :=
  ⟨pair_rungs, pair_tie⟩

/-- **Steelhead at the `5f + 1` pair is the family's composite**, by definition. -/
theorem steelheadAt_bbPair :
    steelheadAt (bbPair Validator BlockId Payload) =
      blueBottlePairAnchored Validator BlockId Payload :=
  rfl

/-- The composite runs a single rung, both halves doing so. -/
@[simp] theorem pairAnchored_rungs :
    (blueBottlePairAnchored Validator BlockId Payload).rungs = 1 := rfl

/-! ## SH-BB16b, the composite's laws and agreement -/

/-- **The `5f + 1` pair's laws**, by SH16a at the family. -/
theorem blueBottlePairLaws : (blueBottlePairAnchored Validator BlockId Payload).Laws :=
  compose_laws _ halvesLawful pair_rungs pair_tie pair_anchor

/-- **SH-BB16b.** -/
theorem pairAgreement [S : Slots Validator] : PairAgreement (S := S) U :=
  ⟨blueBottlePairLaws, fun _ V₂ _ _ v₂ h₁ h₂ =>
    AnchoredRule.decided_unique blueBottlePairLaws trivial h₁ V₂ v₂ h₂⟩

/-! ## SH-BB3, handover -/

section Handover

variable [S : Slots Validator]

/-- **A direct commit is the slot's only linked candidate**, at either half: Odontoceti's O4′ at
kind `0` and Async BlueBottle's ABB4′ elsewhere, each in the strong form that asks nothing of the
tie-break. -/
theorem eq_of_commit_of_link {k : ℕ} {V : View Validator BlockId Payload U} {L₁ L₂ A : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (hc : (blueBottlePairAnchored Validator BlockId Payload).Commit U V L₁ (S.slotRound k)
      (S.kind k))
    (hlink : (blueBottlePairAnchored Validator BlockId Payload).Link 0 U A L₂ S k) :
    L₁ = L₂ := by
  simp only [blueBottlePairAnchored, compose, blueBottlePair] at hc hlink
  split at hc
  · rename_i hk
    rw [hk] at hlink
    exact Odontoceti.eq_of_directCommitIn_of_thickLink hL₁ hL₂ hc hlink
  · rename_i hk
    rw [if_neg hk] at hlink
    exact AsyncBlueBottle.eq_of_directCommitIn_of_weakLink hL₁ hL₂ hc hlink

/-- **A direct commit is the tie-break's choice**: every linked candidate of the slot is the
commit itself, and the order is irreflexive. -/
theorem least_of_commit {k : ℕ} {V : View Validator BlockId Payload U} {L A : BlockId}
    (hL : IsLeaderBlock U k L)
    (hc : (blueBottlePairAnchored Validator BlockId Payload).Commit U V L (S.slotRound k)
      (S.kind k)) :
    (blueBottlePairAnchored Validator BlockId Payload).Least U A 0 k L := by
  intro L' hL' hlink
  rw [eq_of_commit_of_link hL hL' hc hlink]
  simp only [blueBottlePairAnchored, compose, blueBottlePair]
  split <;> exact lt_irrefl L'

/-- **SH-BB3.** -/
theorem pairHandover : PairHandover (S := S) U := by
  intro V₁ V₂ k L hL hc
  refine ⟨fun j A hkj helig hj hmid => ?_, fun hskip => ?_⟩
  · obtain ⟨i, hi, hlink⟩ :=
      blueBottlePairLaws.commit_link trivial hL hc (AnchoredRule.isLeaderBlock_of_decided hj)
        trivial helig
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact AnchoredRule.Decided.indirectCommit (i := 0) hkj helig hj hmid (by simp)
      (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) hL hlink (least_of_commit hL hc)
  · have := AnchoredRule.decided_agree blueBottlePairLaws trivial
      (AnchoredRule.Decided.directCommit hL hc) hskip
    simp at this

end Handover

/-! ## SH-BB16e, the two waves -/

/-- The synchronous kind reads Odontoceti's offset. -/
theorem pairAnchored_waveAt_zero :
    (blueBottlePairAnchored Validator BlockId Payload).waveAt 0 = 1 := rfl

/-- Every other kind reads Async BlueBottle's. -/
theorem pairAnchored_waveAt_of_ne {κ : ℕ} (hκ : κ ≠ 0) :
    (blueBottlePairAnchored Validator BlockId Payload).waveAt κ = 2 := by
  simp only [blueBottlePairAnchored, compose, blueBottlePair, if_neg hκ]
  rfl

/-- **SH-BB16e.** The offsets are Odontoceti's one and Async BlueBottle's two, and the eligibility
floor is `waveAt + 1` above the slot's round. -/
theorem pairWavesDiffer : PairWavesDiffer Validator BlockId Payload := by
  refine ⟨pairAnchored_waveAt_zero, fun _ hκ => pairAnchored_waveAt_of_ne hκ, ?_, ?_⟩
  · intro S k j
    rw [AnchoredRule.eligible_iff]
    by_cases hk : S.kind k = 0
    · rw [if_pos hk, hk, pairAnchored_waveAt_zero]
    · rw [if_neg hk, pairAnchored_waveAt_of_ne hk]
  · rw [pairAnchored_waveAt_zero, pairAnchored_waveAt_of_ne (by omega : (1 : ℕ) ≠ 0)]
    omega

end BlueBottlePair

end Steelhead

end LeanDag
