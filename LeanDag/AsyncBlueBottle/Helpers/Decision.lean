import LeanDag.AsyncBlueBottle.Model.Decision
import LeanDag.AsyncBlueBottle.Helpers.Rules
/-!
# Helpers — the decision layer

Generated lemma infrastructure for `Model/Decision.lean`; not part of the
audit surface. View lifting, the safety lemmas in their slot-indexed
forms, the anchored rule's laws (`asyncBlueBottleLaws`), and the
tie-break's choice at a nonempty rung.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {L A : BlockId} {r : ℕ}

/-! ## A view can only under-report -/

theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) : DirectCommit U L r := h.le

theorem directSkip_of_directSkipIn {V : View Validator BlockId Payload U} {a : Validator}
    (h : DirectSkipIn U V a r) : DirectSkip U a r := h.le

/-- A view caught up to the decision round holds every vote, so it
commits what the DAG commits. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U}
    (h : DirectCommit U L r) (hV : V.CoversUpto (decisionRoundAt r)) : DirectCommitIn U V L r :=
  HoldsAtLeast.of_coversUpto (fun q hq => by
    obtain ⟨hqU, hqr⟩ := voters_spec hq
    exact ⟨hqU, by unfold decisionRoundAt; omega⟩) hV h

/-- The full view commits what the DAG commits. -/
theorem directCommitIn_full (h : DirectCommit U L r) : DirectCommitIn U (View.full U) L r :=
  (HoldsAtLeast.full fun _ hq => (voters_spec hq).1).mpr h

section Slots

variable [S : Slots Validator]

omit S in
@[simp] theorem asyncBlueBottleAnchored_waveAt (κ : ℕ) :
    (asyncBlueBottleAnchored Validator BlockId Payload).waveAt κ = 2 := rfl
omit S in
@[simp] theorem asyncBlueBottleAnchored_rungs :
    (asyncBlueBottleAnchored Validator BlockId Payload).rungs = 1 := rfl

/-- The relation's decision round is the wave's. -/
theorem asyncBlueBottleAnchored_decisionRound (k : ℕ) :
    (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k
      = decisionRoundAt (S.slotRound k) := rfl

/-! ## The safety lemmas, lifted to views and slots -/

/-- Cross-view ABB1: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    (hL : IsLeaderBlock U k L) (h₁ : DirectCommitIn U V₁ L (S.slotRound k))
    (h₂ : DirectSkipIn U V₂ (S.leader k) (S.slotRound k)) : False :=
  not_directSkip_of_directCommit hL.2.1 (directCommit_of_directCommitIn h₁)
    (by rw [hL.2.2]; exact directSkip_of_directSkipIn h₂)

/-- Cross-view ABB1′: two direct commits for one slot agree. -/
theorem eq_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ (S.slotRound k)) (h₂ : DirectCommitIn U V₂ L₂ (S.slotRound k)) :
    L₁ = L₂ :=
  eq_of_directCommit (directCommit_of_directCommitIn h₁) (directCommit_of_directCommitIn h₂)
    (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])

omit S in
/-- ABB3, from a view: a view-level direct commit passes the weak test at
every block three rounds up. -/
theorem weakLink_of_directCommitIn {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) (hA : A ∈ U.ids) (hround : r + 3 ≤ (U.block A).round) :
    WeakLink U A L r :=
  weakLink_of_directCommit (directCommit_of_directCommitIn h) hA hround

/-- A direct commit passes the weak test from any candidate anchor of any
eligible slot. -/
theorem weakLink_of_directCommitIn_at_anchor {V : View Validator BlockId Payload U} {k j : ℕ}
    (h : DirectCommitIn U V L (S.slotRound k)) (hA : IsLeaderBlock U j A)
    (helig : (asyncBlueBottleAnchored Validator BlockId Payload).Eligible k j) :
    WeakLink U A L (S.slotRound k) :=
  weakLink_of_directCommitIn h hA.1 (by
    have := (asyncBlueBottleAnchored Validator BlockId Payload).anchor_round_le hA helig
    simp only [asyncBlueBottleAnchored_waveAt] at this
    omega)

/-- ABB2, from a view: a view-level direct skip fails the weak test
everywhere. -/
theorem not_weakLink_of_directSkipIn {V : View Validator BlockId Payload U} {k : ℕ}
    (h : DirectSkipIn U V (S.leader k) (S.slotRound k)) (hL : IsLeaderBlock U k L) (A : BlockId) :
    ¬ WeakLink U A L (S.slotRound k) :=
  not_weakLink_of_directSkip (directSkip_of_directSkipIn h) hL.2.2 hL.2.1 A

/-- ABB4′, from a view: a view-level direct commit is the only same-slot
candidate that can pass the weak test, at any anchor. -/
theorem eq_of_directCommitIn_of_weakLink {V : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V L₁ (S.slotRound k)) (ht : WeakLink U A L₂ (S.slotRound k)) :
    L₁ = L₂ :=
  eq_of_directCommit_of_weakLink (directCommit_of_directCommitIn h₁) ht
    (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])

/-! ## The laws -/

omit S in
/-- **Async BlueBottle's laws**: the direct/direct cases by ABB1 and
ABB1′, the direct-versus-indirect crossings by ABB2, ABB3 and ABB4′, and
two tie-break choices equal by antisymmetry. -/
theorem asyncBlueBottleLaws : (asyncBlueBottleAnchored Validator BlockId Payload).Laws where
  commit_unique := fun _ hL₁ hL₂ h₁ h₂ => eq_of_directCommitIn hL₁ hL₂ h₁ h₂
  commit_skip := fun _ hL h hskip => not_directSkipIn_of_directCommitIn hL h hskip
  commit_link := fun _ _ h hA _ helig =>
    ⟨0, Nat.one_pos, weakLink_of_directCommitIn_at_anchor h hA helig⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ _ hlink _
    exact eq_of_directCommitIn_of_weakLink hL₁ hL₂ h hlink
  skip_link := fun _ hskip hL _ _ => not_weakLink_of_directSkipIn hskip hL _
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ _ hl₁ hl₂ hm₁ hm₂
    exact le_antisymm (not_lt.mp (show ¬ L₂ < L₁ from hm₁ L₂ hL₂ hl₂))
      (not_lt.mp (show ¬ L₁ < L₂ from hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk _ h => by
    change DirectSkipIn _ _ _ _
    rw [← hround, ← hk]; exact h
  link_congr := (asyncBlueBottleAnchored Validator BlockId Payload).linkCongr_of_round
    (fun _ U A L r => WeakLink U A L r) fun _ _ _ _ _ _ => rfl

omit S in
/-- The rung's tie is the order, so a nonempty rung has a least
candidate. -/
theorem exists_least {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {A : BlockId} {i k : ℕ} (_ : i < (asyncBlueBottleAnchored Validator BlockId Payload).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧
      (asyncBlueBottleAnchored Validator BlockId Payload).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧
      (asyncBlueBottleAnchored Validator BlockId Payload).Link i U A L S k ∧
      (asyncBlueBottleAnchored Validator BlockId Payload).Least (S := S) U A i k L :=
  AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h

end Slots

end AsyncBlueBottle

end LeanDag
