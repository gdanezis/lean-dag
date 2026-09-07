import LeanDag.Hydrozoan.Model.Decided
/-!
# Direct-rule instances and bridges

Generated: decidability for the top-level rule predicates (so witness
models settle them by `decide`), the "views only under-report" bridge
lemmas, and what the anchored relation's laws ask of the direct rules:
they grow with the view, and the skip reads the schedule only at its
slot. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  {U : BlockUniverse Replica BlockId}

instance decidableFastCommit (L : BlockId) (r : ℕ) :
    Decidable (FastCommit U L r) :=
  inferInstanceAs (Decidable (qFast Replica ≤ (supporters U L (r + 1)).card))

instance decidableSlowCommit (L : BlockId) (r : ℕ) :
    Decidable (SlowCommit U L r) :=
  inferInstanceAs (Decidable (qSlow Replica ≤ (certifiers U L r).card))

section Skip

variable [S : Slots Replica]

instance decidableSkippedLeader (k : ℕ) : Decidable (SkippedLeader U k) :=
  inferInstanceAs (Decidable (qFast Replica ≤ (slotBlames U k).card))

end Skip

/-- A view can only under-report fast commits. -/
theorem fastCommit_of_fastCommitInView {V : View U} {L : BlockId} {r : ℕ}
    (h : FastCommitInView U V L r) : FastCommit U L r :=
  le_trans h
    (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-- A view can only under-report slow commits. -/
theorem slowCommit_of_slowCommitInView {V : View U} {L : BlockId} {r : ℕ}
    (h : SlowCommitInView U V L r) : SlowCommit U L r :=
  le_trans h
    (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-- A view can only under-report skips. -/
theorem skippedLeader_of_skippedLeaderInView [S : Slots Replica] {V : View U}
    {k : ℕ} (h : SkippedLeaderInView U V k) : SkippedLeader U k :=
  le_trans h
    (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-! ## The rule's data -/

section Rule

variable [LinearOrder BlockId]

@[simp] theorem hydrozoanAnchored_wave : (hydrozoanAnchored Replica BlockId).wave = 2 := rfl

@[simp] theorem hydrozoanAnchored_rungs : (hydrozoanAnchored Replica BlockId).rungs = 2 := rfl

instance (V : View U) (L : BlockId) (r : ℕ) :
    Decidable ((hydrozoanAnchored Replica BlockId).Commit U V L r) :=
  inferInstanceAs (Decidable (FastCommitInView U V L r ∨ SlowCommitInView U V L r))

instance (V : View U) (S : Slots Replica) (k : ℕ) :
    Decidable ((hydrozoanAnchored Replica BlockId).Skip U V S k) :=
  inferInstanceAs (Decidable (SkippedLeaderInView (S := S) U V k))

end Rule

/-! ## The skip reads the schedule at its slot -/

/-- And so is the direct skip. -/
theorem skippedLeaderInView_congr {S₁ S₂ : Slots Replica} {V : View U} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : SkippedLeaderInView (S := S₁) U V k) : SkippedLeaderInView (S := S₂) U V k := by
  show HoldsAtLeast U V _ (slotBlamers (S := S₂) U k)
  rwa [← slotBlamers_congr hround hk]

end Hydrozoan

end LeanDag
