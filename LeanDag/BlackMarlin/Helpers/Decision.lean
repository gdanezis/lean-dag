import LeanDag.BlackMarlin.Helpers.Rules
/-!
# Black Marlin — the view layer

Generated proof layer; not part of the audit surface. A view holds a
subset of the universe, so each count it takes is at most the universe's
and every verdict it reaches is a verdict of the universe. That direction
is the whole of what the safety results consume from the view layer.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {V : View Validator BlockId Payload U}

omit Rot in
/-- A view's support quorum is a genuine one. -/
theorem supported_of_supportedIn {L : BlockId} {r : ℕ} (h : SupportedIn U V L r) :
    Supported U L r :=
  le_trans h (Finset.card_le_card heldAuthors_subset)

/-- A view's linking anchors link. -/
theorem linkersIn_subset {L : BlockId} {r : ℕ} :
    linkersIn U V L r ⊆ linkers U L r := by
  intro L' hL'
  obtain ⟨hf, -⟩ := Finset.mem_inter.mp hL'
  simp only [Finset.mem_filter, mem_blocksAt] at hf
  exact mem_linkers.mpr
    ⟨⟨hf.1.1, hf.1.2, hf.2.1⟩, hf.2.2.1, supported_of_supportedIn hf.2.2.2⟩

/-- A view's link is a genuine one. -/
theorem linked_of_linkedIn {L : BlockId} {r : ℕ} (h : LinkedIn U V L r) : Linked U L r :=
  Finset.Nonempty.mono linkersIn_subset h

/-- **The view reading is sound.** What a validator commits by reading its
own DAG, the rule commits over the universe. -/
theorem committed_of_committedIn {L : BlockId} {r : ℕ} (h : CommittedIn U V L r) :
    Committed U L r :=
  ⟨h.1, supported_of_supportedIn h.2.1, linked_of_linkedIn h.2.2⟩

/-- A validator that commits an anchor holds it. Not a clause of
`CommittedIn` but a consequence of one: the linking anchor is in the view,
the view is closed under references, and the link is a reference. -/
theorem mem_ids_of_committedIn {L : BlockId} {r : ℕ} (h : CommittedIn U V L r) :
    L ∈ V.ids := by
  obtain ⟨L', hL'⟩ := h.2.2
  obtain ⟨hf, hv⟩ := Finset.mem_inter.mp hL'
  rw [Finset.mem_filter] at hf
  exact V.complete L' hv L hf.2.2.1

end BlackMarlin

end LeanDag
