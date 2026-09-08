import LeanDag.BlackMarlin.Model.Ledger
import LeanDag.BlackMarlin.Helpers.Rules
/-!
# Black Marlin — the flush layer

Generated proof layer; not part of the audit surface. The descent is
unambiguous where it steps by one round, so two records that agree at a
round agree at every round below it that they both reach; the link clause
of the commit rule is what keeps the round above a committed anchor from
being skipped; and the ledger results follow from record agreement.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {ρ σ : ℕ} {L M : BlockId}

/-- Membership in `coneAnchors`, unfolded. -/
theorem mem_coneAnchors {A X : BlockId} :
    X ∈ coneAnchors U A ρ ↔ IsAnchor U ρ X ∧ X ∈ history U A := by
  simp only [coneAnchors, Finset.mem_filter, mem_blocksAt, IsAnchor]
  tauto

/-- **The step is unambiguous.** At most one anchor of round `ρ` lies in
the cone of a round-`(ρ + 1)` block: the round-`ρ` members of that cone
are its references, and `distinct_creators` allows one block per author.
No tie-break is needed where the descent steps by one round. -/
theorem coneAnchors_subsingleton (hM : M ∈ U.ids) (hMr : (U.block M).round = ρ + 1) :
    ∀ X ∈ coneAnchors U M ρ, ∀ Y ∈ coneAnchors U M ρ, X = Y := by
  intro X hX Y hY
  obtain ⟨hXa, hXh⟩ := mem_coneAnchors.mp hX
  obtain ⟨hYa, hYh⟩ := mem_coneAnchors.mp hY
  have hXr : X ∈ (U.block M).refs :=
    mem_refs_of_mem_history_of_round_succ hM hXh (by rw [hXa.2.1, hMr])
  have hYr : Y ∈ (U.block M).refs :=
    mem_refs_of_mem_history_of_round_succ hM hYh (by rw [hYa.2.1, hMr])
  exact (U.valid M hM).distinct_creators X hXr Y hYr (by rw [hXa.2.2, hYa.2.2])

/-- **A Byzantine anchor is necessary for a tie.** Where the round's
elected validator is reliable it has one block at that round, so the
candidates are a singleton however deep the cone the descent is reading —
no skipped round can produce a choice there. -/
theorem coneAnchors_subsingleton_of_correct {C : BlockId}
    (hc : Rot.anchor ρ ∈ (Correct : Finset Validator)) :
    ∀ X ∈ coneAnchors U C ρ, ∀ Y ∈ coneAnchors U C ρ, X = Y := by
  intro X hX Y hY
  obtain ⟨hXa, -⟩ := mem_coneAnchors.mp hX
  obtain ⟨hYa, -⟩ := mem_coneAnchors.mp hY
  exact U.eq_of_creator_eq hXa.1 hYa.1 hc hXa.2.2 hYa.2.2 (by rw [hXa.2.1, hYa.2.1])

/-- A flushed anchor is a candidate of its own round below the anchor
above it. -/
theorem mem_coneAnchors_of_step (f : Flush U)
    (hL : f.block ρ = some L) (hM : f.block (ρ + 1) = some M) :
    L ∈ coneAnchors U M ρ :=
  mem_coneAnchors.mpr ⟨f.isAnchor ρ L hL,
    mem_history_of_mem_refs (f.isAnchor (ρ + 1) M hM).1 (f.step ρ L M hL hM)⟩

/-- **Two records that agree at a round agree at the round below it.**
Where both flush, the step makes their blocks candidates of one cone and
the subsingleton makes them equal; where one does not flush, the cone is
empty and neither does. -/
theorem block_eq_of_succ {f₁ f₂ : Flush U}
    (hM₁ : f₁.block (ρ + 1) = some M) (hM₂ : f₂.block (ρ + 1) = some M) :
    f₁.block ρ = f₂.block ρ := by
  have haM : IsAnchor U (ρ + 1) M := f₁.isAnchor (ρ + 1) M hM₁
  have hsub := coneAnchors_subsingleton (ρ := ρ) haM.1 haM.2.1
  cases hL₁ : f₁.block ρ with
  | none =>
      cases hL₂ : f₂.block ρ with
      | none => rfl
      | some L₂ =>
          exact absurd (f₁.dense ρ M hM₁ ⟨L₂, mem_coneAnchors_of_step f₂ hL₂ hM₂⟩)
            (by rw [hL₁]; exact Bool.false_ne_true)
  | some L₁ =>
      have hne := f₂.dense ρ M hM₂ ⟨L₁, mem_coneAnchors_of_step f₁ hL₁ hM₁⟩
      obtain ⟨L₂, hL₂⟩ := Option.isSome_iff_exists.mp hne
      rw [hL₂]
      exact congrArg some (hsub L₁ (mem_coneAnchors_of_step f₁ hL₁ hM₁)
        L₂ (mem_coneAnchors_of_step f₂ hL₂ hM₂))

/-- **And so throughout a stretch they both descend.** Agreement at
`ρ + d` propagates down to `ρ`, provided the record flushes at every
round strictly between. -/
theorem block_eq_of_add {f₁ f₂ : Flush U} :
    ∀ (d ρ : ℕ), f₁.block (ρ + d) = f₂.block (ρ + d) →
      (∀ i, 0 < i → i ≤ d → (f₁.block (ρ + i)).isSome) →
      f₁.block ρ = f₂.block ρ := by
  intro d
  induction d with
  | zero => intro ρ h _; simpa using h
  | succ d ih =>
      intro ρ h hdef
      refine ih ρ ?_ (fun i h1 h2 => hdef i h1 (by omega))
      have hd : (f₁.block (ρ + d + 1)).isSome := by
        have := hdef (d + 1) (by omega) (by omega)
        rwa [show ρ + (d + 1) = ρ + d + 1 by omega] at this
      obtain ⟨M, hM⟩ := Option.isSome_iff_exists.mp hd
      have h' : f₁.block (ρ + d + 1) = f₂.block (ρ + d + 1) := by
        rwa [show ρ + (d + 1) = ρ + d + 1 by omega] at h
      exact block_eq_of_succ hM (h' ▸ hM)

/-- **The starting point.** Two records that flush directly committed
anchors at one round flush the same block, by anchor uniqueness. This is
what a round every reliable validator commits at supplies. -/
theorem block_eq_of_committed {f₁ f₂ : Flush U} {L₁ L₂ : BlockId}
    (h₁ : f₁.block σ = some L₁) (h₂ : f₂.block σ = some L₂)
    (hc₁ : Committed U L₁ σ) (hc₂ : Committed U L₂ σ) :
    f₁.block σ = f₂.block σ := by
  rw [h₁, h₂]
  exact congrArg some
    (eq_of_isAnchor_of_supported hc₁.1 hc₂.1 hc₁.2.1 hc₂.2.1)

/-- **The link clause keeps the descent from skipping.** Above a
committed anchor at round `ρ` sits a supported anchor at `ρ + 1`, so by
propagation it lies in the cone of every block from round `ρ + 3` up —
stopping the descent from reaching a round where two twins of an
equivocating anchor are both candidates. -/
theorem coneAnchors_succ_nonempty_of_committed (h : Committed U L ρ)
    {C : BlockId} (hC : C ∈ U.ids) (hCr : ρ + 3 ≤ (U.block C).round) :
    (coneAnchors U C (ρ + 1)).Nonempty := by
  obtain ⟨L', hL'⟩ := h.2.2
  obtain ⟨haL', -, hsL'⟩ := mem_linkers.mp hL'
  exact ⟨L', mem_coneAnchors.mpr ⟨haL',
    (mem_history_iff hC).mpr (reaches_of_supported hsL' hC (by omega))⟩⟩

/-! ## The ledger -/

/-! The ledger's own facts — monotone, agreed between agreeing records,
one entry round per block, agreed — are the record's (`Ledger.lean`),
at `f.block`. -/

end BlackMarlin

end LeanDag
