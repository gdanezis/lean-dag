import LeanDag.RedSnapper.Model.Certificates

/-!
# Quorum intersection

Generated: the counting core of the exclusivity claims — two author sets
whose sizes sum above `n + f` share a correct validator — lifted to
`AtLeast` witnesses, plus the threshold arithmetic. Nothing here is part
of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator]

/-- Two validator sets whose sizes sum above `n + f` share a correct
validator. -/
theorem exists_correct_mem_inter {s t : Finset Validator}
    (h : Fintype.card Validator + F.f < s.card + t.card) :
    ∃ v ∈ s ∩ t, v ∈ (Correct : Finset Validator) := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : (s ∪ t).card ≤ Fintype.card Validator := by
    have := Finset.card_le_card (Finset.subset_univ (s ∪ t))
    rwa [Finset.card_univ] at this
  have h3 : F.byzantine.card < (s ∩ t).card := by
    have := F.card_byzantine
    omega
  by_contra hno
  push Not at hno
  have hsub : s ∩ t ⊆ F.byzantine := by
    intro v hv
    by_contra hb
    exact hno v hv (Finset.mem_compl.mpr hb)
  exact absurd (Finset.card_le_card hsub) (by omega)

/-- Two `AtLeast` thresholds whose sum beats `n + f` land on one correct
validator with a block in each witness set. -/
theorem exists_correct_of_atLeast {U : Universe Validator BlockId Tx Obj}
    {k₁ k₂ : ℕ} {s₁ s₂ : Finset BlockId} {P₁ P₂ : BlockId → Prop}
    (h₁ : AtLeast U k₁ s₁ P₁) (h₂ : AtLeast U k₂ s₂ P₂)
    (hk : Fintype.card Validator + F.f < k₁ + k₂) :
    ∃ v ∈ (Correct : Finset Validator),
      (∃ b ∈ s₁, (U.block b).author = v ∧ P₁ b) ∧
        (∃ b ∈ s₂, (U.block b).author = v ∧ P₂ b) := by
  obtain ⟨t₁, ht₁, hP₁, hk₁⟩ := h₁
  obtain ⟨t₂, ht₂, hP₂, hk₂⟩ := h₂
  obtain ⟨v, hv, hcor⟩ := exists_correct_mem_inter
    (s := authorsOf U.block t₁) (t := authorsOf U.block t₂) (by omega)
  rw [Finset.mem_inter] at hv
  obtain ⟨b₁, hb₁, hab₁⟩ := Finset.mem_image.mp hv.1
  obtain ⟨b₂, hb₂, hab₂⟩ := Finset.mem_image.mp hv.2
  exact ⟨v, hcor, ⟨b₁, ht₁ hb₁, hab₁, hP₁ b₁ hb₁⟩, ⟨b₂, ht₂ hb₂, hab₂, hP₂ b₂ hb₂⟩⟩

/-- `2 · quorum > n + f`: two ack-certificate quorums intersect
correctly. -/
theorem quorum_add_quorum :
    Fintype.card Validator + F.f < quorum Validator + quorum Validator := by
  have := F.card_validators
  unfold quorum
  omega

/-- `quorum + half > n + f`: an ack-certificate quorum and a skip or
unlock quorum intersect correctly. -/
theorem quorum_add_half :
    Fintype.card Validator + F.f < quorum Validator + half Validator := by
  have := F.card_validators
  unfold quorum half
  omega

/-- The quorum is positive: parents above genesis exist. -/
theorem quorum_pos : 0 < quorum Validator := by
  have := F.card_validators
  unfold quorum
  omega

/-- The half threshold is positive. -/
theorem half_pos : 0 < half Validator := by
  unfold half
  omega

/-- A block's parent set carries a trivial `AtLeast` at the quorum. -/
theorem atLeast_parents_true {U : Universe Validator BlockId Tx Obj} {b : BlockId}
    (hb : b ∈ U.ids) (hr : 0 < (U.block b).round) :
    AtLeast U (quorum Validator) (U.block b).parents fun _ => True :=
  ⟨(U.block b).parents, Finset.Subset.refl _, fun _ _ => trivial,
    (U.valid b hb).quorum hr⟩

end RedSnapper

end LeanDag
