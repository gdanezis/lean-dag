import LeanDag.BlackMarlin.Model.Decision
/-!
# Black Marlin — the counting layer

Generated proof layer; not part of the audit surface. The universe-level
lemmas behind `Safety/Statement.lean`: the paper's Lemmas 3, 4, 5 and 6
(`black-marlin.md` §4), each stated over the whole universe, where the
counting happens.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- Membership in `linkers`, unfolded. -/
theorem mem_linkers {L L' : BlockId} {r : ℕ} :
    L' ∈ linkers U L r ↔
      IsAnchor U (r + 1) L' ∧ L ∈ (U.block L').refs ∧ Supported U L' (r + 1) := by
  simp only [linkers, Finset.mem_filter, mem_blocksAt, IsAnchor]
  tauto

omit [DecidableEq BlockId] in
/-- Two anchor blocks of one round share an author: the rotation elects
one validator per round. -/
theorem creator_eq_of_isAnchor {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : IsAnchor U r L₁) (h₂ : IsAnchor U r L₂) :
    (U.block L₁).creator = (U.block L₂).creator := by
  rw [h₁.2.2, h₂.2.2]

omit Rot in
/-- **The paper's Lemma 3.** Two supported blocks of one author at one
round are the same block: their support quorums share `n − 2f ≥ f + 1`
authors, each supporting both, and all of them equivocators. Needs only
`n ≥ 3f + 1`, which is the whole committee of this arc. -/
theorem eq_of_supported {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : Supported U L₁ r) (h₂ : Supported U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂ :=
  eq_of_card_supporters U.noEquivOn_honest card_compl_correct_le hcr (n := r + 1)
    (by unfold Supported at h₁ h₂; have := F.card_validators; omega)

/-- Lemma 3 for anchors: at most one anchor block of a round is
supported, so at most one is committed there. -/
theorem eq_of_isAnchor_of_supported {L₁ L₂ : BlockId} {r : ℕ}
    (ha₁ : IsAnchor U r L₁) (ha₂ : IsAnchor U r L₂)
    (h₁ : Supported U L₁ r) (h₂ : Supported U L₂ r) : L₁ = L₂ :=
  eq_of_supported h₁ h₂ (creator_eq_of_isAnchor ha₁ ha₂)

omit Rot in
/-- **The paper's Lemma 5.** A supported block is in the causal history
of every block two rounds above it or higher — Byzantine-authored
included, since validity is structural — via the core's
`reaches_of_honest_support_of_card`, carried upward by
`reaches_pred_of_round_le`. -/
theorem reaches_of_supported {L : BlockId} {r : ℕ} (h : Supported U L r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c L := by
  have hcard : F.f + 1 ≤ (correctSupporters U L (r + 1)).card :=
    card_inter_correct_of_quorum h
  have hbase : ∀ c ∈ U.ids, (U.block c).round = r + 2 → ∃ b, b = L ∧ Reaches U c b := by
    intro c hc hcr
    refine ⟨L, rfl, reaches_of_honest_support_of_card
      (S := correctSupporters U L (r + 1)) (fun v hv => ?_)
      (fun v hv => correctSupporters_correct hv) (lt_card_add_quorumCard hcard) hc hcr⟩
    exact mem_supporters.mp (correctSupporters_subset hv)
  obtain ⟨b, hb, hreach⟩ := reaches_pred_of_round_le hbase hc hcr
  exact hb ▸ hreach

/-- **The paper's Lemma 6**, in the form the round comparison gives: of
two committed anchors, the lower lies in the causal history of the
higher — by Lemma 3 at equal rounds or a gap of one via the shared
linking anchor, by Lemma 5 at a gap of two or more. -/
theorem reaches_of_committed_of_le {L₁ L₂ : BlockId} {r₁ r₂ : ℕ}
    (h₁ : Committed U L₁ r₁) (h₂ : Committed U L₂ r₂) (hr : r₁ ≤ r₂) :
    L₁ = L₂ ∨ Reaches U L₂ L₁ := by
  obtain ⟨ha₁, hs₁, hl₁⟩ := h₁
  obtain ⟨ha₂, hs₂, hl₂⟩ := h₂
  rcases Nat.lt_or_ge (r₁ + 1) r₂ with hgap | hnear
  · exact Or.inr (reaches_of_supported hs₁ ha₂.1 (by rw [ha₂.2.1]; omega))
  · rcases Nat.eq_or_lt_of_le hr with heq | hlt
    · subst heq
      exact Or.inl (eq_of_isAnchor_of_supported ha₁ ha₂ hs₁ hs₂)
    · have hr2 : r₂ = r₁ + 1 := by omega
      subst hr2
      obtain ⟨L', hL'⟩ := hl₁
      obtain ⟨ha', href, hs'⟩ := mem_linkers.mp hL'
      have : L' = L₂ := eq_of_isAnchor_of_supported ha' ha₂ hs' hs₂
      exact Or.inr (this ▸ Reaches.single href)

/-- **The prefix corollary of Lemma 6.** Of two committed anchors, the
causal history of the lower is contained in that of the higher — what
one delivers, the other delivers too. -/
theorem history_subset_of_committed {L₁ L₂ : BlockId} {r₁ r₂ : ℕ}
    (h₁ : Committed U L₁ r₁) (h₂ : Committed U L₂ r₂) (hr : r₁ ≤ r₂) :
    history U L₁ ⊆ history U L₂ := by
  rcases reaches_of_committed_of_le h₁ h₂ hr with heq | hre
  · exact heq ▸ Finset.Subset.refl _
  · exact history_subset_of_reaches h₂.1.1 hre

omit Rot [DecidableEq BlockId] in
/-- **The paper's Lemma 4.** Below the highest round of the DAG, every
round carries blocks from a quorum of distinct authors.

Downward induction on the gap: a valid block names `n − f` distinct
authors one round below, and those authors hold blocks there. -/
theorem quorum_authorsAt_of_lt {c : BlockId} {r : ℕ} (hc : c ∈ U.ids)
    (hlt : r < (U.block c).round) :
    quorumCard Validator ≤ (authorsAt U r).card := by
  suffices H : ∀ d : ℕ, ∀ c ∈ U.ids, (U.block c).round = r + 1 + d →
      quorumCard Validator ≤ (authorsAt U r).card by
    exact H ((U.block c).round - (r + 1)) c hc (by omega)
  intro d
  induction d with
  | zero =>
      intro c hc hcr
      refine le_trans (U.creators_quorum hc (by omega)) (Finset.card_le_card ?_)
      exact creators_refs_subset_authorsAt hc (by omega)
  | succ d ih =>
      intro c hc hcr
      obtain ⟨p, hp⟩ := U.refs_nonempty hc (by omega)
      have hp_ids : p ∈ U.ids := U.complete c hc p hp
      have hp_round := U.round_of_mem_refs hc hp
      exact ih p hp_ids (by omega)

end BlackMarlin

end LeanDag
