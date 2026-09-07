import LeanDag.MahiMahi.Safety.Statement
import LeanDag.MahiMahi.Helpers.Decision
/-!
# Safety at wave `w` — proof

Generated proof layer; not part of the audit surface. Each conjunct is
one helper: the counting lemmas of `Helpers/Rules.lean` for MM1a and
MM1b, `decided_unique` for MM1c, and the wave-three correspondences of
both helper files for MM1d.
-/

namespace LeanDag

namespace MahiMahi

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a r L hw h _ hLc hLr
    exact certificates_eq_empty_of_directSkip (by omega) h hLc hLr
  · intro r L₁ L₂ hw h₁ h₂ hc hr
    exact eq_of_certificates_nonempty (by omega) h₁ h₂ hc hr
  · intro V₁ V₂ k v₁ v₂ hw h₁ h₂
    exact AnchoredRule.decided_unique (mahiMahiLaws (by omega)) trivial h₁ V₂ v₂ h₂
  · intro V k v h
    exact core_decided_of_decided h
  · intro L r _ hLr
    unfold DirectCommit LeanDag.DirectCommit
    rw [certificates_eq_of_three hLr]
  · refine ⟨?_, ?_⟩
    · intro a r h L hL hLc hLr
      refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
      intro q hq
      rw [votingRound_three] at hq
      rw [Finset.mem_filter] at hq
      rw [omissionsOf, Finset.mem_filter]
      exact ⟨hq.1, not_mem_refs_of_blames (mem_blocksAt.mp hq.1).1 hq.2 hLc hLr⟩
    · intro a r L hL hLc hLr huniq
      constructor
      · intro h
        refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
        intro q hq
        rw [votingRound_three] at hq
        rw [Finset.mem_filter] at hq
        rw [omissionsOf, Finset.mem_filter]
        exact ⟨hq.1, not_mem_refs_of_blames (mem_blocksAt.mp hq.1).1 hq.2 hLc hLr⟩
      · intro h
        refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
        intro q hq
        rw [votingRound_three]
        rw [omissionsOf, Finset.mem_filter] at hq
        rw [Finset.mem_filter]
        obtain ⟨hqids, hqr⟩ := mem_blocksAt.mp hq.1
        exact ⟨hq.1, blames_of_not_mem_refs_of_unique hqids hqr hLc hLr huniq hq.2⟩

end Safety

end MahiMahi

end LeanDag
