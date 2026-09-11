import LeanDag.Steelhead.Safety.Statement
import LeanDag.Steelhead.Helpers.Decision
/-!
# Safety at a wavelength function — proof

Generated proof layer; not part of the audit surface. SH1 is Mahi-Mahi's
certificate lemmas at the slot's wave, SH2 and SH5 are `decided_unique`
at Steelhead's and Mahi-Mahi's laws, SH3 is the visibility lemma fed to
the relation's single-rung commit and agreement against the direct
commit, and SH4 is definitional up to `Nat.mod_one` and Mahi-Mahi's
wave-three correspondence, whose converse `decided_of_core_decided`
mirrors it.
-/

namespace LeanDag

namespace Steelhead

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U w ws wa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a r L hw h _ hLc hLr
    exact MahiMahi.certificates_eq_empty_of_directSkip (by omega) h hLc hLr
  · intro r L₁ L₂ hw h₁ h₂ hc hr
    exact MahiMahi.eq_of_certificates_nonempty (by omega) h₁ h₂ hc hr
  · intro L r hw h A hA hAr
    exact MahiMahi.certifiedIn_of_directCommit h hA (by unfold MahiMahi.decisionRoundAt; omega)
  · intro V₁ V₂ k v₁ v₂ hw h₁ h₂
    exact AnchoredRule.decided_unique (steelheadLaws hw) trivial h₁ V₂ v₂ h₂
  · intro V₁ V₂ k L hw hL hc
    refine ⟨fun j A hkj helig hj hmid => ?_, fun hskip => ?_⟩
    · exact AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) hkj helig hj hmid hL
        (certifiedIn_of_commit_at_anchor (fun r => by have := hw r; omega) hc
          (AnchoredRule.isLeaderBlock_of_decided hj) helig)
    · have := AnchoredRule.decided_agree (steelheadLaws hw) trivial
        (AnchoredRule.Decided.directCommit hL hc) hskip
      simp at this
  · exact ⟨fun _ => rfl, fun _ _ => funext fun r => by simp [periodic, Nat.mod_one]⟩
  · intro V k v
    exact ⟨MahiMahi.core_decided_of_decided, decided_of_core_decided⟩
  · intro coin V₁ V₂ r v₁ v₂ hwa h₁ h₂
    exact AnchoredRule.decided_unique (S := chainSlots coin) (MahiMahi.mahiMahiLaws (by omega))
      trivial h₁ V₂ v₂ h₂
  · intro coin V k r L hid hr hlead
    exact direct_agrees_with_chain hid hr hlead

end Safety

end Steelhead

end LeanDag
