import LeanDag.OptimalHydrozoan.SlotAgreement.Statement
import LeanDag.OptimalHydrozoan.Helpers.SlotAgreement
import LeanDag.OptimalHydrozoan.Helpers.IndirectRules
/-!
# Optimal-Hydrozoan: slot agreement — proof

Generated proof layer; not part of the audit surface. Slot agreement is
the anchored relation's `decided_unique` at Optimal's laws, which hold
under leader exclusion at the schedule. What the laws ask is what the
arc had proved: direct-versus-direct pairings close by the direct-safety
cores, a direct commit is linked at some rung from any candidate of an
eligible slot and cannot coexist with a rung choice for a different
block (the "rung fires" / starvation lemmas of
`Optimal/Helpers/SlotAgreement.lean`), a skipped slot links nothing, and
two choices at one rung agree — certificate uniqueness at rung `0`,
`evidenceLinked_unique` at rung `1`, so no tie-break is needed.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace SlotAgreement

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]

/-- **Optimal-Hydrozoan's laws**, under leader exclusion at the schedule. -/
theorem optimalLaws :
    (optimalAnchored Replica BlockId).Laws (fun S U => LeaderExcluded (S := S) U) where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ _ hL₁ hL₂ h₁ h₂
    have hc : (U.block L₁).creator = (U.block L₂).creator := by rw [hL₁.2.2, hL₂.2.2]
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact eq_of_fastCommitOpt_leader hL₁ hL₂ (fastCommitOpt_of_fastCommitOptInView h₁)
        (fastCommitOpt_of_fastCommitOptInView h₂)
    · exact DirectSafety.eq_of_fastCommitOpt_of_slowCommit hc
        (fastCommitOpt_of_fastCommitOptInView h₁) (slowCommit_of_slowCommitInView h₂)
    · exact (DirectSafety.eq_of_fastCommitOpt_of_slowCommit hc.symm
        (fastCommitOpt_of_fastCommitOptInView h₂) (slowCommit_of_slowCommitInView h₁)).symm
    · exact Hydrozoan.DirectSafety.eq_of_certificates_nonempty hc
        (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h₁))
        (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h₂))
  commit_skip := by
    intro S U V₁ V₂ k L _ hL h hskip
    have hb := qCert_le_blames_of_skippedLeaderOptInView hskip
    rcases h with h | h
    · exact Nat.not_le.mpr (DirectSafety.blames_lt_of_fastCommitOpt hL
        (fastCommitOpt_of_fastCommitOptInView h)) hb
    · exact Nat.not_le.mpr (DirectSafety.blames_lt_of_slowCommit hL
        (slowCommit_of_slowCommitInView h)) hb
  commit_link := by
    intro S U V k j L A hI hL h hA helig
    rcases h with h | h
    · exact ⟨1, Nat.one_lt_two,
        evidenceLinked_of_fastCommitOptInView_at_anchor (U := ⟨U, hI⟩) hL h hA helig⟩
    · exact ⟨0, Nat.zero_lt_two,
        certifiedIn_of_slowCommitInView_at_anchor_opt (U := ⟨U, hI⟩) h hA helig⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hI hL₁ hL₂ h hA helig hi hemp hlink _
    have hc : (U.block L₁).creator = (U.block L₂).creator := by rw [hL₁.2.2, hL₂.2.2]
    rcases i with _ | _ | i
    · rcases h with h | h
      · by_contra hne
        exact not_certifiedIn_of_fastCommitOpt (fun e => hne e.symm) hL₁ hL₂
          (fastCommitOpt_of_fastCommitOptInView h) hlink
      · exact Hydrozoan.DirectSafety.eq_of_certificates_nonempty hc
          (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h))
          (LeanDag.Hydrozoan.certificates_nonempty_of_certifiedIn hlink)
    · rcases h with h | h
      · by_contra hne
        exact not_evidenceLinked_of_fastCommitOpt (U := ⟨U, hI⟩) (fun e => hne e.symm) hL₁ hL₂
          (fastCommitOpt_of_fastCommitOptInView h) hlink
      · exact (hemp 0 Nat.zero_lt_one L₁ hL₁
          (certifiedIn_of_slowCommitInView_at_anchor_opt (U := ⟨U, hI⟩) h hA helig)).elim
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  skip_link := by
    intro S U V k i L A _ hskip hL hi
    have hsk := skippedLeaderOpt_of_skippedLeaderOptInView hskip
    rcases i with _ | _ | i
    · exact not_certifiedIn_of_skippedOpt hL hsk
    · exact not_evidenceLinked_of_skippedOpt hL hsk
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ hi _ hl₁ hl₂ _ _
    rcases i with _ | _ | i
    · exact Hydrozoan.DirectSafety.eq_of_certificates_nonempty (by rw [hL₁.2.2, hL₂.2.2])
        (LeanDag.Hydrozoan.certificates_nonempty_of_certifiedIn hl₁) (LeanDag.Hydrozoan.certificates_nonempty_of_certifiedIn hl₂)
    · exact evidenceLinked_unique hL₁ hL₂ hl₁ hl₂
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  commit_mono := by
    intro S U V V' L r _ hsub h
    rcases h with h | h
    · exact Or.inl (HoldsAtLeast.mono hsub h)
    · exact Or.inr (HoldsAtLeast.mono hsub h)
  skip_mono := fun _ hsub h => skippedLeaderOptInView_mono hsub h
  skip_congr := fun _ hround hk h => skippedLeaderOptInView_congr hround hk h
  link_congr := by
    intro S₁ S₂ U A L i k hround hk h
    rcases i with _ | i
    · change LeanDag.Hydrozoan.CertifiedIn U A L (S₁.slotRound k) at h
      change LeanDag.Hydrozoan.CertifiedIn U A L (S₂.slotRound k)
      rw [← hround]; exact h
    · change EvidenceLinked (S := S₁) U A L k at h
      change EvidenceLinked (S := S₂) U A L k
      exact (evidenceLinked_congr hround hk).mp h

variable [S : Slots Replica] {U : OptUniverse Replica BlockId}

/-- **Slot agreement**: the relation's, at Optimal's laws and the
universe's exclusion. -/
theorem decided_unique {V₁ : LeanDag.Hydrozoan.View U.toBlockRecord} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : DecidedOpt U V₁ k v₁) :
    ∀ (V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (v₂ : Option BlockId),
      DecidedOpt U V₂ k v₂ → v₁ = v₂ :=
  AnchoredRule.decided_unique optimalLaws U.leader_excluded h₁

theorem decidedUnique : DecidedUnique U := fun _ V₂ _ _ v₂ h₁ h₂ =>
  decided_unique h₁ V₂ v₂ h₂

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ U
  exact decidedUnique

end SlotAgreement

end OptimalHydrozoan

end LeanDag
