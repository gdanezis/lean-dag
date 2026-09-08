import LeanDag.Hydrozoan.SlotAgreement.Statement
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Hydrozoan.Helpers.DirectRules
import LeanDag.Hydrozoan.DirectSafety.Proof
/-!
# Slot agreement — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

namespace SlotAgreement

open DirectSafety

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- **Hydrozoan's laws.** -/
theorem hydrozoanLaws : (hydrozoanAnchored Replica BlockId).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ _ hL₁ hL₂ h₁ h₂
    have hc : (U.block L₁).creator = (U.block L₂).creator := by rw [hL₁.2.2, hL₂.2.2]
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact eq_of_fastCommit hc (fastCommit_of_fastCommitInView h₁)
        (fastCommit_of_fastCommitInView h₂)
    · exact eq_of_fastCommit_of_slowCommit hc (fastCommit_of_fastCommitInView h₁)
        (slowCommit_of_slowCommitInView h₂)
    · exact (eq_of_fastCommit_of_slowCommit hc.symm (fastCommit_of_fastCommitInView h₂)
        (slowCommit_of_slowCommitInView h₁)).symm
    · exact eq_of_certificates_nonempty hc
        (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h₁))
        (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h₂))
  commit_skip := by
    intro S U V₁ V₂ k L _ hL h hskip
    have hsk := skippedLeader_of_skippedLeaderInView hskip
    rcases h with h | h
    · exact not_skippedLeader_of_fastCommit hL (fastCommit_of_fastCommitInView h) hsk
    · exact not_skippedLeader_of_slowCommit hL (slowCommit_of_slowCommitInView h) hsk
  commit_link := by
    intro S U V k j L A _ hL h hA helig
    rcases h with h | h
    · exact ⟨1, Nat.one_lt_two, weakLinked_of_fastCommitInView_at_anchor h hA helig⟩
    · exact ⟨0, Nat.zero_lt_two, certifiedIn_of_slowCommitInView_at_anchor h hA helig⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h hA helig hi hemp hlink _
    have hc : (U.block L₁).creator = (U.block L₂).creator := by rw [hL₁.2.2, hL₂.2.2]
    rcases i with _ | _ | i
    · rcases h with h | h
      · by_contra hne
        exact not_certifiedIn_of_fastCommit (fun e => hne e.symm) hc.symm
          (fastCommit_of_fastCommitInView h) hlink
      · exact eq_of_certificates_nonempty hc
          (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h))
          (certificates_nonempty_of_certifiedIn hlink)
    · rcases h with h | h
      · by_contra hne
        exact not_weakLinked_of_fastCommit (fun e => hne e.symm) hc.symm
          (fastCommit_of_fastCommitInView h) hlink
      · exact (hemp 0 Nat.zero_lt_one L₁ hL₁
          (certifiedIn_of_slowCommitInView_at_anchor h hA helig)).elim
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  skip_link := by
    intro S U V k i L A _ hskip hL hi
    have hsk := skippedLeader_of_skippedLeaderInView hskip
    rcases i with _ | _ | i
    · exact not_certifiedIn_of_skipped hL hsk
    · exact not_weakLinked_of_skipped hL hsk
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ hi _ hl₁ hl₂ hm₁ hm₂
    rcases i with _ | _ | i
    · exact eq_of_certificates_nonempty (by rw [hL₁.2.2, hL₂.2.2])
        (certificates_nonempty_of_certifiedIn hl₁) (certificates_nonempty_of_certifiedIn hl₂)
    · exact le_antisymm (not_lt.mp (show ¬ L₂ < L₁ from hm₁ L₂ hL₂ hl₂))
        (not_lt.mp (show ¬ L₁ < L₂ from hm₂ L₁ hL₁ hl₁))
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  commit_mono := by
    intro S U V V' L r _ hsub h
    rcases h with h | h
    · exact Or.inl (HoldsAtLeast.mono hsub h)
    · exact Or.inr (HoldsAtLeast.mono hsub h)
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk h => blameSkip_congr hround hk h
  link_congr := (hydrozoanAnchored Replica BlockId).linkCongr_of_round
    (fun i U A L r => match i with | 0 => CertifiedIn U A L r | _ => WeakLinked U A L r)
    fun i _ _ _ _ _ => by rcases i with _ | i <;> rfl

variable [S : Slots Replica] {U : BlockUniverse Replica BlockId}

/-- **Slot agreement**: the relation's, at Hydrozoan's laws. -/
theorem decided_unique {V₁ : View U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View U) (v₂ : Option BlockId), Decided U V₂ k v₂ → v₁ = v₂ :=
  AnchoredRule.decided_unique hydrozoanLaws trivial h₁

theorem decidedUnique : DecidedUnique U := fun _ V₂ _ _ v₂ h₁ h₂ =>
  decided_unique h₁ V₂ v₂ h₂

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ _ U
  exact decidedUnique

end SlotAgreement

end Hydrozoan

end LeanDag
