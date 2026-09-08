import LeanDag.OptimalHydrozoan.DirectSafety.Statement
import LeanDag.OptimalHydrozoan.Helpers.Counting
import LeanDag.Hydrozoan.DirectSafety.Proof
/-!
# Optimal-Hydrozoan: direct-rule safety — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace DirectSafety

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]
  {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

omit S in
/-- Universe-level fast/fast core, given `f ≥ 1`: two fast quorums
exceed `n + f`. -/
theorem eq_of_fastCommitOpt {L₁ L₂ : BlockId} {r : ℕ} (hf : 1 ≤ O.f)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator)
    (h₁ : FastCommitOpt U L₁ r) (h₂ : FastCommitOpt U L₂ r) : L₁ = L₂ :=
  eq_of_card_supporters U.noEquivOn_honest card_compl_nonByzantine_le hcreator (n := r + 1) (by
    have h5 := nf_lt_two_qFastOpt (Replica := Replica) hf
    simp only [FastCommitOpt] at h₁ h₂
    omega)

omit S in
/-- Universe-level fast/slow core. -/
theorem eq_of_fastCommitOpt_of_slowCommit {L₁ L₂ : BlockId} {r : ℕ}
    (hcreator : (U.block L₁).creator = (U.block L₂).creator)
    (h₁ : FastCommitOpt U L₁ r) (h₂ : SlowCommit U L₂ r) : L₁ = L₂ :=
  eq_of_card_supporters U.noEquivOn_honest card_compl_nonByzantine_le hcreator (n := r + 1) (by
    have := Hydrozoan.DirectSafety.qCert_le_card_supporters_of_slowCommit h₂
    have h5 := nf_lt_qFastOpt_add_qCert (Replica := Replica)
    simp only [FastCommitOpt] at h₁
    omega)

/-- Universe-level: a fast commit leaves fewer than `qCert` blamers. -/
theorem blames_lt_of_fastCommitOpt {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (h : FastCommitOpt U L (S.slotRound k)) :
    (slotBlames U k).card < qCert Replica := by
  have := card_supporters_add_card_slotBlames_le U.noEquivOn_honest card_compl_nonByzantine_le hL
  have h5 := nf_lt_qFastOpt_add_qCert (Replica := Replica)
  simp only [FastCommitOpt] at h
  omega

/-- Universe-level: a slow commit leaves fewer than `qCert` blamers. -/
theorem blames_lt_of_slowCommit {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (h : SlowCommit U L (S.slotRound k)) :
    (slotBlames U k).card < qCert Replica := by
  have := card_supporters_add_card_slotBlames_le U.noEquivOn_honest card_compl_nonByzantine_le hL
  have h2 := Hydrozoan.DirectSafety.qCert_le_card_supporters_of_slowCommit h
  have h5 := nf_lt_two_qCert (Replica := Replica)
  omega

theorem holds : Statement := by
  intro Replica BlockId _ _ _ O _ U
  have hbase := Hydrozoan.DirectSafety.holds Replica BlockId U.toBlockRecord
  refine ⟨?_, hbase.2.1, hbase.2.2.1, ?_, ?_⟩
  · intro V₁ V₂ k L₁ L₂ hL₁ hL₂ h₁ h₂
    by_cases hf : 1 ≤ O.f
    · exact eq_of_fastCommitOpt hf (by rw [hL₁.2.2, hL₂.2.2])
        (fastCommitOpt_of_fastCommitOptInView h₁)
        (fastCommitOpt_of_fastCommitOptInView h₂)
    · have hf0 : O.f = 0 := by omega
      have hempty := byzantine_eq_empty_of_f_eq_zero (Replica := Replica) hf0
      have hnb : (U.toBlockRecord.block L₁).creator ∈
          (LeanDag.Hydrozoan.NonByzantine : Finset Replica) := by
        rw [mem_nonByzantine, hempty]
        exact Finset.notMem_empty _
      exact U.toBlockRecord.no_equivocation L₁ hL₁.1 L₂ hL₂.1 hnb (by rw [hL₁.2.2, hL₂.2.2])
        (by rw [hL₁.2.1, hL₂.2.1])
  · intro V₁ V₂ k L₁ L₂ hL₁ hL₂ h₁ h₂
    exact eq_of_fastCommitOpt_of_slowCommit (by rw [hL₁.2.2, hL₂.2.2])
      (fastCommitOpt_of_fastCommitOptInView h₁) (slowCommit_of_slowCommitInView h₂)
  · intro V₁ V₂ k L hL hcommit hskip
    have hb := qCert_le_blames_of_skippedLeaderOptInView hskip
    rcases hcommit with h | h
    · exact absurd hb (Nat.not_le.mpr
        (blames_lt_of_fastCommitOpt hL (fastCommitOpt_of_fastCommitOptInView h)))
    · exact absurd hb (Nat.not_le.mpr
        (blames_lt_of_slowCommit hL (slowCommit_of_slowCommitInView h)))

end DirectSafety

end OptimalHydrozoan

end LeanDag
