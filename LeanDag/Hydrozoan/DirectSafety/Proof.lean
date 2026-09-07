import LeanDag.Hydrozoan.DirectSafety.Statement
import LeanDag.Hydrozoan.Helpers.Counting
import LeanDag.Hydrozoan.Helpers.DirectRules
/-!
# Direct-rule safety — proof

Generated proof layer; not part of the audit surface. Each conjunct
lifts the view rules to the universe (Phase 4a bridges), overlaps two
creator quorums in a non-Byzantine replica (`Helpers/Counting.lean`),
collapses its voting blocks through `no_equivocation`, and collapses
the two candidates through `distinct_creators`.
-/

namespace LeanDag

namespace Hydrozoan

namespace DirectSafety

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica] [S : Slots Replica]
  {U : BlockUniverse Replica BlockId}

omit S in
/-- Universe-level fast/fast core: two fast quorums exceed `n + f`. -/
theorem eq_of_fastCommit {L₁ L₂ : BlockId} {r : ℕ}
    (hcreator : (U.block L₁).creator = (U.block L₂).creator)
    (h₁ : FastCommit U L₁ r) (h₂ : FastCommit U L₂ r) : L₁ = L₂ :=
  eq_of_card_supporters U.noEquivOn_honest card_compl_nonByzantine_le hcreator (n := r + 1)
    (by have := nf_lt_two_qFast (Replica := Replica); simp only [FastCommit] at h₁ h₂; omega)

omit S in
/-- Universe-level certificate-uniqueness core: two certificates' vote
sets exceed `n + f`, so they share a vote block, which cites one author
once. -/
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (hcreator : (U.block L₁).creator = (U.block L₂).creator)
    (h₁ : (certificates U L₁ r).Nonempty)
    (h₂ : (certificates U L₂ r).Nonempty) : L₁ = L₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  obtain ⟨hC₁i, hC₁r, hcert₁⟩ := mem_certificates.mp hC₁
  obtain ⟨hC₂i, hC₂r, hcert₂⟩ := mem_certificates.mp hC₂
  obtain ⟨b, hb₁, hb₂⟩ :=
    exists_common_block U.noEquivOn_honest card_compl_nonByzantine_le
      (s := voteBlocks U C₁ L₁) (t := voteBlocks U C₂ L₂) (n := r + 1)
      (fun b hb => ⟨(mem_voteBlocks_spec hC₁i hC₁r hb).1,
        (mem_voteBlocks_spec hC₁i hC₁r hb).2.1⟩)
      (fun b hb => ⟨(mem_voteBlocks_spec hC₂i hC₂r hb).1,
        (mem_voteBlocks_spec hC₂i hC₂r hb).2.1⟩)
      (by
        have h5 := nf_lt_two_qCert (Replica := Replica)
        simp only [IsCertificate] at hcert₁ hcert₂
        omega)
  have hbids : b ∈ U.ids := (mem_voteBlocks_spec hC₁i hC₁r hb₁).1
  exact U.distinct_creators hbids
    (mem_voteBlocks_spec hC₁i hC₁r hb₁).2.2
    (mem_voteBlocks_spec hC₂i hC₂r hb₂).2.2 hcreator

omit S in
/-- A slow commit's certificate carries `q_cert` supporters. -/
theorem qCert_le_card_supporters_of_slowCommit {L : BlockId} {r : ℕ} (h : SlowCommit U L r) :
    qCert Replica ≤ (supporters U L (r + 1)).card := by
  obtain ⟨C, hC⟩ := certificates_nonempty_of_slowCommit h
  obtain ⟨hCi, hCr, hcert⟩ := mem_certificates.mp hC
  have hle := Finset.card_le_card (creators_voteBlocks_subset_supporters (L := L) hCi hCr)
  simp only [IsCertificate] at hcert
  omega

omit S in
/-- Universe-level fast/slow core: a fast quorum and a certificate's
support exceed `n + f`. -/
theorem eq_of_fastCommit_of_slowCommit {L₁ L₂ : BlockId} {r : ℕ}
    (hcreator : (U.block L₁).creator = (U.block L₂).creator)
    (h₁ : FastCommit U L₁ r) (h₂ : SlowCommit U L₂ r) : L₁ = L₂ :=
  eq_of_card_supporters U.noEquivOn_honest card_compl_nonByzantine_le hcreator (n := r + 1) (by
    have := qCert_le_card_supporters_of_slowCommit h₂
    have := nf_lt_qFast_add_qCert (Replica := Replica)
    simp only [FastCommit] at h₁
    omega)

/-- Universe-level fast-commit/skip exclusion core. -/
theorem not_skippedLeader_of_fastCommit {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (h : FastCommit U L (S.slotRound k)) :
    ¬ SkippedLeader U k := by
  intro hskip
  have := card_supporters_add_card_slotBlames_le U.noEquivOn_honest card_compl_nonByzantine_le hL
  have h5 := nf_lt_two_qFast (Replica := Replica)
  simp only [FastCommit] at h
  simp only [SkippedLeader] at hskip
  omega

/-- Universe-level slow-commit/skip exclusion core. -/
theorem not_skippedLeader_of_slowCommit {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (h : SlowCommit U L (S.slotRound k)) :
    ¬ SkippedLeader U k := by
  intro hskip
  have := card_supporters_add_card_slotBlames_le U.noEquivOn_honest card_compl_nonByzantine_le hL
  have h2 := qCert_le_card_supporters_of_slowCommit h
  have h5 := nf_lt_qFast_add_qCert (Replica := Replica)
  simp only [SkippedLeader] at hskip
  omega

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V₁ V₂ k L₁ L₂ hL₁ hL₂ h₁ h₂
    exact eq_of_fastCommit (by rw [hL₁.2.2, hL₂.2.2])
      (fastCommit_of_fastCommitInView h₁) (fastCommit_of_fastCommitInView h₂)
  · intro k L₁ L₂ hL₁ hL₂ h₁ h₂
    exact eq_of_certificates_nonempty (by rw [hL₁.2.2, hL₂.2.2]) h₁ h₂
  · intro V₁ V₂ k L₁ L₂ hL₁ hL₂ h₁ h₂
    exact eq_of_certificates_nonempty (by rw [hL₁.2.2, hL₂.2.2])
      (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h₁))
      (certificates_nonempty_of_slowCommit (slowCommit_of_slowCommitInView h₂))
  · intro V₁ V₂ k L₁ L₂ hL₁ hL₂ h₁ h₂
    exact eq_of_fastCommit_of_slowCommit (by rw [hL₁.2.2, hL₂.2.2])
      (fastCommit_of_fastCommitInView h₁) (slowCommit_of_slowCommitInView h₂)
  · intro V₁ V₂ k L hL hcommit hskip
    have hsk := skippedLeader_of_skippedLeaderInView hskip
    rcases hcommit with h | h
    · exact not_skippedLeader_of_fastCommit hL
        (fastCommit_of_fastCommitInView h) hsk
    · exact not_skippedLeader_of_slowCommit hL
        (slowCommit_of_slowCommitInView h) hsk

end DirectSafety

end Hydrozoan

end LeanDag
