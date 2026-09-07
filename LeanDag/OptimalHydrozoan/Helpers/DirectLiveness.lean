import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.OptimalHydrozoan.Helpers.DirectRules
import LeanDag.OptimalHydrozoan.Helpers.SlotAgreement
import LeanDag.Hydrozoan.Helpers.DirectLiveness
/-!
# Optimal-Hydrozoan: direct-liveness lemmas

Generated proof infrastructure; not part of the audit surface. The slow
path reuses Hydrozoan's wave chain (`Helpers/DirectLiveness.lean`)
unchanged. New here: the Optimal fast quorum from the fault count, and
the guaranteed skip of a candidate-less slot — `T`'s voting-round blocks
are slotBlames, `T`'s decision-round blocks are (vacuously) no-evidence, and
`q_cert ≤ q ≤ |T|`.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]

omit [DecidableEq BlockId] in
/-- With at most `pOpt` actual faults, the correct replicas alone reach
the Optimal fast quorum. -/
theorem qFastOpt_le_card_correct
    (h : (O.byzantine ∪ O.crashed).card ≤ pOpt Replica) :
    qFastOpt Replica ≤ (LeanDag.Hydrozoan.Correct : Finset Replica).card := by
  have hcompl : (LeanDag.Hydrozoan.Correct : Finset Replica).card
      = Fintype.card Replica - (O.byzantine ∪ O.crashed).card :=
    Finset.card_compl _
  have hle : (O.byzantine ∪ O.crashed).card ≤ Fintype.card Replica :=
    Finset.card_le_univ _
  simp only [qFastOpt]
  omega

section Skip

variable [S : Slots Replica] {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {V : LeanDag.Hydrozoan.View U} {T : Finset Replica} {k : ℕ}

/-- Every `T`-authored voting-round block slotBlames a candidate-less slot, in
any view caught up to the voting round. -/
theorem subset_blamesInView_of_coversUpto
    (hpop : PopulatedOn U T (S.slotRound k + 1))
    (hnolead : ∀ L, ¬ IsLeaderBlock U k L)
    (hcov : V.CoversUpto (S.slotRound k + 1)) :
    T ⊆ slotBlamesIn U V k := by
  intro v hv
  obtain ⟨b, hb, hba, hbr⟩ := hpop v hv
  exact mem_heldAuthors.mpr ⟨b, mem_slotBlamers.mpr ⟨hb, hbr, fun j _ hj => hnolead j hj⟩,
    hcov b hb (le_of_eq hbr), hba⟩

/-- Every `T`-authored decision-round block is (vacuously) fast evidence
for nothing at a candidate-less slot, so `T`'s decision-round blocks are a
no-evidence quorum in any view caught up to the decision round. -/
theorem noEvidenceQuorumInView_of_coversUpto
    (hcard : q Replica ≤ T.card)
    (hpop : PopulatedOn U T (S.slotRound k + 2))
    (hnolead : ∀ L, ¬ IsLeaderBlock U k L)
    (hcov : V.CoversUpto (S.slotRound k + 2)) :
    NoEvidenceQuorumInView U V k := by
  refine ⟨(blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
    (fun b => (U.block b).creator ∈ T), fun b hb => ?_, ?_⟩
  · obtain ⟨hb1, -⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbu, hbr⟩ := mem_blocksAt.mp hb1
    exact ⟨hb1, hcov b hbu (le_of_eq hbr), fun L hL _ => hnolead L hL⟩
  · have hsub : T ⊆ creatorsOf U.block ((blocksAt U (LeanDag.Hydrozoan.decisionRound Replica k)).filter
        (fun b => (U.block b).creator ∈ T)) := by
      intro v hv
      obtain ⟨b, hb, hba, hbr⟩ := hpop v hv
      exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr
        ⟨mem_blocksAt.mpr ⟨hb, by simp only [LeanDag.Hydrozoan.decisionRound]; exact hbr⟩, hba ▸ hv⟩, hba⟩
    have h1 := Finset.card_le_card hsub
    have h2 := qCert_le_q_opt (Replica := Replica)
    omega

/-- **The guaranteed skip**: a candidate-less slot whose voting and
decision rounds are filled by a quorum of correct replicas is directly
skipped, in any view caught up to the decision round. -/
theorem skippedLeaderOptInView_of_coversUpto
    (hcard : q Replica ≤ T.card)
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hnolead : ∀ L, ¬ IsLeaderBlock U k L)
    (hcov : V.CoversUpto (S.slotRound k + 2)) :
    SkippedLeaderOptInView U V k := by
  refine ⟨?_, noEvidenceQuorumInView_of_coversUpto hcard hpop2 hnolead hcov⟩
  have h1 := Finset.card_le_card
    (subset_blamesInView_of_coversUpto hpop1 hnolead (hcov.mono (by omega)))
  have h2 := qCert_le_q_opt (Replica := Replica)
  show qCert Replica ≤ (slotBlamesIn U V k).card
  omega

end Skip

end OptimalHydrozoan

end LeanDag
