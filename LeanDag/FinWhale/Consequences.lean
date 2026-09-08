import LeanDag.FinWhale.Evidence
/-!
# FinWhale — what follows from Lemma 4

The paper's Lemmas 2, 5, 8, and the direct-commit halves of 9 and 10.
Voters for conflicting blocks are disjoint (`parentsVoting_disjoint`),
since validity gives a block one edge per validator and two blocks of a
slot share an author; that fact carries Lemma 2 and Lemma 8.
`not_fpEvidence_conflicting` proves Lemma 9's third case from
FP-evidence's own two branches rather than from Lemma 4 as the paper
argues, since Lemma 4 does not itself rule out a block being evidence
for both of a conflicting pair.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- **A validator's parent votes once**: one edge per validator and a
shared author across the slot's blocks make the two voter sets
disjoint. -/
theorem parentsVoting_disjoint {b l l' : BlockId} (hb : b ∈ D.ids)
    (hconf : Conflicting D l l') :
    Disjoint (parentsVoting D b l) (parentsVoting D b l') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv hv'
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  obtain ⟨q', ⟨hq', hq'ref⟩, hq'v⟩ := hv'
  -- one edge per validator makes the two parents the same block
  have heq : q = q' :=
    (D.valid b hb).distinct_creators q hq q' hq' (by rw [hqv, hq'v])
  subst heq
  -- which then references both `l` and `l'`, sharing an author
  have hqids : q ∈ D.ids := D.complete b hb q hq
  exact hconf.1 ((D.valid q hqids).distinct_creators l hqref l' hq'ref hconf.2.2)

/-- **A quorum for one block bounds the parents voting for the other**:
disjoint inside a parent set of at most `n`, `2f + p` for one leaves at
most `f + p − 1` for the other. -/
theorem conflicting_le_of_spQuorum {b l l' : BlockId} (hb : b ∈ D.ids)
    (hconf : Conflicting D l l') (hcert : SPCertificate D b l) :
    (parentsVoting D b l').card + 1 ≤ F.f + P.p := by
  have hdisj := parentsVoting_disjoint hb hconf
  have hunion : (parentsVoting D b l ∪ parentsVoting D b l').card
      ≤ Fintype.card Validator := by
    rw [← Finset.card_univ]; exact Finset.card_le_univ _
  have hcard := Finset.card_union_of_disjoint hdisj
  have := params_arith (Validator := Validator)
  simp only [SPCertificate, spQuorum] at hcert
  omega

/-- **Lemma 2**: any SP-certificate for `l` is also FP-evidence for `l`,
its `2f + p` parents clearing both branches. -/
theorem lemma2 {b l : BlockId} (hb : b ∈ D.ids) (hcert : SPCertificate D b l) :
    FPEvidence D b l := by
  have hq : spQuorum Validator ≤ (parentsVoting D b l).card := hcert
  have := params_arith (Validator := Validator)
  simp only [FPEvidence]
  by_cases hexp : ExposesEquivocationBy D b (D.block l).creator
  · rw [if_pos hexp]
    refine ⟨by simp only [spQuorum] at hq; omega, fun l' _ hconf => ?_⟩
    exact conflicting_le_of_spQuorum hb hconf hcert
  · rw [if_neg hexp]
    simp only [spQuorum] at hq; omega

/-- **Lemma 8**: at most one block of a slot gathers a quorum of votes,
since two such quorums would share a correct validator who votes
once. -/
theorem lemma8 {l l' : BlockId} (hconf : Conflicting D l l')
    (h : spQuorum Validator ≤ (voters D l).card)
    (h' : spQuorum Validator ≤ (voters D l').card) : False := by
  -- the two voter sets meet in more than `f` validators
  have hmeet := card_add_card_le_card_inter_add_card (voters D l) (voters D l')
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ (voters D l ∩ voters D l').card := by
    simp only [spQuorum] at h h'; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hv
  exact not_voter_of_conflicting hconf v hv.2 hvc hv.1

/-- A fast commit carries a quorum of votes, so it feeds the above. -/
theorem spQuorum_le_of_fastCommit {l : BlockId} (hfast : FastCommit D l) :
    spQuorum Validator ≤ (voters D l).card :=
  le_trans spQuorum_le_fastCard hfast

/-- **Lemma 9's third case, proved from the definition rather than from
Lemma 4.** Under a fast commit for `l`, no round-`(r+2)` block is
FP-evidence for a conflicting `l'`: whichever branch a block's own
FP-evidence for `l` falls in bounds its parents voting for `l'` below
what evidence for `l'` needs. -/
theorem not_fpEvidence_conflicting {b l l' : BlockId}
    (hb : b ∈ D.ids) (hl : l ∈ D.ids) (hl' : l' ∈ D.ids)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hconf : Conflicting D l l') (hfast : FastCommit D l) :
    ¬ FPEvidence D b l' := by
  intro hev'
  have hev : FPEvidence D b l := lemma4 hb hl hround hfast
  have := params_arith (Validator := Validator)
  have hcc : (D.block l').creator = (D.block l).creator := hconf.2.2.symm
  simp only [FPEvidence, hcc] at hev hev'
  by_cases hexp : ExposesEquivocationBy D b (D.block l).creator
  · -- it has seen the equivocation, so its own branch caps the parents
    -- voting for `l'` below what FP-evidence for `l'` would need
    rw [if_pos hexp] at hev hev'
    have hbound := hev.2 l' hl' hconf
    have hneed := hev'.1
    omega
  · -- it has not, so its parents are leader-consistent and cannot vote for
    -- both; both counts are positive, which is the equivocation it would
    -- have to have seen
    rw [if_neg hexp] at hev hev'
    refine hexp ⟨l, hl, l', hl', hconf, rfl, ?_, ?_⟩
    · rw [← Finset.card_pos]; omega
    · rw [← Finset.card_pos]; omega

/-- **The same exclusion, under a slow-path commit**: a block carrying
an SP-certificate for `l` is not FP-evidence for a conflicting `l'`, by
the same case split on whether it has seen the equivocation. -/
theorem not_fpEvidence_of_spCertificate {c l l' : BlockId}
    (hl : l ∈ D.ids) (hl' : l' ∈ D.ids)
    (hconf : Conflicting D l l') (hcert : SPCertificate D c l) :
    ¬ FPEvidence D c l' := by
  intro hev'
  have := params_arith (Validator := Validator)
  have hcard : spQuorum Validator ≤ (parentsVoting D c l).card := hcert
  simp only [spQuorum] at hcard
  simp only [FPEvidence] at hev'
  by_cases hexp : ExposesEquivocationBy D c (D.block l').creator
  · rw [if_pos hexp] at hev'
    have := hev'.2 l hl ⟨Ne.symm hconf.1, hconf.2.1.symm, hconf.2.2.symm⟩
    omega
  · rw [if_neg hexp] at hev'
    refine hexp ⟨l, hl, l', hl', hconf, hconf.2.2, ?_, ?_⟩
    · rw [← Finset.card_pos]; omega
    · rw [← Finset.card_pos]; omega

end FinWhale

end LeanDag
