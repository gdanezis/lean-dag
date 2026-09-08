import LeanDag.FinWhale.Model.Rule
import LeanDag.FinWhale.Committee
import LeanDag.FinWhale.Counting
/-!
# FinWhale — Lemma 4 in the shape the paper states it, and what follows

`Counting.lean` proves the arithmetic; this file spends it, supplying
what it cannot see — that a correct validator's single round-`(r+1)`
block is the one it voted with, wherever it is later referenced
(`parentsVoting_of_correct_voter`). With that, Lemma 4 is the two counts
applied to a block's parent set. The equivocating branch also needs the
leader to be Byzantine, which `parents_byzantine_lt` gives via the
validity clause dropping it from an exposing block's parents.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- A block's parents sit one round below it. -/
theorem parent_round {b i : BlockId} (hb : b ∈ D.ids) (hi : i ∈ (D.block b).refs) :
    (D.block i).round + 1 = (D.block b).round :=
  (D.valid b hb).predecessor i hi

/-- **A FinWhale DAG is a causal structure**: closure under references
and validity's predecessor clause. -/
theorem causalStructure (D : Dag Validator BlockId Payload) :
    CausalStructure D.block D.ids :=
  ⟨D.complete, fun i hi j hj => (D.valid i hi).predecessor j hj⟩

/-- **No block references two blocks of one author.** Validity's
`distinct_creators` says so directly. -/
theorem not_refs_conflicting {c l l' : BlockId}
    (hc : c ∈ D.ids) (hconf : Conflicting D l l')
    (hl : l ∈ (D.block c).refs) (hl' : l' ∈ (D.block c).refs) : False :=
  hconf.1 ((D.valid c hc).distinct_creators l hl l' hl' hconf.2.2)

/-- **The bridge.** A correct validator that both parents `b` and votes
for `l` votes for `l` among `b`'s parents: its single round-`(r+1)`
block is both. -/
theorem parentsVoting_of_correct_voter {b l : BlockId}
    (hb : b ∈ D.ids) (hround : (D.block b).round = (D.block l).round + 2) :
    parentSet D b ∩ (voters D l ∩ (Correct : Finset Validator)) ⊆ parentsVoting D b l := by
  intro v hv
  rw [Finset.mem_inter, Finset.mem_inter] at hv
  obtain ⟨hpar, hvot, hcorr⟩ := hv
  -- the parent block of `b` authored by `v`
  simp only [parentSet, mem_creatorsOf] at hpar
  obtain ⟨q, hq, hqv⟩ := hpar
  -- the voting block authored by `v`
  simp only [voters, supporters, votesFor, mem_creatorsOf, blocksAt, Finset.mem_filter] at hvot
  obtain ⟨q', ⟨⟨hq'ids, hq'round⟩, hq'ref⟩, hq'v⟩ := hvot
  -- both are round-`(r+1)` blocks of the same correct validator, hence equal
  have hqids : q ∈ D.ids := D.complete b hb q hq
  have hqround : (D.block q).round = (D.block l).round + 1 := by
    have := parent_round hb hq; omega
  have heq : q = q' :=
    D.no_equivocation q hqids q' hq'ids (by rw [hqv]; exact hcorr)
      (by rw [hqv, hq'v]) (by rw [hqround, hq'round])
  refine mem_creatorsOf.2 ⟨q, ?_, hqv⟩
  rw [Finset.mem_filter]
  exact ⟨hq, by rw [heq]; exact hq'ref⟩

/-- A validator with two distinct blocks at one round is Byzantine. -/
theorem byzantine_of_conflicting {l l' : BlockId}
    (hl : l ∈ D.ids) (hl' : l' ∈ D.ids) (hconf : Conflicting D l l') :
    (D.block l).creator ∉ (Correct : Finset Validator) := by
  intro hcorr
  exact hconf.1 (D.no_equivocation l hl l' hl' hcorr hconf.2.2 hconf.2.1)

/-- **A correct validator votes for at most one block of a slot**: its
single round-`(r+1)` block carries at most one edge per validator. -/
theorem not_voter_of_conflicting {l l' : BlockId} (hconf : Conflicting D l l') :
    ∀ v ∈ voters D l', v ∈ (Correct : Finset Validator) → v ∉ voters D l := by
  intro v hv' hcorr hv
  simp only [voters, supporters, votesFor, mem_creatorsOf, blocksAt, Finset.mem_filter] at hv hv'
  obtain ⟨q, ⟨⟨hqids, hqr⟩, hqref⟩, hqv⟩ := hv
  obtain ⟨q', ⟨⟨hq'ids, hq'r⟩, hq'ref⟩, hq'v⟩ := hv'
  -- the two voting blocks are the same block, by `no_equivocation`
  have heq : q = q' :=
    D.no_equivocation q hqids q' hq'ids (by rw [hqv]; exact hcorr) (by rw [hqv, hq'v])
      (by rw [hqr, hq'r, hconf.2.1])
  -- so one block references both `l` and `l'`, which share a creator
  subst heq
  exact hconf.1 ((D.valid q hqids).distinct_creators l hqref l' hq'ref hconf.2.2)

/-- **Lemma 4, the non-equivocating branch, at the block level.** -/
theorem fpEvidence_nonequivocating {b l : BlockId}
    (hb : b ∈ D.ids) (hround : (D.block b).round = (D.block l).round + 2)
    (hfast : FastCommit D l) :
    F.f + P.p ≤ (parentsVoting D b l).card + 1 := by
  have hpar : quorumCard Validator ≤ (parentSet D b).card :=
    (D.valid b hb).quorum (by omega)
  have hcount := nonequivocating_voters (voters := voters D l)
    (parents := parentSet D b) hfast hpar
  have hsub := Finset.card_le_card (parentsVoting_of_correct_voter hb hround)
  omega

/-- **Lemma 4, the equivocating branch, at the block level**: the
leader is dropped from the parents and is Byzantine, so at most `f − 1`
of the parents are, and the count reaches `f + p`. -/
theorem fpEvidence_equivocating {b l : BlockId}
    (hb : b ∈ D.ids) (hround : (D.block b).round = (D.block l).round + 2)
    (hfast : FastCommit D l)
    (hbyz : (parentSet D b ∩ F.byzantine).card + 1 ≤ F.f) :
    F.f + P.p ≤ (parentsVoting D b l).card := by
  have hpar : quorumCard Validator ≤ (parentSet D b).card :=
    (D.valid b hb).quorum (by omega)
  have hcount := equivocating_voters (voters := voters D l)
    (parents := parentSet D b) hfast hpar hbyz
  exact le_trans hcount (Finset.card_le_card (parentsVoting_of_correct_voter hb hround))

/-- **The conflicting side**: under a fast commit for `l`, such a block
references fewer than `f + p` parents voting for any conflicting
`l'`. -/
theorem conflicting_parents_lt {b l l' : BlockId}
    (hb : b ∈ D.ids)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hconf : Conflicting D l l') (hfast : FastCommit D l)
    (hbyz : (parentSet D b ∩ F.byzantine).card + 1 ≤ F.f) :
    (parentsVoting D b l').card + 1 ≤ F.f + P.p := by
  have hround' : (D.block b).round = (D.block l').round + 2 := by
    rw [hround, hconf.2.1]
  have hsub : parentsVoting D b l' ⊆ parentSet D b ∩ voters D l' := by
    intro v hv
    simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv
    obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
    have hqids : q ∈ D.ids := D.complete b hb q hq
    have hqround : (D.block q).round = (D.block l').round + 1 := by
      have := parent_round hb hq; omega
    refine Finset.mem_inter.2 ⟨mem_creatorsOf.2 ⟨q, hq, hqv⟩, ?_⟩
    refine mem_creatorsOf.2 ⟨q, ?_, hqv⟩
    rw [votesFor, Finset.mem_filter]
    exact ⟨by rw [blocksAt, Finset.mem_filter]; exact ⟨hqids, hqround⟩, hqref⟩
  have hcount := conflicting_voters_le (voters := voters D l) (parents := parentSet D b)
    (conflicting := voters D l') hfast hbyz (not_voter_of_conflicting hconf)
  have hle : (parentsVoting D b l').card ≤ (parentSet D b ∩ voters D l').card :=
    Finset.card_le_card hsub
  omega

/-- **A block that exposes a validator's equivocation drops it**:
validity's first clause fails at `w`, so the second holds and `w`'s
block is not a parent. -/
theorem exposed_not_parent {b : BlockId} (hb : b ∈ D.ids) {w : Validator}
    (hexp : ExposesEquivocationBy D b w) : w ∉ parentSet D b := by
  obtain ⟨l, hl, l', hl', hconf, hlead, ⟨v, hv⟩, ⟨v', hv'⟩⟩ := hexp
  rcases (D.valid b hb).leader_clause w with hcons | hdrop
  · -- the parents vote for two of the leader's blocks, so they are not
    -- leader-consistent, contradicting the first clause
    exfalso
    simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv hv'
    obtain ⟨q, ⟨hq, hqref⟩, -⟩ := hv
    obtain ⟨q', ⟨hq', hq'ref⟩, -⟩ := hv'
    exact hconf.1 (hcons q hq q' hq' l hqref l' hq'ref hlead (by rw [← hconf.2.2]; exact hlead))
  · intro hmem
    simp only [parentSet, mem_creatorsOf] at hmem
    obtain ⟨i, hi, hiv⟩ := hmem
    exact hdrop i hi hiv

/-- **The `f − 1` bound**: the equivocator is Byzantine and not a
parent, so at most `f − 1` of the parents are Byzantine. -/
theorem parents_byzantine_lt {b : BlockId} {w : Validator}
    (hb : b ∈ D.ids) (hexp : ExposesEquivocationBy D b w) :
    (parentSet D b ∩ F.byzantine).card + 1 ≤ F.f := by
  obtain ⟨l, hl, l', hl', hconf, hlead, hv, hv'⟩ := hexp
  have hbyz : w ∈ F.byzantine := by
    have := byzantine_of_conflicting hl hl' hconf
    rw [hlead] at this
    simpa using this
  have hnot := exposed_not_parent hb ⟨l, hl, l', hl', hconf, hlead, hv, hv'⟩
  have hsub : parentSet D b ∩ F.byzantine ⊆ F.byzantine.erase w := by
    intro x hx
    rw [Finset.mem_inter] at hx
    refine Finset.mem_erase.2 ⟨fun h => hnot (h ▸ hx.1), hx.2⟩
  have hcard := Finset.card_le_card hsub
  have herase := Finset.card_erase_of_mem hbyz
  have := F.card_byzantine
  have hpos : 1 ≤ F.byzantine.card := Finset.card_pos.2 ⟨_, hbyz⟩
  omega

/-- **Lemma 4.** If `n − p` distinct validators vote for a leader block
`l` of round `r`, every round-`(r+2)` block is FP-evidence for `l`. Both
branches of the definition are met, and no schedule is needed: the rule
reads the equivocation at `l`'s own author. -/
theorem lemma4 {b l : BlockId}
    (hb : b ∈ D.ids) (_hl : l ∈ D.ids)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hfast : FastCommit D l) :
    FPEvidence D b l := by
  simp only [FPEvidence]
  by_cases hexp : ExposesEquivocationBy D b (D.block l).creator
  · rw [if_pos hexp]
    have hbyz := parents_byzantine_lt hb hexp
    exact ⟨fpEvidence_equivocating hb hround hfast hbyz,
      fun l' _ hconf => conflicting_parents_lt hb hround hconf hfast hbyz⟩
  · rw [if_neg hexp]
    exact fpEvidence_nonequivocating hb hround hfast

end FinWhale

end LeanDag
