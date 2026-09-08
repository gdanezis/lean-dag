import LeanDag.FinWhale.Propagation
import LeanDag.FinWhale.Model.Decision
import LeanDag.Common.Anchored
/-!
# FinWhale — what a direct verdict excludes

Lemma 12 splits on whether a validator decided **directly**; this file
settles that branch, `Consistency.lean` the anchored one. Every direct
commit carries a quorum of round-`(r+1)` voters, which excludes another
commit for a conflicting block (Lemma 8) and the SP-skip half of the
skip rule (Lemma 6) — the relation's `commit_unique` and `commit_skip`.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Slots Validator}

/-- **A slot's blocks are its candidates**: the shared `IsLeaderBlock`. -/
theorem mem_slotBlocks {b : BlockId} {n : ℕ} :
    b ∈ slotBlocks S D n ↔ IsLeaderBlock D n b := mem_leaderBlocksAt

/-- Naming the witnesses is a restriction, not a weakening. -/
theorem spCommit_of_spCommitBy {l : BlockId} {T : Finset Validator}
    (h : SPCommitBy D l T) : SPCommit D l := by
  obtain ⟨certs, -, hcard, hcertb⟩ := h
  exact ⟨certs, hcard, hcertb⟩

/-- **An SP-certificate exhibits the voters it certifies.** Its parents
voting for `l` are round-`(r+1)` blocks referencing `l`, so a certificate
carries a quorum of voters with it. -/
theorem voters_of_spCertificate {b l : BlockId} (hb : b ∈ D.ids)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hcert : SPCertificate D b l) :
    spQuorum Validator ≤ (voters D l).card := by
  refine le_trans hcert (Finset.card_le_card ?_)
  intro v hv
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  have hqids : q ∈ D.ids := D.complete b hb q hq
  have hqround : (D.block q).round = (D.block l).round + 1 := by
    have := parent_round hb hq; omega
  refine mem_creatorsOf.2 ⟨q, ?_, hqv⟩
  rw [votesFor, Finset.mem_filter]
  exact ⟨by rw [blocksAt, Finset.mem_filter]; exact ⟨hqids, hqround⟩, hqref⟩

/-- **Every direct commit carries a quorum of voters.** The fast path by
its threshold, the slow path through its certificates. -/
theorem voters_of_directCommit {l : BlockId} (hcom : DirectCommit D l) :
    spQuorum Validator ≤ (voters D l).card := by
  rcases hcom with hfast | ⟨certs, hcard, hcerts⟩
  · exact spQuorum_le_of_fastCommit hfast
  · have hpos : 0 < certs.card := by
      have := params_arith (Validator := Validator)
      simp only [spQuorum] at hcard; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    obtain ⟨b, hb, -, hcert⟩ := hcerts v hv
    simp only [blocksAt, Finset.mem_filter] at hb
    exact voters_of_spCertificate hb.1 hb.2 hcert

/-- **Corollary 11, the direct half.** Two blocks of one slot cannot both
be directly committed. -/
theorem direct_commit_unique {r : ℕ} {l l' : BlockId}
    (hl : l ∈ slotBlocks S D r) (hl' : l' ∈ slotBlocks S D r)
    (hcom : DirectCommit D l) (hcom' : DirectCommit D l') : l = l' := by
  by_contra hne
  rw [mem_slotBlocks] at hl hl'
  exact lemma8 ⟨hne, by rw [hl.2.1, hl'.2.1], by rw [hl.2.2, hl'.2.2]⟩
    (voters_of_directCommit hcom) (voters_of_directCommit hcom')

/-- **Lemma 6 and Lemma 7, the direct half.** A slot with a directly
committed block is not directly skipped. The SP-skip half of the rule is
already unsatisfiable, so the FP-evidence half is not needed. -/
theorem no_directSkip_of_commit {r : ℕ} {l : BlockId}
    (hl : l ∈ slotBlocks S D r) (hcom : DirectCommit D l) : ¬ DirectSkip S D r := by
  rintro ⟨hskip, -⟩
  exact no_skip_of_quorum (voters_of_directCommit hcom) (hskip l hl)

end FinWhale

end LeanDag
