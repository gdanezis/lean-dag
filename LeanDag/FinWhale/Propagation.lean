import LeanDag.FinWhale.Skip
/-!
# FinWhale — Lemmas 3 and 5, the evidence reaching upward

Once a leader block is committed, its evidence must survive into every
later block's history, or a later anchor could skip past it. Lemma 3
gets there for the slow path by quorum intersection, one round at a
time; Lemma 5 gets there for the fast path without intersection, since
Lemma 4 leaves no round-`(r+2)` block that is not evidence.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- A block above genesis has a parent: validity gives it `n − f`, and
`n − f` is positive. -/
theorem exists_parent {c : BlockId} (hc : c ∈ D.ids) (hround : 0 < (D.block c).round) :
    ∃ q, q ∈ (D.block c).refs := by
  have hq := (D.valid c hc).quorum hround
  have := params_arith (Validator := Validator)
  have hpos : 0 < (creators D.block (D.block c)).card := by
    have hp : P.p ≤ Fintype.card Validator := by
      have := Finset.card_le_univ (F.byzantine); omega
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  simp only [creators, mem_creatorsOf] at hv
  obtain ⟨q, hq', -⟩ := hv
  exact ⟨q, hq'⟩

/-- **Lemma 3, one round up.** A round-`(r+3)` block references one of the
`2f + p` SP-certificates for `l`. -/
theorem references_spCertificate {c l : BlockId}
    (hc : c ∈ D.ids) (hround : (D.block c).round = (D.block l).round + 3)
    {certs : Finset Validator} (hcert : spQuorum Validator ≤ certs.card)
    (hcertb : ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l) :
    ∃ b ∈ (D.block c).refs, SPCertificate D b l := by
  have hpar : quorumCard Validator ≤ (parentSet D c).card :=
    (D.valid c hc).quorum (by omega)
  have hmeet := card_add_card_le_card_inter_add_card (parentSet D c) certs
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ (parentSet D c ∩ certs).card := by
    simp only [spQuorum] at hcert; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hv
  obtain ⟨q, hq, hqv⟩ := mem_creatorsOf.1 hv.1
  obtain ⟨b, hb, hbv, hbcert⟩ := hcertb v hv.2
  simp only [blocksAt, Finset.mem_filter] at hb
  -- the parent and the certificate are one block, by `no_equivocation`
  have hqids : q ∈ D.ids := D.complete c hc q hq
  have hqround : (D.block q).round = (D.block l).round + 2 := by
    have := parent_round hc hq; omega
  have heq : q = b :=
    D.no_equivocation q hqids b hb.1 (by rw [hqv]; exact hvc) (by rw [hqv, hbv])
      (by rw [hqround, hb.2])
  exact ⟨q, hq, heq ▸ hbcert⟩

/-- **Lemma 3.** Every block above round `r + 2` reaches an SP-certificate
for `l` from round `r + 2`. -/
theorem reaches_spCertificate {l : BlockId} {certs : Finset Validator}
    (hcert : spQuorum Validator ≤ certs.card)
    (hcertb : ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l) :
    ∀ k : ℕ, ∀ c ∈ D.ids, (D.block c).round = (D.block l).round + 3 + k →
      ∃ b, ReachesFrom D.block c b ∧ SPCertificate D b l := by
  intro k
  induction k with
  | zero =>
    intro c hc hround
    obtain ⟨b, hb, hbcert⟩ := references_spCertificate hc (by omega) hcert hcertb
    exact ⟨b, ReachesFrom.single hb, hbcert⟩
  | succ k ih =>
    intro c hc hround
    obtain ⟨q, hq⟩ := exists_parent hc (by omega)
    have hqids : q ∈ D.ids := D.complete c hc q hq
    have hqround : (D.block q).round = (D.block l).round + 3 + k := by
      have := parent_round hc hq; omega
    obtain ⟨b, hreach, hbcert⟩ := ih q hqids hqround
    exact ⟨b, ReachesFrom.of_mem_refs hq hreach, hbcert⟩

/-- **Lemma 5.** Under a fast commit for `l`, a round-`(r+3)` block's
parents are all FP-evidence for `l`, and validity gives it `n − f` of
them. No intersection argument is needed: Lemma 4 leaves no round-`(r+2)`
block that is not evidence. -/
theorem parents_all_fpEvidence {c l : BlockId}
    (hc : c ∈ D.ids) (hl : l ∈ D.ids)
    (hround : (D.block c).round = (D.block l).round + 3)
    (hfast : FastCommit D l) :
    quorumCard Validator ≤ (parentSet D c).card ∧
      ∀ q ∈ (D.block c).refs, FPEvidence D q l := by
  refine ⟨(D.valid c hc).quorum (by omega), fun q hq => ?_⟩
  have hqids : q ∈ D.ids := D.complete c hc q hq
  have hqround : (D.block q).round = (D.block l).round + 2 := by
    have := parent_round hc hq; omega
  exact lemma4 hqids hl hqround hfast

/-- **Descent.** A block reaches a block of its own view at every round
below its own. The `k`-fold step is the same one `reaches_spCertificate`
takes: validity gives a parent one round down, and the view is closed
under references. -/
theorem reaches_round : ∀ k : ℕ, ∀ c ∈ D.ids, ∀ t : ℕ, (D.block c).round = t + k →
    ∃ b, b ∈ D.ids ∧ ReachesFrom D.block c b ∧ (D.block b).round = t := by
  intro k
  induction k with
  | zero => intro c hc t hround; exact ⟨c, hc, ReachesFrom.refl, by omega⟩
  | succ k ih =>
    intro c hc t hround
    obtain ⟨q, hq⟩ := exists_parent hc (by omega)
    have hqids : q ∈ D.ids := D.complete c hc q hq
    have hqround : (D.block q).round = t + k := by
      have := parent_round hc hq; omega
    obtain ⟨b, hb, hreach, hbr⟩ := ih q hqids t hqround
    exact ⟨b, hb, ReachesFrom.of_mem_refs hq hreach, hbr⟩

/-- **Lemma 5, at any height.** Under a fast commit for `l`, every block
at round `r + 3` or above reaches `n − f` round-`(r+2)` blocks, from
distinct validators, all FP-evidence for `l` — reached by descending to
round `r + 3` first, where Lemma 5 applies directly. -/
theorem reaches_fpEvidence_quorum {c l : BlockId} (hc : c ∈ D.ids) (hl : l ∈ D.ids)
    (hround : (D.block l).round + 3 ≤ (D.block c).round)
    (hfast : FastCommit D l) :
    ∃ ev : Finset Validator, quorumCard Validator ≤ ev.card ∧
      ∀ v ∈ ev, ∃ b ∈ blocksAt D ((D.block l).round + 2),
        ReachesFrom D.block c b ∧ (D.block b).creator = v ∧ FPEvidence D b l := by
  obtain ⟨d, hd, hreach, hdr⟩ :=
    reaches_round ((D.block c).round - ((D.block l).round + 3)) c hc
      ((D.block l).round + 3) (by omega)
  obtain ⟨hqcard, hall⟩ := parents_all_fpEvidence hd hl hdr hfast
  refine ⟨parentSet D d, hqcard, ?_⟩
  intro v hv
  obtain ⟨q, hq, hqv⟩ := mem_creatorsOf.1 hv
  have hqids : q ∈ D.ids := D.complete d hd q hq
  have hqround : (D.block q).round = (D.block l).round + 2 := by
    have := parent_round hd hq; omega
  refine ⟨q, ?_, ReachesFrom.trans hreach (ReachesFrom.single hq), hqv, hall q hq⟩
  simp only [blocksAt, Finset.mem_filter]
  exact ⟨hqids, hqround⟩

/-- The same, at the slow path's quorum, which is what the indirect rule
reads. -/
theorem reaches_fpEvidence_spQuorum {c l : BlockId} (hc : c ∈ D.ids) (hl : l ∈ D.ids)
    (hround : (D.block l).round + 3 ≤ (D.block c).round)
    (hfast : FastCommit D l) :
    ∃ ev : Finset Validator, spQuorum Validator ≤ ev.card ∧
      ∀ v ∈ ev, ∃ b ∈ blocksAt D ((D.block l).round + 2),
        ReachesFrom D.block c b ∧ (D.block b).creator = v ∧ FPEvidence D b l := by
  obtain ⟨ev, hev, hevb⟩ := reaches_fpEvidence_quorum hc hl hround hfast
  exact ⟨ev, le_trans (spQuorum_le_quorumCard (Validator := Validator)) hev, hevb⟩

/-- **An SP-certificate sits two rounds above what it certifies.** Its
parents that vote for `l` are one round below it and one round above `l`,
and it has at least one. -/
theorem spCertificate_round {b l : BlockId} (hb : b ∈ D.ids)
    (hcert : SPCertificate D b l) : (D.block b).round = (D.block l).round + 2 := by
  have hpos : 0 < (parentsVoting D b l).card := by
    have := params_arith (Validator := Validator)
    simp only [SPCertificate, spQuorum] at hcert; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv
  obtain ⟨q, ⟨hq, hql⟩, -⟩ := hv
  have h1 := parent_round hb hq
  have h2 := parent_round (D.complete b hb q hq) hql
  omega

end FinWhale

end LeanDag
