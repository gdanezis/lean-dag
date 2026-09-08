import LeanDag.FinWhale.Consequences
import LeanDag.FinWhale.Model.Skip
/-!
# FinWhale — why a commit rules the skip out

Lemmas 6 and 7 say a commit and a skip cannot both happen, by two
counting arguments over `Model/Skip.lean`'s rule. The slow-path side is
quorum intersection over validators (`no_skip_of_quorum`). The fast-path
side needs a *correct* author in the intersection, not merely a distinct
one, since a Byzantine author could write one block of each kind
(`no_skip_of_fpEvidence`) — the margin is exactly one validator wide.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- **No correct validator both votes and declines.** Its round-`(r+1)`
block is one block, and either references `l` or does not. -/
theorem not_nonVoter_of_voter {l : BlockId} :
    ∀ v ∈ voters D l, v ∈ (Correct : Finset Validator) → v ∉ nonVoters D l :=
  fun _ hv hcorr hnv => not_mem_of_supports_of_blames D.noEquivOn_honest hv hnv hcorr

/-- **Lemma 6, the slow-path side.** A quorum of votes for `l` and a
quorum declining to vote for it cannot both exist: they meet in a correct
validator, which does one or the other. -/
theorem no_skip_of_quorum {l : BlockId}
    (hvote : spQuorum Validator ≤ (voters D l).card)
    (hskip : SPSkip D l) : False := by
  have hmeet := card_add_card_le_card_inter_add_card (voters D l) (nonVoters D l)
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ (voters D l ∩ nonVoters D l).card := by
    simp only [SPSkip, spQuorum] at hvote hskip; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hv
  exact not_nonVoter_of_voter v hv.1 hvc hv.2

/-- **Lemma 6, the fast-path side.** A quorum of FP-evidence blocks for
`l` and a quorum of Non-FP-evidence blocks cannot both exist: the counts
meet in `f + 1` authors, and a correct one among them writes a single
round-`(r+2)` block that cannot be both. -/
theorem no_skip_of_fpEvidence {l : BlockId} {slot : Finset BlockId}
    (hl : l ∈ slot) {ev nonev : Finset Validator}
    (hev : spQuorum Validator ≤ ev.card) (hnon : spQuorum Validator ≤ nonev.card)
    (hevb : ∀ v ∈ ev, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ FPEvidence D b l)
    (hnonb : ∀ v ∈ nonev, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ NonFPEvidence D b slot) : False := by
  have hmeet := card_add_card_le_card_inter_add_card ev nonev
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ (ev ∩ nonev).card := by
    simp only [spQuorum] at hev hnon; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hv
  obtain ⟨b, hb, hbv, hbev⟩ := hevb v hv.1
  obtain ⟨b', hb', hb'v, hb'non⟩ := hnonb v hv.2
  -- a correct author's round-`(r+2)` block is one block
  simp only [blocksAt, Finset.mem_filter] at hb hb'
  have heq : b = b' :=
    D.no_equivocation b hb.1 b' hb'.1 (by rw [hbv]; exact hvc) (by rw [hbv, hb'v])
      (by rw [hb.2, hb'.2])
  exact hb'non l hl (heq ▸ hbev)

/-- **Lemma 7's fast-path premise.** Under a fast commit, every
round-`(r+2)` block is FP-evidence for the committed block, so no
round-`(r+2)` block is Non-FP-evidence for its slot. The skip rule's
second condition is then unsatisfiable, whatever the first says. -/
theorem no_nonFPEvidence_of_fastCommit {b l : BlockId} {slot : Finset BlockId}
    (hb : b ∈ D.ids) (hl : l ∈ D.ids) (hlslot : l ∈ slot)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hfast : FastCommit D l) :
    ¬ NonFPEvidence D b slot :=
  fun hnon => hnon l hlslot (lemma4 hb hl hround hfast)

end FinWhale

end LeanDag
