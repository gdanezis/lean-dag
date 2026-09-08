import LeanDag.FinWhale.Decision
import LeanDag.FinWhale.Model.Anchor
/-!
# FinWhale — the anchor, and why its tie-break is safe

The indirect rule commits a slot from a committed **anchor** above it:
either the anchor reaches an SP-certificate for a block of the slot, or
it reaches a quorum of FP-evidence blocks for one. The paper notes that
both conditions may hold at once for *conflicting* blocks, and resolves
that "according to a deterministic rule".

That is the shape of the defect the Black Marlin arc found (§18): a
support-blind deterministic choice among an equivocator's twins. FinWhale
escapes it, and this file is why.

**The tie-break's input is the anchor's causal history, and nothing
else.** `IndirectCommit` is a predicate of the anchor, the slot and the
candidate block — no view appears in it. A validator holding the anchor
holds everything the anchor reaches, since views are closed under
references (`indirect_view_independent`), so two validators that commit
the same anchor feed the same data to the same rule. Black Marlin's
descent failed because the two validators descended from *different*
anchors; FinWhale's cannot, once the anchors agree.

**And the conflicting pattern only arises where nobody could decide
directly.** A direct commit of `b` rules out an indirect commit of any
conflicting `b'` (`no_indirectCommit_of_directCommit`), and a direct skip
rules out an indirect commit altogether
(`no_indirectCommit_of_directSkip`). Those are the paper's two claims,
and both are proved here from Lemma 8 and Lemma 4.

What remains for Lemma 12 is that the anchors agree, which is the
maximality induction and is stated in `Consistency.lean`.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Slots Validator}

/-- **And they are the same condition**, for an anchor of the DAG. -/
theorem indirectCommitOn_iff {A : BlockId} (hA : A ∈ D.ids) {r : ℕ} {b : BlockId} :
    IndirectCommitOn S D A r b ↔ IndirectCommit S D A r b := by
  have hiff : ∀ c, c ∈ historyFrom D.block A ↔ ReachesFrom D.block A c := fun c =>
    (causalStructure D).mem_history_iff hA
  constructor
  · rintro ⟨hb, hroute⟩
    refine ⟨hb, ?_⟩
    rcases hroute with ⟨c, hc, hreach, hcert⟩ | ⟨ev, hev, hevb⟩
    · exact Or.inl ⟨c, hc, (hiff c).1 hreach, hcert⟩
    · refine Or.inr ⟨ev, hev, fun v hv => ?_⟩
      obtain ⟨c, hc, hreach, hcv, hfp⟩ := hevb v hv
      exact ⟨c, hc, (hiff c).1 hreach, hcv, hfp⟩
  · rintro ⟨hb, hroute⟩
    refine ⟨hb, ?_⟩
    rcases hroute with ⟨c, hc, hreach, hcert⟩ | ⟨ev, hev, hevb⟩
    · exact Or.inl ⟨c, hc, (hiff c).2 hreach, hcert⟩
    · refine Or.inr ⟨ev, hev, fun v hv => ?_⟩
      obtain ⟨c, hc, hreach, hcv, hfp⟩ := hevb v hv
      exact ⟨c, hc, (hiff c).2 hreach, hcv, hfp⟩

/-- **The tie-break reads only the anchor.** A validator whose view holds
the anchor holds every block the anchor reaches, so the whole condition
is evaluable there and gives the same answer as anywhere else. This is
what Black Marlin's descent lacked: there the input differed because the
anchors differed. -/
theorem indirect_view_independent {A : BlockId} {S : Finset BlockId}
    (hS : ∀ i ∈ S, ∀ j ∈ (D.block i).refs, j ∈ S) (hA : A ∈ S)
    {c : BlockId} (hreach : ReachesFrom D.block A c) : c ∈ S :=
  mem_of_reaches_of_closed hS hA hreach

/-- **A direct commit rules out an indirect commit of a conflicting
block.** Either route to `b'` would need a quorum of validators behind
it: an SP-certificate carries a quorum of voters, which Lemma 8 forbids
beside `b`'s; and a quorum of FP-evidence blocks for `b'` is impossible
under a fast commit for `b`, since no round-`(r+2)` block is FP-evidence
for a conflicting block at all. -/
theorem no_indirectCommit_of_fastCommit {A : BlockId} {r : ℕ} {b b' : BlockId}
    (hb : b ∈ D.ids) (hb' : b' ∈ D.ids) (hbslot : b ∈ slotBlocks S D r)
    (hconf : Conflicting D b b') (hfast : FastCommit D b) :
    ¬ IndirectCommit S D A r b' := by
  have hbround : (D.block b).round = S.slotRound r := by
    rw [mem_slotBlocks] at hbslot; exact hbslot.2.1
  rintro ⟨-, hroute⟩
  rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
  · -- an SP-certificate for `b'` carries a quorum of voters for `b'`
    simp only [blocksAt, Finset.mem_filter] at hc
    exact lemma8 hconf (spQuorum_le_of_fastCommit hfast)
      (voters_of_spCertificate hc.1 (by rw [hc.2, ← hconf.2.1, hbround]) hcert)
  · -- a quorum of FP-evidence blocks for `b'` cannot exist under a fast
    -- commit for `b`, since no round-`(r+2)` block is FP-evidence for a
    -- block conflicting with the fast-committed one
    have hpos : 0 < ev.card := by
      have := params_arith (Validator := Validator)
      simp only [spQuorum] at hev; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    obtain ⟨c, hc, -, -, hfp⟩ := hevb v hv
    simp only [blocksAt, Finset.mem_filter] at hc
    exact not_fpEvidence_conflicting hc.1 hb hb' (by rw [hc.2, hbround]) hconf hfast hfp

/-- **A direct skip rules out an indirect commit.** Either route needs a
quorum the skip pattern denies: an SP-certificate carries a quorum of
voters against the SP-skip half, and a quorum of FP-evidence blocks meets
the quorum of Non-FP-evidence blocks in a correct author, whose single
round-`(r+2)` block cannot be both. -/
theorem no_indirectCommit_of_directSkip {A : BlockId} {r : ℕ} {b : BlockId}
    (hskip : DirectSkip S D r) : ¬ IndirectCommit S D A r b := by
  obtain ⟨hsp, nonev, hnon, hnonb⟩ := hskip
  rintro ⟨hbslot, hroute⟩
  have hbround : (D.block b).round = S.slotRound r := by
    rw [mem_slotBlocks] at hbslot; exact hbslot.2.1
  rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
  · simp only [blocksAt, Finset.mem_filter] at hc
    exact no_skip_of_quorum
      (voters_of_spCertificate hc.1 (by rw [hc.2, hbround]) hcert) (hsp b hbslot)
  · have hevb' : ∀ v ∈ ev, ∃ c ∈ blocksAt D ((D.block b).round + 2),
        (D.block c).creator = v ∧ FPEvidence D c b := by
      intro v hv
      obtain ⟨c, hc, -, hcv, hfp⟩ := hevb v hv
      exact ⟨c, by rw [hbround]; exact hc, hcv, hfp⟩
    have hnonb' : ∀ v ∈ nonev, ∃ c ∈ blocksAt D ((D.block b).round + 2),
        (D.block c).creator = v ∧ NonFPEvidence D c (slotBlocks S D r) := by
      intro v hv
      obtain ⟨c, hc, hcv, hnonfp⟩ := hnonb v hv
      exact ⟨c, by rw [hbround]; exact hc, hcv, hnonfp⟩
    exact no_skip_of_fpEvidence hbslot hev hnon hevb' hnonb'

/-- **A direct commit is visible from every anchor above it.** This is
Lemma 7's indirect half: whichever path committed `l` directly leaves a
trail that any block at round `r + 3` or above reaches — a quorum of
FP-evidence blocks under the fast path, an SP-certificate under the slow
one. So the anchor's rule always has a candidate to name. -/
theorem indirectCommit_of_directCommit {A : BlockId} {r : ℕ} {l : BlockId}
    (hA : A ∈ D.ids) (hAround : S.slotRound r + 3 ≤ (D.block A).round)
    (hl : l ∈ slotBlocks S D r) (hcom : DirectCommit D l) :
    IndirectCommit S D A r l := by
  have hl' := hl
  rw [mem_slotBlocks] at hl'
  obtain ⟨hlids, hlround, -⟩ := hl'
  refine ⟨hl, ?_⟩
  rcases hcom with hfast | hsp
  · refine Or.inr ?_
    obtain ⟨ev, hev, hevb⟩ := reaches_fpEvidence_spQuorum hA hlids (by omega) hfast
    refine ⟨ev, hev, fun v hv => ?_⟩
    obtain ⟨b, hb, hreach, hbv, hfp⟩ := hevb v hv
    exact ⟨b, by rw [hlround] at hb; exact hb, hreach, hbv, hfp⟩
  · refine Or.inl ?_
    obtain ⟨certs, hcerts, hcertb⟩ := hsp
    obtain ⟨b, hreach, hbcert⟩ :=
      reaches_spCertificate hcerts hcertb ((D.block A).round - ((D.block l).round + 3))
        A hA (by omega)
    have hbids : b ∈ D.ids :=
      mem_of_reaches_of_closed (fun i hi j hj => D.complete i hi j hj) hA hreach
    refine ⟨b, ?_, hreach, hbcert⟩
    simp only [blocksAt, Finset.mem_filter]
    exact ⟨hbids, by rw [spCertificate_round hbids hbcert, hlround]⟩

/-- **A slow-path commit rules out an indirect commit of a conflicting
block.** An SP-certificate for the conflicting block would carry a second
quorum of voters, which Lemma 8 forbids. A quorum of FP-evidence blocks
for it meets the quorum of SP-certificates in a correct validator, whose
single round-`(r+2)` block would have to be both. -/
theorem no_indirectCommit_of_spCommit {A : BlockId} {r : ℕ} {b b' : BlockId}
    (hb : b ∈ D.ids) (hb' : b' ∈ D.ids) (hbslot : b ∈ slotBlocks S D r)
    (hconf : Conflicting D b b') (hsp : SPCommit D b) :
    ¬ IndirectCommit S D A r b' := by
  have hbround : (D.block b).round = S.slotRound r := by
    rw [mem_slotBlocks] at hbslot; exact hbslot.2.1
  obtain ⟨certs, hcerts, hcertb⟩ := hsp
  rintro ⟨-, hroute⟩
  rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
  · simp only [blocksAt, Finset.mem_filter] at hc
    exact lemma8 hconf (voters_of_directCommit (Or.inr ⟨certs, hcerts, hcertb⟩))
      (voters_of_spCertificate hc.1 (by rw [hc.2, ← hconf.2.1, hbround]) hcert)
  · -- the two quorums meet in a correct validator
    have hmeet := card_add_card_le_card_inter_add_card certs ev
    have := params_arith (Validator := Validator)
    have hcard : F.f + 1 ≤ (certs ∩ ev).card := by
      simp only [spQuorum] at hcerts hev; omega
    obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
    rw [Finset.mem_inter] at hv
    obtain ⟨c₁, hc₁, hc₁v, hc₁cert⟩ := hcertb v hv.1
    obtain ⟨c₂, hc₂, -, hc₂v, hc₂fp⟩ := hevb v hv.2
    simp only [blocksAt, Finset.mem_filter] at hc₁ hc₂
    have heq : c₁ = c₂ :=
      D.no_equivocation c₁ hc₁.1 c₂ hc₂.1 (by rw [hc₁v]; exact hvc) (by rw [hc₁v, hc₂v])
        (by rw [hc₁.2, hc₂.2, hbround])
    exact not_fpEvidence_of_spCertificate hb hb' hconf hc₁cert (heq ▸ hc₂fp)

/-- **A direct commit rules out an indirect commit of a conflicting
block**, by either path. -/
theorem no_indirectCommit_of_directCommit {A : BlockId} {r : ℕ} {b b' : BlockId}
    (hb : b ∈ D.ids) (hb' : b' ∈ D.ids) (hbslot : b ∈ slotBlocks S D r)
    (hconf : Conflicting D b b') (hcom : DirectCommit D b) :
    ¬ IndirectCommit S D A r b' := by
  rcases hcom with hfast | hsp
  · exact no_indirectCommit_of_fastCommit hb hb' hbslot hconf hfast
  · exact no_indirectCommit_of_spCommit hb hb' hbslot hconf hsp

end FinWhale

end LeanDag
