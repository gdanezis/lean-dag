import LeanDag.FinWhale.Decided
import LeanDag.FinWhale.Model.View
import LeanDag.FinWhale.Consistency
/-!
# FinWhale — views, and the direct rules relative to one

The direct rules are evaluated on the validator's own sub-DAG. This
file proves what relates them to the universe — a view's direct verdict
is one of the universe, and, for liveness, the universe's direct commit
is one of the view (`hsees`) — and assembles FinWhale's laws for the
anchored relation from them.

A **view** is a reference-closed subset of the universe's blocks, and it
is a `Dag` in its own right: validity and non-equivocation are inherited,
and closure is its completeness. `restrict` builds it.

Three facts make the transfer work.

**Most of the vocabulary does not read the population at all.**
`parentsVoting`, `parentSet` and `SPCertificate` are computed from a
block's references, so they are the same in a view as in the universe.

**Closure carries a block into the view whenever anything in the view
votes for it.** `mem_view_of_parentsVoting` is the immediate form, and
`mem_view_of_voters` is the counting form: a view holding a single
round-`(r+2)` block holds every block a quorum of round-`(r+1)`
validators votes for, because that block's `n − f` parents meet the
quorum in a correct author.

**And so FP-evidence is view-independent.** Its equivocation test
quantifies over the population, but the blocks it can find are voted for
by the block's own parents, hence in any view holding the block.

The skip rule is where the two directions part. Its first condition
quantifies over the slot's blocks *as the view sees them*, so a view's
skip is not a skip of the universe, and the exclusions it takes part in
have to be proved directly — `no_directSkip_of_commit_view` and
`no_indirectCommit_of_directSkip_view` below. Both run through the second
condition, the quorum of Non-FP-evidence blocks, which is what makes the
missing block visible. The same quorum is what makes the skip grow with
the view (`directSkip_mono`): a candidate a larger view adds is
referenced by no block of the smaller one, so the no-evidence blocks'
parents all decline to vote for it and none of them is evidence for it.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {Elig : ℕ → ℕ → Prop}
variable {D : Dag Validator BlockId Payload} {V : D.View}
variable {S : Slots Validator}

/-- The population shrinks, so a round's blocks do. -/
theorem blocksAt_restrict {r : ℕ} : blocksAt (V.toRecord) r ⊆ blocksAt D r := by
  intro b hb
  simp only [blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter] at hb ⊢
  exact ⟨V.subset_ids hb.1, hb.2⟩

/-- And so does a slot's. -/
theorem slotBlocks_restrict {r : ℕ} : slotBlocks S (V.toRecord) r ⊆ slotBlocks S D r := by
  intro b hb
  simp only [slotBlocks, Finset.mem_filter] at hb ⊢
  exact ⟨blocksAt_restrict hb.1, hb.2⟩

/-- Membership form. -/
theorem slotBlocks_restrict' {r : ℕ} {b : BlockId} (h : b ∈ slotBlocks S (V.toRecord) r) :
    b ∈ slotBlocks S D r := slotBlocks_restrict h

/-- A candidate of the universe the view holds is a candidate of the
view. -/
theorem mem_slotBlocks_view {r : ℕ} {b : BlockId} (hb : b ∈ V.ids)
    (h : b ∈ slotBlocks S D r) : b ∈ slotBlocks S (V.toRecord) r := by
  simp only [slotBlocks, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block,
    Finset.mem_filter] at h ⊢
  exact ⟨⟨hb, h.1.2⟩, h.2⟩

/-- Fewer blocks, fewer voters. -/
theorem voters_restrict {l : BlockId} : voters (V.toRecord) l ⊆ voters D l := by
  intro v hv
  simp only [voters, supporters, votesFor, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  exact ⟨q, ⟨blocksAt_restrict hq, hqref⟩, hqv⟩

/-- And fewer validators declining to vote. -/
theorem nonVoters_restrict {l : BlockId} : nonVoters (V.toRecord) l ⊆ nonVoters D l := by
  intro v hv
  simp only [nonVoters, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  exact ⟨q, ⟨blocksAt_restrict hq, hqref⟩, hqv⟩

/-- **What a block's parents say is view-independent.** -/
@[simp] theorem parentsVoting_restrict {b l : BlockId} :
    parentsVoting (V.toRecord) b l = parentsVoting D b l := rfl

/-- So an SP-certificate is a certificate in either reading. -/
@[simp] theorem spCertificate_restrict {b l : BlockId} :
    SPCertificate (V.toRecord) b l ↔ SPCertificate D b l := Iff.rfl

/-- **Closure, in its immediate form.** A view holding a block holds
everything the block's parents vote for. -/
theorem mem_view_of_parentsVoting {b l : BlockId} (hb : b ∈ V.ids)
    (h : (parentsVoting D b l).Nonempty) : l ∈ V.ids := by
  obtain ⟨v, hv⟩ := h
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv
  obtain ⟨q, ⟨hq, hql⟩, -⟩ := hv
  exact V.complete q (V.complete b hb q hq) l hql

/-- **Closure, in its counting form.** A view holding one round-`(r+2)`
block holds every block a quorum of round-`(r+1)` validators votes for:
that block carries `n − f` parents, which meet the quorum in `f + p`
authors, one of them correct — and a correct author's round-`(r+1)` block
is one block, so the parent and the vote are the same block. -/
theorem mem_view_of_voters {c l : BlockId} (hc : c ∈ V.ids)
    (hcround : (D.block c).round = (D.block l).round + 2)
    (hvote : spQuorum Validator ≤ (voters D l).card) : l ∈ V.ids := by
  have hcids : c ∈ D.ids := V.subset_ids hc
  have hpar : quorumCard Validator ≤ (parentSet D c).card :=
    (D.valid c hcids).quorum (by omega)
  have hmeet := card_add_card_le_card_inter_add_card (parentSet D c) (voters D l)
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ ((parentSet D c) ∩ (voters D l)).card := by
    simp only [spQuorum] at hvote
    omega
  obtain ⟨w, hw, hwc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hw
  obtain ⟨q, hq, hqw⟩ := mem_creatorsOf.1 hw.1
  obtain ⟨q', hq', hq'w⟩ := mem_creatorsOf.1 hw.2
  rw [votesFor, Finset.mem_filter] at hq'
  simp only [blocksAt, Finset.mem_filter] at hq'
  have hqids : q ∈ D.ids := D.complete c hcids q hq
  have hqround : (D.block q).round = (D.block l).round + 1 := by
    have := parent_round hcids hq; omega
  have heq : q = q' :=
    D.no_equivocation q hqids q' hq'.1.1 (by rw [hqw]; exact hwc) (by rw [hqw, hq'w])
      (by rw [hqround, hq'.1.2])
  exact V.complete q (V.complete c hc q hq) l (heq ▸ hq'.2)

/-- **Exposing an equivocation is view-independent**, for a block the view
holds: the conflicting versions it finds are voted for by the block's own
parents, so closure puts them in the view. -/
theorem exposesBy_restrict {b : BlockId} (hb : b ∈ V.ids) (v : Validator) :
    ExposesEquivocationBy (V.toRecord) b v ↔ ExposesEquivocationBy D b v := by
  constructor
  · rintro ⟨l, hl, l', hl', hconf, hlead, h1, h2⟩
    exact ⟨l, V.subset_ids hl, l', V.subset_ids hl', hconf, hlead, h1, h2⟩
  · rintro ⟨l, -, l', -, hconf, hlead, h1, h2⟩
    exact ⟨l, mem_view_of_parentsVoting  hb h1, l',
      mem_view_of_parentsVoting  hb h2, hconf, hlead, h1, h2⟩

/-- **FP-evidence is view-independent** for a block the view holds. The
equivocating branch bounds the parents voting for anything conflicting;
a conflicting block outside the view has no such parents, and the bound
holds of it for nothing. -/
theorem fpEvidence_restrict {b l : BlockId} (hb : b ∈ V.ids) :
    FPEvidence (V.toRecord) b l ↔ FPEvidence D b l := by
  have := params_arith (Validator := Validator)
  simp only [FPEvidence, parentsVoting_restrict, BlockRecord.View.toRecord_block]
  by_cases hexp : ExposesEquivocationBy D b (D.block l).creator
  · rw [if_pos ((exposesBy_restrict hb _).2 hexp), if_pos hexp]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun l' _ hconf => ?_⟩
      rcases Finset.eq_empty_or_nonempty (parentsVoting D b l') with he | hne
      · rw [he]; simp; omega
      · exact h2 l' (mem_view_of_parentsVoting  hb hne) hconf
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l' hl' hconf => h2 l' (V.subset_ids hl') hconf⟩
  · rw [if_neg fun h => hexp ((exposesBy_restrict hb _).1 h), if_neg hexp]

/-- Every FP-evidence block has a parent voting for what it is evidence
for: both branches ask for at least `f + p − 1 ≥ 1`. -/
theorem parentsVoting_nonempty_of_fpEvidence {b l : BlockId} (h : FPEvidence D b l) :
    (parentsVoting D b l).Nonempty := by
  have := params_arith (Validator := Validator)
  rw [← Finset.card_pos]
  simp only [FPEvidence] at h
  by_cases hexp : ExposesEquivocationBy D b (D.block l).creator
  · rw [if_pos hexp] at h; omega
  · rw [if_neg hexp] at h; omega

/-! ## The direct rules, in both directions -/

/-- A view's fast commit is one of the universe. -/
theorem fastCommit_restrict {l : BlockId} (h : FastCommit (V.toRecord) l) :
    FastCommit D l :=
  le_trans h (Finset.card_le_card voters_restrict)

/-- And its slow commit. -/
theorem spCommit_restrict {l : BlockId} (h : SPCommit (V.toRecord) l) : SPCommit D l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbv, hbcert⟩ := hcerts v hv
  exact ⟨b, blocksAt_restrict hb, hbv, hbcert⟩

/-- So its direct commit is one of the universe: the condition safety
took as a hypothesis. -/
theorem directCommit_restrict {l : BlockId} (h : DirectCommit (V.toRecord) l) :
    DirectCommit D l :=
  h.imp fastCommit_restrict spCommit_restrict

/-- A view's SP-skip is one of the universe: it counts validators
declining to vote, and the view has fewer of them. -/
theorem spSkip_restrict {l : BlockId} (h : SPSkip (V.toRecord) l) : SPSkip D l :=
  le_trans h (Finset.card_le_card nonVoters_restrict)

/-- Where the view holds a whole round, it counts the same voters. -/
theorem voters_restrict_eq {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V.ids) :
    voters (V.toRecord) l = voters D l := by
  refine Finset.Subset.antisymm voters_restrict fun v hv => ?_
  simp only [voters, supporters, votesFor, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  refine ⟨q, ⟨?_, hqref⟩, hqv⟩
  simp only [blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
  simp only [blocksAt, Finset.mem_filter] at hq
  exact ⟨hV1 (by simp only [blocksAt, Finset.mem_filter]; exact hq), hq.2⟩

/-- **The liveness direction, fast path.** A view holding round `r + 1`
sees the fast commit the universe sees. -/
theorem fastCommit_of_holds {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V.ids) (h : FastCommit D l) :
    FastCommit (V.toRecord) l := by
  change fastCard Validator ≤ (voters (V.toRecord) l).card
  rw [voters_restrict_eq hV1]
  exact h

/-- **And the slow path**, for a view holding round `r + 2`. -/
theorem spCommit_of_holds {l : BlockId}
    (hV2 : blocksAt D ((D.block l).round + 2) ⊆ V.ids) (h : SPCommit D l) :
    SPCommit (V.toRecord) l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbv, hbcert⟩ := hcerts v hv
  refine ⟨b, ?_, hbv, hbcert⟩
  simp only [blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
  simp only [blocksAt, Finset.mem_filter] at hb
  exact ⟨hV2 (by simp only [blocksAt, Finset.mem_filter]; exact hb), hb.2⟩

/-- **`hsees`, discharged.** A view holding the two rounds above a slot
sees whatever direct commit the universe has there. -/
theorem directCommit_of_holds {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V.ids)
    (hV2 : blocksAt D ((D.block l).round + 2) ⊆ V.ids) (h : DirectCommit D l) :
    DirectCommit (V.toRecord) l :=
  h.imp (fastCommit_of_holds hV1) (spCommit_of_holds hV2)

/-! ## The two exclusions the skip rule needs

A view's direct skip is *not* a direct skip of the universe: its first
condition quantifies over the slot blocks the view holds, and a view
holding none of them satisfies it for nothing. Both exclusions therefore
run through the second condition, the quorum of Non-FP-evidence blocks —
which is also what forces the committed block into the view. -/

/-- **A view's direct skip is incompatible with a direct commit.** The
skip carries a quorum of round-`(r+2)` blocks, and a single one of them
already puts the committed block in the view; then either Lemma 4 or
Lemma 2 makes one of those blocks FP-evidence for it, which is what
Non-FP-evidence denies. -/
theorem no_directSkip_of_commit_view {r : ℕ} {l : BlockId}
    (hl : l ∈ slotBlocks S D r) (hcom : DirectCommit D l) :
    ¬ DirectSkip S (V.toRecord) r := by
  rintro ⟨-, nonev, hnon, hnonb⟩
  have hlu : l ∈ D.ids ∧ (D.block l).round = S.slotRound r ∧
      (D.block l).creator = S.leader r := by
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hl
    exact ⟨hl.1.1, hl.1.2, hl.2⟩
  have hvote := voters_of_directCommit hcom
  have harith := params_arith (Validator := Validator)
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨b₀, hb₀, -, hnonfp₀⟩ := hnonb v₀ hv₀
  have hb₀V : b₀ ∈ V.ids := by
    simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hb₀; exact hb₀.1
  have hb₀round : (D.block b₀).round = S.slotRound r + 2 := by
    simp only [blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hb₀; exact hb₀.2
  -- the committed block is in the view, whatever the view had seen of the slot
  have hlV : l ∈ V.ids := mem_view_of_voters  hb₀V (by rw [hb₀round, hlu.2.1]) hvote
  have hlslot : l ∈ slotBlocks S (V.toRecord) r := by
    simp only [slotBlocks, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
    exact ⟨⟨hlV, hlu.2.1⟩, hlu.2.2⟩
  rcases hcom with hfast | ⟨certs, hcerts, hcertb⟩
  · -- under a fast commit every round-`(r+2)` block is evidence (Lemma 4)
    have hfp : FPEvidence D b₀ l :=
      lemma4 (V.subset_ids hb₀V) hlu.1 (by rw [hb₀round, hlu.2.1]) hfast
    exact hnonfp₀ l hlslot ((fpEvidence_restrict hb₀V).2 hfp)
  · -- under a slow commit the two quorums meet in a correct author
    have hmeet := card_add_card_le_card_inter_add_card certs nonev
    have hcard : F.f + 1 ≤ (certs ∩ nonev).card := by
      simp only [spQuorum] at hcerts hnon; omega
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_card hcard
    rw [Finset.mem_inter] at hw
    obtain ⟨c₁, hc₁, hc₁w, hc₁cert⟩ := hcertb w hw.1
    obtain ⟨c₂, hc₂, hc₂w, hnonfp⟩ := hnonb w hw.2
    replace hc₂w : (D.block c₂).creator = w := hc₂w
    simp only [blocksAt, Finset.mem_filter] at hc₁
    have hc₂V : c₂ ∈ V.ids := by
      simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hc₂; exact hc₂.1
    have hc₂round : (D.block c₂).round = S.slotRound r + 2 := by
      simp only [blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hc₂; exact hc₂.2
    have heq : c₁ = c₂ :=
      D.no_equivocation c₁ hc₁.1 c₂ (V.subset_ids hc₂V) (by rw [hc₁w]; exact hwc)
        (by rw [hc₁w, hc₂w]) (by rw [hc₁.2, hc₂round, hlu.2.1])
    exact hnonfp l hlslot ((fpEvidence_restrict hc₂V).2 (heq ▸ lemma2 hc₁.1 hc₁cert))

/-- **A view's direct skip is incompatible with an indirect commit.**
Either route puts the candidate in the view — an SP-certificate through
the voter count, a quorum of evidence through the author the two quorums
share — and then the skip's own conditions deny it. -/
theorem no_indirectCommit_of_directSkip_view {A : BlockId} {r : ℕ} {b : BlockId}
    (hskip : DirectSkip S (V.toRecord) r) : ¬ IndirectCommit S D A r b := by
  obtain ⟨hsp, nonev, hnon, hnonb⟩ := hskip
  rintro ⟨hbslot, hroute⟩
  have harith := params_arith (Validator := Validator)
  have hbu : b ∈ D.ids ∧ (D.block b).round = S.slotRound r ∧
      (D.block b).creator = S.leader r := by
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hbslot
    exact ⟨hbslot.1.1, hbslot.1.2, hbslot.2⟩
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨b₀, hb₀, -, -⟩ := hnonb v₀ hv₀
  have hb₀V : b₀ ∈ V.ids := by
    simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hb₀; exact hb₀.1
  have hb₀round : (D.block b₀).round = S.slotRound r + 2 := by
    simp only [blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hb₀; exact hb₀.2
  -- the candidate is in the view, and so the slot's blocks include it
  have hin : b ∈ V.ids → False := by
    intro hbV
    have hbslotV : b ∈ slotBlocks S (V.toRecord) r := by
      simp only [slotBlocks, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block,   Finset.mem_filter]
      exact ⟨⟨hbV, hbu.2.1⟩, hbu.2.2⟩
    rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
    · simp only [blocksAt, Finset.mem_filter] at hc
      exact no_skip_of_quorum
        (voters_of_spCertificate hc.1 (by rw [hc.2, hbu.2.1]) hcert)
        (spSkip_restrict (hsp b hbslotV))
    · have hmeet := card_add_card_le_card_inter_add_card ev nonev
      have hcard : F.f + 1 ≤ (ev ∩ nonev).card := by
        simp only [spQuorum] at hev hnon; omega
      obtain ⟨w, hw, hwc⟩ := exists_correct_of_card hcard
      rw [Finset.mem_inter] at hw
      obtain ⟨c₁, hc₁, -, hc₁w, hc₁fp⟩ := hevb w hw.1
      obtain ⟨c₂, hc₂, hc₂w, hnonfp⟩ := hnonb w hw.2
      replace hc₂w : (D.block c₂).creator = w := hc₂w
      simp only [blocksAt, Finset.mem_filter] at hc₁
      have hc₂V : c₂ ∈ V.ids := by
        simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hc₂; exact hc₂.1
      have hc₂round : (D.block c₂).round = S.slotRound r + 2 := by
        simp only [blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hc₂; exact hc₂.2
      have heq : c₁ = c₂ :=
        D.no_equivocation c₁ hc₁.1 c₂ (V.subset_ids hc₂V) (by rw [hc₁w]; exact hwc)
          (by rw [hc₁w, hc₂w]) (by rw [hc₁.2, hc₂round])
      exact hnonfp b hbslotV ((fpEvidence_restrict hc₂V).2 (heq ▸ hc₁fp))
  -- and it is: either route exhibits a quorum behind `b`
  refine hin ?_
  rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
  · simp only [blocksAt, Finset.mem_filter] at hc
    exact mem_view_of_voters  hb₀V (by rw [hb₀round, hbu.2.1])
      (voters_of_spCertificate hc.1 (by rw [hc.2, hbu.2.1]) hcert)
  · have hevpos : 0 < ev.card := by simp only [spQuorum] at hev; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.1 hevpos
    obtain ⟨c, hc, -, -, hcfp⟩ := hevb w hw
    have hmeet := card_add_card_le_card_inter_add_card ev nonev
    have hcard : F.f + 1 ≤ (ev ∩ nonev).card := by
      simp only [spQuorum] at hev hnon; omega
    obtain ⟨w', hw', hw'c⟩ := exists_correct_of_card hcard
    rw [Finset.mem_inter] at hw'
    obtain ⟨c₁, hc₁, -, hc₁w, hc₁fp⟩ := hevb w' hw'.1
    obtain ⟨c₂, hc₂, hc₂w, -⟩ := hnonb w' hw'.2
    replace hc₂w : (D.block c₂).creator = w' := hc₂w
    simp only [blocksAt, Finset.mem_filter] at hc₁
    have hc₂V : c₂ ∈ V.ids := by
      simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hc₂; exact hc₂.1
    have hc₂round : (D.block c₂).round = S.slotRound r + 2 := by
      simp only [blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hc₂; exact hc₂.2
    have heq : c₁ = c₂ :=
      D.no_equivocation c₁ hc₁.1 c₂ (V.subset_ids hc₂V) (by rw [hc₁w]; exact hw'c)
        (by rw [hc₁w, hc₂w]) (by rw [hc₁.2, hc₂round])
    exact mem_view_of_parentsVoting  (heq ▸ hc₂V)
      (parentsVoting_nonempty_of_fpEvidence hc₁fp)

/-- **A view holding the reliable blocks sees the commits.** The liveness
interface names its certificates as reliable validators' blocks, and a
view holds those; the leader's own block is reliable too, the slot being
correct-led. Nothing is asked of the view about Byzantine authors, which
is as much as a schedule can give. -/
theorem sees_of_commits_of_held {V : D.View} {R N : ℕ}
    (hcommits : CommitsCorrectLeaders S D R N)
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V.ids) :
    SeesCommits S D (viewCommit S D V ) R N := by
  intro s hR hN hlead
  obtain ⟨l, hslot, certs, hsub, hcard, hcertb⟩ := hcommits s hR hN hlead
  have hlu : l ∈ blocksAt D (S.slotRound s) ∧ (D.block l).creator = S.leader s := by
    simp only [slotBlocks, Finset.mem_filter] at hslot
    exact hslot
  have hlround : (D.block l).round = S.slotRound s := by
    simp only [blocksAt, Finset.mem_filter] at hlu
    exact hlu.1.2
  have hlV : l ∈ V.ids := hheld (S.slotRound s) (by omega) (by omega) l hlu.1
    (by rw [hlu.2]; exact hlead)
  refine ⟨l, hslot, ?_, Or.inr ⟨certs, hcard, fun v hv => ?_⟩⟩
  · simp only [slotBlocks, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
    exact ⟨⟨hlV, hlround⟩, hlu.2⟩
  · obtain ⟨b, hb, hbc, hcert⟩ := hcertb v hv
    have hbV : b ∈ V.ids :=
      hheld ((D.block l).round + 2) (by omega) (by omega) b hb (by rw [hbc]; exact hsub hv)
    refine ⟨b, ?_, hbc, hcert⟩
    simp only [blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
    simp only [blocksAt, Finset.mem_filter] at hb
    exact ⟨hbV, hb.2⟩

/-- **Lemma 23, on a view.** A validator whose view holds the blocks up
to the horizon decides every slot below it. `hsees` is discharged by
`directCommit_of_holds`: holding the two rounds above a slot is seeing
whatever direct commit is there. -/
theorem all_decided_of_view {V : D.View}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed Elig (viewCommit S D V ) (viewSkip S D V ) choose dec) {R N r : ℕ}
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V.ids)
    (hcommits : CommitsCorrectLeaders S D R N)
    (hrr : RoundRobin S.leader) (hEl : ∀ r a, Elig r a ↔ r + 2 < a) (hid : ∀ s, S.slotRound s = s)
    (hN : max r R + (3 * F.f + 5) ≤ N) :
    dec r ≠ Verdict.undecided :=
  all_decided hwf (sees_of_commits_of_held  hcommits hheld) hrr hEl hid hN

/-! ## What a slot reads of its schedule

Every rule reads the schedule at the slot it is deciding and nowhere
else: the round the candidate proposes at, and who proposes it. Two
schedules agreeing there give the same verdict, which is what a bound on
a decision means — the relation's `skip_congr` and `link_congr`, and the
second quantifier of `Properties.Indirect`. -/

/-- **A slot's blocks read the schedule only at that slot.** -/
theorem slotBlocks_congr {S S' : Slots Validator} {D : Dag Validator BlockId Payload} {k : ℕ}
    (hr : S.slotRound k = S'.slotRound k) (hl : S.leader k = S'.leader k) :
    slotBlocks S D k = slotBlocks S' D k := by
  unfold slotBlocks; rw [hr, hl]

/-- **And so does the direct skip rule.** -/
theorem directSkip_congr {S S' : Slots Validator} {D : Dag Validator BlockId Payload} {k : ℕ}
    (hr : S.slotRound k = S'.slotRound k) (hl : S.leader k = S'.leader k) :
    DirectSkip S D k ↔ DirectSkip S' D k := by
  unfold DirectSkip; rw [slotBlocks_congr hr hl, hr]

/-- **The indirect rule reads the schedule only at the slot it decides.** -/
theorem indirectCommit_congr {S S' : Slots Validator} {D : Dag Validator BlockId Payload}
    {A : BlockId} {k : ℕ} {b : BlockId}
    (hr : S.slotRound k = S'.slotRound k) (hl : S.leader k = S'.leader k) :
    IndirectCommit S D A k b ↔ IndirectCommit S' D A k b := by
  unfold IndirectCommit; rw [slotBlocks_congr hr hl, hr]

open scoped Classical in
/-- **And so does the tie-break.** -/
theorem chooseLeast_congr [LinearOrder BlockId] {S S' : Slots Validator}
    {D : Dag Validator BlockId Payload} {A : BlockId} {r : ℕ}
    (hr : S.slotRound r = S'.slotRound r) (hl : S.leader r = S'.leader r) :
    chooseLeast S D A r = chooseLeast S' D A r := by
  have hset : (slotBlocks S D r).filter (fun b => IndirectCommit S D A r b) =
      (slotBlocks S' D r).filter (fun b => IndirectCommit S' D A r b) := by
    rw [slotBlocks_congr hr hl]
    exact Finset.filter_congr fun b _ => by
      simp [indirectCommit_congr (D := D) (A := A) (b := b) hr hl]
  unfold chooseLeast
  simp only [hset]

/-- **A view's direct rules read the schedule only at the slot they
decide**, since the rules they restrict do. -/
theorem viewCommit_congr {S S' : Slots Validator} {D : Dag Validator BlockId Payload}
    {V : D.View} {r : ℕ} {l : BlockId}
    (hr : S.slotRound r = S'.slotRound r) (hl : S.leader r = S'.leader r) :
    viewCommit S D V r l ↔ viewCommit S' D V r l := by
  unfold viewCommit; rw [slotBlocks_congr hr hl]

/-- The skip half. -/
theorem viewSkip_congr {S S' : Slots Validator} {D : Dag Validator BlockId Payload}
    {V : D.View} {r : ℕ}
    (hr : S.slotRound r = S'.slotRound r) (hl : S.leader r = S'.leader r) :
    viewSkip S D V r ↔ viewSkip S' D V r := by
  unfold viewSkip; exact directSkip_congr hr hl

/-! ## Views only grow -/

/-- A larger view holds every block of a round the smaller one does. -/
theorem blocksAt_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {r : ℕ} :
    blocksAt (V.toRecord) r ⊆ blocksAt (V'.toRecord) r := by
  intro b hb
  simp only [blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block,
    Finset.mem_filter] at hb ⊢
  exact ⟨hsub hb.1, hb.2⟩

/-- More blocks, more voters. -/
theorem voters_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId} :
    voters (V.toRecord) l ⊆ voters (V'.toRecord) l := by
  intro v hv
  simp only [voters, supporters, votesFor, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  exact ⟨q, ⟨blocksAt_mono hsub hq, hqref⟩, hqv⟩

/-- And more validators declining to vote. -/
theorem nonVoters_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId} :
    nonVoters (V.toRecord) l ⊆ nonVoters (V'.toRecord) l := by
  intro v hv
  simp only [nonVoters, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  exact ⟨q, ⟨blocksAt_mono hsub hq, hqref⟩, hqv⟩

/-- A fast commit survives the view growing. -/
theorem fastCommit_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId}
    (h : FastCommit (V.toRecord) l) : FastCommit (V'.toRecord) l :=
  le_trans h (Finset.card_le_card (voters_mono hsub))

/-- And a slow one: its certificates are blocks, and a certificate is a
fact about the block's own references. -/
theorem spCommit_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId}
    (h : SPCommit (V.toRecord) l) : SPCommit (V'.toRecord) l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbc, hcert⟩ := hcerts v hv
  exact ⟨b, blocksAt_mono hsub hb, hbc, hcert⟩

/-- So does the direct commit. -/
theorem directCommit_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId}
    (h : DirectCommit (V.toRecord) l) : DirectCommit (V'.toRecord) l :=
  h.elim (fun h => Or.inl (fastCommit_mono hsub h)) (fun h => Or.inr (spCommit_mono hsub h))

/-- A view holds what it directly commits: a commit carries votes, and a
vote is a reference the view is closed under. -/
theorem mem_view_of_directCommit {l : BlockId} (h : DirectCommit (V.toRecord) l) :
    l ∈ V.ids := by
  have harith := params_arith (Validator := Validator)
  rcases h with hfast | ⟨certs, hcard, hcerts⟩
  · have hpos : 0 < (voters (V.toRecord) l).card := by
      have := hfast
      have hfc : fastCard Validator = Fintype.card Validator - P.p := rfl
      simp only [FastCommit] at this
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    simp only [voters, supporters, votesFor, mem_creatorsOf, Finset.mem_filter, blocksAt,
      BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block] at hv
    obtain ⟨q, ⟨⟨hqV, -⟩, hql⟩, -⟩ := hv
    exact V.complete q hqV l hql
  · have hpos : 0 < certs.card := by simp only [spQuorum] at hcard; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    obtain ⟨b, hb, -, hcert⟩ := hcerts v hv
    have hbV : b ∈ V.ids := by
      simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hb; exact hb.1
    have hne : (parentsVoting D b l).Nonempty := by
      have hpos' : 0 < (parentsVoting (V.toRecord) b l).card := by
        have := hcert; simp only [SPCertificate, spQuorum] at this; omega
      exact Finset.card_pos.1 hpos'
    exact mem_view_of_parentsVoting hbV hne

/-- **The direct skip survives the view growing.** For a candidate the
smaller view held, its blames and its no-evidence blocks carry over. For
a candidate the larger view adds, no block of the smaller view
references it: the no-evidence blocks' parents — a quorum of them, by
validity — all decline to vote for it, and none of those blocks has a
parent voting for it, so none is evidence for it. -/
theorem directSkip_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {k : ℕ}
    (h : DirectSkip S (V.toRecord) k) : DirectSkip S (V'.toRecord) k := by
  obtain ⟨hsp, nonev, hnon, hnonb⟩ := h
  have harith := params_arith (Validator := Validator)
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨b₀, hb₀, -, -⟩ := hnonb v₀ hv₀
  have hb₀V : b₀ ∈ V.ids := by
    simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hb₀; exact hb₀.1
  have hb₀round : (D.block b₀).round = S.slotRound k + 2 := by
    simp only [blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hb₀; exact hb₀.2
  have hpar : quorumCard Validator ≤ (parentSet D b₀).card :=
    (D.valid b₀ (V.subset_ids hb₀V)).quorum (by omega)
  refine ⟨fun l hl => ?_, nonev, hnon, fun v hv => ?_⟩
  · by_cases hlV : l ∈ V.ids
    · exact le_trans (hsp l (mem_slotBlocks_view hlV (slotBlocks_restrict hl)))
        (Finset.card_le_card (nonVoters_mono hsub))
    · have hlr : (D.block l).round = S.slotRound k := by
        simp only [slotBlocks, blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hl
        exact hl.1.2
      refine le_trans (le_trans spQuorum_le_quorumCard hpar) (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨q, hq, hqw⟩ := mem_creatorsOf.1 hw
      have hqV : q ∈ V.ids := V.complete b₀ hb₀V q hq
      have hqr : (D.block q).round = S.slotRound k + 1 := by
        have := parent_round (V.subset_ids hb₀V) hq; omega
      refine mem_creatorsOf.2 ⟨q, ?_, hqw⟩
      simp only [nonVoters, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block,
        Finset.mem_filter]
      exact ⟨⟨hsub hqV, by rw [hqr, hlr]⟩, fun hlq => hlV (V.complete q hqV l hlq)⟩
  · obtain ⟨b, hb, hbc, hnonfp⟩ := hnonb v hv
    have hbV : b ∈ V.ids := by
      simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hb; exact hb.1
    refine ⟨b, blocksAt_mono hsub hb, hbc, fun l hl hfp => ?_⟩
    have hfpD : FPEvidence D b l := (fpEvidence_restrict (V := V') (hsub hbV)).1 hfp
    by_cases hlV : l ∈ V.ids
    · exact hnonfp l (mem_slotBlocks_view hlV (slotBlocks_restrict hl))
        ((fpEvidence_restrict (V := V) hbV).2 hfpD)
    · exact hlV (mem_view_of_parentsVoting hbV (parentsVoting_nonempty_of_fpEvidence hfpD))

/-! ## The reverse pass lands in the relation -/

section Pass

variable [LinearOrder BlockId]

/-- **The reverse pass lands in the relation.** Every slot a well-formed
assignment decides, it decides as the relation does: a direct verdict
is the direct constructor; an indirect one reads the anchor — the least
eligible unskipped slot, hence committed and with every eligible slot
between skipped, both by the induction hypothesis — and the tie-break's
choice is the rung's, or the rung is empty and the slot skips. -/
theorem decided_of_wellFormed {V : D.View} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed (EligibleAt (S := S) 2) (viewCommit S D V) (viewSkip S D V)
      (chooseLeast S D) dec)
    {N : ℕ} (hN : ∀ s, N ≤ s → dec s = Verdict.undecided) :
    ∀ r, dec r ≠ Verdict.undecided → Decided D V r (dec r).optOf := by
  suffices h : ∀ d r, N ≤ r + d → dec r ≠ Verdict.undecided → Decided D V r (dec r).optOf by
    intro r; exact h N r (by omega)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r hNr hr
    have hd0 : d ≠ 0 := by rintro rfl; exact hr (hN r (by omega))
    have IH : ∀ s, r < s → dec s ≠ Verdict.undecided → Decided D V s (dec s).optOf :=
      fun s hs hd => ih (d - 1) (by omega) s (by omega) hd
    by_cases hdc : ∃ l, viewCommit S D V r l
    · obtain ⟨l, hslot, hcom⟩ := hdc
      rw [hwf.direct_commit r l ⟨hslot, hcom⟩]
      exact Decided.directCommit (mem_slotBlocks.1 (slotBlocks_restrict hslot)) hcom
    · by_cases hds : viewSkip S D V r
      · rw [hwf.direct_skip r hds]
        exact Decided.directSkip hds
      · obtain ⟨a, hanc⟩ := hwf.has_anchor r hdc hds hr
        rcases hva : dec a with A | - | -
        · have hra : r < a := lt_of_eligibleAt hanc.1
          have hA : Decided D V a (some A) := by
            have := IH a hra (by rw [hva]; simp)
            rwa [hva] at this
          have hmid : ∀ m, r < m → m < a → EligibleAt (S := S) 2 r m → Decided D V m none := by
            intro m h1 h2 h3
            have hsk := hanc.2.2 m h3 h2
            have := IH m h1 (by rw [hsk]; simp)
            rwa [hsk] at this
          have hval := hwf.indirect_commit r a A hdc hds hanc hva
          rcases hch : chooseLeast S D A r with - | b
          · rw [hch] at hval
            rw [hval]
            refine Decided.indirectSkip hra hanc.1 hA hmid (fun i hi L hL hlink => ?_)
            have : i = 0 := by change i < 1 at hi; omega
            subst this
            exact absurd (chooseSound_least.total A r ⟨L, hlink⟩) (by rw [hch]; simp)
          · rw [hch] at hval
            rw [hval]
            have hind := chooseSound_least.sound A r b hch
            exact Decided.indirectCommit (i := 0) hra hanc.1 hA hmid Nat.one_pos
              (fun _ h => absurd h (Nat.not_lt_zero _)) (mem_slotBlocks.1 hind.1) hind
              (chooseLeast_least hch)
        · exact absurd hva hanc.2.1
        · exact absurd (hwf.indirect_undecided r a hdc hds hanc hva) hr

end Pass

/-! ## The laws

What the relation asks of the rule, each a theorem above or in
`Decision.lean` and `Anchor.lean`: a direct commit lifts from the view
to the universe, where two of one slot are one block and a commit bars
the skip; a direct commit is certified or evidenced in every eligible
anchor's history, and no rival candidate is; a skipped slot links
nothing; the least of two choices is both; and the direct rules grow
with the view and read the schedule at their slot alone. -/

/-- **FinWhale's laws.** -/
theorem finWhaleLaws [LinearOrder BlockId] :
    (finWhaleAnchored Validator BlockId Payload).Laws where
  commit_unique := fun _ hL₁ hL₂ h₁ h₂ =>
    direct_commit_unique (mem_slotBlocks.2 hL₁) (mem_slotBlocks.2 hL₂)
      (directCommit_restrict h₁) (directCommit_restrict h₂)
  commit_skip := fun _ hL h hskip =>
    no_directSkip_of_commit_view (mem_slotBlocks.2 hL) (directCommit_restrict h) hskip
  commit_link := by
    intro S U V k j L A _ hL h hA helig
    refine ⟨0, Nat.one_pos, indirectCommit_of_directCommit hA.1 ?_ (mem_slotBlocks.2 hL)
      (directCommit_restrict h)⟩
    have := (finWhaleAnchored Validator BlockId Payload).anchor_round_le hA helig
    simp only [finWhaleAnchored_wave] at this
    omega
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ hlink _
    by_contra hne
    exact no_indirectCommit_of_directCommit hL₁.1 hL₂.1 (mem_slotBlocks.2 hL₁)
      ⟨hne, by rw [hL₁.2.1, hL₂.2.1], by rw [hL₁.2.2, hL₂.2.2]⟩ (directCommit_restrict h) hlink
  skip_link := fun _ hskip _ _ => no_indirectCommit_of_directSkip_view hskip
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ hl₁ hl₂ hm₁ hm₂
    exact le_antisymm (not_lt.mp (show ¬ L₂ < L₁ from hm₁ L₂ hL₂ hl₂))
      (not_lt.mp (show ¬ L₁ < L₂ from hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => directCommit_mono hsub h
  skip_mono := fun _ hsub h => directSkip_mono hsub h
  skip_congr := fun _ hround hk h => (directSkip_congr hround hk).1 h
  link_congr := fun hround hk h => (indirectCommit_congr hround hk).1 h

/-! ## The two theorems, end to end -/

/-- **Theorem 24 (Agreement), end to end.** Two validators of one DAG,
each running the reverse pass on its own view, deliver the same sequence
at every horizon the DAG supports. The relation's agreement makes the
verdicts agree wherever both are decided — each pass lands in the
relation — and Lemma 23 makes them decided. `hsees` is the liveness
interface, and the schedule that supplies it does not appear. -/
theorem agreement_of_commits [LinearOrder BlockId] {V V' : D.View}
    {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed (EligibleAt (S := S) 2) (viewCommit S D V) (viewSkip S D V)
      (chooseLeast S D) dec)
    (hwf' : WellFormed (EligibleAt (S := S) 2) (viewCommit S D V') (viewSkip S D V')
      (chooseLeast S D) dec')
    {M : ℕ} (hbound : ∀ s, M ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {R N : ℕ} (hsees : SeesCommits S D (viewCommit S D V) R N)
    (hsees' : SeesCommits S D (viewCommit S D V') R N)
    (hrr : RoundRobin S.leader) (hid : ∀ s, S.slotRound s = s)
    {k : ℕ} (hkN : max k R + (3 * F.f + 5) ≤ N)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  have hEl : ∀ r a, EligibleAt (S := S) 2 r a ↔ r + 2 < a := fun r a => by
    simp only [EligibleAt, hid]
  have hagree : ∀ s, dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided →
      dec s = dec' s := by
    intro s h1 h2
    exact Verdict.optOf_inj h1 h2 (AnchoredRule.decided_agree finWhaleLaws trivial
      (decided_of_wellFormed hwf (fun s hs => (hbound s hs).1) s h1)
      (decided_of_wellFormed hwf' (fun s hs => (hbound s hs).2) s h2))
  refine theorem24 hagree
    (fun s hs => all_decided hwf hsees hrr hEl hid (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    (fun s hs => all_decided hwf' hsees' hrr hEl hid (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    hist

end FinWhale

end LeanDag
