import LeanDag.FinWhale.Procedure.Decided
import LeanDag.FinWhale.Model.View
import LeanDag.FinWhale.Procedure.Consistency
/-!
# FinWhale — views, and the direct rules relative to one

A view is a reference-closed subset of the universe's blocks, and a
`Dag` in its own right, with validity and non-equivocation inherited.
This file relates its direct verdicts to the universe's and assembles
FinWhale's laws for the anchored relation. The skip rule is where the
two directions part: it quantifies over the slot's blocks as the view
sees them, so its exclusions (`no_directSkip_of_commit_view`,
`no_indirectCommit_of_directSkip_view`) and its growth
(`directSkip_mono`) are proved directly, through the quorum of
Non-FP-evidence blocks.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {Elig : ℕ → ℕ → Prop}
variable {D : Dag Validator BlockId Payload} {V : D.View}
variable {S : Slots Validator}

/-! A view holds fewer blocks at a round, fewer supporters and fewer
blamers: `blocksAt_toRecord_subset`, `supporters_toRecord_subset` and
`blames_toRecord_subset` of the record, which `voters` and `nonVoters`
are read at. -/

/-- A slot's blocks shrink with the view. -/
theorem slotBlocks_restrict {r : ℕ} : slotBlocks S (V.toRecord) r ⊆ slotBlocks S D r := by
  intro b hb
  simp only [slotBlocks, leaderBlocksAt, Finset.mem_filter] at hb ⊢
  exact ⟨blocksAt_toRecord_subset hb.1, hb.2⟩

/-- A candidate of the universe the view holds is a candidate of the
view. -/
theorem mem_slotBlocks_view {r : ℕ} {b : BlockId} (hb : b ∈ V.ids)
    (h : b ∈ slotBlocks S D r) : b ∈ slotBlocks S (V.toRecord) r := by
  simp only [slotBlocks, leaderBlocksAt, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block,
    Finset.mem_filter] at h ⊢
  exact ⟨⟨hb, h.1.2⟩, h.2⟩

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
the two quorums meet in a correct author, whose vote and parent
coincide. -/
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
  le_trans h (Finset.card_le_card supporters_toRecord_subset)

/-- And its slow commit. -/
theorem spCommit_restrict {l : BlockId} (h : SPCommit (V.toRecord) l) : SPCommit D l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbv, hbcert⟩ := hcerts v hv
  exact ⟨b, blocksAt_toRecord_subset hb, hbv, hbcert⟩

/-- So its direct commit is one of the universe: the condition safety
took as a hypothesis. -/
theorem directCommit_restrict {l : BlockId} (h : DirectCommit (V.toRecord) l) :
    DirectCommit D l :=
  h.imp fastCommit_restrict spCommit_restrict

/-- A view's SP-skip is one of the universe: it counts validators
declining to vote, and the view has fewer of them. -/
theorem spSkip_restrict {l : BlockId} (h : SPSkip (V.toRecord) l) : SPSkip D l :=
  le_trans h (Finset.card_le_card blames_toRecord_subset)

/-- Where the view holds a whole round, it counts the same voters. -/
theorem voters_restrict_eq {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V.ids) :
    voters (V.toRecord) l = voters D l := by
  refine Finset.Subset.antisymm supporters_toRecord_subset fun v hv => ?_
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

A view's direct skip is not one of the universe's, since its first
condition quantifies over the slot blocks the view holds. Both
exclusions run through the second condition instead, the quorum of
Non-FP-evidence blocks, which is also what forces the committed block
into the view. -/

/-- **A view's direct skip is incompatible with a direct commit**: a
single round-`(r+2)` block of the skip's quorum puts the committed
block in the view, and Lemma 4 or Lemma 2 makes it evidence for it,
which Non-FP-evidence denies. -/
theorem no_directSkip_of_commit_view {r : ℕ} {l : BlockId}
    (hl : l ∈ slotBlocks S D r) (hcom : DirectCommit D l) :
    ¬ DirectSkip S (V.toRecord) r := by
  rintro ⟨-, nonev, hnon, hnonb⟩
  have hlu : l ∈ D.ids ∧ (D.block l).round = S.slotRound r ∧
      (D.block l).creator = S.leader r := by
    simp only [slotBlocks, leaderBlocksAt, blocksAt, Finset.mem_filter] at hl
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
    simp only [slotBlocks, leaderBlocksAt, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
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
Either route puts the candidate in the view, and the skip's own
conditions deny it there. -/
theorem no_indirectCommit_of_directSkip_view {A : BlockId} {r : ℕ} {b : BlockId}
    (hskip : DirectSkip S (V.toRecord) r) : ¬ IndirectCommit S D A r b := by
  obtain ⟨hsp, nonev, hnon, hnonb⟩ := hskip
  rintro ⟨hbslot, hroute⟩
  have harith := params_arith (Validator := Validator)
  have hbu : b ∈ D.ids ∧ (D.block b).round = S.slotRound r ∧
      (D.block b).creator = S.leader r := by
    simp only [slotBlocks, leaderBlocksAt, blocksAt, Finset.mem_filter] at hbslot
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
      simp only [slotBlocks, leaderBlocksAt, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block,   Finset.mem_filter]
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

/-- **A view holding the reliable blocks sees the commits.** Nothing is
asked of it about Byzantine authors, which is as much as a schedule can
give. -/
theorem sees_of_commits_of_held {V : D.View} {R N : ℕ}
    (hcommits : CommitsCorrectLeaders S D R N)
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V.ids) :
    SeesCommits S D (viewCommit S D V ) R N := by
  intro s hR hN hlead
  obtain ⟨l, hslot, certs, hsub, hcard, hcertb⟩ := hcommits s hR hN hlead
  have hlu : l ∈ blocksAt D (S.slotRound s) ∧ (D.block l).creator = S.leader s := by
    simp only [slotBlocks, leaderBlocksAt, Finset.mem_filter] at hslot
    exact hslot
  have hlround : (D.block l).round = S.slotRound s := by
    simp only [blocksAt, Finset.mem_filter] at hlu
    exact hlu.1.2
  have hlV : l ∈ V.ids := hheld (S.slotRound s) (by omega) (by omega) l hlu.1
    (by rw [hlu.2]; exact hlead)
  refine ⟨l, hslot, ?_, Or.inr ⟨certs, hcard, fun v hv => ?_⟩⟩
  · simp only [slotBlocks, leaderBlocksAt, blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
    exact ⟨⟨hlV, hlround⟩, hlu.2⟩
  · obtain ⟨b, hb, hbc, hcert⟩ := hcertb v hv
    have hbV : b ∈ V.ids :=
      hheld ((D.block l).round + 2) (by omega) (by omega) b hb (by rw [hbc]; exact hsub hv)
    refine ⟨b, ?_, hbc, hcert⟩
    simp only [blocksAt, BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block, Finset.mem_filter]
    simp only [blocksAt, Finset.mem_filter] at hb
    exact ⟨hbV, hb.2⟩

/-! ## What a slot reads of its schedule

Every rule reads the schedule only at the slot it is deciding, so two
schedules agreeing there give the same verdict — the relation's
`skip_congr` and `link_congr`. -/

/-- **A slot's blocks read the schedule only at that slot.** -/
theorem slotBlocks_congr {S S' : Slots Validator} {D : Dag Validator BlockId Payload} {k : ℕ}
    (hr : S.slotRound k = S'.slotRound k) (hl : S.leader k = S'.leader k) :
    slotBlocks S D k = slotBlocks S' D k := by
  unfold slotBlocks leaderBlocksAt; rw [hr, hl]

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

/-! A larger view holds more of a round, more supporters and more
blamers: `blocksAt_toRecord_mono`, `supporters_toRecord_mono` and
`blames_toRecord_mono` of the record. -/

/-- A fast commit survives the view growing. -/
theorem fastCommit_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId}
    (h : FastCommit (V.toRecord) l) : FastCommit (V'.toRecord) l :=
  le_trans h (Finset.card_le_card (supporters_toRecord_mono hsub))

/-- And a slow one: its certificates are blocks, and a certificate is a
fact about the block's own references. -/
theorem spCommit_mono {V' : D.View} (hsub : V.ids ⊆ V'.ids) {l : BlockId}
    (h : SPCommit (V.toRecord) l) : SPCommit (V'.toRecord) l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbc, hcert⟩ := hcerts v hv
  exact ⟨b, blocksAt_toRecord_mono hsub hb, hbc, hcert⟩

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

/-- **The direct skip survives the view growing.** A held candidate's
blames and no-evidence blocks carry over; a new candidate is referenced
by no block the smaller view holds, so it collects no votes and no
evidence either. -/
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
        (Finset.card_le_card (blames_toRecord_mono hsub))
    · have hlr : (D.block l).round = S.slotRound k := by
        simp only [slotBlocks, leaderBlocksAt, blocksAt, BlockRecord.View.toRecord_block, Finset.mem_filter] at hl
        exact hl.1.2
      refine le_trans (le_trans spQuorum_le_quorumCard hpar) (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨q, hq, hqw⟩ := mem_creatorsOf.1 hw
      have hqV : q ∈ V.ids := V.complete b₀ hb₀V q hq
      have hqr : (D.block q).round = S.slotRound k + 1 := by
        have := parent_round (V.subset_ids hb₀V) hq; omega
      refine mem_creatorsOf.2 ⟨q, ?_, hqw⟩
      rw [mem_omissionsOf]
      refine ⟨hsub hqV, ?_, fun hlq => hlV (V.complete q hqV l hlq)⟩
      show (D.block q).round = (D.block l).round + 1
      rw [hqr, hlr]
  · obtain ⟨b, hb, hbc, hnonfp⟩ := hnonb v hv
    have hbV : b ∈ V.ids := by
      simp only [blocksAt, BlockRecord.View.toRecord_ids, Finset.mem_filter] at hb; exact hb.1
    refine ⟨b, blocksAt_toRecord_mono hsub hb, hbc, fun l hl hfp => ?_⟩
    have hfpD : FPEvidence D b l := (fpEvidence_restrict (V := V') (hsub hbV)).1 hfp
    by_cases hlV : l ∈ V.ids
    · exact hnonfp l (mem_slotBlocks_view hlV (slotBlocks_restrict hl))
        ((fpEvidence_restrict (V := V) hbV).2 hfpD)
    · exact hlV (mem_view_of_parentsVoting hbV (parentsVoting_nonempty_of_fpEvidence hfpD))

/-! ## The reverse pass lands in the relation -/

section Pass

variable [LinearOrder BlockId]

end Pass

/-! ## The laws

What the relation asks of the rule, assembled from the theorems above
and in `Decision.lean` and `Anchor.lean`. -/

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
    simp only [finWhaleAnchored_waveAt] at this
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

end FinWhale

end LeanDag
