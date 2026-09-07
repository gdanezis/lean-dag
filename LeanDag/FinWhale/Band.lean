import LeanDag.FinWhale.View
import LeanDag.Common.Anchored.Band
/-!
# FinWhale — what a band of rounds carries

`docs/target-properties.md` §3.8 asks every rule for a band: a range of
rounds such that any DAG agreeing there reaches the same verdicts. The
induction over the derivation is the relation's; what this file supplies
is the transport of each of FinWhale's predicates across a band, the
relation's band laws at the end.

**The band is one-directional in membership**, which is what makes it
work at all and what makes it awkward. `D'` holds every block of `D` in
the range, at the round the offset names and with the same author and
references; it may hold *more*. So the rules split three ways.

* **Anchored rules transport both ways.** `IndirectCommit S D A k b`
  says something about `A`'s causal history, and a band preserves a
  history in both directions — nothing new can enter it, because the
  blocks that would witness the entry are old and their references are
  unchanged. This is what lets the tie-break be the same function on
  both sides, which is what the reverse pass needs.
* **Positive rules transport forwards.** A vote, a certificate, a blame
  is evidence, and evidence survives.
* **The skip rule quantifies over the slot's candidates**, and a band
  may add one. That is the shape §3.2 recorded as a defect in the core
  and §3.12 in Odontoceti, and FinWhale escapes it for a reason neither
  of those had: a new candidate is *not referenced by any old block*, so
  no old block is FP-evidence for it, and the old blamers' parents — a
  quorum of them, by validity — are all non-voters for it. The skip
  survives the new candidate rather than being repaired to ignore it.

Nothing here mentions a schedule beyond `Slots.slotRound` and `Slots.leader`
at the slot in hand. The band is the shared `AgreeBand` at any rule on
FinWhale's record, read at views through the relation's `agreeBand_view`.
-/

namespace LeanDag

namespace FinWhale

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D D' : Dag Validator BlockId Payload}

/-- A block an old block's parents voted for is old, and two rounds
below it: an edge drops exactly one round, and a DAG is closed under
edges. -/
theorem old_of_parentsVoting {b l : BlockId} (hbD : b ∈ D.ids)
    (hne : (parentsVoting D b l).Nonempty) :
    l ∈ D.ids ∧ (D.block l).round + 2 = (D.block b).round := by
  obtain ⟨v, hv⟩ := hne
  simp only [parentsVoting, creatorsOf, Finset.mem_image, Finset.mem_filter] at hv
  obtain ⟨q, ⟨hqm, hql⟩, -⟩ := hv
  have hqD : q ∈ D.ids := D.complete b hbD q hqm
  have hqr : (D.block q).round + 1 = (D.block b).round := (D.valid b hbD).predecessor q hqm
  have hlr : (D.block l).round + 1 = (D.block q).round := (D.valid q hqD).predecessor l hql
  exact ⟨D.complete q hqD l hql, by omega⟩

/-- **A block nothing votes for is no evidence.** `f + p` is at least
two — `1 ≤ p ≤ f` — so neither branch of the rule is met by an empty
count. This is what a new candidate of the band runs into. -/
theorem not_fpEvidence_of_empty {b l : BlockId}
    (h : parentsVoting D b l = ∅) : ¬ FPEvidence D b l := by
  have hfp : 2 ≤ F.f + P.p := by have := P.p_pos; have := P.p_le_f; omega
  unfold FPEvidence
  split
  · rintro ⟨hc, -⟩; rw [h] at hc; simp only [Finset.card_empty] at hc; omega
  · intro hc; rw [h] at hc; simp only [Finset.card_empty] at hc; omega

/-- A new block of the band collects no votes from an old block. -/
theorem parentsVoting_eq_empty {D₀ : Dag Validator BlockId Payload} {b l : BlockId} (hbD : b ∈ D₀.ids)
    (hl : l ∉ D₀.ids) : parentsVoting D₀ b l = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
  simp only [parentsVoting, creatorsOf, Finset.mem_image, Finset.mem_filter] at hw
  obtain ⟨q, ⟨hqm, hql⟩, -⟩ := hw
  exact hl (D₀.complete q (D₀.complete b hbD q hqm) l hql)

/-- A block a block reaches is a block. -/
theorem band_reaches_mem {D₀ : Dag Validator BlockId Payload} {A C : BlockId} (hA : A ∈ D₀.ids)
    (h : ReachesFrom D₀.block A C) : C ∈ D₀.ids := by
  induction h with
  | refl => exact hA
  | tail _ hstep ih => exact D₀.complete _ ih _ hstep

/-- And it does not sit above it. -/
theorem band_reaches_round {D₀ : Dag Validator BlockId Payload} {A C : BlockId} (hA : A ∈ D₀.ids)
    (h : ReachesFrom D₀.block A C) : (D₀.block C).round ≤ (D₀.block A).round := by
  induction h with
  | refl => exact le_refl _
  | @tail b c hab hstep ih =>
      have hbD := band_reaches_mem hA hab
      have := (D₀.valid b hbD).predecessor c hstep
      omega

/-- Evidence names a voter: `f + p` is at least two, so an empty count is
no evidence. -/
theorem nonempty_of_fpEvidence {D₀ : Dag Validator BlockId Payload} {c b : BlockId}
    (h : FPEvidence D₀ c b) : (parentsVoting D₀ c b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  exact fun he => not_fpEvidence_of_empty he h

/-- A certificate names one too, the quorum being positive. -/
theorem nonempty_of_spCertificate {D₀ : Dag Validator BlockId Payload} {c b : BlockId}
    (h : SPCertificate D₀ c b) : (parentsVoting D₀ c b).Nonempty := by
  have := params_arith (Validator := Validator)
  have hq : 0 < spQuorum Validator := by simp only [spQuorum]; omega
  exact Finset.card_pos.1 (lt_of_lt_of_le hq h)

namespace Band

variable {lo hi g g' : ℕ}
variable {R : AnchoredRule Validator BlockId Payload ValidHere (Correct : Finset Validator)}
variable (hb : AgreeBand R.toDagRule D D' lo hi g g')
include hb

/-! ## Layers

Everything below reads a round layer, so the two facts about layers come
first: an old layer lands on the layer the offset names, and an old
block of `D'` in that layer was in the layer it came from. -/

/-- **An old layer lands on the layer the offset names.** -/
theorem blocksAt_subset {n n' : ℕ} (hn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + g ≤ hi) :
    blocksAt D n ⊆ blocksAt D' n' := by
  intro b hbm
  simp only [blocksAt, Finset.mem_filter] at hbm ⊢
  obtain ⟨hbD, hbr⟩ := hbm
  have hband := AnchoredRule.band_block hb hbD (by omega) (by omega)
  exact ⟨AnchoredRule.band_mem hb hbD (by omega) (by omega), by omega⟩

/-- **And an old block of that layer of `D'` was in it.** -/
theorem mem_blocksAt_of_old {n n' : ℕ} (hn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + g ≤ hi)
    {b : BlockId} (hbD : b ∈ D.ids) (hbm : b ∈ blocksAt D' n') : b ∈ blocksAt D n := by
  simp only [blocksAt, Finset.mem_filter] at hbm ⊢
  refine ⟨hbD, ?_⟩
  have := AnchoredRule.band_block' hb hbD hbm.1 (by omega) (by omega)
  omega

/-! ## What a block's parents see

`parentsVoting`, and everything counted against it, reads a block's
references and *their* references — two rounds down. So the lemma is
stated two rounds above the floor, and from there the vote counts are
equal rather than merely monotone, whatever block they are counted for:
a new block is referenced by nothing old, so it collects no votes on
either side. -/

/-- **A block two rounds above the floor votes the same way in both
DAGs**, for every block whatever. -/
theorem parentsVoting_eq {b : BlockId} (hbD : b ∈ D.ids)
    (h1 : lo + 1 < (D.block b).round + g) (h2 : (D.block b).round + g ≤ hi) (l : BlockId) :
    parentsVoting D' b l = parentsVoting D b l := by
  classical
  have hq : ∀ q ∈ (D.block b).refs,
      (D'.block q).refs = (D.block q).refs ∧ (D'.block q).creator = (D.block q).creator := by
    intro q hqm
    have hqD : q ∈ D.ids := D.complete b hbD q hqm
    have hqr : (D.block q).round + 1 = (D.block b).round := (D.valid b hbD).predecessor q hqm
    exact ⟨AnchoredRule.band_refs hb hqD (by omega) (by omega), (AnchoredRule.band_block hb hqD (by omega) (by omega)).2⟩
  unfold parentsVoting creatorsOf
  rw [AnchoredRule.band_refs hb hbD (by omega) (by omega)]
  rw [Finset.filter_congr (fun q hqm => by rw [(hq q hqm).1])]
  exact Finset.image_congr fun q hqm => (hq q (Finset.mem_of_mem_filter q hqm)).2

/-- **Conflict is read off rounds and authors**, so the band settles it
for the blocks it holds. -/
theorem conflicting_iff {l l' : BlockId} (hlD : l ∈ D.ids) (hl'D : l' ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g ≤ hi)
    (h1' : lo ≤ (D.block l').round + g) (h2' : (D.block l').round + g ≤ hi) :
    Conflicting D' l l' ↔ Conflicting D l l' := by
  have hl := AnchoredRule.band_block hb hlD h1 h2
  have hl' := AnchoredRule.band_block hb hl'D h1' h2'
  unfold Conflicting
  constructor
  · rintro ⟨hne, hr, hc⟩; exact ⟨hne, by omega, by rw [← hl.2, ← hl'.2]; exact hc⟩
  · rintro ⟨hne, hr, hc⟩; exact ⟨hne, by omega, by rw [hl.2, hl'.2]; exact hc⟩

/-- **And so is the equivocation a block exposes.** Both directions: a
witness on the `D'` side is voted for by an old parent, so it is old. -/
theorem exposes_iff {b : BlockId} (hbD : b ∈ D.ids)
    (h1 : lo + 2 ≤ (D.block b).round + g) (h2 : (D.block b).round + g ≤ hi) (v : Validator) :
    ExposesEquivocationBy D' b v ↔ ExposesEquivocationBy D b v := by
  have hpv := parentsVoting_eq hb hbD (by omega) h2
  have hkey : ∀ l : BlockId, (parentsVoting D b l).Nonempty →
      l ∈ D.ids ∧ lo ≤ (D.block l).round + g ∧ (D.block l).round + g ≤ hi := by
    intro l hne
    obtain ⟨hlD, hlr⟩ := old_of_parentsVoting hbD hne
    exact ⟨hlD, by omega, by omega⟩
  constructor
  · rintro ⟨l, -, l', -, hcf, hcr, hn, hn'⟩
    rw [hpv] at hn hn'
    obtain ⟨hlD, hl1, hl2⟩ := hkey l hn
    obtain ⟨hl'D, hl'1, hl'2⟩ := hkey l' hn'
    refine ⟨l, hlD, l', hl'D, (conflicting_iff hb hlD hl'D hl1 hl2 hl'1 hl'2).1 hcf, ?_, hn, hn'⟩
    rw [← (AnchoredRule.band_block hb hlD hl1 hl2).2]; exact hcr
  · rintro ⟨l, hlD, l', hl'D, hcf, hcr, hn, hn'⟩
    obtain ⟨-, hl1, hl2⟩ := hkey l hn
    obtain ⟨-, hl'1, hl'2⟩ := hkey l' hn'
    refine ⟨l, AnchoredRule.band_mem hb hlD hl1 hl2, l', AnchoredRule.band_mem hb hl'D hl'1 hl'2,
      (conflicting_iff hb hlD hl'D hl1 hl2 hl'1 hl'2).2 hcf, ?_, ?_, ?_⟩
    · rw [(AnchoredRule.band_block hb hlD hl1 hl2).2]; exact hcr
    · rw [hpv]; exact hn
    · rw [hpv]; exact hn'

/-- **FP-evidence is the same evidence.** The counts are equal, and the
negative clause of the equivocating branch survives the band's new
blocks: a new conflicting version collects no votes, and an empty count
clears the threshold on the right side of the inequality. -/
theorem fpEvidence_iff {b : BlockId} (hbD : b ∈ D.ids)
    (h1 : lo + 2 ≤ (D.block b).round + g) (h2 : (D.block b).round + g ≤ hi) (l : BlockId) :
    FPEvidence D' b l ↔ FPEvidence D b l := by
  have hfp : 2 ≤ F.f + P.p := by have := P.p_pos; have := P.p_le_f; omega
  have hpv := parentsVoting_eq hb hbD (by omega) h2
  by_cases hlne : (parentsVoting D b l).Nonempty
  · obtain ⟨hlD, hlr⟩ := old_of_parentsVoting hbD hlne
    have hlb := AnchoredRule.band_block hb hlD (by omega) (by omega)
    have hcard : (parentsVoting D' b l).card = (parentsVoting D b l).card := by rw [hpv]
    have hexq : ExposesEquivocationBy D' b (D'.block l).creator ↔
        ExposesEquivocationBy D b (D.block l).creator := by
      rw [hlb.2]; exact exposes_iff hb hbD h1 h2 _
    have hall : (∀ l' ∈ D'.ids, Conflicting D' l l' →
          (parentsVoting D' b l').card + 1 ≤ F.f + P.p) ↔
        (∀ l' ∈ D.ids, Conflicting D l l' → (parentsVoting D b l').card + 1 ≤ F.f + P.p) := by
      constructor
      · intro h l' hl'D hcf
        have hr' : (D.block l').round = (D.block l).round := hcf.2.1.symm
        rw [← hpv]
        exact h l' (AnchoredRule.band_mem hb hl'D (by omega) (by omega))
          ((conflicting_iff hb hlD hl'D (by omega) (by omega) (by omega) (by omega)).2 hcf)
      · intro h l' hl'D hcf
        by_cases hl'old : l' ∈ D.ids
        · have hr' : (D'.block l').round = (D'.block l).round := hcf.2.1.symm
          have hl'b := AnchoredRule.band_block' hb hl'old hl'D (by omega) (by omega)
          rw [hpv]
          exact h l' hl'old ((conflicting_iff hb hlD hl'old (by omega) (by omega)
            (by omega) (by omega)).1 hcf)
        · rw [hpv, parentsVoting_eq_empty hbD hl'old]
          simp only [Finset.card_empty]; omega
    unfold FPEvidence
    by_cases hex : ExposesEquivocationBy D b (D.block l).creator
    · rw [if_pos hex, if_pos (hexq.2 hex)]
      exact and_congr (by rw [hcard]) hall
    · rw [if_neg hex, if_neg (fun h => hex (hexq.1 h)), hcard]
  · have hemp : parentsVoting D b l = ∅ := Finset.not_nonempty_iff_eq_empty.1 hlne
    exact iff_of_false (not_fpEvidence_of_empty (by rw [hpv]; exact hemp))
      (not_fpEvidence_of_empty hemp)

/-! ## The commit rules, forwards

A vote, a certificate and a fast quorum are evidence, and a band only
adds blocks, so each of them survives. Nothing here is an equivalence:
`D'` may commit a slot `D` left undecided, and that is what the
exclusions of `Consistency.lean` — read inside `D'` alone — are for. -/

/-- Votes survive: an old voter is a voter. -/
theorem voters_subset {l : BlockId} (hlD : l ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g + 1 ≤ hi) :
    voters D l ⊆ voters D' l := by
  intro v hv
  simp only [voters, supporters, votesFor, creatorsOf, Finset.mem_image, Finset.mem_filter, blocksAt] at hv ⊢
  obtain ⟨q, ⟨⟨hqD, hqr⟩, hql⟩, hqc⟩ := hv
  have hlb := AnchoredRule.band_block hb hlD h1 (by omega)
  have hqb := AnchoredRule.band_block hb hqD (by omega) (by omega)
  refine ⟨q, ⟨⟨AnchoredRule.band_mem hb hqD (by omega) (by omega), by omega⟩, ?_⟩, ?_⟩
  · rw [AnchoredRule.band_refs hb hqD (by omega) (by omega)]; exact hql
  · rw [hqb.2]; exact hqc

/-- And so does a fast commit. -/
theorem fastCommit {l : BlockId} (hlD : l ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g + 1 ≤ hi)
    (h : FastCommit D l) : FastCommit D' l :=
  le_trans h (Finset.card_le_card (voters_subset hb hlD h1 h2))

/-- A certificate is a vote count two rounds up, so the band settles it
either way. -/
theorem spCertificate_iff {c l : BlockId} (hcD : c ∈ D.ids)
    (h1 : lo + 2 ≤ (D.block c).round + g) (h2 : (D.block c).round + g ≤ hi) :
    SPCertificate D' c l ↔ SPCertificate D c l := by
  unfold SPCertificate
  rw [parentsVoting_eq hb hcD (by omega) h2]

/-- And a slow-path commit survives. -/
theorem spCommit {l : BlockId} (hlD : l ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g + 2 ≤ hi)
    (h : SPCommit D l) : SPCommit D' l := by
  obtain ⟨certs, hcard, hcert⟩ := h
  have hlb := AnchoredRule.band_block hb hlD h1 (by omega)
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨c, hc, hcc, hcert⟩ := hcert v hv
  simp only [blocksAt, Finset.mem_filter] at hc
  have hcb := AnchoredRule.band_block hb hc.1 (by omega) (by omega)
  refine ⟨c, ?_, ?_, (spCertificate_iff hb hc.1 (by omega) (by omega)).2 hcert⟩
  · simp only [blocksAt, Finset.mem_filter]
    exact ⟨AnchoredRule.band_mem hb hc.1 (by omega) (by omega), by omega⟩
  · rw [hcb.2]; exact hcc

/-- Either path. -/
theorem directCommit {l : BlockId} (hlD : l ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g + 2 ≤ hi)
    (h : DirectCommit D l) : DirectCommit D' l :=
  h.imp (fastCommit hb hlD h1 (by omega)) (spCommit hb hlD h1 h2)

/-! ## The skip rule, and the candidate a band may add

`DirectSkip` quantifies over the slot's candidates, so a band adding one
could destroy it. This is where the core (§3.2) and Odontoceti (§3.12)
had to be repaired, and FinWhale does not, for a reason those rules
could not use: FinWhale's blames are counted against what a block's
*parents* reference, and an old block's parents reference only old
blocks. A new candidate therefore collects no FP-evidence at all, and
the old blamers' parents — a quorum of them, by validity — are all
non-voters for it. -/

/-- Declining to vote survives, since references do. -/
theorem nonVoters_subset {l : BlockId} (hlD : l ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g + 1 ≤ hi) :
    nonVoters D l ⊆ nonVoters D' l := by
  intro v hv
  simp only [nonVoters, creatorsOf, Finset.mem_image, Finset.mem_filter, blocksAt] at hv ⊢
  obtain ⟨q, ⟨⟨hqD, hqr⟩, hql⟩, hqc⟩ := hv
  have hlb := AnchoredRule.band_block hb hlD h1 (by omega)
  have hqb := AnchoredRule.band_block hb hqD (by omega) (by omega)
  refine ⟨q, ⟨⟨AnchoredRule.band_mem hb hqD (by omega) (by omega), by omega⟩, ?_⟩, ?_⟩
  · rw [AnchoredRule.band_refs hb hqD (by omega) (by omega)]; exact hql
  · rw [hqb.2]; exact hqc

/-- So an old candidate that was skipped stays skipped. -/
theorem spSkip {l : BlockId} (hlD : l ∈ D.ids)
    (h1 : lo ≤ (D.block l).round + g) (h2 : (D.block l).round + g + 1 ≤ hi)
    (h : SPSkip D l) : SPSkip D' l :=
  le_trans h (Finset.card_le_card (nonVoters_subset hb hlD h1 h2))

/-- **And a candidate the band adds is skipped too.** An old block two
rounds above the slot carries a quorum of parents by validity; they sit
one round above the slot, they are old, and their references are old, so
none of them votes for the new candidate. -/
theorem spSkip_new {c l : BlockId} {n n' : ℕ} (hcD : c ∈ D.ids)
    (hcr : (D.block c).round = n + 2) (hn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + g + 2 ≤ hi)
    (hlnew : l ∉ D.ids) (hlr : (D'.block l).round = n') : SPSkip D' l := by
  classical
  have hquorum : quorumCard Validator ≤ (creatorsOf D.block ((D.block c).refs)).card :=
    (D.valid c hcD).quorum (by omega)
  refine le_trans (spQuorum_le_quorumCard (Validator := Validator)) (le_trans hquorum ?_)
  refine Finset.card_le_card fun v hv => ?_
  simp only [creatorsOf, Finset.mem_image] at hv
  obtain ⟨q, hqm, hqc⟩ := hv
  have hqD : q ∈ D.ids := D.complete c hcD q hqm
  have hqr : (D.block q).round + 1 = (D.block c).round := (D.valid c hcD).predecessor q hqm
  have hqb := AnchoredRule.band_block hb hqD (by omega) (by omega)
  simp only [nonVoters, creatorsOf, Finset.mem_image, Finset.mem_filter, blocksAt]
  refine ⟨q, ⟨⟨AnchoredRule.band_mem hb hqD (by omega) (by omega), by omega⟩, ?_⟩, by rw [hqb.2]; exact hqc⟩
  rw [AnchoredRule.band_refs hb hqD (by omega) (by omega)]
  exact fun hmem => hlnew (D.complete q hqD l hmem)

/-! ## Slots, and the skip rule assembled -/

variable {S S' : Slots Validator} {k k' : ℕ}

/-- An old candidate of the slot is a candidate of the corresponding
slot. -/
theorem slotBlocks_subset (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi) :
    slotBlocks S D k ⊆ slotBlocks S' D' k' := by
  intro l hl
  simp only [slotBlocks, Finset.mem_filter, blocksAt] at hl ⊢
  obtain ⟨⟨hlD, hlr⟩, hlc⟩ := hl
  have hlb := AnchoredRule.band_block hb hlD (by omega) (by omega)
  exact ⟨⟨AnchoredRule.band_mem hb hlD (by omega) (by omega), by omega⟩, by rw [hlb.2, hlc, hlk]⟩

/-- And an old candidate of the corresponding slot came from this one. -/
theorem mem_slotBlocks_of_old (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi)
    {l : BlockId} (hlD : l ∈ D.ids) (hl : l ∈ slotBlocks S' D' k') : l ∈ slotBlocks S D k := by
  simp only [slotBlocks, Finset.mem_filter, blocksAt] at hl ⊢
  obtain ⟨⟨hlD', hlr⟩, hlc⟩ := hl
  have hlb := AnchoredRule.band_block' hb hlD hlD' (by omega) (by omega)
  exact ⟨⟨hlD, by omega⟩, by rw [← hlb.2, hlc, hlk]⟩

/-- **A blame stays a blame.** For the old candidates because FP-evidence
is the same evidence; for a candidate the band added because nothing old
is evidence for it at all. -/
theorem nonFPEvidence (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g + 2 ≤ hi)
    {c : BlockId} (hcD : c ∈ D.ids) (hcr : (D.block c).round = S.slotRound k + 2)
    (h : NonFPEvidence D c (slotBlocks S D k)) :
    NonFPEvidence D' c (slotBlocks S' D' k') := by
  intro l hl hfp
  by_cases hlD : l ∈ D.ids
  · exact h l (mem_slotBlocks_of_old hb hrk hlk h1 (by omega) hlD hl)
      ((fpEvidence_iff hb hcD (by omega) (by omega) l).1 hfp)
  · exact not_fpEvidence_of_empty
      (by rw [parentsVoting_eq hb hcD (by omega) (by omega) l,
        parentsVoting_eq_empty hcD hlD]) hfp

/-- **The direct skip survives the band**, new candidates and all. -/
theorem directSkip (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g + 2 ≤ hi)
    (h : DirectSkip S D k) : DirectSkip S' D' k' := by
  classical
  obtain ⟨hsp, nonev, hcard, hnon⟩ := h
  have hpos : 0 < nonev.card := by
    have := params_arith (Validator := Validator)
    simp only [spQuorum] at hcard
    omega
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨c₀, hc₀, -, -⟩ := hnon v₀ hv₀
  simp only [blocksAt, Finset.mem_filter] at hc₀
  refine ⟨fun l hl => ?_, nonev, hcard, fun v hv => ?_⟩
  · by_cases hlD : l ∈ D.ids
    · have hlS := mem_slotBlocks_of_old hb hrk hlk h1 (by omega) hlD hl
      have hlr : (D.block l).round = S.slotRound k := by
        simp only [slotBlocks, Finset.mem_filter, blocksAt] at hlS; exact hlS.1.2
      exact spSkip hb hlD (by omega) (by omega) (hsp l hlS)
    · have hlr : (D'.block l).round = S'.slotRound k' := by
        simp only [slotBlocks, Finset.mem_filter, blocksAt] at hl
        exact hl.1.2
      exact spSkip_new hb hc₀.1 hc₀.2 hrk h1 (by omega) hlD hlr
  · obtain ⟨c, hc, hcc, hcn⟩ := hnon v hv
    simp only [blocksAt, Finset.mem_filter] at hc
    have hcb := AnchoredRule.band_block hb hc.1 (by omega) (by omega)
    refine ⟨c, ?_, by rw [hcb.2]; exact hcc,
      nonFPEvidence hb hrk hlk h1 h2 hc.1 hc.2 hcn⟩
    simp only [blocksAt, Finset.mem_filter]
    exact ⟨AnchoredRule.band_mem hb hc.1 (by omega) (by omega), by omega⟩

/-- **The indirect rule is the same rule on both sides.** Every clause of
it is read off the anchor's causal history — the certifying block is
reached from the anchor, and the candidate is voted for by that block's
parents — so the band settles all of them, new blocks included: a new
block is in no old block's history, so it is neither certified nor
evidenced, and neither DAG indirectly commits it. -/
theorem indirectCommit_iff (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g + 2 ≤ hi)
    {A : BlockId} (hAD : A ∈ D.ids) (hAlo : lo ≤ (D.block A).round + g)
    (hAhi : (D.block A).round + g ≤ hi) (b : BlockId) :
    IndirectCommit S' D' A k' b ↔ IndirectCommit S D A k b := by
  have hlayer : ∀ {c : BlockId}, c ∈ blocksAt D' (S'.slotRound k' + 2) →
      ReachesFrom D'.block A c →
      c ∈ blocksAt D (S.slotRound k + 2) ∧ ReachesFrom D.block A c := by
    intro c hc hre
    have hcr : (D'.block c).round = S'.slotRound k' + 2 := by
      simp only [blocksAt, Finset.mem_filter] at hc; exact hc.2
    have hlink : (R.toDagRule.block D' c).round = (D'.block c).round := rfl
    obtain ⟨hcD, hcre, hceq⟩ := AgreeBand.reaches_old hb hAD hAlo hAhi hre (by omega)
    have hceq' : (D.block c).round + g = (D'.block c).round + g' := hceq
    exact ⟨by simp only [blocksAt, Finset.mem_filter]; exact ⟨hcD, by omega⟩, hcre⟩
  have hlayer' : ∀ {c : BlockId}, c ∈ blocksAt D (S.slotRound k + 2) → ReachesFrom D.block A c →
      c ∈ blocksAt D' (S'.slotRound k' + 2) ∧ ReachesFrom D'.block A c := by
    intro c hc hre
    have hcr : (D.block c).round = S.slotRound k + 2 := by
      simp only [blocksAt, Finset.mem_filter] at hc; exact hc.2
    have hlink : (R.toDagRule.block D c).round = (D.block c).round := rfl
    exact ⟨blocksAt_subset hb (by omega) (by omega) (by omega) hc,
      AgreeBand.reaches_of hb hAD hAhi hre (by omega)⟩
  have hold : ∀ {c : BlockId}, c ∈ blocksAt D (S.slotRound k + 2) →
      (parentsVoting D c b).Nonempty → b ∈ D.ids := by
    intro c hc hne
    have hcD : c ∈ D.ids := by simp only [blocksAt, Finset.mem_filter] at hc; exact hc.1
    exact (old_of_parentsVoting hcD hne).1
  constructor
  · rintro ⟨hslot, hbranch⟩
    have hbold : b ∈ D.ids := by
      rcases hbranch with ⟨c, hc, hre, hcert⟩ | ⟨ev, hcard, hev⟩
      · obtain ⟨hcD, hcre⟩ := hlayer hc hre
        refine hold hcD ?_
        rw [← parentsVoting_eq hb (by simp only [blocksAt, Finset.mem_filter] at hcD; exact hcD.1)
          (by simp only [blocksAt, Finset.mem_filter] at hcD; omega)
          (by simp only [blocksAt, Finset.mem_filter] at hcD; omega) b]
        exact nonempty_of_spCertificate hcert
      · have hpos : 0 < ev.card := by
          have := params_arith (Validator := Validator)
          simp only [spQuorum] at hcard; omega
        obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
        obtain ⟨c, hc, hre, -, hfp⟩ := hev v₀ hv₀
        obtain ⟨hcD, hcre⟩ := hlayer hc hre
        refine hold hcD ?_
        rw [← parentsVoting_eq hb (by simp only [blocksAt, Finset.mem_filter] at hcD; exact hcD.1)
          (by simp only [blocksAt, Finset.mem_filter] at hcD; omega)
          (by simp only [blocksAt, Finset.mem_filter] at hcD; omega) b]
        exact nonempty_of_fpEvidence hfp
    refine ⟨mem_slotBlocks_of_old hb hrk hlk h1 (by omega) hbold hslot, ?_⟩
    rcases hbranch with ⟨c, hc, hre, hcert⟩ | ⟨ev, hcard, hev⟩
    · obtain ⟨hcD, hcre⟩ := hlayer hc hre
      simp only [blocksAt, Finset.mem_filter] at hcD
      exact Or.inl ⟨c, by simp only [blocksAt, Finset.mem_filter]; exact hcD, hcre,
        (spCertificate_iff hb hcD.1 (by omega) (by omega)).1 hcert⟩
    · refine Or.inr ⟨ev, hcard, fun v hv => ?_⟩
      obtain ⟨c, hc, hre, hcc, hfp⟩ := hev v hv
      obtain ⟨hcD, hcre⟩ := hlayer hc hre
      have hcD' : c ∈ D.ids ∧ (D.block c).round = S.slotRound k + 2 := by
        simp only [blocksAt, Finset.mem_filter] at hcD; exact hcD
      refine ⟨c, hcD, hcre, ?_, (fpEvidence_iff hb hcD'.1 (by omega) (by omega) b).1 hfp⟩
      rw [← (AnchoredRule.band_block hb hcD'.1 (by omega) (by omega)).2]; exact hcc
  · rintro ⟨hslot, hbranch⟩
    refine ⟨slotBlocks_subset hb hrk hlk h1 (by omega) hslot, ?_⟩
    rcases hbranch with ⟨c, hc, hre, hcert⟩ | ⟨ev, hcard, hev⟩
    · have hcD : c ∈ D.ids ∧ (D.block c).round = S.slotRound k + 2 := by
        simp only [blocksAt, Finset.mem_filter] at hc; exact hc
      obtain ⟨hc', hre'⟩ := hlayer' hc hre
      exact Or.inl ⟨c, hc', hre', (spCertificate_iff hb hcD.1 (by omega) (by omega)).2 hcert⟩
    · refine Or.inr ⟨ev, hcard, fun v hv => ?_⟩
      obtain ⟨c, hc, hre, hcc, hfp⟩ := hev v hv
      have hcD : c ∈ D.ids ∧ (D.block c).round = S.slotRound k + 2 := by
        simp only [blocksAt, Finset.mem_filter] at hc; exact hc
      obtain ⟨hc', hre'⟩ := hlayer' hc hre
      refine ⟨c, hc', hre', ?_, (fpEvidence_iff hb hcD.1 (by omega) (by omega) b).2 hfp⟩
      rw [(AnchoredRule.band_block hb hcD.1 (by omega) (by omega)).2]; exact hcc

open scoped Classical in
/-- **And so the tie-break is the same function.** It names the least
block of the slot the anchor indirectly commits, and both the slot and
the rule are settled by the band, so the two sides filter the same set
and take the same minimum. This is what lets the reverse pass be
compared across a band at all: `choose` is shared between validators by
construction, and here it is shared between DAGs. -/
theorem chooseLeast_band [LinearOrder BlockId] (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g + 2 ≤ hi)
    {A : BlockId} (hAD : A ∈ D.ids) (hAlo : lo ≤ (D.block A).round + g)
    (hAhi : (D.block A).round + g ≤ hi) :
    chooseLeast S' D' A k' = chooseLeast S D A k := by
  have hset : (slotBlocks S' D' k').filter (fun b => IndirectCommit S' D' A k' b) =
      (slotBlocks S D k).filter (fun b => IndirectCommit S D A k b) := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      have hd := (indirectCommit_iff hb hrk hlk h1 h2 hAD hAlo hAhi b).1 h
      exact ⟨hd.1, hd⟩
    · rintro ⟨-, h⟩
      have hd := (indirectCommit_iff hb hrk hlk h1 h2 hAD hAlo hAhi b).2 h
      exact ⟨hd.1, hd⟩
  unfold chooseLeast
  simp only [hset]

end Band

/-! ## The band laws

What the relation's band induction asks of the rules: the direct
predicates a view evaluates carry across a band the view holds, the rung
carries across at the universe both ways, and a candidate the band did
not carry is linked from no old anchor — which is the forward direction
of `indirectCommit_iff` read at a block the band could not have
placed. -/

/-- **FinWhale's band laws.** -/
theorem finWhaleBandLaws [LinearOrder BlockId] :
    (finWhaleAnchored Validator BlockId Payload).BandLaws where
  commit_band := by
    intro S S' U U' lo hi g g' V V' k k' L h hkk hlk hlo hhi hV hL hc
    simp only [finWhaleAnchored_wave] at hhi
    have hbV := AnchoredRule.agreeBand_view h hV
    have hLr : (U.block L).round = S.slotRound k := hL.2.1
    have hlink : ((V.toRecord).block L).round = (U.block L).round := rfl
    exact Band.directCommit hbV (mem_view_of_directCommit hc) (by omega) (by omega) hc
  skip_band := by
    intro S S' U U' lo hi g g' V V' k k' h hkk hlk hlo hhi hV hs
    simp only [finWhaleAnchored_wave] at hhi
    exact Band.directSkip (AnchoredRule.agreeBand_view h hV) hkk hlk (by omega) (by omega) hs
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk hlk hlo hhi hi _
    simp only [finWhaleAnchored_wave] at hhi
    rcases i with _ | i
    · exact Band.indirectCommit_iff h hkk hlk hlo (by omega) hA hAlo hAhi L
    · exact absurd hi (by change ¬ (i + 1 < 1); omega)
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk hlk hlo hhi hi _ hLo hlink
    simp only [finWhaleAnchored_wave] at hhi
    rcases i with _ | i
    · exact hLo (mem_slotBlocks.1
        ((Band.indirectCommit_iff h hkk hlk hlo (by omega) hA hAlo hAhi L).1 hlink).1).1
    · exact absurd hi (by change ¬ (i + 1 < 1); omega)

end FinWhale

end LeanDag
