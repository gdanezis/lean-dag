import LeanDag.Common.Causality
import LeanDag.Common.Participation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Density, over the raw block data

**A cone cannot be selectively blind.** A valid block references a
quorum of distinct authors one round below, of which at most `f` are
Byzantine, so a correct author always appears one round down — and, by
induction, all but at most `f` of the correct authors appear at *every*
round below (D25). Stated at the lowest level it is true: a block
assignment, a set of ids, the causal structure relating them, and one
counting law about references — nothing about verdicts, views or
schedules — so one induction serves every rule that shows
`Properties.Quorate`.

Two results: `card_missingAtFrom_le` is D25 itself; `mem_historyFrom_of_correct`
is the **backbone** it feeds — after synchrony settles, a correct
block's history holds every correct block of every round since.
Neither needs population, delivery or self-parents.

**The fault model is a parameter.** Six fault classes are in play across
the rules, and `Reliability` bundles what density's count actually
needs of any of them: a reliable set, a slack bounding everything
outside it, and the slack a minority.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

/-- **A reliable set, and the slack around it.** What a counting
argument needs of a fault model, with no commitment to which one: the
validators worth counting, a bound on everything else, and that bound a
minority — which is what lets a quorum of references always contain a
reliable one, the step density's induction takes. -/
structure Reliability (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The validators the count is about. -/
  correct : Finset Validator
  /-- A bound on everything outside them. -/
  slack : ℕ
  /-- And it is a bound. -/
  covers : correctᶜ.card ≤ slack
  /-- The slack is a minority of the committee. -/
  minority : 2 * slack < Fintype.card Validator

namespace Reliability

variable (rel : Reliability Validator)

/-- The reliable set is what the slack leaves. -/
theorem card_correct : Fintype.card Validator ≤ rel.correct.card + rel.slack := by
  have := Finset.card_add_card_compl rel.correct
  have := rel.covers
  omega

/-- **A quorum of the reliable set**: inside it, and at least `n − slack`
strong — which is each rule's own quorum read off its fault model, the
core's `n − f`, Nemo's majority, Hydrozoan's `n − f − c`. -/
def IsQuorum (T : Finset Validator) : Prop :=
  T ⊆ rel.correct ∧ Fintype.card Validator - rel.slack ≤ T.card

/-- Decidable on concrete data. -/
instance decidableIsQuorum (T : Finset Validator) : Decidable (rel.IsQuorum T) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The reliable set is a quorum of itself. -/
theorem isQuorum_correct : rel.IsQuorum rel.correct :=
  ⟨Finset.Subset.rfl, by have := rel.card_correct; omega⟩

/-- A set clearing the quorum threshold meets the reliable set. -/
theorem exists_correct_of_card {S : Finset Validator}
    (h : Fintype.card Validator - rel.slack ≤ S.card) :
    ∃ v ∈ S, v ∈ rel.correct := by
  by_contra hno
  push Not at hno
  have hsub : S ⊆ rel.correctᶜ := fun v hv => Finset.mem_compl.2 (hno v hv)
  have := Finset.card_le_card hsub
  have := rel.covers
  have := rel.minority
  omega

end Reliability

variable {rel : Reliability Validator}

/-- **A quorum of authors below every block.** The counting half of
block validity, and the only half density reads. Stated over the
references rather than a `ValidWrt`-style record, so a rule whose
validity is packaged differently supplies it by projection. -/
def QuorateOn (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (rel : Reliability Validator) : Prop :=
  ∀ b ∈ ids, 0 < (blk b).round →
    Fintype.card Validator - rel.slack ≤ (creatorsOf blk (blk b).refs).card

/-- **A correct author one round down.** A non-genesis block references
`n − f` distinct authors and at most `f` of them are Byzantine, so one
of its references is a correct block of the round below. -/
theorem exists_correct_memRefs (C : CausalStructure blk ids) (hq : QuorateOn blk ids rel)
    {b : BlockId} (hb : b ∈ ids) (hround : 0 < (blk b).round) :
    ∃ i ∈ (blk b).refs, i ∈ ids ∧
      (blk i).creator ∈ rel.correct ∧
      (blk i).round + 1 = (blk b).round := by
  obtain ⟨v, hv, hvc⟩ := rel.exists_correct_of_card (hq b hb hround)
  obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hv
  exact ⟨i, hi, C.complete b hb i hi, hvc, C.refs_round b hb i hi⟩

section Density

variable [DecidableEq BlockId]

/-- The correct authors with no block at round `δ` in `b`'s history. -/
def missingAtFrom (blk : BlockId → Block Validator BlockId Payload)
    (rel : Reliability Validator) (b : BlockId) (δ : ℕ) : Finset Validator :=
  rel.correct.filter fun v =>
    ∀ i ∈ historyFrom blk b, ¬ ((blk i).creator = v ∧ (blk i).round = δ)

theorem mem_missingAtFrom {b : BlockId} {δ : ℕ} {v : Validator} :
    v ∈ missingAtFrom blk rel b δ ↔ v ∈ rel.correct ∧
      ∀ i ∈ historyFrom blk b, ¬ ((blk i).creator = v ∧ (blk i).round = δ) := by
  simp [missingAtFrom]

/-- Missing is monotone through references: what `b` lacks, its
references lack. -/
theorem missingAtFrom_subset_of_mem_refs (C : CausalStructure blk ids)
    {b p : BlockId} (hb : b ∈ ids) (hp : p ∈ (blk b).refs) {δ : ℕ} :
    missingAtFrom blk rel b δ ⊆ missingAtFrom blk rel p δ := by
  intro v hv
  rw [mem_missingAtFrom] at hv ⊢
  exact ⟨hv.1, fun i hi => hv.2 i
    (C.history_subset_of_reaches hb (Relation.ReflTransGen.single hp) hi)⟩

/-- The one-round case: the references themselves witness all but at
most `f` of the correct authors of the round below. -/
private theorem card_missingAtFrom_le_base (C : CausalStructure blk ids)
    (hq : QuorateOn blk ids rel) {b : BlockId} (hb : b ∈ ids) {δ : ℕ}
    (hδ : δ + 1 = (blk b).round) : (missingAtFrom blk rel b δ).card ≤ rel.slack := by
  have hquorum := hq b hb (by omega)
  have hinter : (creatorsOf blk (blk b).refs).card ≤
      (creatorsOf blk (blk b).refs ∩ rel.correct).card + rel.correctᶜ.card := by
    have hsplit : creatorsOf blk (blk b).refs ⊆
        (creatorsOf blk (blk b).refs ∩ rel.correct) ∪ rel.correctᶜ := by
      intro v hv
      by_cases hc : v ∈ rel.correct
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, hc⟩)
      · exact Finset.mem_union_right _ (Finset.mem_compl.2 hc)
    exact le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  have hbad := rel.covers
  have hpart : rel.correct.card + rel.correctᶜ.card = Fintype.card Validator :=
    Finset.card_add_card_compl _
  have hdisj : ∀ v ∈ creatorsOf blk (blk b).refs ∩ rel.correct,
      v ∉ missingAtFrom blk rel b δ := by
    intro v hv hmiss
    rw [Finset.mem_inter] at hv
    obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hv.1
    rw [mem_missingAtFrom] at hmiss
    exact hmiss.2 p (C.mem_history_of_mem_refs hb hp)
      ⟨hpc, by have := C.refs_round b hb p hp; omega⟩
  have hsub : (creatorsOf blk (blk b).refs ∩ rel.correct)
      ∪ missingAtFrom blk rel b δ ⊆ rel.correct := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact (mem_missingAtFrom.mp h).1
  have hunion := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr hdisj)] at hunion
  omega

private theorem card_missingAtFrom_le_aux (C : CausalStructure blk ids)
    (hq : QuorateOn blk ids rel) (n : ℕ) :
    ∀ {b : BlockId}, b ∈ ids → ∀ {δ : ℕ}, δ < (blk b).round →
      (blk b).round - δ ≤ n + 1 → (missingAtFrom blk rel b δ).card ≤ rel.slack := by
  induction n with
  | zero =>
      intro b hb δ hδ hfuel
      exact card_missingAtFrom_le_base C hq hb (by omega)
  | succ n ih =>
      intro b hb δ hδ hfuel
      rcases Nat.lt_or_ge δ ((blk b).round - 1) with hlt | hge
      · obtain ⟨p, hp, hpids, -, hpround⟩ := exists_correct_memRefs C hq hb (by omega)
        exact le_trans
          (Finset.card_le_card (missingAtFrom_subset_of_mem_refs C hb hp))
          (ih hpids (by omega) (by omega))
      · exact card_missingAtFrom_le_base C hq hb (by omega)

/-- **D25 (density).** A block's history contains a block by all but at
most `f` of the correct authors at every round strictly below it. -/
theorem card_missingAtFrom_le (C : CausalStructure blk ids) (hq : QuorateOn blk ids rel)
    {b : BlockId} (hb : b ∈ ids) {δ : ℕ} (hδ : δ < (blk b).round) :
    (missingAtFrom blk rel b δ).card ≤ rel.slack :=
  card_missingAtFrom_le_aux C hq ((blk b).round - δ) hb hδ (by omega)

/-- **The backbone.** After `R`, a correct block's history holds every
correct block of every round from `R` up to its own — no population
hypothesis, since a block always has a correct reference one round down
(`exists_correct_memRefs`). -/
theorem mem_historyFrom_of_correct (C : CausalStructure blk ids) (hq : QuorateOn blk ids rel)
    {R : ℕ} (hs : SynchronisedFrom blk ids rel.correct R) :
    ∀ d : ℕ, ∀ c ∈ ids, ∀ a ∈ ids,
      (blk c).creator ∈ rel.correct →
      (blk a).creator ∈ rel.correct →
      R ≤ (blk a).round → (blk a).round + 1 + d = (blk c).round →
      a ∈ historyFrom blk c := by
  intro d
  induction d with
  | zero =>
      intro c hc a ha hcc hac hR hround
      exact C.mem_history_of_mem_refs hc
        (hs (blk a).round hR c hc (by omega) hcc a ha rfl hac)
  | succ d ih =>
      intro c hc a ha hcc hac hR hround
      obtain ⟨w, hw, hwids, hwc, hwround⟩ := exists_correct_memRefs C hq hc (by omega)
      exact C.history_subset_of_reaches hc (Relation.ReflTransGen.single hw)
        (ih w hwids a ha hwc hac hR (by omega))

end Density

end LeanDag
