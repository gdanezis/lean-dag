import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Candidate
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Optional.SelfParent
/-!
# Chain quality, for any protocol with a quorum law

`docs/target-properties.md` §11.4. CQ1–CQ7 over `Properties.DagRule`,
for any rule with `causal`, `Quorate` and `CommitsCandidate`; the
inclusion half adds `LeaderCommits`, `SelfParent` and `NoEquiv` for the
author's self-reference chain, with no synchrony. Chain quality is a
statement about what a *single* commit carries, so no band, agreement
or view monotonicity is needed either.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload} {rel : Reliability Validator}
variable {U : R.Universe} {b L : BlockId} {δ : ℕ}

/-! ## Coverage -/

/-- The reliable validators whose round-`δ` block a cone carries — the
complement, within the reliable set, of `missingAtFrom`. -/
def coveredAt (R : DagRule Validator BlockId Payload) (rel : Reliability Validator)
    (U : R.Universe) (b : BlockId) (δ : ℕ) : Finset Validator :=
  rel.correct.filter fun v =>
    ∃ i ∈ historyFrom (R.block U) b, (R.block U i).creator = v ∧ (R.block U i).round = δ

theorem mem_coveredAt {v : Validator} :
    v ∈ coveredAt R rel U b δ ↔ v ∈ rel.correct ∧
      ∃ i ∈ historyFrom (R.block U) b,
        (R.block U i).creator = v ∧ (R.block U i).round = δ :=
  Finset.mem_filter

theorem coveredAt_subset_correct : coveredAt R rel U b δ ⊆ rel.correct :=
  Finset.filter_subset _ _

/-- Covered and missing partition the reliable validators. -/
theorem coveredAt_eq_sdiff :
    coveredAt R rel U b δ = rel.correct \ missingAtFrom (R.block U) rel b δ := by
  ext v
  rw [mem_coveredAt, Finset.mem_sdiff, mem_missingAtFrom]
  constructor
  · rintro ⟨hv, i, hi, hic, hir⟩
    exact ⟨hv, fun ⟨_, hall⟩ => hall i hi ⟨hic, hir⟩⟩
  · rintro ⟨hv, hmiss⟩
    refine ⟨hv, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hmiss ⟨hv, fun i hi ⟨hic, hir⟩ => hnone i hi hic hir⟩

/-- **CQ1, the count.** A block's cone covers all but at most the slack
of the reliable validators, at every round below it. Purely structural:
density plus the partition. -/
theorem card_coveredAt_ge (hq : Quorate R rel)
    (hb : b ∈ R.ids U) (hδ : δ < (R.block U b).round) :
    rel.correct.card - rel.slack ≤ (coveredAt R rel U b δ).card := by
  have hsub : missingAtFrom (R.block U) rel b δ ⊆ rel.correct := Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_of_subset hsub
  have hmiss := card_missingAtFrom_le (R.causal U) (hq U) hb hδ
  rw [coveredAt_eq_sdiff, hcard]
  omega

/-- **CQ2, where the committee gives it.** Every cone carries, at every
round below it, blocks from at least half the reliable validators.
`hhalf` is a hypothesis rather than a field of `Reliability`, since not
every model's committee gives it. -/
theorem card_correct_le_two_mul_coveredAt (hq : Quorate R rel)
    (hhalf : 2 * rel.slack ≤ rel.correct.card)
    (hb : b ∈ R.ids U) (hδ : δ < (R.block U b).round) :
    rel.correct.card ≤ 2 * (coveredAt R rel U b δ).card := by
  have := card_coveredAt_ge hq hb hδ
  omega

/-! ## What a commit carries

`CommitsCandidate` makes a committed block a block, so coverage applies
to it. -/

section Decided

variable {S : Slots Validator} {V : R.View U} {k : ℕ}

/-- **CQ1.** A committed leader's flush covers all but the slack of the
reliable validators at every round below it — any route, any view, no
synchrony. -/
theorem card_coveredAt_ge_of_decided (hq : Quorate R rel)
    (hcc : CommitsCandidate R) (h : R.Decided S V k (some L))
    (hδ : δ < (R.block U L).round) :
    rel.correct.card - rel.slack ≤ (coveredAt R rel U L δ).card :=
  card_coveredAt_ge hq (hcc.mem h) hδ

/-- **CQ2.** -/
theorem card_correct_le_two_mul_coveredAt_of_decided (hq : Quorate R rel)
    (hcc : CommitsCandidate R) (hhalf : 2 * rel.slack ≤ rel.correct.card)
    (h : R.Decided S V k (some L)) (hδ : δ < (R.block U L).round) :
    rel.correct.card ≤ 2 * (coveredAt R rel U L δ).card :=
  card_correct_le_two_mul_coveredAt hq hhalf (hcc.mem h) hδ

/-- **The ledger a verdict assignment names**: everything in the causal
history of a committed leader of a slot below `n`. The core's
`ledgerSet` at the carrier. -/
def ledgerSetOf (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ ReachesFrom (R.block U) L b}

/-- A cone block of a committed slot is in the ledger. -/
theorem mem_ledgerSetOf_of_mem_history {g : ℕ → Option BlockId} {n : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ R.ids U)
    (hb : b ∈ historyFrom (R.block U) L) : b ∈ ledgerSetOf R U g n :=
  ⟨k, hk, L, hg, ((R.causal U).mem_history_iff hL).mp hb⟩

/-- **CQ3 (ledger coverage, cumulative).** For a verdict assignment `g`
with a committed slot `k < n` whose leader sits at round `r`: for every
`δ < r`, at least `|correct| − slack` reliable validators each have a
round-`δ` block in the ledger. The set is exhibited, so no choice and no
decidability of the ledger is needed. -/
theorem ledger_coverage (hq : Quorate R rel) (hcc : CommitsCandidate R)
    {g : ℕ → Option BlockId} {n : ℕ}
    (hdec : R.Decided S V k (some L)) (hg : g k = some L) (hk : k < n)
    (hδ : δ < (R.block U L).round) :
    ∃ W : Finset Validator, W ⊆ rel.correct ∧
      rel.correct.card - rel.slack ≤ W.card ∧
      ∀ v ∈ W, ∃ i ∈ ledgerSetOf R U g n,
        (R.block U i).creator = v ∧ (R.block U i).round = δ := by
  refine ⟨coveredAt R rel U L δ, coveredAt_subset_correct,
    card_coveredAt_ge_of_decided hq hcc hdec hδ, ?_⟩
  intro v hv
  obtain ⟨-, i, hi, hic, hir⟩ := mem_coveredAt.mp hv
  exact ⟨i, mem_ledgerSetOf_of_mem_history hg hk (hcc.mem hdec) hi, hic, hir⟩

/-! ## Inclusion, from self-reference

A reliable author's blocks form a chain — one per round (`NoEquiv`),
each referencing the one before (`SelfParent`) — so any later block by
the author reaches every earlier one, with no synchrony needed. -/

/-- **CQ5.** A reliable block is in the cone of every committed leader
block by the same author at or above its round — any commit route, any
view, no synchrony. -/
theorem mem_history_of_decided_commit (hsp : SelfParent R) (hne : NoEquiv R rel)
    (hcc : CommitsCandidate R)
    (hdec : R.Decided S V k (some L))
    (hLc : (R.block U L).creator ∈ rel.correct)
    (hb : b ∈ R.ids U) (hbc : (R.block U b).creator = (R.block U L).creator)
    (hle : (R.block U b).round ≤ (R.block U L).round) :
    b ∈ historyFrom (R.block U) L :=
  ((R.causal U).mem_history_iff (hcc.mem hdec)).mpr
    (hsp.reaches_of_creator hne hb (hcc.mem hdec) (by rw [hbc]; exact hLc) hbc.symm hle)

/-! ## Inclusion liveness

The slot is fixed by the schedule before the universe is quantified;
any execution meeting the rule's own liveness precondition commits
it. -/

/-- **What a reliably-led slot includes.** Any execution meeting the
rule's precondition at slot `k'` commits a leader block whose history
holds every block by that leader at any round up to the slot's; hence
every such block is in the ledger of any verdict assignment covering
the slot. -/
theorem includes_of_leads
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator →
      ℕ → ℕ → Prop}
    (hsp : SelfParent R) (hne : NoEquiv R rel) (hcc : CommitsCandidate R)
    (hlc : LeaderCommits R Live) (S : Slots Validator) {T : Finset Validator}
    (hT : T ⊆ rel.correct) {k' m : ℕ} (hlead : S.leader k' ∈ T) (hm : m ≤ S.slotRound k')
    (U : R.Universe) (V : R.View U) (hlive : Live S V T k' (k' + 1)) :
    ∃ L, R.Decided S V k' (some L) ∧
      ∀ b ∈ R.ids U, (R.block U b).creator = S.leader k' → (R.block U b).round = m →
        b ∈ historyFrom (R.block U) L ∧
          ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
            b ∈ ledgerSetOf R U g n := by
  obtain ⟨L, -, hdec, -⟩ := hlc S V T k' (k' + 1) hlive k' le_rfl (Nat.lt_succ_self k') hlead
  refine ⟨L, hdec, fun b hb hbc hbr => ?_⟩
  obtain ⟨-, hLr, hLc⟩ := hcc S U V k' L hdec
  have hmem : b ∈ historyFrom (R.block U) L :=
    mem_history_of_decided_commit hsp hne hcc hdec (by rw [hLc]; exact hT hlead) hb
      (by rw [hbc, hLc]) (by rw [hbr, hLr]; exact hm)
  exact ⟨hmem, fun g n hg hn => mem_ledgerSetOf_of_mem_history hg hn (hcc.mem hdec) hmem⟩

/-- **CQ6 (inclusion liveness).** Under a schedule returning to every
reliable validator, every reliable block is in the ledger of the slot
its author next leads and commits. Fairness is per validator, since the
argument runs along one author's chain. -/
theorem committed_of_correct_block
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator →
      ℕ → ℕ → Prop}
    (hsp : SelfParent R) (hne : NoEquiv R rel) (hcc : CommitsCandidate R)
    (hlc : LeaderCommits R Live) (S : Slots Validator) {T : Finset Validator}
    (hT : T ⊆ rel.correct) (fair : ∀ v ∈ T, ∀ n, ∃ k, n ≤ k ∧ S.leader k = v)
    (m : ℕ) {v : Validator} (hv : v ∈ T) :
    ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      ∀ (U : R.Universe) (V : R.View U), Live S V T k' (k' + 1) →
        ∃ L, R.Decided S V k' (some L) ∧
          ∀ b ∈ R.ids U, (R.block U b).creator = v → (R.block U b).round = m →
            b ∈ historyFrom (R.block U) L ∧
              ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
                b ∈ ledgerSetOf R U g n := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded m
  obtain ⟨k', hk', hlead⟩ := fair v hv k₀
  have hm : m ≤ S.slotRound k' := le_trans hk₀ (S.mono hk')
  refine ⟨k', hm, hlead, fun U V hlive => ?_⟩
  have h := includes_of_leads hsp hne hcc hlc S hT (by rw [hlead]; exact hv) hm U V hlive
  rw [hlead] at h
  exact h

/-! ## The capstone -/

/-- **CQ7 (the capstone).** Chain quality in one statement: every
commit's flush covers half the reliable validators, and under a
returning schedule every reliable block is in the flush of a slot its
author leads. -/
theorem chain_quality
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator →
      ℕ → ℕ → Prop}
    (hq : Quorate R rel) (hsp : SelfParent R) (hne : NoEquiv R rel) (hcc : CommitsCandidate R)
    (hlc : LeaderCommits R Live) (hhalf : 2 * rel.slack ≤ rel.correct.card)
    (S : Slots Validator) {T : Finset Validator} (hT : T ⊆ rel.correct)
    (fair : ∀ v ∈ T, ∀ n, ∃ k, n ≤ k ∧ S.leader k = v) (m : ℕ) :
    (∀ (U : R.Universe) (V : R.View U) (k : ℕ) (L : BlockId) (δ : ℕ),
        R.Decided S V k (some L) → δ < (R.block U L).round →
        rel.correct.card ≤ 2 * (coveredAt R rel U L δ).card) ∧
    ∀ v ∈ T, ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      ∀ (U : R.Universe) (V : R.View U), Live S V T k' (k' + 1) →
        ∃ L, R.Decided S V k' (some L) ∧
          ∀ b ∈ R.ids U, (R.block U b).creator = v → (R.block U b).round = m →
            b ∈ historyFrom (R.block U) L ∧
              ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
                b ∈ ledgerSetOf R U g n :=
  ⟨fun _ _ _ _ _ hdec hδ =>
    card_correct_le_two_mul_coveredAt_of_decided hq hcc hhalf hdec hδ,
   fun v hv => committed_of_correct_block hsp hne hcc hlc S hT fair m hv⟩

end Decided

end Arcs

end Properties

end LeanDag
