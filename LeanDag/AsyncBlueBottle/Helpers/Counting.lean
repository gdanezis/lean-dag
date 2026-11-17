import LeanDag.AsyncBlueBottle.Model.Good
import LeanDag.AsyncBlueBottle.Helpers.Rules
import LeanDag.MahiMahi.Helpers.Counting
import LeanDag.Common.CommonCore
import Mathlib.Combinatorics.Enumerative.DoubleCounting
/-!
# Helpers — the counting layer

Generated lemma infrastructure for `Counting/Statement.lean`; not part of
the audit surface. Reaching a correct candidate is voting for it, so a
candidate every decision-round block reaches is directly committed by a
reliable quorum; the common core supplies one such candidate, and a
double count over the references from the reliable round-`(r + 1)`
blocks to the correct round-`r` blocks supplies `2f + 1` of them, each
referenced by `f + 1` reliable blocks and hence reached by every
round-`(r + 2)` block. The multi-leader corollary is counting over
these.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

theorem mem_goodAt {r : ℕ} {v : Validator} :
    v ∈ goodAt U r ↔ ∃ L ∈ U.ids,
      (U.block L).round = r ∧ (U.block L).creator = v ∧ DirectCommit U L r := by
  simp [goodAt]

/-- If every decision-round block reaches a correct candidate, and a
quorum populates the decision round, the candidate is directly
committed: reaching a correct block is voting for it. -/
theorem directCommit_of_reach {r : ℕ} {L : BlockId} {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) (hpop : PopulatedOn U T (r + 2))
    (hL : L ∈ U.ids) (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hreach : ∀ q ∈ U.ids, (U.block q).round = r + 2 → Reaches U q L) :
    DirectCommit U L r := by
  unfold DirectCommit
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqc, hqr⟩ := hpop v hv
  rw [mem_supporters]
  exact ⟨q, hq, hqr, MahiMahi.votes_of_reaches hq hL hLc (hreach q hq hqr), hqc⟩

/-- **ABB6.** The common core of round `r` is reached by every block two
rounds up, so every decision-round block of the populating quorum votes
for it — correct or not. -/
theorem goodNonempty {T : Finset Validator} {r : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hpop : PopulatedOn U T (r + 2)) :
    (goodAt U r ∩ (Correct : Finset Validator)).Nonempty := by
  obtain ⟨v₀, hv₀⟩ := MahiMahi.nonempty_of_quorum hcard
  obtain ⟨c₀, hc₀, -, hc₀r⟩ := hpop v₀ hv₀
  obtain ⟨b, hb, hbr, hbc, hreach⟩ := exists_commonCore card_compl_correct_le card_add_f_lt_two_mul_quorum hc₀ hc₀r
  refine ⟨(U.block b).creator, Finset.mem_inter.mpr ⟨?_, hbc⟩⟩
  rw [mem_goodAt]
  exact ⟨b, hb, hbr, rfl,
    directCommit_of_reach hcard hpop hb hbc fun q hq hqr => hreach q hq (by omega)⟩

/-! ## The double count

Every left vertex has at least `m` neighbours; the right vertices with
more than `d` neighbours number enough to absorb the surplus. -/

/-- **Double counting, threshold form.** If every `a ∈ s` relates to at
least `m` members of `t`, then `|s|·m` is at most `|s|` times the number
of `b ∈ t` related to more than `d` members of `s`, plus `|t|·d`. -/
theorem card_mul_le_of_bipartite {α β : Type*} (s : Finset α) (t : Finset β)
    (rel : α → β → Prop) [∀ a b, Decidable (rel a b)] {m d : ℕ}
    (hm : ∀ a ∈ s, m ≤ (t.bipartiteAbove rel a).card) :
    s.card * m ≤
      (t.filter (fun b => d < (s.bipartiteBelow rel b).card)).card * s.card + t.card * d := by
  classical
  have h1 : s.card * m ≤ ∑ a ∈ s, (t.bipartiteAbove rel a).card := by
    have := Finset.card_nsmul_le_sum s (fun a => (t.bipartiteAbove rel a).card) m hm
    simpa [smul_eq_mul] using this
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow] at h1
  have hsplit := Finset.sum_filter_add_sum_filter_not t
    (fun b => d < (s.bipartiteBelow rel b).card) (fun b => (s.bipartiteBelow rel b).card)
  have hX : ∑ b ∈ t.filter (fun b => d < (s.bipartiteBelow rel b).card),
      (s.bipartiteBelow rel b).card ≤
        (t.filter (fun b => d < (s.bipartiteBelow rel b).card)).card * s.card := by
    have := Finset.sum_le_card_nsmul (t.filter (fun b => d < (s.bipartiteBelow rel b).card))
      (fun b => (s.bipartiteBelow rel b).card) s.card
      (fun b _ => Finset.card_le_card fun a ha => (Finset.mem_filter.mp ha).1)
    simpa [smul_eq_mul] using this
  have hnX : ∑ b ∈ t.filter (fun b => ¬ d < (s.bipartiteBelow rel b).card),
      (s.bipartiteBelow rel b).card ≤
        (t.filter (fun b => ¬ d < (s.bipartiteBelow rel b).card)).card * d := by
    have := Finset.sum_le_card_nsmul (t.filter (fun b => ¬ d < (s.bipartiteBelow rel b).card))
      (fun b => (s.bipartiteBelow rel b).card) d
      (fun b hb => by have := (Finset.mem_filter.mp hb).2; omega)
    simpa [smul_eq_mul] using this
  have hcard : (t.filter (fun b => ¬ d < (s.bipartiteBelow rel b).card)).card ≤ t.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have := Nat.mul_le_mul_right d hcard
  linarith

/-- The arithmetic core of ABB7, isolated from the combinatorics. With
`b = |Byzantine|`, `c = |Correct|`, `l ≥ n − f` reliable round-`(r+1)`
blocks and `x` heavily referenced correct round-`r` authors, the double
count gives `hA`, and fewer than `n − 3f` such authors would force
`(n − f)(2f + 1 − b) ≤ (n − b) f`, false at `n ≥ 5f + 1`. -/
private theorem goodCard_arith {n f b c l x : ℕ} (h5 : 5 * f + 1 ≤ n) (hb : b ≤ f)
    (hcb : c + b = n) (hl : n ≤ l + f) (hA : l * (n - f - b) ≤ x * l + c * f) :
    n ≤ x + 3 * f := by
  -- write f = b + g and n = 3f + b + e, so that no subtraction remains
  obtain ⟨g, hg⟩ : ∃ g, f = b + g := ⟨f - b, by omega⟩
  subst hg
  obtain ⟨e, he⟩ : ∃ e, n = 3 * (b + g) + b + e := ⟨n - 3 * (b + g) - b, by omega⟩
  subst he
  rw [show 3 * (b + g) + b + e - (b + g) - b = 2 * (b + g) + e from by omega] at hA
  have hc : c = 3 * (b + g) + e := by omega
  subst hc
  by_contra hx
  push Not at hx
  -- x + 1 ≤ e + b, and l ≥ 2f + e + b
  have hx' : x + 1 ≤ e + b := by omega
  have hl' : 2 * (b + g) + e + b ≤ l := by omega
  have h1 : (x + 1) * l ≤ (e + b) * l := Nat.mul_le_mul_right l hx'
  have h2 : (2 * (b + g) + e + b) * (b + g + g + 1) ≤ l * (b + g + g + 1) :=
    Nat.mul_le_mul_right _ hl'
  nlinarith [h1, h2, hA, h5]

/-- **ABB7.** -/
theorem goodCard {T : Finset Validator} {r : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1)) (hpop2 : PopulatedOn U T (r + 2)) :
    Fintype.card Validator ≤ (goodAt U r ∩ (Correct : Finset Validator)).card + 3 * F.f := by
  classical
  obtain ⟨hcb, hbf, -⟩ := faults_arith (Validator := Validator)
  have h5 := F.card_validators5
  -- the reliable round-(r+1) blocks, and the reference relation
  set L := (blocksAt U (r + 1)).filter (fun q => (U.block q).creator ∈ T) with hL
  set rel : BlockId → Validator → Prop :=
    fun q w => w ∈ creatorsOf U.block (U.block q).refs with hrel
  set X := (Correct : Finset Validator).filter (fun w => F.f < (L.bipartiteBelow rel w).card)
    with hX
  -- each reliable round-(r+1) block names at least n − f − b correct authors
  have hper : ∀ q ∈ L,
      quorumCard Validator - F.byzantine.card ≤
        ((Correct : Finset Validator).bipartiteAbove rel q).card := by
    intro q hq
    obtain ⟨hqb, -⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq_ids, hq_round⟩ := mem_blocksAt.mp hqb
    have h := le_trans (U.creators_quorum hq_ids (by omega))
      (card_le_card_inter_correct_add_byzantine (creatorsOf U.block (U.block q).refs))
    change quorumCard Validator - F.byzantine.card
      ≤ ((Correct : Finset Validator).filter
          (fun v => v ∈ creatorsOf U.block (U.block q).refs)).card
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
    omega
  have hdouble := card_mul_le_of_bipartite L (Correct : Finset Validator) rel (d := F.f) hper
  -- the reliable set injects into L through its round-(r+1) blocks
  have hTL : T.card ≤ L.card := by
    refine le_trans (Finset.card_le_card (t := creatorsOf U.block L) ?_) Finset.card_image_le
    intro v hv
    obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
    exact mem_creatorsOf.mpr
      ⟨q, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hq, hqr⟩, hqc ▸ hv⟩, hqc⟩
  -- the arithmetic: at least n − 3f heavily referenced correct authors
  have hXcard : Fintype.card Validator ≤ X.card + 3 * F.f :=
    goodCard_arith h5 hbf hcb (by omega) hdouble
  -- and each of them is good
  have hsub : X ⊆ goodAt U r ∩ (Correct : Finset Validator) := by
    intro w hw
    obtain ⟨hwC, hdeg⟩ := Finset.mem_filter.mp hw
    set Lw := L.bipartiteBelow rel w with hLw
    -- some reliable block references a round-r block by `w`
    obtain ⟨q₀, hq₀⟩ := Finset.card_pos.mp (by omega : 0 < Lw.card)
    obtain ⟨hq₀L, hq₀w⟩ := Finset.mem_filter.mp hq₀
    obtain ⟨hq₀b, -⟩ := Finset.mem_filter.mp hq₀L
    obtain ⟨hq₀_ids, hq₀_round⟩ := mem_blocksAt.mp hq₀b
    obtain ⟨bw, hbw_mem, hbw_creator⟩ := mem_creatorsOf.mp hq₀w
    have hbw_ids : bw ∈ U.ids := U.complete _ hq₀_ids _ hbw_mem
    have hbw_round : (U.block bw).round = r := by
      have := U.round_of_mem_refs hq₀_ids hbw_mem; omega
    have hbw_correct : (U.block bw).creator ∈ (Correct : Finset Validator) := by
      rw [hbw_creator]; exact hwC
    -- the authors of `Lw`: f + 1 reliable validators, each referencing `bw`
    set Sw := creatorsOf U.block Lw with hSw
    have hSw_sub : Sw ⊆ T := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := mem_creatorsOf.mp hv
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    have hSw_card : F.f + 1 ≤ Sw.card := by
      rw [hSw, creatorsOf, Finset.card_image_of_injOn]
      · omega
      · intro q hq q' hq' h
        obtain ⟨hqb, hqT⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
        obtain ⟨hq'b, -⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hq').1
        obtain ⟨hq_ids, hq_round⟩ := mem_blocksAt.mp hqb
        obtain ⟨hq'_ids, hq'_round⟩ := mem_blocksAt.mp hq'b
        exact U.eq_of_creator_eq hq_ids hq'_ids (hT hqT) rfl h.symm (by rw [hq_round, hq'_round])
    have hSw_support : ∀ v ∈ Sw, ∃ b' ∈ U.ids,
        (U.block b').round = r + 1 ∧ bw ∈ (U.block b').refs ∧ (U.block b').creator = v := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := mem_creatorsOf.mp hv
      obtain ⟨hqL, hqw⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqb, -⟩ := Finset.mem_filter.mp hqL
      obtain ⟨hq_ids, hq_round⟩ := mem_blocksAt.mp hqb
      obtain ⟨i, hi_mem, hi_creator⟩ := mem_creatorsOf.mp hqw
      have hi_ids : i ∈ U.ids := U.complete q hq_ids i hi_mem
      have hi_round : (U.block i).round = r := by
        have := U.round_of_mem_refs hq_ids hi_mem; omega
      have hib : i = bw :=
        U.eq_of_creator_eq hi_ids hbw_ids hwC hi_creator hbw_creator (by rw [hi_round, hbw_round])
      exact ⟨q, hq_ids, hq_round, hib ▸ hi_mem, rfl⟩
    -- every round-(r+2) block reaches `bw`, so every reliable one votes for it
    have hreach : ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw := fun c hc hcr =>
      reaches_of_honest_support_of_card hSw_support (fun v hv => hT (hSw_sub hv))
        (lt_card_add_quorumCard hSw_card) hc hcr
    refine Finset.mem_inter.mpr ⟨?_, hwC⟩
    rw [mem_goodAt]
    exact ⟨bw, hbw_ids, hbw_round, hbw_creator,
      directCommit_of_reach hcard hpop2 hbw_ids hbw_correct hreach⟩
  have := Finset.card_le_card hsub
  omega

/-- **ABB8.** `n − 3f` good correct validators and `3f + 1` leaders cannot
be disjoint in `n`. -/
theorem multiLeader [S : Slots Validator] {T : Finset Validator} {r : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1)) (hpop2 : PopulatedOn U T (r + 2))
    {M : Finset Validator} (hM : ∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v)
    (hMcard : 3 * F.f + 1 ≤ M.card) :
    ∃ k, S.slotRound k = r ∧ S.leader k ∈ good U k := by
  have hg := goodCard hT hcard hpop1 hpop2
  have hne : (M ∩ (goodAt U r ∩ (Correct : Finset Validator))).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.card_union_add_card_inter M (goodAt U r ∩ (Correct : Finset Validator))
    have h2 : (M ∪ (goodAt U r ∩ (Correct : Finset Validator))).card ≤ Fintype.card Validator :=
      Finset.card_le_univ _
    omega
  obtain ⟨v, hv⟩ := hne
  rw [Finset.mem_inter] at hv
  obtain ⟨k, hk, hkv⟩ := hM v hv.1
  refine ⟨k, hk, ?_⟩
  unfold good
  rw [hk, hkv]
  exact (Finset.mem_inter.mp hv.2).1

end AsyncBlueBottle

end LeanDag
