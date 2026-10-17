import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
/-!
# Counting in a committee

Two sets whose sizes sum past `n + m` meet outside any set of at most
`m` members. Every quorum-intersection lemma of the development is this
at its thresholds, and every "two quorums cannot both exist" argument
its contrapositive.
-/

namespace LeanDag

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two sets meet in at least `|A| + |B| − n` members, stated additively
so that `omega` never sees a truncated subtraction. -/
theorem card_add_card_le_card_inter_add_card (A B : Finset α) :
    A.card + B.card ≤ (A ∩ B).card + Fintype.card α := by
  have hadd := Finset.card_union_add_card_inter A B
  have hunion : (A ∪ B).card ≤ Fintype.card α := Finset.card_le_univ _
  omega

/-- **Two sets meeting only inside a small set are small together.** -/
theorem card_add_card_le_of_inter_subset {A B Bad : Finset α} {m : ℕ}
    (hbad : Bad.card ≤ m) (hsub : A ∩ B ⊆ Bad) :
    A.card + B.card ≤ Fintype.card α + m := by
  have := card_add_card_le_card_inter_add_card A B
  have := Finset.card_le_card hsub
  omega

/-- **The intersection lemma.** Two sets whose sizes sum past `n + m`
share a member outside any set of at most `m`. -/
theorem exists_mem_inter_notMem {A B Bad : Finset α} {m : ℕ}
    (hbad : Bad.card ≤ m) (h : Fintype.card α + m < A.card + B.card) :
    ∃ v ∈ A ∩ B, v ∉ Bad := by
  by_contra hcon
  push Not at hcon
  exact absurd (card_add_card_le_of_inter_subset hbad fun v hv => hcon v hv) (by omega)

/-- **Double counting, threshold form.** If every `a ∈ s` relates to at
least `m` members of `t`, then `|s|·m` is at most `|s|` times the number of
`b ∈ t` related to more than `d` members of `s`, plus `d` times the number
of the others. -/
theorem card_mul_le_of_bipartite_filter {α β : Type*} (s : Finset α) (t : Finset β)
    (rel : α → β → Prop) [∀ a b, Decidable (rel a b)] {m d : ℕ}
    (hm : ∀ a ∈ s, m ≤ (t.bipartiteAbove rel a).card) :
    s.card * m ≤
      (t.filter (fun b => d < (s.bipartiteBelow rel b).card)).card * s.card +
        (t.filter (fun b => ¬ d < (s.bipartiteBelow rel b).card)).card * d := by
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
  omega

end LeanDag
