import Mathlib.Data.Fintype.Card
/-!
# Counting in a committee

The one counting fact every quorum argument in the development makes:
two sets whose sizes sum past `n + m` meet outside any set of at most
`m` members. Every quorum-intersection lemma — the core's T0 at
`n − f`, Nemo's two majorities, Hydrozoan's certificate uniqueness,
Hybrid's at the honest class, FinWhale's fast path — is this at its own
thresholds, and every "the two quorums cannot both exist" argument is its
contrapositive: two sets meeting only inside a set of at most `m` sum to
at most `n + m`.
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

end LeanDag
