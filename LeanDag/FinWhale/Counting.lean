import LeanDag.FinWhale.Committee
import LeanDag.Common.Counting
/-!
# FinWhale — the counting behind the fast path

The fast path commits a leader block when `n − p` validators vote for it
at the round above; the paper's Lemma 4 is that this makes every
round-`(r+2)` block, in any DAG, FP-evidence for it. This file is that
counting, one theorem per branch of the FP-evidence definition, and
nothing else — the DAG, the decision rules and the lemma in the paper's
own shape are `Model/Rule.lean` and `Evidence.lean`.

Only honest voters count: a Byzantine validator may show one DAG a vote
and another DAG nothing, so the `n − p` votes one validator sees are
worth `n − p − f` across DAGs. That subtraction is why the fast path
costs `p` and the committee is `3f + 2p − 1` rather than `3f + 1`, and
`equivocating_voters_fails_below` shows the bound is tight.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]

/-- **The honest votes.** Of the `n − p` votes a validator sees, at
least `n − p − f` are by correct validators, the same in every DAG. -/
theorem honest_voters (voters : Finset Validator)
    (hvot : fastCard Validator ≤ voters.card) :
    2 * F.f + P.p ≤ (voters ∩ (Correct : Finset Validator)).card + 1 := by
  have hsplit := card_le_card_inter_correct_add_byzantine voters
  have := params_arith (Validator := Validator)
  have hp : P.p ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine); omega
  simp only [fastCard] at hvot
  omega

/-- **Lemma 4, non-equivocating branch**: such a block references at
least `f + p − 1` parents voting for `b`. -/
theorem nonequivocating_voters {voters parents : Finset Validator}
    (hvot : fastCard Validator ≤ voters.card)
    (hpar : quorumCard Validator ≤ parents.card) :
    F.f + P.p ≤ (parents ∩ (voters ∩ (Correct : Finset Validator))).card + 1 := by
  have hmeet := card_add_card_le_card_inter_add_card
    parents (voters ∩ (Correct : Finset Validator))
  have hhon := honest_voters voters hvot
  have := params_arith (Validator := Validator)
  have hf : F.f ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine); omega
  omega

/-- **At most `p` correct validators fail to vote**: the votes another
DAG might not see and the validators `Correct` excludes are the same
size, so they cancel. -/
theorem honest_nonvoters {voters : Finset Validator}
    (hvot : fastCard Validator ≤ voters.card) :
    ((Correct : Finset Validator) \ voters).card ≤ P.p := by
  have hnv : ((Correct : Finset Validator) \ voters).card +
      (voters ∩ (Correct : Finset Validator)).card = (Correct : Finset Validator).card := by
    have := Finset.card_inter_add_card_sdiff (Correct : Finset Validator) voters
    rw [Finset.inter_comm] at this
    omega
  have hsplit := card_le_card_inter_correct_add_byzantine voters
  have := params_arith (Validator := Validator)
  have hp : P.p ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine); omega
  simp only [fastCard] at hvot
  omega

/-- **Lemma 4, equivocating branch**: such a block excludes the
equivocating leader, so at most `f − 1` of its parents are Byzantine,
and at most `p` of its `n − 2f + 1` honest parents fail to vote. -/
theorem equivocating_voters {voters parents : Finset Validator}
    (hvot : fastCard Validator ≤ voters.card)
    (hpar : quorumCard Validator ≤ parents.card)
    (hbyz : (parents ∩ F.byzantine).card + 1 ≤ F.f) :
    F.f + P.p ≤ (parents ∩ (voters ∩ (Correct : Finset Validator))).card := by
  -- the honest parents, after excluding the equivocating leader
  have hph := Finset.card_inter_add_card_sdiff parents (Correct : Finset Validator)
  have hpb : (parents \ (Correct : Finset Validator)).card ≤ (parents ∩ F.byzantine).card := by
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_sdiff] at hx
    exact Finset.mem_inter.2 ⟨hx.1, by simpa using hx.2⟩
  -- the honest parents that fail to vote lie among the honest non-voters
  have hsplit := Finset.card_inter_add_card_sdiff
    (parents ∩ (Correct : Finset Validator)) voters
  have hnv : ((parents ∩ (Correct : Finset Validator)) \ voters).card
      ≤ ((Correct : Finset Validator) \ voters).card := by
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_sdiff, Finset.mem_inter] at hx
    exact Finset.mem_sdiff.2 ⟨hx.1.2, hx.2⟩
  have hassoc : (parents ∩ (Correct : Finset Validator)) ∩ voters
      = parents ∩ (voters ∩ (Correct : Finset Validator)) := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [hassoc] at hsplit
  have := honest_nonvoters hvot
  have := params_arith (Validator := Validator)
  have hf : F.f ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine); omega
  omega

/-- **The conflicting side of Lemma 4**: such a block references at most
`f + p − 1` parents voting for any block conflicting with `b`, `conflicting`
being any set no correct voter for `b` belongs to. -/
theorem conflicting_voters_le {voters parents conflicting : Finset Validator}
    (hvot : fastCard Validator ≤ voters.card)
    (hbyz : (parents ∩ F.byzantine).card + 1 ≤ F.f)
    (hdisj : ∀ v ∈ conflicting, v ∈ (Correct : Finset Validator) → v ∉ voters) :
    (parents ∩ conflicting).card + 1 ≤ F.f + P.p := by
  have hsplit := Finset.card_inter_add_card_sdiff
    (parents ∩ conflicting) (Correct : Finset Validator)
  have hb : ((parents ∩ conflicting) \ (Correct : Finset Validator)).card
      ≤ (parents ∩ F.byzantine).card := by
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_sdiff, Finset.mem_inter] at hx
    exact Finset.mem_inter.2 ⟨hx.1.1, by simpa using hx.2⟩
  have hh : ((parents ∩ conflicting) ∩ (Correct : Finset Validator)).card
      ≤ ((Correct : Finset Validator) \ voters).card := by
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_inter, Finset.mem_inter] at hx
    exact Finset.mem_sdiff.2 ⟨hx.2, hdisj x hx.1.2 hx.2⟩
  have := honest_nonvoters hvot
  have := params_arith (Validator := Validator)
  omega

/-- **The committee bound is tight**: at `n = 3f + 2p − 1` the
equivocating branch clears its threshold with nothing to spare, and one
validator fewer misses it by one, for every `f` and `p` in range. -/
theorem equivocating_margin (f p n m : ℕ) (hp : 1 ≤ p) (_hpf : p ≤ f)
    (hn : n + 1 = 3 * f + 2 * p) (hm : m + 2 = 3 * f + 2 * p) :
    (n - 2 * f + 1) - p = f + p ∧ (m - 2 * f + 1) - p + 1 = f + p := by
  omega

/-! ## The arithmetic of the findings

Three pure facts about `f`, `p` and `n`, checking the counting behind
report §20.8; whether the paper's proofs depend on it is a reading of
their text, which no formalisation can check. -/

/-- **Lemma 22's window against the cycle**: its `3f + 3`-round window
reads as a full cycle plus two rounds exactly at `p ≤ 1`. -/
theorem window_margin (f p n : ℕ) (hp : 1 ≤ p) (hn : n + 1 = 3 * f + 2 * p) :
    3 * f + 3 + 2 * p = n + 4 ∧ (n + 2 ≤ 3 * f + 3 ↔ p ≤ 1) := by
  omega

/-- **When C3 becomes reachable**: at `j` honest validators ahead of it,
C3's threshold `n − f` is within reach exactly from `j = n − 2f − 1`. -/
theorem c3_reachable (f n j : ℕ) (hn : 2 * f ≤ n) :
    n - f ≤ j + 1 + f ↔ n - 2 * f - 1 ≤ j := by
  omega

/-- **And what that one member costs**: the pigeonhole margin `|H| − f`
drops from `2p − 1` at the paper's `|H|` to `2p − 2` at the correct one,
vanishing at `p = 1`. -/
theorem c3_margin (f p n : ℕ) (hp : 1 ≤ p) (hn : n + 1 = 3 * f + 2 * p) :
    (n - 2 * f) + 1 = f + 2 * p ∧ (n - 2 * f - 1) + 2 = f + 2 * p ∧
      (p = 1 → n - 2 * f - 1 = f) := by
  omega

end FinWhale

end LeanDag
