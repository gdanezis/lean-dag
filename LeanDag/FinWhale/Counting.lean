import LeanDag.FinWhale.Committee
import LeanDag.Common.Counting
/-!
# FinWhale — the counting behind the fast path

The fast path commits a leader block `b` of round `r` when `n − p`
distinct validators vote for it at round `r + 1`. What makes that safe is
the paper's Lemma 4: once those votes exist *anywhere*, every round-`(r+2)`
block *in any DAG* is FP-evidence for `b`. This file proves the counting
that Lemma 4 is, and nothing else — the DAG, the decision rules and the
lemma in the shape the paper states it are `Model/Rule.lean` and
`Evidence.lean`.

Three counts, one per branch of the FP-evidence definition.

* A round-`(r+2)` block that **does not** expose the leader's equivocation
  needs `f + p − 1` of its parents voting for `b`. It has `n − f` parents
  and there are `n − p − f` *honest* voters, so the two meet in
  `(n − f) + (n − p − f) − n = f + p − 1`. Exactly the threshold, with
  nothing to spare (`nonequivocating_voters`).
* A block that **does** expose the equivocation may not reference the
  equivocating leader, so at most `f − 1` of its parents are Byzantine. Its
  honest parents number `n − 2f + 1`, of which at most `p` are honest
  non-voters, leaving `f + p` voting for `b` (`equivocating_voters`).
* The same split bounds the parents voting for a *conflicting* block by
  `f + p − 1`: at most `p` honest non-voters and at most `f − 1` Byzantine
  parents (`conflicting_voters_le`).

Only honest voters count. A Byzantine validator may show a vote for `b` to
the validator that fast-commits and a different block to everyone else, so
the `n − p` votes one validator sees are worth `n − p − f` across DAGs.
That subtraction is why the fast path costs `p` and why the committee is
`3f + 2p − 1` rather than `3f + 1`.

**The committee bound is tight**, and `equivocating_voters_fails_below`
says so: one validator fewer and the equivocating branch misses its
threshold by one, for every `f` and `p` in range.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]

/-- **The honest votes.** Of the `n − p` votes a validator sees on the
fast path, at least `n − p − f` are by correct validators, and those are
the same in every DAG. -/
theorem honest_voters (voters : Finset Validator)
    (hvot : fastCard Validator ≤ voters.card) :
    2 * F.f + P.p ≤ (voters ∩ (Correct : Finset Validator)).card + 1 := by
  have hsplit := card_le_card_inter_correct_add_byzantine voters
  have := params_arith (Validator := Validator)
  have hp : P.p ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine); omega
  simp only [fastCard] at hvot
  omega

/-- **Lemma 4, non-equivocating branch.** A round-`(r+2)` block that does
not expose the leader's equivocation references at least `f + p − 1`
parents voting for `b`. -/
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

/-- **At most `p` correct validators fail to vote.** The `n − p` votes may
include up to `|byzantine|` that no other DAG sees, but the same
`|byzantine|` is missing from `Correct`, so the two cancel: whatever the
actual fault load, at most `p` correct validators are non-voters. -/
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

/-- **Lemma 4, equivocating branch.** A round-`(r+2)` block that exposes
the equivocation may not reference the equivocating leader, so at most
`f − 1` of its parents are Byzantine. Its honest parents number
`n − 2f + 1`, of which at most `p` fail to vote, leaving `f + p` voting
for `b` — one more than the other branch, which is what the definition
asks of a block that has seen the equivocation. -/
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

/-- **The conflicting side of Lemma 4.** Under the same hypotheses, a
block that exposes the equivocation references at most `f + p − 1`
parents voting for any block conflicting with `b`: at most `p` correct
non-voters, and at most `f − 1` Byzantine parents.

`conflicting` is any set of validators no correct voter belongs to — a
correct validator votes once per slot, so it cannot vote for two blocks
of it. -/
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

/-- **The committee bound is tight.** The equivocating branch counts the
honest parents of a block that excludes the equivocating leader,
`n − 2f + 1`, less the correct non-voters, at most `p`. At
`n = 3f + 2p − 1` that is exactly `f + p`, the threshold the FP-evidence
definition asks for, with nothing to spare. One validator fewer and it is
`f + p − 1`, one short, for every `f` and `p` in range.

So the committee is not chosen with slack: it is the least at which
Lemma 4 holds. -/
theorem equivocating_margin (f p n m : ℕ) (hp : 1 ≤ p) (_hpf : p ≤ f)
    (hn : n + 1 = 3 * f + 2 * p) (hm : m + 2 = 3 * f + 2 * p) :
    (n - 2 * f + 1) - p = f + p ∧ (m - 2 * f + 1) - p + 1 = f + p := by
  omega

/-! ## The arithmetic of the findings

Three facts about the paper's own arguments, in the same form as
`equivocating_margin` above: pure statements about `f`, `p` and `n`,
so that the counting behind report §20.8 is checked rather than asserted.

What these settle is the arithmetic. That the paper's proofs *depend* on
it is a reading of their text, and no formalisation can check that. -/

/-- **Lemma 22's window against the cycle.** Its proof reads a window of
`3f + 3` rounds as "a full cycle of `n` rounds plus the first two rounds
of the next". The difference `3f + 3 − n` is `4 − 2p` and does not
involve `f`, so the reading is available exactly at `p ≤ 1`: a cycle plus
two rounds at `p = 1`, one cycle at `p = 2`, and short of a cycle
beyond. -/
theorem window_margin (f p n : ℕ) (hp : 1 ≤ p) (hn : n + 1 = 3 * f + 2 * p) :
    3 * f + 3 + 2 * p = n + 4 ∧ (n + 2 ≤ 3 * f + 3 ↔ p ≤ 1) := by
  omega

/-- **When C3 becomes reachable.** A validator with `j` honest validators
ahead of it holds at most `j + 1 + f` blocks of its own round, so C3's
threshold of `n − f` is within reach exactly from `j = n − 2f − 1`. The
validators that certainly cannot use C3 are therefore the fastest
`n − 2f − 1`, one fewer than the `n − 2f` the paper's set has. -/
theorem c3_reachable (f n j : ℕ) (hn : 2 * f ≤ n) :
    n - f ≤ j + 1 + f ↔ n - 2 * f - 1 ≤ j := by
  omega

/-- **And what that one member costs.** The pigeonhole margin over the
`f` faulty authors is `|H| − f`. At the paper's `|H| = n − 2f` it is
`2p − 1`, positive at every `p`; at the correct `|H| = n − 2f − 1` it is
`2p − 2`, and at `p = 1` the set has exactly `f` members, so the
intersection bound is zero and the argument names no block. -/
theorem c3_margin (f p n : ℕ) (hp : 1 ≤ p) (hn : n + 1 = 3 * f + 2 * p) :
    (n - 2 * f) + 1 = f + 2 * p ∧ (n - 2 * f - 1) + 2 = f + 2 * p ∧
      (p = 1 → n - 2 * f - 1 = f) := by
  omega

end FinWhale

end LeanDag
