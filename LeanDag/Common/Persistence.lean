import LeanDag.Common.Support
/-!
# Persistence

`spec.md` T3. If a block `b` at round `r` is referenced by a quorum of
round-`(r+1)` blocks, every block from round `r+2` onward has `b` in its
causal history: once a quorum backs a block, it can never be forgotten.

The bound is `r+2`, not `r+1`, and tight — a round-`(r+1)` block outside
the quorum need not reference `b` at all, and `r+2` is the first round
with two ref-quorums to intersect. The quorum hypothesis is on `Q`'s
creator set, not `Q.card`, since `Q` is an arbitrary set of ids with no
distinctness invariant of its own. Quorum intersection is used exactly
once, in the base case; above it, height is carried by transitivity
alone.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The quorum hypothesis already forces `b` into the universe at round
`r`, so T3 need not assume either: a nonempty `Q` has a member in the
universe referencing `b`, which pins it by completeness. -/
theorem mem_ids_and_round_of_quorum_support
    {b : BlockId} {r : ℕ} {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : quorumCard Validator ≤ (creatorsOf U.block Q).card) :
    b ∈ U.ids ∧ (U.block b).round = r := by
  have hpos : 0 < (creatorsOf U.block Q).card := by
    have := F.card_validators
    omega
  obtain ⟨q, hq⟩ := nonempty_of_creatorsOf_card_pos hpos
  have hq_ids := hQ hq
  have hb_ref := hQref q hq
  refine ⟨U.complete q hq_ids b hb_ref, ?_⟩
  have h1 := U.round_of_mem_refs hq_ids hb_ref
  have h2 := hQround q hq
  omega

/-- **T3 (Persistence).** If `b` is referenced by a quorum of
round-`(r+1)` blocks, every block at round `r+2` or later has `b` in its
causal history — neither `b ∈ U.ids` nor its round assumed, both
following from the quorum hypothesis. -/
theorem reaches_of_quorum_support
    {b : BlockId} {r : ℕ}
    {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : quorumCard Validator ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b := by
  -- Base case at `r+2`; everything above is `reaches_pred_of_round_le`.
  have hbase : ∀ c' ∈ U.ids, (U.block c').round = r + 2 → ∃ x, x = b ∧ Reaches U c' x := by
    intro c' hc' hc'r
    refine ⟨b, rfl, ?_⟩
    -- The quorum contains at least `f+1` *correct* creators, and those are
    -- exactly the supporters the uniform coverage lemma consumes.
    refine reaches_of_honest_support_of_card (b := b) (r := r)
      (S := creatorsOf U.block Q ∩ (Correct : Finset Validator)) ?_ ?_ ?_ hc' hc'r
    · intro v hv
      rw [Finset.mem_inter, mem_creatorsOf] at hv
      obtain ⟨⟨q, hq_mem, hq_creator⟩, _⟩ := hv
      exact ⟨q, hQ hq_mem, hQround q hq_mem, hQref q hq_mem, hq_creator⟩
    · exact fun v hv => Finset.mem_of_mem_inter_right hv
    · exact lt_card_add_quorumCard (card_inter_correct_of_quorum hQquorum)
  obtain ⟨x, hx, hreach⟩ := reaches_pred_of_round_le hbase hc hcr
  exact hx ▸ hreach

end LeanDag
