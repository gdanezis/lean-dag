import LeanDag.Common.Validators
/-!
# Blocks, validity, and the block-level quorum lemma

`spec.md` §3.1–3.2 and the corollary T0'.

Blocks are referenced by `BlockId`, never by value, so `Block` is
non-recursive. The price is that a `BlockId` means nothing on its own: it
must be resolved through a lookup function `blk : BlockId → Block`, and so
validity is a predicate on `(blk, b)` rather than on `b`. That is deliberate
— taking the lookup function rather than a whole universe is what lets
`BlockUniverse` (§3.3) state "every member is valid" as one of its own
fields without referring to the structure being defined.
-/

namespace LeanDag

/-- A block: its round, its author, the ids it references from the
preceding round, and an opaque payload. -/
structure Block (Validator BlockId Payload : Type*) where
  /-- The round this block was produced in. -/
  round : ℕ
  /-- The validator that authored the block. -/
  creator : Validator
  /-- Ids of the blocks this one references, all from round `round - 1`. -/
  refs : Finset BlockId
  /-- Opaque application data. Inert throughout Phase 1. -/
  payload : Payload

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*}
variable {Payload : Type*}

/-- The validators that authored a set of ids. Defined on an arbitrary
`Finset BlockId`, not just on a block's refs: T3's hypothesis, T4's commit
rule, and T0' all quantify over id-sets that are nobody's refs. -/
def creatorsOf (blk : BlockId → Block Validator BlockId Payload)
    (s : Finset BlockId) : Finset Validator :=
  s.image (fun i => (blk i).creator)

/-- The validators behind a block's references. -/
def creators (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Finset Validator :=
  creatorsOf blk b.refs

omit [Fintype Validator] F in
/-- Membership in `creatorsOf`, unfolded: a validator is a creator of a set of ids exactly when it authored one of them. -/
@[simp]
theorem mem_creatorsOf {blk : BlockId → Block Validator BlockId Payload}
    {s : Finset BlockId} {v : Validator} :
    v ∈ creatorsOf blk s ↔ ∃ i ∈ s, (blk i).creator = v :=
  Finset.mem_image

/-- Block validity, relative to a lookup function. The predecessor
condition is stated additively (`+ 1 = round`, not `round - 1`), which
avoids `ℕ`-subtraction and makes the genesis case derivable rather than
a branch: at round `0`, `refs = ∅` follows from unsatisfiability
(`refs_empty_of_round_zero`). The quorum is on the *creator set*, not
`refs.card` — the faithful reading of "2f+1 validators". -/
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- A block never cites the same author twice. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- Non-genesis blocks reference a quorum of distinct validators. -/
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card
  /-- Non-genesis blocks reference *some* block by their own creator, not
  a unique one — an equivocator's blocks form a forest of predecessor
  chains, one edge per block, which this does not collapse. -/
  self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator

omit [Fintype Validator] F in
/-- A nonempty creator set can only come from a nonempty set of ids:
the image of `∅` is `∅`. -/
theorem nonempty_of_creatorsOf_card_pos {blk : BlockId → Block Validator BlockId Payload}
    {s : Finset BlockId} (h : 0 < (creatorsOf blk s).card) : s.Nonempty := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp [creatorsOf] at h
  · exact hne

/-- `ValidWrt` is decidable on concrete data. Not needed by any proof below,
but it lets a small hand-built DAG be checked by `decide`, which is how the
definitions here are confirmed to be satisfiable rather than vacuous. -/
instance [DecidableEq BlockId] (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Decidable (ValidWrt blk b) :=
  decidable_of_iff
    ((∀ i ∈ b.refs, (blk i).round + 1 = b.round) ∧
      (∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j) ∧
      (0 < b.round → quorumCard Validator ≤ (creators blk b).card) ∧
      (0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.predecessor, h.distinct_creators, h.quorum, h.self_parent⟩⟩

namespace ValidWrt

variable {blk : BlockId → Block Validator BlockId Payload}
  {b : Block Validator BlockId Payload}

/-- Genesis blocks have no references — derived from the predecessor
condition, not assumed. -/
theorem refs_empty_of_round_zero (h : ValidWrt blk b) (h0 : b.round = 0) : b.refs = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  have := h.predecessor i hi
  omega

/-- Distinct creators means the creator map does not collapse the refs, so
the creator set has exactly as many elements as there are references. -/
theorem card_creators (h : ValidWrt blk b) : (creators blk b).card = b.refs.card := by
  refine Finset.card_image_of_injOn ?_
  intro i hi j hj hij
  exact h.distinct_creators i hi j hj hij

/-- A non-genesis block references at least `2f+1` blocks. -/
theorem card_refs (h : ValidWrt blk b) (h0 : 0 < b.round) : quorumCard Validator ≤ b.refs.card := by
  rw [← h.card_creators]
  exact h.quorum h0

/-- A non-genesis block has at least one reference; T3's inductive step
needs only this much of validity. Proved from the quorum condition
alone, not via `card_refs`, so `distinct_creators` never enters T3's
dependency path. -/
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty := by
  have hq : quorumCard Validator ≤ (creatorsOf blk b.refs).card := h.quorum h0
  have hpos : 0 < (creatorsOf blk b.refs).card := by
    have := F.card_validators
    omega
  exact nonempty_of_creatorsOf_card_pos hpos

end ValidWrt

/-- **T0'.** Two id-sets whose creator sets are quorums share a
*correct* author. Stated on bare `Finset BlockId`s, since call sites
intersect arbitrary sets that are nobody's refs; for a block, apply with
`s := b.refs` and `ValidWrt.quorum`. -/
theorem exists_correct_mem_creators_inter
    {blk : BlockId → Block Validator BlockId Payload} {s t : Finset BlockId}
    (hs : quorumCard Validator ≤ (creatorsOf blk s).card)
    (ht : quorumCard Validator ≤ (creatorsOf blk t).card) :
    ∃ v ∈ creatorsOf blk s ∩ creatorsOf blk t, v ∈ (Correct : Finset Validator) :=
  exists_correct_mem_inter hs ht

end LeanDag
