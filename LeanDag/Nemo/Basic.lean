import LeanDag.Common.Block
import LeanDag.Common.BlockRecord
/-!
# Nemo-Nemo: the crash-fault DAG foundation

"Finding Nemo-Nemo: CFT DAG-based Consensus in the WAN."

Nemo-Nemo is crash-fault-tolerant: `n ≥ 2f+1` validators, all honest — they may
halt, but never equivocate. Its quorum is a bare **majority** `n/2+1`, which is
mathematically outside the core Byzantine model (`Faults` forces `n − f`, a
`~2n/3` supermajority). So this arc builds a self-contained crash foundation
consuming only the fault-agnostic parts of the core (`Block`, `creatorsOf`).

The crash setting is *leaner* than the Byzantine one: there is no `byzantine`
set, every validator is correct, so non-equivocation is universal and the single
quorum fact is that **two majorities intersect** — no correct-member filtering.

This file provides the majority quorum, its intersection lemma, crash block
validity, the crash universe, and the block-level lemmas the commit rule needs.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}

/-- The majority quorum: strictly more than half the validators, `n/2 + 1`. -/
def majority (Validator : Type*) [Fintype Validator] : ℕ :=
  Fintype.card Validator / 2 + 1

/-- **A majority is more than a block can miss**: a block references a
majority of distinct creators, so it misses fewer than a majority. This
turns a majority of backers into the form the hitting lemma reads. -/
theorem lt_card_add_majority {T : Finset Validator} (h : majority Validator ≤ T.card) :
    Fintype.card Validator < T.card + majority Validator := by
  unfold majority at *
  omega

/-- Crash block validity: like the core `ValidWrt`, but the parents quorum is the
majority `n/2+1` rather than `n − f`, and the core's `self_parent` and
`distinct_creators` fields are gone. The implementation's block verifier imposes
neither: there is no self-parent check, and duplicate-author includes are
deduplicated by the stake aggregator, not rejected. Under crash the second is
also derivable — universal non-equivocation makes duplicate creators among refs
impossible (`Universe.eq_of_mem_refs_of_creator_eq`). -/
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- Non-genesis blocks reference a **majority** of distinct validators. -/
  quorum : 0 < b.round → majority Validator ≤ (creators blk b).card

instance [DecidableEq BlockId] (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Decidable (ValidWrt blk b) :=
  decidable_of_iff
    ((∀ i ∈ b.refs, (blk i).round + 1 = b.round) ∧
      (0 < b.round → majority Validator ≤ (creators blk b).card))
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.predecessor, h.quorum⟩⟩

namespace ValidWrt

variable {blk : BlockId → Block Validator BlockId Payload}
  {b : Block Validator BlockId Payload}

/-- A non-genesis block has at least one reference (the majority quorum is
positive). -/
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty := by
  have hq : majority Validator ≤ (creatorsOf blk b.refs).card := h.quorum h0
  have hpos : 0 < (creatorsOf blk b.refs).card := by unfold majority at hq; omega
  exact nonempty_of_creatorsOf_card_pos hpos

end ValidWrt

/-- **Nemo's validity is the family** at the majority, with no clause. -/
theorem ValidWrt.iff_validAt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) :
    ValidWrt blk b ↔ ValidAt (majority Validator) Clause.none blk b :=
  ⟨fun h => ⟨h.predecessor, h.quorum, True.intro⟩, fun h => ⟨h.predecessor, h.quorum⟩⟩

/-- **Nemo's validity is mechanised**, along the family. -/
instance ValidWrt.mechanised :
    Validity.Mechanised
      (ValidWrt (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Validity.Mechanised.of_iff ValidWrt.iff_validAt

/-- **And quorate at the majority.** -/
instance ValidWrt.quorate :
    Validity.Quorate
      (ValidWrt (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (majority Validator) :=
  Validity.Quorate.of_validAt (by unfold majority; omega) ValidWrt.iff_validAt

/-- **And does not read the creator.** -/
instance ValidWrt.copyStable :
    Validity.CopyStable
      (ValidWrt (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Validity.CopyStable.of_iff ValidWrt.iff_validAt

/-- **Nemo's universe**: the block record at Nemo's validity, with
non-equivocation asked of everyone — the crash model has no Byzantine
validators. -/
abbrev Universe (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] :=
  BlockRecord Validator BlockId Payload ValidWrt (Finset.univ : Finset Validator)

/-- A view: one validator's local, reference-closed sub-DAG. -/
abbrev View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] (U : Universe Validator BlockId Payload) :=
  BlockRecord.View U

namespace Universe

variable {U : Universe Validator BlockId Payload}

/-- Distinct creators among references are automatic under crash: two refs of
the same block sharing a creator sit at the same round (`predecessor`), so
universal `no_equivocation` identifies them. This is why the crash `ValidWrt`
has no `distinct_creators` field. -/
theorem eq_of_mem_refs_of_creator_eq {i j k : BlockId} (hi : i ∈ U.ids)
    (hj : j ∈ (U.block i).refs) (hk : k ∈ (U.block i).refs)
    (hc : (U.block j).creator = (U.block k).creator) : j = k := by
  have h1 := U.round_of_mem_refs hi hj
  have h2 := U.round_of_mem_refs hi hk
  exact U.eq_of_creator_eq (U.refs_subset hi hj) (U.refs_subset hi hk) (Finset.mem_univ _)
    hc rfl (by omega)

end Universe

end Nemo

end LeanDag
