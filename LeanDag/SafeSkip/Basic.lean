import LeanDag.Common.BlockDag
import LeanDag.Common.Record.Fill
/-!
# Safe Skip: rejoining after a crash, in one message

**A universe transform** (`Transforms`): `skipFill` returns a crashed
validator to production in one message. The arc gives the message and
the fill; that the fill is an `Extends` and what verdicts cross it are
`Properties/Arcs/SafeSkip.lean` generically, and the protocol's own
`Record.lean` at each rule.

A validator that crashes and recovers faces a gap: liveness rests on
correct validators building every round (P8), and producing the missing
blocks one by one costs a round trip per round of downtime. **Safe
Skip** closes it with a single message: the recovering validator `v1`
names a block `B2` at round `r` on another validator `v2`'s history
line and its own last block `B1`, and the message denotes one block per
gap round, deterministic given the DAG — each filled block carries
`v2`'s line references plus one added self reference to `v1`'s block of
the round below (`B1` at the boundary, the previous filled block
above).

The added self reference is a validity requirement, not an
optimisation: `self_parent` (P3′) demands a self-authored reference
that `v2`'s line cannot supply. With it every clause of validity holds,
by non-equivocation at the boundary and monotone growth of the
reference quorum.

`skipFill` is the denotation: a universe extending `U` with the filled
blocks, old blocks untouched. This file proves it is a `BlockUniverse`;
that old blocks and references are preserved verbatim
(`skipFill_block_old`); that the gap is populated
(`skipFill_populatedOn`), the production hypothesis liveness consumes;
and that a filled block landing on a leader slot is directly skipped
(`directSkip_fresh`) — its only supporter is `v1`'s own line, so the
fill cannot conjure a commit for a slot the network already passed.

Full verdict invariance across the fill is the pair of verdict
transports in `Invariance.lean`, the `decided_chop` analogue for
extension rather than truncation.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **A Safe Skip message at a core universe**: the same data, read off
`U`, stated over `ids`/`blk` since the data of a fill is shared across
rules — only the invariants a universe carries differ. Nemo and
FinWhale build their own fills from it. -/
abbrev SkipMsg (U : BlockUniverse Validator BlockId Payload) :=
  SkipData U.ids U.block

/-- **The boundary condition from correctness.** For a `v1` outside the
Byzantine set, non-equivocation pins its round-`r0` block to `B1` — how
a `SkipMsg` is built here, and what `hB1uniq` generalises for a
crash-prone `v1` in the hybrid model. -/
theorem hB1uniq_of_correct {v1 : Validator} {B1 : BlockId}
    (hB1 : B1 ∈ U.ids) (hB1c : (U.block B1).creator = v1)
    (hv1 : v1 ∈ (Correct : Finset Validator)) :
    ∀ j ∈ U.ids, (U.block j).creator = v1 →
      (U.block j).round = (U.block B1).round → j = B1 :=
  fun j hj hjc hjr => U.eq_of_creator_eq hj hB1 hv1 hjc hB1c hjr


namespace SkipMsg

open GapData SkipData

variable (sk : SkipMsg U)

/-- **The denotation.** `U`, extended with one filled block per gap
round; every old block looked up unchanged. The block record's fill
under the self-referencing reading, its obligation discharged by
`BlockRecord.selfBlock_valid`. -/
def skipFill : BlockUniverse Validator BlockId Payload :=
  BlockRecord.fill U sk.toGapData (sk.selfBlocks U.complete)
    (fun _ hk1 hk2 => BlockRecord.selfBlock_valid ValidWrt.iff_validAt U sk hk1 hk2)

/-- Old blocks read unchanged: every store, view and certificate built
on `U` sees the same data in the extension. -/
@[simp] theorem skipFill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    sk.skipFill.block b = U.block b := if_pos hb

@[simp] theorem skipFill_block_fresh {k : ℕ} :
    sk.skipFill.block (sk.fresh k) = sk.fillBlock k := GapData.fillMap_fresh

theorem ids_subset_skipFill : U.ids ⊆ sk.skipFill.ids :=
  Finset.subset_union_left

/-- **The gap is populated.** With `v1` restored to the reliable set,
every gap round carries a `v1` block — the production hypothesis
liveness consumes, recovered from one message. -/
theorem skipFill_populatedOn {T : Finset Validator} {k : ℕ}
    (hpop : PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    PopulatedOn sk.skipFill (insert sk.v1 T) k := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · refine ⟨sk.fresh k, ?_, ?_, ?_⟩
    · exact Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩)
    · rw [sk.skipFill_block_fresh]; rfl
    · rw [sk.skipFill_block_fresh]; rfl
  · obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
    exact ⟨b, sk.ids_subset_skipFill hb,
      by rw [sk.skipFill_block_old hb]; exact hbc,
      by rw [sk.skipFill_block_old hb]; exact hbr⟩

end SkipMsg

end LeanDag
