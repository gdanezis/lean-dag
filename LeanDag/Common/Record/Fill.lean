import LeanDag.SafeSkip.Data
/-!
# The fill, at the block record

`fill U sk B hB` extends a record with one block per gap round, decoded
from a Safe Skip message under a reading `B` of the filled blocks, given
that each filled block is valid under the extended map (`hB`). Old
blocks are looked up unchanged. Closure and non-equivocation are proved
once; validity of the old blocks is the predicate's `reads`; validity of
the new ones is the one thing a reading owes.

`copyFill` discharges that obligation for any predicate that does not
read the author (`CopyStable`): the copied block is the donor's, valid
by the donor's validity. `selfBlock_valid` discharges it for the
self-referencing fill at any predicate equivalent to the family with
distinct creators and the self-parent clause, at any quorum (L0).
-/

namespace LeanDag

namespace BlockRecord

variable {Validator : Type*} {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [P.Mechanised]

/-- **The fill.** -/
def fill (U : BlockRecord Validator BlockId Payload P honest) (sk : GapData U.ids U.block)
    (B : sk.Blocks) (hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k)) :
    BlockRecord Validator BlockId Payload P honest where
  ids := U.ids ∪ sk.freshIds
  block := sk.fillMap B
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [GapData.fillMap_old ho] at hj
      exact Finset.mem_union_left _ (U.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      rw [GapData.fillMap_fresh] at hj
      exact B.refs_mem k hk1 hk2 j hj
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [GapData.fillMap_old ho]
      exact Validity.Mechanised.reads U.block (sk.fillMap B) U.ids (U.block i) U.complete
        (U.complete i ho) (fun j hj => GapData.fillMap_old hj) (U.valid i ho)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      rw [GapData.fillMap_fresh]
      exact hB k hk1 hk2
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rcases Finset.mem_union.mp hi with ho | hf <;>
      rcases Finset.mem_union.mp hj with ho' | hf'
    · simp only [GapData.fillMap_old ho, GapData.fillMap_old ho'] at hic hcc hrr
      exact U.no_equivocation i ho j ho' hic hcc hrr
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
      simp only [GapData.fillMap_old ho, GapData.fillMap_fresh, B.creator, B.round] at hcc hrr
      exact (sk.hgap i ho hcc (by change (U.block sk.B1).round < k at hk1; omega)
        (by omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      simp only [GapData.fillMap_old ho', GapData.fillMap_fresh, B.creator, B.round] at hcc hrr
      exact (sk.hgap j ho' hcc.symm (by change (U.block sk.B1).round < k at hk1; omega)
        (by omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
      simp only [GapData.fillMap_fresh, B.round] at hrr
      rw [hrr]

variable {U : BlockRecord Validator BlockId Payload P honest} {sk : GapData U.ids U.block}
variable {B : sk.Blocks} {hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k)}

@[simp] theorem fill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (fill U sk B hB).block b = U.block b := if_pos hb

@[simp] theorem fill_block_fresh {k : ℕ} :
    (fill U sk B hB).block (sk.fresh k) = B.blk k := GapData.fillMap_fresh

theorem fill_block : (fill U sk B hB).block = sk.fillMap B := rfl

theorem fill_ids : (fill U sk B hB).ids = U.ids ∪ sk.freshIds := rfl

theorem ids_subset_fill : U.ids ⊆ (fill U sk B hB).ids := Finset.subset_union_left

theorem mem_fill_ids {b : BlockId} :
    b ∈ (fill U sk B hB).ids ↔ b ∈ U.ids ∨ b ∈ sk.freshIds := Finset.mem_union

/-- A view of the original is a view of the fill, unchanged. -/
def View.lift (V : U.View) : (fill U sk B hB).View where
  ids := V.ids
  subset_ids := V.subset_ids.trans ids_subset_fill
  complete := by
    intro i hi j hj
    rw [fill_block_old (V.subset_ids hi)] at hj
    exact V.complete i hi j hj

@[simp] theorem View.lift_ids (V : U.View) : (View.lift (hB := hB) V).ids = V.ids := rfl

/-! ## The copy fill -/

section Copy

variable [P.CopyStable] {sk : SkipData U.ids U.block}

/-- **A copied block is valid** wherever the predicate does not read the
author: it is the donor's block re-authored, judged under a map that
agrees with the original on every old id. -/
theorem copyBlock_valid (U : BlockRecord Validator BlockId Payload P honest)
    (sk : SkipData U.ids U.block) {k : ℕ} (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    P (sk.fillMap (sk.copyBlocks U.complete)) (sk.copyBlock k) := by
  have hlm := sk.hline_mem k (sk.r0_le_of_lt hk1) hk2
  have hlr := sk.hline_round k (sk.r0_le_of_lt hk1) hk2
  have hv := Validity.CopyStable.copy U.block (U.block (sk.line k)) sk.v1 (U.valid _ hlm)
  have e : sk.copyBlock k = { U.block (sk.line k) with creator := sk.v1 } := by
    unfold SkipData.copyBlock; simp only [hlr]
  rw [e]
  exact Validity.Mechanised.reads U.block _ U.ids _ U.complete (U.complete _ hlm)
    (fun j hj => GapData.fillMap_old hj) hv

/-- **The copy fill**: the fill under the copy reading, its obligation
discharged. -/
def copyFill (U : BlockRecord Validator BlockId Payload P honest)
    (sk : SkipData U.ids U.block) : BlockRecord Validator BlockId Payload P honest :=
  fill U sk.toGapData (sk.copyBlocks U.complete) (fun _ hk1 hk2 => copyBlock_valid U sk hk1 hk2)

@[simp] theorem copyFill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (copyFill U sk).block b = U.block b := if_pos hb

@[simp] theorem copyFill_block_fresh {k : ℕ} :
    (copyFill U sk).block (sk.fresh k) = sk.copyBlock k := GapData.fillMap_fresh

theorem copyFill_ids : (copyFill U sk).ids = U.ids ∪ sk.freshIds := rfl

/-- A view of the original is a view of the copy fill, unchanged. -/
def View.liftCopy (V : U.View) : (copyFill U sk).View :=
  View.lift (B := sk.copyBlocks U.complete)
    (hB := fun _ hk1 hk2 => copyBlock_valid U sk hk1 hk2) V

@[simp] theorem View.liftCopy_ids (V : U.View) : (View.liftCopy (sk := sk) V).ids = V.ids := rfl

end Copy

/-! ## The self-referencing fill -/

section Self

variable [DecidableEq Validator] {q : ℕ} {sk : SkipData U.ids U.block}

/-- **L0: the self-referencing filled block is valid** at any predicate
equivalent to the family at `q` with distinct creators and the
self-parent clause: the copied references sit one round below, `v1`
appears among their authors only as `B1` (by `hB1uniq` at the boundary
and the crash above it), the authors only grow, and the added self
reference is the self-parent. -/
theorem selfBlock_valid
    (hP : ∀ blk b, P blk b ↔ ValidAt q (Clause.distinct.and Clause.selfParent) blk b)
    (U : BlockRecord Validator BlockId Payload P honest) (sk : SkipData U.ids U.block) {k : ℕ}
    (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    P (sk.fillMap (sk.selfBlocks U.complete)) (sk.fillBlock k) := by
  rw [hP]
  have hR0 : sk.r0 = (U.block sk.B1).round := rfl
  have hk0 : (U.block sk.B1).round ≤ k := by omega
  have hlr := sk.hline_round k hk0 hk2
  have hlm := sk.hline_mem k hk0 hk2
  have hlv := (hP _ _).mp (U.valid _ hlm)
  -- the self reference is an old id at round `k − 1` with creator `v1`
  have hprev_round : (sk.fillMap (sk.selfBlocks U.complete) (sk.prev k)).round = k - 1 := by
    by_cases hb : k = sk.r0 + 1
    · simp only [GapData.prev, if_pos hb, GapData.fillMap_old sk.hB1]
      omega
    · simp only [GapData.prev, if_neg hb, GapData.fillMap_fresh]
      rfl
  have hprev_creator : (sk.fillMap (sk.selfBlocks U.complete) (sk.prev k)).creator = sk.v1 := by
    by_cases hb : k = sk.r0 + 1
    · simp only [GapData.prev, if_pos hb, GapData.fillMap_old sk.hB1]
      exact sk.hB1c
    · simp only [GapData.prev, if_neg hb, GapData.fillMap_fresh]
      rfl
  -- no copied reference is `v1`-authored, except possibly the anchor itself
  have hno_v1 : ∀ j ∈ (U.block (sk.line k)).refs,
      (U.block j).creator = sk.v1 → j = sk.prev k := by
    intro j hj hjc
    have hjo := U.complete _ hlm j hj
    have hjr : (U.block j).round + 1 = k := by rw [hlv.predecessor j hj, hlr]
    by_cases hb : k = sk.r0 + 1
    · simp only [GapData.prev, if_pos hb]
      exact sk.hB1uniq j hjo hjc (by omega)
    · exact (sk.hgap j hjo hjc (by omega) (by omega)).elim
  have hold : ∀ j ∈ (U.block (sk.line k)).refs,
      sk.fillMap (sk.selfBlocks U.complete) j = U.block j :=
    fun j hj => GapData.fillMap_old (U.complete _ hlm j hj)
  refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
  · intro j hj
    simp only [SkipData.fillBlock, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · rw [hprev_round]; show k - 1 + 1 = k; omega
    · rw [hold j hj, hlv.predecessor j hj]
      exact hlr
  · intro h0
    refine le_trans (hlv.quorum (by rw [hlr]; exact h0)) (Finset.card_le_card ?_)
    intro c hc
    obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨j, Finset.mem_insert_of_mem hj, by rw [hold j hj]; exact hjc⟩
  · intro j hj l hl hjl
    simp only [SkipData.fillBlock, Finset.mem_insert] at hj hl
    rcases hj with rfl | hj <;> rcases hl with rfl | hl
    · rfl
    · rw [hprev_creator, hold l hl] at hjl
      exact (hno_v1 l hl hjl.symm).symm
    · rw [hprev_creator, hold j hj] at hjl
      exact hno_v1 j hj hjl
    · rw [hold j hj, hold l hl] at hjl
      exact hlv.clause.1 j hj l hl hjl
  · intro _
    exact ⟨sk.prev k, Finset.mem_insert_self _ _, hprev_creator⟩

end Self

end BlockRecord

end LeanDag
