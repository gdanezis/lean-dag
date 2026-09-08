import LeanDag.Common.BlockRecord
/-!
# Safe Skip: the data of a fill

A recovering validator `v1` closes the gap left by a crash with a
single message: it names a block `B2` on another validator `v2`'s
history line and its own last block `B1`, and the message denotes one
block per gap round, deterministic given the DAG (`Basic.lean`).

`SkipData` is that message, stated over an id set and a block map
rather than a universe, since the data of a fill is shared across rules
and only the invariants a universe carries differ. `fillBlock` adds a
self reference to `v1`'s block of the round below, which the core's
self-parent clause demands; `copyBlock` carries the donor's references
verbatim, for a rule without that clause. `Blocks` is what a reading
owes the record for the fill to close (`Record/Fill.lean`).
-/

namespace LeanDag

variable {Validator : Type*}
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- The denotation of a Safe Skip message, with the freshness data an
implementation supplies. `line` is `v2`'s history line, one block per
round from `r0 := round B1` up to `r`, each referencing the one below;
`hgap` is the crash itself, `v1` authoring nothing strictly between
`B1` and `r`. -/
structure SkipData (ids : Finset BlockId)
    (blk : BlockId → Block Validator BlockId Payload) where
  /-- The recovering validator. -/
  v1 : Validator
  /-- Its last block before the crash. -/
  B1 : BlockId
  /-- The donor of the reference structure. -/
  v2 : Validator
  /-- The target round — the round of the pinned block `B2 = line r`. -/
  r : ℕ
  /-- `v2`'s history line, meaningful on rounds `[round B1, r]`. -/
  line : ℕ → BlockId
  /-- Fresh ids for the filled blocks, and their decoder. -/
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  /-- `B1` is `v1`'s only block at its round — the whole of what the
  boundary argument needs, stated directly rather than as `v1 ∈ Correct`
  since a crash-prone `v1` needs it too (report §14). -/
  hB1uniq : ∀ j ∈ ids, (blk j).creator = v1 →
    (blk j).round = (blk B1).round → j = B1
  hv12 : v1 ≠ v2
  hB1 : B1 ∈ ids
  hB1c : (blk B1).creator = v1
  hline_mem : ∀ k, (blk B1).round ≤ k → k ≤ r → line k ∈ ids
  hline_creator : ∀ k, (blk B1).round ≤ k → k ≤ r →
    (blk (line k)).creator = v2
  hline_round : ∀ k, (blk B1).round ≤ k → k ≤ r →
    (blk (line k)).round = k
  hline_chain : ∀ k, (blk B1).round < k → k ≤ r →
    line (k - 1) ∈ (blk (line k)).refs
  hfresh_new : ∀ k, fresh k ∉ ids
  hidx : ∀ k, idx (fresh k) = k
  /-- The crash: `v1` authored nothing in the gap. -/
  hgap : ∀ b ∈ ids, (blk b).creator = v1 →
    (blk B1).round < (blk b).round → (blk b).round ≤ r → False

namespace SkipData

variable {ids : Finset BlockId} {blk : BlockId → Block Validator BlockId Payload}
variable (sk : SkipData ids blk)

/-- The round of the anchor block — the bottom of the gap. -/
def r0 : ℕ := (blk sk.B1).round

/-- The self reference of the filled block at round `k`: the anchor at
the boundary, the previous filled block above it. -/
def prev (k : ℕ) : BlockId :=
  if k = sk.r0 + 1 then sk.B1 else sk.fresh (k - 1)

/-- The filled block at gap round `k`: `v2`'s references at that round,
plus the added self reference. -/
def fillBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := insert (sk.prev k) (blk (sk.line k)).refs
  payload := (blk (sk.line k)).payload

/-- The filled block **without the self reference**: `v2`'s references
at that round, re-authored. The self reference exists only to satisfy
`self_parent`, and it is the one thing a rule constraining a pair of
references together — FinWhale's `leader_clause` — cannot survive; a
rule with no self-parent clause takes this block instead, and validity
is the donor's verbatim. -/
def copyBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := (blk (sk.line k)).refs
  payload := (blk (sk.line k)).payload

/-- The gap rounds, as a `Finset`. -/
def gap : Finset ℕ := (Finset.range (sk.r + 1)).filter (fun k => sk.r0 < k)

/-- The ids of the filled blocks. -/
def freshIds : Finset BlockId := sk.gap.image sk.fresh

theorem mem_freshIds {b : BlockId} :
    b ∈ sk.freshIds ↔ ∃ k, sk.r0 < k ∧ k ≤ sk.r ∧ b = sk.fresh k := by
  simp only [freshIds, gap, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨h2, h1⟩, h3⟩; exact ⟨k, h1, by omega, h3.symm⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨by omega, h1⟩, h3.symm⟩

theorem r0_le_of_lt {k : ℕ} (h : sk.r0 < k) : (blk sk.B1).round ≤ k := le_of_lt h

/-- **What a reading of the filled blocks owes the record**: one block
per gap round, at that round, by the recovering validator, referencing
only old ids and filled ids. -/
structure Blocks where
  /-- The filled block at gap round `k`. -/
  blk : ℕ → Block Validator BlockId Payload
  round : ∀ k, (blk k).round = k
  creator : ∀ k, (blk k).creator = sk.v1
  refs_mem : ∀ k, sk.r0 < k → k ≤ sk.r → ∀ j ∈ (blk k).refs, j ∈ ids ∪ sk.freshIds

/-- The block map of the fill: old ids as before, filled ids decoded. -/
def fillMap (B : sk.Blocks) (b : BlockId) : Block Validator BlockId Payload :=
  if b ∈ ids then blk b else B.blk (sk.idx b)

variable {sk}

@[simp] theorem fillMap_old {B : sk.Blocks} {b : BlockId} (hb : b ∈ ids) :
    sk.fillMap B b = blk b := if_pos hb

@[simp] theorem fillMap_fresh {B : sk.Blocks} {k : ℕ} :
    sk.fillMap B (sk.fresh k) = B.blk k := by
  simp only [fillMap, if_neg (sk.hfresh_new k), sk.hidx]

variable (sk)

/-- The copy reading: the donor's references verbatim. Needs only that
the old universe is closed under references. -/
def copyBlocks (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) : sk.Blocks where
  blk := sk.copyBlock
  round := fun _ => rfl
  creator := fun _ => rfl
  refs_mem := fun k hk1 hk2 j hj =>
    Finset.mem_union_left _ (hc _ (sk.hline_mem k (sk.r0_le_of_lt hk1) hk2) j hj)

/-- The self-referencing reading: the donor's references plus `v1`'s
block of the round below. -/
def selfBlocks (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) : sk.Blocks where
  blk := sk.fillBlock
  round := fun _ => rfl
  creator := fun _ => rfl
  refs_mem := fun k hk1 hk2 j hj => by
    simp only [fillBlock, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · by_cases hb : k = sk.r0 + 1
      · simp only [prev, if_pos hb]
        exact Finset.mem_union_left _ sk.hB1
      · simp only [prev, if_neg hb]
        exact Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k - 1, by omega, by omega, rfl⟩)
    · exact Finset.mem_union_left _ (hc _ (sk.hline_mem k (sk.r0_le_of_lt hk1) hk2) j hj)

@[simp] theorem copyBlocks_blk (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) :
    (sk.copyBlocks hc).blk = sk.copyBlock := rfl

@[simp] theorem selfBlocks_blk (hc : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) :
    (sk.selfBlocks hc).blk = sk.fillBlock := rfl

end SkipData

end LeanDag
