import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.Properties.Extends
import LeanDag.Common.Record.Invariant
import LeanDag.GC.ChopDecided
/-!
# A carrier on the block record, and the witnesses every mechanism owes

A rule whose universes are block records gets its cut, fill and
re-genesis from `Record/`, and the witnesses those mechanisms owe the
properties (`Truncates`, `Extends`, `Sustains`) are proved here once.
`DagRule.OnRecord` says how a carrier's universes and views are read as
records, with an invariant `I` the carrier adds that the record's
constructions preserve (`Invariant.Mechanised`) — `Any` for most rules,
`HonestNoEquiv` for Orcaella. Nothing here mentions verdicts, so one
structure serves rules with different view types; the verdict cells are
`Arcs/Record.lean`.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A carrier read as block records.** -/
structure DagRule.OnRecord (R : DagRule Validator BlockId Payload)
    (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (I : BlockRecord Validator BlockId Payload P honest → Prop) where
  /-- A universe, as a record. -/
  toRec : R.Universe → BlockRecord Validator BlockId Payload P honest
  /-- The record of a universe has the invariant. -/
  inv : ∀ U, I (toRec U)
  /-- A record with the invariant, as a universe. -/
  ofRec : ∀ W : BlockRecord Validator BlockId Payload P honest, I W → R.Universe
  ids_to : ∀ U, (toRec U).ids = R.ids U
  block_to : ∀ U, (toRec U).block = R.block U
  ids_of : ∀ W h, R.ids (ofRec W h) = W.ids
  block_of : ∀ W h, R.block (ofRec W h) = W.block
  /-- A view, as a view of the record. -/
  toView : ∀ {U : R.Universe}, R.View U → (toRec U).View
  /-- A view of a record, as a view of the universe it makes. -/
  ofView : ∀ {W : BlockRecord Validator BlockId Payload P honest} {h : I W},
    W.View → R.View (ofRec W h)
  viewIds_to : ∀ {U : R.Universe} (V : R.View U), (toView V).ids = R.viewIds V
  viewIds_of : ∀ {W : BlockRecord Validator BlockId Payload P honest} {h : I W} (V : W.View),
    R.viewIds (ofView (h := h) V) = V.ids

/-- The core's cut rebases the schedule: a schedule fact with no universe
in it. -/
theorem rebases_chop {S : Slots Validator} {G d : ℕ} (hd : G ≤ S.slotRound d) :
    Rebases S (S.chop G d hd) G d where
  slotRound := fun k => by
    simp only [Slots.chop_slotRound]
    have := horizon_le_slotRound hd k
    omega
  leader := fun _ => rfl
  base := hd

namespace DagRule.OnRecord

open BlockRecord

variable {R : DagRule Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {I : BlockRecord Validator BlockId Payload P honest → Prop}
variable (c : R.OnRecord P honest I) [P.Mechanised] [Invariant.Mechanised I]

/-- Membership, read through the record. -/
theorem mem_toRec {U : R.Universe} {b : BlockId} : b ∈ (c.toRec U).ids ↔ b ∈ R.ids U := by
  rw [c.ids_to]

/-! ## The cut -/

/-- The cut, at the carrier. -/
def chop (U : R.Universe) (G : ℕ) : R.Universe :=
  c.ofRec ((c.toRec U).chop G) (Invariant.Mechanised.chop G (c.inv U))

variable {G d : ℕ} {S : Slots Validator}

theorem ids_chop (U : R.Universe) :
    R.ids (c.chop U G) = (R.ids U).filter fun i => G ≤ (R.block U i).round := by
  rw [chop, c.ids_of, BlockRecord.chop_ids, c.ids_to, c.block_to]

theorem block_chop (U : R.Universe) : R.block (c.chop U G) = chopBlk (R.block U) G := by
  rw [chop, c.block_of, BlockRecord.chop_block, c.block_to]

/-- **The cut sustains the carrier from its horizon.** -/
theorem sustains_chop (U : R.Universe) : Sustains R U (c.chop U G) G G where
  mem := fun b => by
    rw [c.ids_chop, c.block_chop, Finset.mem_filter, chopBlk_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by rw [c.block_chop, chopBlk_round]; omega
  creator := fun b _ _ => by rw [c.block_chop, chopBlk_creator]
  refs := fun b _ hr => by rw [c.block_chop, chopBlk_refs_of_lt hr]

/-- **The cut is a truncation of the carrier.** -/
theorem truncates_chop (U : R.Universe) (hd : G ≤ S.slotRound d) :
    Truncates R U (c.chop U G) S (S.chop G d hd) G d :=
  { c.sustains_chop U, rebases_chop hd with }

/-- The truncated view: keep what clears the cut. -/
def chopView {U : R.Universe} (V : R.View U) (G : ℕ) : R.View (c.chop U G) :=
  c.ofView ((c.toView V).chop G)

theorem viewIds_chopView {U : R.Universe} (V : R.View U) :
    R.viewIds (c.chopView V G) = (R.viewIds V).filter fun i => G ≤ (R.block U i).round := by
  have h := c.viewIds_of (h := Invariant.Mechanised.chop G (c.inv U)) ((c.toView V).chop G)
  rw [BlockRecord.View.chop_ids, c.viewIds_to, c.block_to] at h
  exact h

/-- **The truncated view agrees with the original above the cut.** -/
theorem viewAgreeAbove_chop {U : R.Universe} {V : R.View U} :
    ViewAgreeAbove R V (c.chopView V G) G :=
  fun b _ hr => by
    rw [c.viewIds_chopView, Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-! ## The fill -/

/-- The fill, at the carrier, under a reading of the filled blocks and
with the invariant supplied. -/
def fill (U : R.Universe) (sk : SkipData (c.toRec U).ids (c.toRec U).block) (B : sk.Blocks)
    (hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k))
    (hI : I (BlockRecord.fill (c.toRec U) sk B hB)) : R.Universe :=
  c.ofRec (BlockRecord.fill (c.toRec U) sk B hB) hI

variable {U : R.Universe} {sk : SkipData (c.toRec U).ids (c.toRec U).block} {B : sk.Blocks}
variable {hB : ∀ k, sk.r0 < k → k ≤ sk.r → P (sk.fillMap B) (B.blk k)}
variable {hI : I (BlockRecord.fill (c.toRec U) sk B hB)}

theorem ids_fill : R.ids (c.fill U sk B hB hI) = (c.toRec U).ids ∪ sk.freshIds := by
  rw [fill, c.ids_of, BlockRecord.fill_ids]

theorem block_fill : R.block (c.fill U sk B hB hI) = sk.fillMap B := by
  rw [fill, c.block_of, BlockRecord.fill_block]

theorem block_fill_old {b : BlockId} (hb : b ∈ R.ids U) :
    R.block (c.fill U sk B hB hI) b = R.block U b := by
  rw [c.block_fill, ← c.block_to]
  exact SkipData.fillMap_old (c.mem_toRec.mpr hb)

/-- **The fill is an extension of the carrier.** -/
theorem extends_fill : Extends R U (c.fill U sk B hB hI) where
  subset := fun b hb => by
    rw [c.ids_fill]; exact Finset.mem_union_left _ (c.mem_toRec.mpr hb)
  block := fun b hb => c.block_fill_old hb

/-- **And it sustains the carrier from the top of its gap.** -/
theorem sustains_fill : Sustains R U (c.fill U sk B hB hI) 0 (sk.r + 1) where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      refine ⟨by rw [c.ids_fill]; exact Finset.mem_union_left _ (c.mem_toRec.mpr hb), ?_⟩
      rw [c.block_fill_old hb]; omega
    · rintro ⟨hb, hr⟩
      rw [c.ids_fill] at hb
      have hbU : b ∈ R.ids U := by
        rcases Finset.mem_union.mp hb with ho | hf
        · exact c.mem_toRec.mp ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
          rw [c.block_fill, SkipData.fillMap_fresh, B.round] at hr
          omega
      exact ⟨hbU, by rw [c.block_fill_old hbU] at hr; omega⟩
  round := fun b hb _ => by rw [c.block_fill_old hb]; omega
  creator := fun b hb _ => by rw [c.block_fill_old hb]
  refs := fun b hb _ => by rw [c.block_fill_old hb]

/-- The pre-crash view, read in the fill. -/
def liftView (V : R.View U) : R.View (c.fill U sk B hB hI) :=
  c.ofView (BlockRecord.View.lift (hB := hB) (c.toView V))

theorem viewIds_liftView (V : R.View U) :
    R.viewIds (c.liftView (hI := hI) V) = R.viewIds V := by
  have h := c.viewIds_of (h := hI) (BlockRecord.View.lift (hB := hB) (c.toView V))
  rw [BlockRecord.View.lift_ids, c.viewIds_to] at h
  exact h

theorem viewIds_subset_liftView (V : R.View U) :
    R.viewIds V ⊆ R.viewIds (c.liftView (hI := hI) V) := by
  rw [c.viewIds_liftView]

section Copy

variable [P.CopyStable]

/-- The copy fill, at a carrier whose validity does not read the author. -/
def copyFill (U : R.Universe) (sk : SkipData (c.toRec U).ids (c.toRec U).block) :
    R.Universe :=
  c.ofRec (BlockRecord.copyFill (c.toRec U) sk) (Invariant.Mechanised.copyFill sk (c.inv U))

theorem copyFill_eq (U : R.Universe) (sk : SkipData (c.toRec U).ids (c.toRec U).block) :
    c.copyFill U sk = c.fill U sk (sk.copyBlocks (c.toRec U).complete)
      (fun _ hk1 hk2 => BlockRecord.copyBlock_valid (c.toRec U) sk hk1 hk2)
      (Invariant.Mechanised.copyFill sk (c.inv U)) := rfl

theorem extends_copyFill (U : R.Universe)
    (sk : SkipData (c.toRec U).ids (c.toRec U).block) : Extends R U (c.copyFill U sk) :=
  c.extends_fill

theorem sustains_copyFill (U : R.Universe)
    (sk : SkipData (c.toRec U).ids (c.toRec U).block) :
    Sustains R U (c.copyFill U sk) 0 (sk.r + 1) :=
  c.sustains_fill

theorem block_copyFill_old (sk : SkipData (c.toRec U).ids (c.toRec U).block)
    {b : BlockId} (hb : b ∈ R.ids U) : R.block (c.copyFill U sk) b = R.block U b :=
  c.block_fill_old hb

/-- The pre-crash view, read in the copy fill. -/
def liftViewCopy (sk : SkipData (c.toRec U).ids (c.toRec U).block) (V : R.View U) :
    R.View (c.copyFill U sk) :=
  c.liftView (hI := Invariant.Mechanised.copyFill sk (c.inv U)) V

theorem viewIds_liftViewCopy (sk : SkipData (c.toRec U).ids (c.toRec U).block) (V : R.View U) :
    R.viewIds (c.liftViewCopy sk V) = R.viewIds V :=
  c.viewIds_liftView V

end Copy

/-! ## Re-genesis -/

/-- Re-genesis, at the carrier. -/
def addGenesis (U : R.Universe) (v : Validator) (g : BlockId) (p : Payload)
    (hg : g ∉ (c.toRec U).ids) (hsev : ∀ b ∈ (c.toRec U).ids, ((c.toRec U).block b).creator ≠ v) :
    R.Universe :=
  c.ofRec (BlockRecord.addGenesis (c.toRec U) v g p hg hsev)
    (Invariant.Mechanised.addGenesis v g p hg hsev (c.inv U))

variable {v : Validator} {g : BlockId} {p : Payload}
variable {hg : g ∉ (c.toRec U).ids} {hsev : ∀ b ∈ (c.toRec U).ids, ((c.toRec U).block b).creator ≠ v}

theorem ids_addGenesis : R.ids (c.addGenesis U v g p hg hsev) = insert g (R.ids U) := by
  rw [addGenesis, c.ids_of, BlockRecord.addGenesis_ids, c.ids_to]

theorem block_addGenesis_old {b : BlockId} (hb : b ∈ R.ids U) :
    R.block (c.addGenesis U v g p hg hsev) b = R.block U b := by
  rw [addGenesis, c.block_of, ← c.block_to]
  exact BlockRecord.addGenesis_block_old (by rw [c.ids_to]; exact hb)

theorem block_addGenesis_new :
    R.block (c.addGenesis U v g p hg hsev) g = ⟨0, v, ∅, p⟩ := by
  rw [addGenesis, c.block_of]
  exact BlockRecord.addGenesis_block_new

/-- **Re-genesis is an extension of the carrier.** -/
theorem extends_addGenesis : Extends R U (c.addGenesis U v g p hg hsev) where
  subset := fun b hb => by rw [c.ids_addGenesis]; exact Finset.mem_insert_of_mem hb
  block := fun b hb => c.block_addGenesis_old hb

/-- **And it sustains the carrier from round one.** -/
theorem sustains_addGenesis : Sustains R U (c.addGenesis U v g p hg hsev) 0 1 where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨by rw [c.ids_addGenesis]; exact Finset.mem_insert_of_mem hb,
        by rw [c.block_addGenesis_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      rw [c.ids_addGenesis] at hb
      rcases Finset.mem_insert.mp hb with rfl | ho
      · rw [c.block_addGenesis_new] at hr
        simp at hr
      · exact ⟨ho, by rw [c.block_addGenesis_old ho] at hr; omega⟩
  round := fun b hb _ => by rw [c.block_addGenesis_old hb]; omega
  creator := fun b hb _ => by rw [c.block_addGenesis_old hb]
  refs := fun b hb _ => by rw [c.block_addGenesis_old hb]

end DagRule.OnRecord

end Properties

end LeanDag
