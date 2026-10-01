import LeanDag.Bluestreak.Carrier
import LeanDag.Properties.Arcs.Record
/-!
# Bluestreak: the discipline across the cut, re-genesis and the chain fill

A retained block's claim names a block two rounds below, at or above
the horizon once the claimer is two rounds above it; the claimed
block's voters sit one round above it, strictly above the horizon,
where the cut keeps every reference. The retained blocks of the two
lowest rounds claim blocks the cut dropped, and those claims are read
by no slot. The chain fill's blocks are ordinary and claim nothing, so
they add no claim to any cone.
-/

namespace LeanDag

namespace Bluestreak

open BlockRecord

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable [Format BlockId Payload] {U : Universe Validator BlockId Payload} {G : ℕ}

/-- A path of the cut is a path of the record. -/
theorem reaches_of_reaches_chop {b i : BlockId} (h : Reaches (U.chop G) b i) : Reaches U b i := by
  induction h with
  | refl => exact Reaches.refl
  | tail _ hstep ih => exact ih.trans (Reaches.single (chopBlk_refs_subset hstep))

/-- At or above the horizon, a block's voters are unchanged by the cut. -/
theorem supporters_chop {L : BlockId} (hL : G ≤ (U.block L).round) :
    supporters (U.chop G) L (((U.chop G).block L).round + 1) =
      supporters U L ((U.block L).round + 1) := by
  ext v
  simp only [mem_supporters, mem_chop_ids, chop_block, chopBlk_round, chopBlk_creator]
  constructor
  · rintro ⟨q, ⟨hq, hqG⟩, hqr, hqL, hqv⟩
    exact ⟨q, hq, by omega, chopBlk_refs_subset hqL, hqv⟩
  · rintro ⟨q, hq, hqr, hqL, hqv⟩
    exact ⟨q, ⟨hq, by omega⟩, by omega, by rw [chopBlk_refs_of_lt (by omega)]; exact hqL, hqv⟩

/-- At or above the horizon, certification is unchanged by the cut. -/
theorem certified_chop_iff {L : BlockId} (hL : G ≤ (U.block L).round) :
    Certified (U.chop G) L ↔ Certified U L := by
  unfold Certified
  rw [supporters_chop hL]

/-- **The discipline survives the cut.** -/
theorem disciplined_chop (hI : Disciplined U) : Disciplined (U.chop G) where
  honest_backed := by
    intro B hB hc X hBX L hcl h2
    rw [mem_chop_ids] at hB
    simp only [claimOf, chop_block, chopBlk_creator, chopBlk_round, chopBlk_payload] at hc hcl h2 ⊢
    obtain ⟨hr, hcert⟩ := hI.honest_backed B hB.1 hc X (reaches_of_reaches_chop hBX) L hcl
      (by omega)
    exact ⟨by omega, (certified_chop_iff (by omega)).mpr hcert⟩

/-! ## Re-genesis -/

section Genesis

variable {v : Validator} {g : BlockId} {p : Payload}
variable {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}

/-- A certified block is held: its voters reference it. -/
theorem mem_of_certified {L : BlockId} (h : Certified U L) : L ∈ U.ids := by
  obtain ⟨w, hw, -⟩ := exists_correct_of_card (S := supporters U L ((U.block L).round + 1))
    (by have := F.card_validators; change quorumCard Validator ≤ _ at h; omega)
  obtain ⟨c, hc, -, hcL, -⟩ := mem_supporters.mp hw
  exact U.complete c hc L hcL

/-- A path from an old block stays among the old blocks. -/
theorem reaches_of_reaches_addGenesis {b i : BlockId} (hb : b ∈ U.ids)
    (h : Reaches (U.addGenesis v g p hg hsev) b i) : Reaches U b i ∧ i ∈ U.ids := by
  induction h with
  | refl => exact ⟨Reaches.refl, hb⟩
  | tail _ hstep ih =>
      obtain ⟨hr, hy⟩ := ih
      change _ ∈ ((U.addGenesis v g p hg hsev).block _).refs at hstep
      rw [addGenesis_block_old hy] at hstep
      exact ⟨hr.trans (Reaches.single hstep), U.complete _ hy _ hstep⟩

/-- An old block's voters are unchanged by re-genesis: the new block
references nothing. -/
theorem supporters_addGenesis {L : BlockId} (hL : L ∈ U.ids) :
    supporters (U.addGenesis v g p hg hsev) L
        (((U.addGenesis v g p hg hsev).block L).round + 1) =
      supporters U L ((U.block L).round + 1) := by
  ext w
  rw [addGenesis_block_old hL, mem_supporters, mem_supporters]
  constructor
  · rintro ⟨q, hq, hqr, hqL, hqw⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [addGenesis_block_new] at hqL; exact absurd hqL (Finset.notMem_empty _)
    · rw [addGenesis_block_old hq] at hqr hqL hqw
      exact ⟨q, hq, hqr, hqL, hqw⟩
  · rintro ⟨q, hq, hqr, hqL, hqw⟩
    exact ⟨q, Finset.mem_insert_of_mem hq, by rw [addGenesis_block_old hq]; exact hqr,
      by rw [addGenesis_block_old hq]; exact hqL, by rw [addGenesis_block_old hq]; exact hqw⟩

/-- An old block's certification is unchanged by re-genesis. -/
theorem certified_addGenesis_iff {L : BlockId} (hL : L ∈ U.ids) :
    Certified (U.addGenesis v g p hg hsev) L ↔ Certified U L := by
  unfold Certified
  rw [supporters_addGenesis hL]

/-- **The discipline survives re-genesis.** The new block sits at round
zero with no references, so it votes for nothing and carries no read
claim. -/
theorem disciplined_addGenesis (hI : Disciplined U) :
    Disciplined (U.addGenesis v g p hg hsev) where
  honest_backed := by
    intro B hB hc X hBX L hcl h2
    rcases Finset.mem_insert.mp hB with rfl | hB
    · have hX : X = B := by
        rcases hBX.cases_head with rfl | ⟨j, hj, -⟩
        · rfl
        · change j ∈ ((U.addGenesis v B p hg hsev).block B).refs at hj
          rw [addGenesis_block_new] at hj; exact absurd hj (Finset.notMem_empty _)
      subst hX
      rw [addGenesis_block_new] at h2; exact absurd h2 (by simp)
    · rw [addGenesis_block_old hB] at hc
      obtain ⟨hr, hX⟩ := reaches_of_reaches_addGenesis hB hBX
      simp only [claimOf] at hcl
      rw [addGenesis_block_old hX] at h2 hcl ⊢
      obtain ⟨hrL, hcert⟩ := hI.honest_backed B hB hc X hr L hcl h2
      have hL := mem_of_certified hcert
      rw [addGenesis_block_old hL]
      exact ⟨hrL, (certified_addGenesis_iff hL).mpr hcert⟩

end Genesis

/-! ## The chain fill -/

section Chain

variable (sk : GapData U.ids U.block) {p : Payload}
  (hp : Format.leader (BlockId := BlockId) p = false)

/-- The self reference of a filled block: `v1`'s block of the round
below, under the extended map. -/
theorem prev_chain {k : ℕ} (hk1 : sk.r0 < k) :
    (sk.fillMap (sk.chainBlocks p) (sk.prev k)).round = k - 1 ∧
      (sk.fillMap (sk.chainBlocks p) (sk.prev k)).creator = sk.v1 := by
  by_cases hb : k = sk.r0 + 1
  · simp only [GapData.prev, if_pos hb, GapData.fillMap_old sk.hB1]
    exact ⟨by have : sk.r0 = (U.block sk.B1).round := rfl; omega, sk.hB1c⟩
  · simp only [GapData.prev, if_neg hb, GapData.fillMap_fresh, GapData.chainBlocks_blk]
    exact ⟨rfl, rfl⟩

include hp in
/-- **A chain block is valid**: one reference, to its author's block of
the round below, and an ordinary block's format. -/
theorem chainBlock_valid {k : ℕ} (hk1 : sk.r0 < k) :
    ValidWrt (sk.fillMap (sk.chainBlocks p)) (sk.chainBlock p k) := by
  have hpr := prev_chain sk (p := p) hk1
  refine ⟨fun j hj => ?_, fun _ => Nat.zero_le _, ⟨⟨fun j hj l hl _ => ?_, fun _ => ?_⟩,
    fun ht => ?_, fun _ j hj => ?_⟩⟩
  · simp only [GapData.chainBlock, Finset.mem_singleton] at hj
    subst hj
    show _ + 1 = k
    omega
  · simp only [GapData.chainBlock, Finset.mem_singleton] at hj hl
    rw [hj, hl]
  · exact ⟨sk.prev k, Finset.mem_singleton_self _, hpr.2⟩
  · exact absurd ht (by simp only [GapData.chainBlock, hp]; decide)
  · simp only [GapData.chainBlock, Finset.mem_singleton] at hj
    subst hj
    exact Or.inl hpr.2

/-- **The chain fill**: `U` with `v1`'s gap filled by a chain of ordinary
blocks carrying the payload `p`. -/
def chainFill : Universe Validator BlockId Payload :=
  BlockRecord.fill U sk (sk.chainBlocks p) (fun _ hk1 _ => chainBlock_valid sk hp hk1)

/-- A path from an old block stays among the old blocks. -/
theorem reaches_of_reaches_chainFill {b X : BlockId} (hb : b ∈ U.ids)
    (h : Reaches (chainFill sk hp) b X) : Reaches U b X ∧ X ∈ U.ids := by
  induction h with
  | refl => exact ⟨Reaches.refl, hb⟩
  | tail _ hstep ih =>
      obtain ⟨hr, hy⟩ := ih
      change _ ∈ ((chainFill sk hp).block _).refs at hstep
      rw [chainFill, BlockRecord.fill_block_old hy] at hstep
      exact ⟨hr.trans (Reaches.single hstep), U.complete _ hy _ hstep⟩

/-- A path from a filled block reaches old blocks only through `B1`. -/
theorem reaches_B1_of_reaches_chainFill {b X : BlockId} (hb : b ∈ sk.freshIds)
    (h : Reaches (chainFill sk hp) b X) :
    X ∈ (chainFill sk hp).ids ∧ (X ∈ U.ids → Reaches U sk.B1 X) := by
  induction h with
  | refl =>
      refine ⟨Finset.mem_union_right _ hb, fun hbU => ?_⟩
      obtain ⟨k, -, -, rfl⟩ := sk.mem_freshIds.mp hb
      exact absurd hbU (sk.hfresh_new k)
  | tail _ hstep ih =>
      rename_i y z _
      obtain ⟨hy, hyB⟩ := ih
      change z ∈ ((chainFill sk hp).block y).refs at hstep
      refine ⟨(chainFill sk hp).complete y hy z hstep, fun hz => ?_⟩
      rcases Finset.mem_union.mp hy with hyU | hyF
      · rw [chainFill, BlockRecord.fill_block_old hyU] at hstep
        exact (hyB hyU).trans (Reaches.single hstep)
      · obtain ⟨k, hk1, -, rfl⟩ := sk.mem_freshIds.mp hyF
        rw [chainFill, BlockRecord.fill_block_fresh] at hstep
        simp only [GapData.chainBlocks_blk, GapData.chainBlock, Finset.mem_singleton] at hstep
        by_cases hkb : k = sk.r0 + 1
        · simp only [GapData.prev, if_pos hkb] at hstep
          subst hstep
          exact Reaches.refl
        · simp only [GapData.prev, if_neg hkb] at hstep
          subst hstep
          exact absurd hz (sk.hfresh_new _)

/-- An old block's certification survives the fill: its voters remain. -/
theorem certified_chainFill {L : BlockId} (hL : L ∈ U.ids) (h : Certified U L) :
    Certified (chainFill sk hp) L := by
  unfold Certified at h ⊢
  rw [chainFill, BlockRecord.fill_block_old hL]
  refine le_trans h (Finset.card_le_card fun w hw => ?_)
  obtain ⟨q, hq, hqr, hqL, hqw⟩ := mem_supporters.mp hw
  exact mem_supporters.mpr ⟨q, Finset.mem_union_left _ hq,
    by rw [BlockRecord.fill_block_old hq]; exact hqr,
    by rw [BlockRecord.fill_block_old hq]; exact hqL,
    by rw [BlockRecord.fill_block_old hq]; exact hqw⟩

/-- **The discipline survives the chain fill**, when the filled blocks
claim nothing: an old block's cone is unchanged, and a filled block's
cone is the chain and `B1`'s. -/
theorem disciplined_chainFill (hI : Disciplined U)
    (hc : Format.claim (BlockId := BlockId) p = none) : Disciplined (chainFill sk hp) where
  honest_backed := by
    intro B hB hcB X hBX L hcl h2
    have hXf : X ∈ (chainFill sk hp).ids := mem_ids_of_reaches hB hBX
    have hX : X ∈ U.ids := by
      rcases Finset.mem_union.mp hXf with hXU | hXF
      · exact hXU
      · obtain ⟨k, -, -, rfl⟩ := sk.mem_freshIds.mp hXF
        change Format.claim ((chainFill sk hp).block (sk.fresh k)).payload = some L at hcl
        rw [chainFill, BlockRecord.fill_block_fresh] at hcl
        simp only [GapData.chainBlocks_blk, GapData.chainBlock, hc] at hcl
        exact absurd hcl (by simp)
    -- an honest block of `U` whose cone holds `X`
    obtain ⟨B', hB', hcB', hr⟩ : ∃ B' ∈ U.ids,
        (U.block B').creator ∈ (Correct : Finset Validator) ∧ Reaches U B' X := by
      rcases Finset.mem_union.mp hB with hBU | hBF
      · rw [chainFill, BlockRecord.fill_block_old hBU] at hcB
        exact ⟨B, hBU, hcB, (reaches_of_reaches_chainFill sk hp hBU hBX).1⟩
      · obtain ⟨k, -, -, hk⟩ := sk.mem_freshIds.mp hBF
        have hv1 : sk.v1 ∈ (Correct : Finset Validator) := by
          rw [hk, chainFill, BlockRecord.fill_block_fresh] at hcB; exact hcB
        exact ⟨sk.B1, sk.hB1, by rw [sk.hB1c]; exact hv1,
          (reaches_B1_of_reaches_chainFill sk hp hBF hBX).2 hX⟩
    have hold : (chainFill sk hp).block X = U.block X := BlockRecord.fill_block_old hX
    simp only [claimOf, hold] at hcl h2 ⊢
    obtain ⟨hrL, hcert⟩ := hI.honest_backed B' hB' hcB' X hr L hcl h2
    have hL := mem_of_certified hcert
    rw [show (chainFill sk hp).block L = U.block L from BlockRecord.fill_block_old hL]
    exact ⟨hrL, certified_chainFill sk hp hL hcert⟩

end Chain

instance : Invariant.Chops (Disciplined (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  chop := fun _ h => disciplined_chop h

instance : Invariant.Regenesis (Disciplined (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  addGenesis := fun _ _ _ _ _ h => disciplined_addGenesis h

end Bluestreak

namespace BluestreakProperties

open LeanDag.Properties LeanDag.Bluestreak

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} [Format BlockId Payload]

/-- **Bluestreak's carrier, on the record**: the identity maps, under
`Disciplined`. -/
def onRecord :
    (bluestreakRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).OnRecord
      Bluestreak.ValidWrt (Correct : Finset Validator)
      (Disciplined (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  toRec := fun U => U.val
  inv := fun U => U.property
  ofRec := fun W h => ⟨W, h⟩
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toRec_ofRec := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

/-- **The fill, at Bluestreak's carrier**: the chain fill through
`onRecord`, with `disciplined_chainFill` as the invariant. -/
def fill (U : (bluestreakRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)).Universe) (sk : GapData U.val.ids U.val.block) {p : Payload}
    (hp : Format.leader (BlockId := BlockId) p = false)
    (hc : Format.claim (BlockId := BlockId) p = none) :
    (bluestreakRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Universe :=
  onRecord.fill U sk (sk.chainBlocks p) (fun _ hk1 _ => chainBlock_valid sk hp hk1)
    (disciplined_chainFill sk hp U.property hc)

end BluestreakProperties

end LeanDag
