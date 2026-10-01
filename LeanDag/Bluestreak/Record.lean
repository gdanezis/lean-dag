import LeanDag.Bluestreak.Carrier
import LeanDag.Properties.Arcs.Record
/-!
# Bluestreak: the discipline survives the cut and re-genesis

A retained block's claim names a block two rounds below, at or above
the horizon once the claimer is two rounds above it; the claimed
block's voters sit one round above it, strictly above the horizon,
where the cut keeps every reference. The retained blocks of the two
lowest rounds claim blocks the cut dropped, and those claims are read
by no slot.
-/

namespace LeanDag

namespace Bluestreak

open BlockRecord

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload} [ClaimMap BlockId] {G : ℕ}

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
  certified_quorate := by
    intro A hA hc h0
    rw [mem_chop_ids] at hA
    simp only [chop_block, chopBlk_round] at h0
    have hq := hI.certified_quorate A hA.1 ((certified_chop_iff hA.2).mp hc) (by omega)
    simp only [creators, chop_block, chopBlk_refs_of_lt (show G < (U.block A).round by omega),
      creatorsOf_chopBlk]
    exact hq
  honest_backed := by
    intro B hB hc X hBX L hcl h2
    rw [mem_chop_ids] at hB
    simp only [chop_block, chopBlk_creator, chopBlk_round] at hc h2 ⊢
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
  certified_quorate := by
    intro A hA hc h0
    rcases Finset.mem_insert.mp hA with rfl | hA
    · rw [addGenesis_block_new] at h0; exact absurd h0 (Nat.lt_irrefl 0)
    · rw [addGenesis_block_old hA] at h0
      have hq := hI.certified_quorate A hA ((certified_addGenesis_iff hA).mp hc) h0
      have hcr : creators (U.addGenesis v g p hg hsev).block
          ((U.addGenesis v g p hg hsev).block A) = creators U.block (U.block A) := by
        rw [addGenesis_block_old hA]
        unfold creators creatorsOf
        exact Finset.image_congr fun j hj => by
          rw [addGenesis_block_old (U.complete A hA j hj)]
      rw [hcr]; exact hq
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
      rw [addGenesis_block_old hX] at h2 ⊢
      obtain ⟨hrL, hcert⟩ := hI.honest_backed B hB hc X hr L hcl h2
      have hL := mem_of_certified hcert
      rw [addGenesis_block_old hL]
      exact ⟨hrL, (certified_addGenesis_iff hL).mpr hcert⟩

end Genesis

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
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} [ClaimMap BlockId]

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

end BluestreakProperties

end LeanDag
