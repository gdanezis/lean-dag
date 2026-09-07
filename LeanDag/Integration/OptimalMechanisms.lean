import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.Integration.HydrozoanMechanisms
/-!
# Garbage collection, crash recovery and re-genesis for Optimal-Hydrozoan

Optimal-Hydrozoan's universes are Hydrozoan's under leader exclusion.
`Excluded` is that invariant on the record, and it is mechanised: it
survives the cut because a block two rounds above the horizon keeps its
refs and its refs keep theirs; the copy fill because a filled
block's refs are the donor's and old blocks vote only for old
blocks; and re-genesis because the new block is bound by no exclusion
and is its creator's only block. The carrier then reads as records under
`Excluded`, through Hydrozoan's adapter, and every mechanism cell is
`Arcs/Record.lean` at that instance.

The fill cell is the one the skip-fill refutation had put out of
scope. That was a fact about the core's `skipFill`, whose self
reference grafts the anchor's refs onto the donor's; the copy fill
adds no edge, and the objection does not apply.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs
open LeanDag.OptimalHydrozoan (LeaderExcludedAll IsCandidateAt WitnessesAt)

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable {S : Slots Replica} {G d : ℕ}

section HZ

variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- **Leader exclusion survives the cut.** A block bound by exclusion
sits two rounds above the horizon, so it keeps its refs, its refs
keep theirs and their creators, and its candidates are old blocks at a
rebased round. -/
theorem leaderExcludedAll_chop (hU : LeaderExcludedAll U) :
    LeaderExcludedAll (BlockRecord.chop U G) := by
  intro b hb v h2 hwit j hj
  rw [BlockRecord.mem_chop_ids] at hb
  have h2' := h2
  simp only [BlockRecord.chop_block, chopBlk_round] at h2'
  have hjb := hj
  rw [BlockRecord.chop_block, chopBlk_refs_of_lt (by omega)] at hjb
  have hjU := U.complete b hb.1 j hjb
  simp only [BlockRecord.chop_block, chopBlk_creator]
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  have hpar : ∀ j', j' ∈ ((BlockRecord.chop U G).block b).refs → j' ∈ (U.block b).refs := by
    intro j' hj'
    rwa [BlockRecord.chop_block, chopBlk_refs_of_lt (by omega)] at hj'
  have hcand : ∀ L j', j' ∈ (U.block b).refs →
      IsVote (BlockRecord.chop U G) j' L →
      IsCandidateAt (BlockRecord.chop U G) (((BlockRecord.chop U G).block b).round - 2) v L →
      IsCandidateAt U ((U.block b).round - 2) v L ∧ IsVote U j' L := by
    intro L j' hj' hv hc
    have hj'U := U.complete b hb.1 j' hj'
    have hj'r := (U.valid b hb.1).predecessor j' hj'
    unfold IsVote at hv ⊢
    rw [BlockRecord.chop_block, chopBlk_refs_of_lt (by omega)] at hv
    obtain ⟨hLm, hLr, hLa⟩ := hc
    rw [BlockRecord.mem_chop_ids] at hLm
    simp only [BlockRecord.chop_block, chopBlk_round] at hLr
    simp only [BlockRecord.chop_block, chopBlk_creator] at hLa
    exact ⟨⟨hLm.1, by omega, hLa⟩, hv⟩
  obtain ⟨hc₁, hv₁'⟩ := hcand L₁ j₁ (hpar j₁ hj₁) hv₁ hL₁
  obtain ⟨hc₂, hv₂'⟩ := hcand L₂ j₂ (hpar j₂ hj₂) hv₂ hL₂
  exact hU b hb.1 v (by omega) ⟨L₁, L₂, hc₁, hc₂, hne, ⟨j₁, hpar j₁ hj₁, hv₁'⟩,
    ⟨j₂, hpar j₂ hj₂, hv₂'⟩⟩ j hjb

variable {sk : SkipData U.ids U.block}

/-- A candidate voted for by an old block is old, and a candidate in the
old universe. -/
theorem isCandidateAt_of_old {r : ℕ} {v : Replica} {j L : BlockId} (hj : j ∈ U.ids)
    (hv : IsVote (BlockRecord.copyFill U sk) j L)
    (hc : IsCandidateAt (BlockRecord.copyFill U sk) r v L) : IsCandidateAt U r v L := by
  unfold IsVote at hv
  rw [BlockRecord.copyFill_block_old hj] at hv
  have hLU := U.complete j hj L hv
  obtain ⟨-, hLr, hLa⟩ := hc
  rw [BlockRecord.copyFill_block_old hLU] at hLr hLa
  exact ⟨hLU, hLr, hLa⟩

/-- **Leader exclusion survives the copy fill.** A filled block's refs
are the donor's; old blocks vote only for old blocks; so whatever a
block of the fill witnesses, a block of the old universe with the same
refs witnessed, and its refs were already excluded. -/
theorem leaderExcludedAll_copyFill (hU : LeaderExcludedAll U) :
    LeaderExcludedAll (BlockRecord.copyFill U sk) := by
  intro b hb v h2 hwit j hj
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  rcases Finset.mem_union.mp hb with ho | hf
  · -- an old block: refs, round and witnesses are the old universe's
    rw [BlockRecord.copyFill_block_old ho] at h2 hj hj₁ hj₂
    have hj₁U := U.complete b ho j₁ hj₁
    have hj₂U := U.complete b ho j₂ hj₂
    have hjU := U.complete b ho j hj
    rw [BlockRecord.copyFill_block_old hjU]
    refine hU b ho v h2 ⟨L₁, L₂, isCandidateAt_of_old hj₁U hv₁ ?_,
      isCandidateAt_of_old hj₂U hv₂ ?_, hne, ⟨j₁, hj₁, ?_⟩, ⟨j₂, hj₂, ?_⟩⟩ j hj
    · rw [BlockRecord.copyFill_block_old ho] at hL₁; exact hL₁
    · rw [BlockRecord.copyFill_block_old ho] at hL₂; exact hL₂
    · unfold IsVote at hv₁ ⊢
      rw [BlockRecord.copyFill_block_old hj₁U] at hv₁; exact hv₁
    · unfold IsVote at hv₂ ⊢
      rw [BlockRecord.copyFill_block_old hj₂U] at hv₂; exact hv₂
  · -- a filled block: everything is the donor's
    obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    have hlm := sk.hline_mem k (by omega) hk2
    have hlr : (U.block (sk.line k)).round = k := sk.hline_round k (by omega) hk2
    rw [BlockRecord.copyFill_block_fresh] at h2 hj hj₁ hj₂ hL₁ hL₂
    simp only [SkipData.copyBlock] at h2 hj hj₁ hj₂ hL₁ hL₂
    have hj₁U := U.complete _ hlm j₁ hj₁
    have hj₂U := U.complete _ hlm j₂ hj₂
    have hjU := U.complete _ hlm j hj
    rw [BlockRecord.copyFill_block_old hjU]
    have h2' : 2 ≤ (U.block (sk.line k)).round := by omega
    have hr : k - 2 = (U.block (sk.line k)).round - 2 := by omega
    rw [hr] at hL₁ hL₂
    exact hU _ hlm v h2' ⟨L₁, L₂, isCandidateAt_of_old hj₁U hv₁ hL₁,
      isCandidateAt_of_old hj₂U hv₂ hL₂, hne,
      ⟨j₁, hj₁, by unfold IsVote at hv₁ ⊢
                   rw [BlockRecord.copyFill_block_old hj₁U] at hv₁; exact hv₁⟩,
      ⟨j₂, hj₂, by unfold IsVote at hv₂ ⊢
                   rw [BlockRecord.copyFill_block_old hj₂U] at hv₂; exact hv₂⟩⟩ j hj

/-- **Leader exclusion survives re-genesis.** The new block sits at round
zero, so it is bound by no exclusion; and it is its creator's only
block, so it can be no second candidate of a witnessed equivocation and
no parent of anything old. Every old block's witnesses and refs are
unchanged. -/
theorem leaderExcludedAll_addGenesis {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (hU : LeaderExcludedAll U) {v : Replica} {g : BlockId} {hg : g ∉ U.ids}
    {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v} :
    LeaderExcludedAll (BlockRecord.addGenesis U v g () hg hsev) := by
  intro b hb u h2 hwit j hj
  rcases Finset.mem_insert.mp hb with rfl | hbU
  · rw [BlockRecord.addGenesis_block_new] at h2
    simp at h2
  · rw [BlockRecord.addGenesis_block_old hbU] at h2 hwit hj
    have hjU := U.complete b hbU j hj
    rw [BlockRecord.addGenesis_block_old hjU]
    obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
    have hj₁' : j₁ ∈ (U.block b).refs := by rwa [BlockRecord.addGenesis_block_old hbU] at hj₁
    have hj₂' : j₂ ∈ (U.block b).refs := by rwa [BlockRecord.addGenesis_block_old hbU] at hj₂
    by_cases huv : u = v
    · subst huv
      have hc : ∀ L, IsCandidateAt (BlockRecord.addGenesis U u g () hg hsev) ((U.block b).round - 2) u L →
          L = g := by
        rintro L ⟨hLm, -, hLa⟩
        rcases Finset.mem_insert.mp hLm with rfl | hLU
        · rfl
        · rw [BlockRecord.addGenesis_block_old hLU] at hLa
          exact absurd hLa (hsev L hLU)
      exact absurd ((hc L₁ hL₁).trans (hc L₂ hL₂).symm) hne
    · have hcand : ∀ L, IsCandidateAt (BlockRecord.addGenesis U v g () hg hsev) ((U.block b).round - 2) u L →
          IsCandidateAt U ((U.block b).round - 2) u L := by
        rintro L ⟨hLm, hLr, hLa⟩
        rcases Finset.mem_insert.mp hLm with rfl | hLU
        · rw [BlockRecord.addGenesis_block_new] at hLa
          exact absurd hLa.symm huv
        · rw [BlockRecord.addGenesis_block_old hLU] at hLr hLa
          exact ⟨hLU, hLr, hLa⟩
      have hvote : ∀ j ∈ (U.block b).refs, ∀ L,
          IsVote (BlockRecord.addGenesis U v g () hg hsev) j L →
          IsVote U j L := by
        intro j hj L hv
        have hjU := U.complete b hbU j hj
        unfold IsVote at hv ⊢
        rw [BlockRecord.addGenesis_block_old hjU] at hv
        exact hv
      exact hU b hbU u h2 ⟨L₁, L₂, hcand L₁ hL₁, hcand L₂ hL₂, hne,
        ⟨j₁, hj₁', hvote j₁ hj₁' L₁ hv₁⟩, ⟨j₂, hj₂', hvote j₂ hj₂' L₂ hv₂⟩⟩ j hj

/-- **Leader exclusion, as an invariant on the record.** -/
def Excluded (W : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  LeaderExcludedAll W

/-- **And it is mechanised**: the three facts above, read at the record. -/
instance Excluded.mechanised :
    BlockRecord.Invariant.Mechanised (Excluded (Replica := Replica) (BlockId := BlockId)) where
  chop := fun G h => leaderExcludedAll_chop (G := G) h
  copyFill := fun sk h => leaderExcludedAll_copyFill (sk := sk) h
  addGenesis := fun v g _ hg hsev h =>
    leaderExcludedAll_addGenesis (v := v) (g := g) (hg := hg) (hsev := hsev) h

end HZ

section Opt

variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan's carrier, on the record**: Hydrozoan's adapter,
under `Excluded`. -/
def optOnRecord :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).OnRecord LeanDag.Hydrozoan.ValidWrt
      (LeanDag.Hydrozoan.NonByzantine : Finset Replica) Excluded where
  toRec := fun W => W.val
  inv := fun W => W.property
  ofRec := fun W h => ⟨W, h⟩
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  ofView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

variable {W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
  (BlockId := BlockId)).Universe}

/-! The cut, the copy fill and re-genesis at Optimal-Hydrozoan's carrier
are the record's, through `optOnRecord`. -/

end Opt

end Integration

end LeanDag
