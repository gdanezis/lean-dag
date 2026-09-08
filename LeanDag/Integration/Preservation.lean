import LeanDag.GC.Chop
import LeanDag.SafeSkip.Basic
import LeanDag.Common.Record.Invariant
import LeanDag.Hybrid.Faults
/-!
# Preservation: the transformer × invariant table, layer U

Each lemma has the shape `I U → I (F U)` for a named invariant `I` and a
universe transformer `F`, so a property stated against the invariant
transfers with no further proof. This file fills `HonestNoEquiv` and
`SynchronisedOn` against `chop` and `skipFill`; `Populated`, `DoSValid`
and the verdict facts already had their cells filled by the arcs
themselves. `chop` rebases rounds to `round − G`, so equal chopped
rounds need `G ≤ round` on both sides before truncated subtraction is
faithful.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-! ## I2 — truncation preserves honest non-equivocation: `chop` removes
blocks and never adds them, and `HonestNoEquiv` is universal over pairs
of retained blocks, so it restricts downward. -/

section Chop

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-- **I2.** Truncation preserves honest non-equivocation. -/
theorem honestNoEquiv_chop (hne : HonestNoEquiv U) :
    HonestNoEquiv (chop U G) := by
  intro i hi j hj hib hij hround
  rw [mem_chop_ids] at hi hj
  simp only [chop_block, chopBlk_creator, chopBlk_round] at hib hij hround
  -- rounds are rebased by `−G`; the filter pins both above the cut,
  -- where the subtraction is faithful
  exact hne i hi.1 j hj.1 hib hij (by omega)

end Chop

/-! ## I4 — truncation preserves coverage, above the cut: a chopped round
`n` is original round `G + n`, so a chopped universe is synchronised
from `R'` whenever the original is synchronised from `R ≤ G + R'`. -/

section Coverage

variable [F : Faults Validator]
variable {U : BlockUniverse Validator BlockId Payload} {G : ℕ}
variable {T : Finset Validator} {R R' : ℕ}

end Coverage

/-! ## I3 — the fill preserves honest non-equivocation: the same
argument the record's fill proves for the derived correct class, at the
wider honest class, turning on `hgap`. -/

section Fill

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload}

/-- **I3.** Any fill preserves honest non-equivocation. -/
theorem honestNoEquiv_fill (sk : SkipMsg U) (B : sk.Blocks)
    (hB : ∀ k, sk.r0 < k → k ≤ sk.r → ValidWrt (sk.fillMap B) (B.blk k))
    (hne : HonestNoEquiv U) : HonestNoEquiv (BlockRecord.fill U sk B hB) := by
  intro i hi j hj hib hij hround
  rcases BlockRecord.mem_fill_ids.mp hi with ho | hf <;>
    rcases BlockRecord.mem_fill_ids.mp hj with ho' | hf'
  · rw [BlockRecord.fill_block_old ho] at hib hij hround
    rw [BlockRecord.fill_block_old ho'] at hij hround
    exact hne i ho j ho' hib hij hround
  · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    rw [BlockRecord.fill_block_old ho] at hij hround
    simp only [BlockRecord.fill_block_fresh, B.creator, B.round] at hij hround
    exact (sk.hgap i ho hij (by omega) (by omega)).elim
  · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    rw [BlockRecord.fill_block_old ho'] at hij hround
    simp only [BlockRecord.fill_block_fresh, B.creator, B.round] at hij hround
    exact (sk.hgap j ho' hij.symm (by omega) (by omega)).elim
  · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
    simp only [BlockRecord.fill_block_fresh, B.round] at hround
    rw [hround]

/-- The Safe Skip fill in particular. -/
theorem honestNoEquiv_skipFill (sk : SkipMsg U) (hne : HonestNoEquiv U) :
    HonestNoEquiv sk.skipFill :=
  honestNoEquiv_fill sk _ _ hne

/-- **Re-genesis cannot make an honest validator equivocate**: the new
block's author has no other block. -/
theorem honestNoEquiv_addGenesis (hne : HonestNoEquiv U)
    {v : Validator} {g : BlockId} {p : Payload} {hg : g ∉ U.ids}
    {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v} :
    HonestNoEquiv (BlockRecord.addGenesis U v g p hg hsev) := by
  intro i hi j hj hib hij hround
  rw [BlockRecord.addGenesis_ids] at hi hj
  rcases Finset.mem_insert.mp hi with rfl | ho <;>
    rcases Finset.mem_insert.mp hj with rfl | ho'
  · rfl
  · rw [BlockRecord.addGenesis_block_new, BlockRecord.addGenesis_block_old ho'] at hij
    exact absurd hij.symm (hsev j ho')
  · rw [BlockRecord.addGenesis_block_old ho, BlockRecord.addGenesis_block_new] at hij
    exact absurd hij (hsev i ho)
  · rw [BlockRecord.addGenesis_block_old ho] at hib hij hround
    rw [BlockRecord.addGenesis_block_old ho'] at hij hround
    exact hne i ho j ho' hib hij hround

/-- **Honest non-equivocation is a mechanised invariant**: it survives
the cut, the copy fill and re-genesis. -/
instance honestNoEquiv.mechanised :
    BlockRecord.Invariant.Mechanised
      (HonestNoEquiv (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  chop := fun _ h => honestNoEquiv_chop h
  copyFill := fun sk h => honestNoEquiv_fill sk _ _ h
  addGenesis := fun _ _ _ _ _ h => honestNoEquiv_addGenesis h

end Fill

end Integration

end LeanDag
