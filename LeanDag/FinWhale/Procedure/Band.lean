import LeanDag.FinWhale.View
import LeanDag.Common.Anchored.Band
import LeanDag.FinWhale.Band
/-!
# FinWhale — the band lemma the tie-break needs

Procedure side: these mention a verdict assignment or the reverse pass.
-/

namespace LeanDag
namespace FinWhale
open LeanDag.Properties
variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D D' : Dag Validator BlockId Payload}
variable [LinearOrder BlockId]

namespace Band

variable {lo hi g g' : ℕ}
variable {R : AnchoredRule Validator BlockId Payload ValidHere (Correct : Finset Validator)}
variable (hb : AgreeBand R.toDagRule D D' lo hi g g')
include hb

open scoped Classical in
/-- **And so the tie-break is the same function**: both the slot and the
rule are settled by the band, so the two sides filter the same set and
take the same minimum. -/
theorem chooseLeast_band [LinearOrder BlockId] (hrk : S.slotRound k + g = S'.slotRound k' + g')
    (hlk : S.leader k = S'.leader k') (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g + 2 ≤ hi)
    {A : BlockId} (hAD : A ∈ D.ids) (hAlo : lo ≤ (D.block A).round + g)
    (hAhi : (D.block A).round + g ≤ hi) :
    chooseLeast S' D' A k' = chooseLeast S D A k := by
  have hset : (slotBlocks S' D' k').filter (fun b => IndirectCommit S' D' A k' b) =
      (slotBlocks S D k).filter (fun b => IndirectCommit S D A k b) := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      have hd := (indirectCommit_iff hb hrk hlk h1 h2 hAD hAlo hAhi b).1 h
      exact ⟨hd.1, hd⟩
    · rintro ⟨-, h⟩
      have hd := (indirectCommit_iff hb hrk hlk h1 h2 hAD hAlo hAhi b).2 h
      exact ⟨hd.1, hd⟩
  unfold chooseLeast
  simp only [hset]

end Band

end FinWhale

end LeanDag
