import LeanDag.FinWhale.Anchor
import LeanDag.FinWhale.Procedure.Model.Verdict
import LeanDag.FinWhale.Model.Decided
import LeanDag.Common.Anchored.Bounded
/-!
# FinWhale — the reverse pass lands in the relation

`decided_of_wellFormed` (`View.lean`) says every verdict a well-formed
assignment reaches is a derivation of `Model/Decided.lean`'s anchored
relation; this file supplies what it reads of the tie-break.
`IndirectCommit` mentions no view, and `chooseLeast` takes only the
anchor and the round, so it is the relation's choice at its one rung:
sound (`chooseSound_least`) and least (`chooseLeast_least`).
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Slots Validator}

omit [DecidableEq BlockId] in
/-- Two decided verdicts with one option are one verdict. -/
theorem Verdict.optOf_inj {w w' : Verdict BlockId} (h : w ≠ Verdict.undecided)
    (h' : w' ≠ Verdict.undecided) (he : w.optOf = w'.optOf) : w = w' := by
  cases w <;> cases w' <;> simp_all [Verdict.optOf]

section Rule

variable [LinearOrder BlockId]

@[simp] theorem finWhaleAnchored_wave :
    (finWhaleAnchored Validator BlockId Payload).wave = 2 := rfl

@[simp] theorem finWhaleAnchored_rungs :
    (finWhaleAnchored Validator BlockId Payload).rungs = 1 := rfl

open scoped Classical in
/-- The exhibited tie-break names only candidates, and one whenever
there is one. -/
theorem chooseSound_least : ChooseSound S D (chooseLeast S D) where
  sound := by
    intro A r b h
    simp only [chooseLeast] at h
    split at h
    · rename_i hne
      have hb : (((slotBlocks S D r).filter (fun b => IndirectCommit S D A r b)).min' hne) = b :=
        Option.some.inj h
      have hmem := Finset.min'_mem ((slotBlocks S D r).filter (fun b => IndirectCommit S D A r b)) hne
      rw [hb] at hmem
      exact (Finset.mem_filter.1 hmem).2
    · exact absurd h (by simp)
  total := by
    intro A r ⟨b, hb⟩
    have hne : ((slotBlocks S D r).filter (fun b => IndirectCommit S D A r b)).Nonempty :=
      ⟨b, Finset.mem_filter.2 ⟨hb.1, hb⟩⟩
    refine ⟨((slotBlocks S D r).filter (fun b => IndirectCommit S D A r b)).min' hne, ?_⟩
    simp only [chooseLeast, dif_pos hne]

open scoped Classical in
/-- And what it names is the least candidate: the relation's choice at
the rung. -/
theorem chooseLeast_least {A : BlockId} {r : ℕ} {b : BlockId}
    (h : chooseLeast S D A r = some b) :
    (finWhaleAnchored Validator BlockId Payload).Least (S := S) D A 0 r b := by
  intro L' hL' hind hlt
  simp only [chooseLeast] at h
  split at h
  · rename_i hne
    have hb := Option.some.inj h
    have hmem : L' ∈ (slotBlocks S D r).filter (fun b => IndirectCommit S D A r b) :=
      Finset.mem_filter.2 ⟨hind.1, hind⟩
    have := Finset.min'_le _ L' hmem
    rw [hb] at this
    exact absurd hlt (not_lt.mpr this)
  · exact absurd h (by simp)

end Rule

end FinWhale

end LeanDag
