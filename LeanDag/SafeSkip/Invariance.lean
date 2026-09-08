import LeanDag.SafeSkip.Basic
import LeanDag.Mysticeti.Liveness
/-!
# The lifted view, and reachability across the fill

What is left of the bespoke verdict transport across a Safe Skip fill.
The transport itself, that every verdict a view reached before the fill
re-derives in the extension, is `Arcs/SafeSkip.lean`'s
`decided_fill_of_persist`, `Persist` applied. Two things remain because
other files read them: the view of the extension a pre-crash view
lifts to, consumed by `Arcs/SafeSkip.lean` and the hybrid, Odontoceti
and Mahi-Mahi cells; and that reachability from an old block never
leaves the old ids, consumed by the exposure and coverage arcs.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

namespace SkipMsg

variable (sk : SkipMsg U)

/-- A view of `U` is a view of the extension, unchanged: its blocks are
old, and old references are preserved. -/
def liftView (V : View Validator BlockId Payload U) :
    View Validator BlockId Payload sk.skipFill :=
  BlockRecord.View.lift V

@[simp] theorem liftView_ids (V : View Validator BlockId Payload U) :
    (sk.liftView V).ids = V.ids := rfl

/-- Reachability from an old block never leaves the old ids, in either
universe, and coincides between them. -/
theorem reaches_fill_old {a b : BlockId} (ha : a ∈ U.ids) :
    Reaches sk.skipFill a b ↔ b ∈ U.ids ∧ Reaches U a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | tail _ hstep ih =>
        obtain ⟨hbo, hr⟩ := ih
        unfold RefStepFrom at hstep
        rw [sk.skipFill_block_old hbo] at hstep
        exact ⟨U.complete _ hbo _ hstep, hr.tail hstep⟩
  · rintro ⟨_, h⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hr hstep ih =>
        have hbo : b ∈ U.ids := by
          clear ih hstep
          induction hr with
          | refl => exact ha
          | @tail x y _ hstep' ih' => exact U.complete _ ih' _ hstep'
        refine (ih hbo).tail ?_
        unfold RefStepFrom
        rw [sk.skipFill_block_old hbo]
        exact hstep

end SkipMsg

end LeanDag
