import LeanDag.Properties.Arcs.Record
import LeanDag.FinWhale.Carrier
/-!
# Garbage collection, crash recovery and re-genesis for FinWhale

FinWhale's DAG is the block record at `ValidHere`, so its carrier reads
as records by the identity, and every mechanism cell is
`Arcs/Record.lean` at that instance (`ValidHere.mechanised` and
`ValidHere.copyStable`, `FinWhale/Model/Rule.lean`). The fill copies
only the donor's references, adding no self reference:
`ValidHere.leader_clause` would object to grafting the anchor's
reference set onto the donor's.
-/

namespace LeanDag

namespace FinWhaleProperties

open LeanDag.Properties
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **FinWhale's carrier, on the record**: the identity on universes,
repacking on views. -/
def onRecord :
    (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).OnRecord ValidHere (Correct : Finset Validator)
      BlockRecord.Any where
  toRec := fun D => D
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

/-! The cut, the copy fill and re-genesis at FinWhale's DAG are the
record's, through `onRecord`. -/

end FinWhaleProperties

end LeanDag
