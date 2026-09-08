import LeanDag.Properties.Arcs.Record
import LeanDag.Nemo.Properties
/-!
# Garbage collection, crash recovery and re-genesis for Nemo

Nemo's universe is the block record at Nemo's own validity, a majority
parent quorum with non-equivocation asked of every validator, so its
carrier reads as records by the identity maps and every mechanism cell
is `Arcs/Record.lean` at that instance (`Nemo.ValidWrt.mechanised` and
`.copyStable`, `Nemo/Basic.lean`). Nemo has no self-parent clause, so
the fill takes the copy reading, the filled block's validity being the
donor's verbatim.
-/

namespace LeanDag

namespace NemoProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Nemo's carrier, on the record**: every map the identity. -/
def onRecord :
    (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).OnRecord Nemo.ValidWrt (Finset.univ : Finset Validator)
      BlockRecord.Any where
  toRec := fun U => U
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

/-! The cut, the copy fill and re-genesis at Nemo's universe are the
record's, through `onRecord`: `onRecord.chop`,
`onRecord.copyFill`, `onRecord.addGenesis`. -/

end NemoProperties

end LeanDag
